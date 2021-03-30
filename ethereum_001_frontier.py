import json
import math
import crypto


verbose = 0
debug = 0


# This file implements some sections of the Ethereum yellowpaper.



##############################
# 2. The Blockchain Paradigm #
##############################

# sigma is the state, T is a transaction

# the Ethereum state transition function (STF)
#def Upsilon(sigma,T):
#  # defined in section 6.2
#   pass

# B is a block, which includes a list of transactions, see section 4.3

# the block-level state-transition function (called "state-accumulation function" in section 4.3.2)
#def Pi(sigma,B):
#  # defined in section 11.4
#  pass


# the block-finalization state transition function; rewards the miner
#def Omega(sigma,B):
#  # defined in section 9
#  pass



##################
# 3. Conventions #
##################

# lowercase Greek letters are state values
# sigma is the world state
# mu is the machine state

# uppercase Greek letters are functions which operate on the state
# e.g. Upsilon is the Ethereum STF

# keccak-256
def KEC(bytes_):
  return crypto.keccak256(bytes_)

# keccak-512
def KEC512(bytes_):
  return crypto.keccak512(bytes_)

# uppercase letters are functions or tuples
# e.g. C is the cost function
# e.g. T is a transaction
# can be subscripted
#   with uppercase subscript is component of tuple e.g. C_SSTORE
#   with component e.g. T.n is nonce of tx

# lowercase letters denote scalars and byte arrays (bold in yellowpaper)
# e.g. n is nonce
# e.g. greek delta is number of items required on stack for a give operation
# e.g. o is byte array output by a message call

# bold uppercase can be used for important values

# $\mathbb{N}$ is non-negative integers
# $\mathbb{B}$ is all byte sequences, see appx B
# $\mathbb{B}_{32}$ is all byte sequences of length 32
# $\mathbb{N}_{256}$ is non-negative integers less than 2^256, see section 4.3

# square brackets index components or subsequences of a sequence
# e.g. mu.s[0] is top of stack
# ellipses specify a range
# e.g. mu_m[0..31] is first 32 items of memory

# state sigma is sequence of accounts, use square brackets to access account by address

# if value takes intermediate values, first value is <blah>, modified value is <blah>', intermediate values are <blah>*, <blah>**, ..., <blah>'
# may also use alpha-numeric subscripts to denote intermediate values

# given function f, f* is f over a sequence, element-wise, see section 4.3

# last item of a sequence
def l(x):
  return x[len(x)-1]



######################################
# 4. Blocks, State, and Transactions #
######################################



#################
# 4.1 World State

# sigma (i.e. greek letter "𝛔") is the world state, maps storage tree addresses/keys to their Account/leaf instance
# world state is usually implemented with a "state database" of key-value pairs of hashes to their values
# we define our state tree as a dict: address or key -> leaf value, and as a root node as described in appx D
# The state tree includes the underlying tree, accessed through root_node, see appx D for how we implement the tree nodes
class StateTree(dict):
  def __init__(self, leafs={}, memoized_tree=None):
    dict.__init__(self, leafs)            # state leafs are in a dict
    self.memoized_tree = memoized_tree    # yellowpaper appx D suggests memoizing the tree and hashes
    #self.updated = set()                  # all changed leaf addresses/keys, useful when remerkleizing/rememoizing
  def checkpoint(self): # section 6.2 discusses checkpointing the state
    # a shallow copy of state leafs, but reuses existing memoized_tree
    # this is useful in preparation for revert, avoiding a full deep copy
    # this is expensive in space and time once the state gets big, since even a shallow copy of a big hash table is expensive, and must copy each one, including storage
    copied = StateTree(self.copy(), self.memoized_tree)
    if type(next(iter(self)))==Account: # if account tree, then also shallow copy each storage tree
      for k in self:
        copied[k].storage = copied[k].storage.copy()
    return copied
  def __setitem__(self, k, v):   # override setting with brackets, eg sigma[a] = my_account
    # deep copy modifiable parts, so can write in a revertable copy
    #if not super().__contains__(k):
    #  self.updated.add(k)
    if type(v)==Account:
      super().__setitem__(k, Account(v.n,v.b,v.s[:],v.c,v.bytecode,v.storage,v.address) )
    else:
      super().__setitem__(k,v[:])
  def __delitem__(self, key):   # override del, eg del sigma[a]
    #self[key] = None
    super().__delitem__(key)   # call parent classes del, since `del self[k]` would recurse

def StateTree_merkleize(sigma):
  for k in sigma:
    if sigma[k].storage and len(sigma[k].storage):
      print("StateTree_merkleize() at key",k.hex())
      sigma[k].s = TRIE(y(sigma[k].storage))
      print("StateTree_merkleize() ",sigma[k].s.hex())
  stateRoot = TRIE(y(sigma))
  #print("StateTree_merkleize() stateRoot",stateRoot.hex())
  return stateRoot

# a (i.e. the letter "a") denotes an Account instance
class Account:
  def __init__(self,nonce,balance,storageRoot,codeHash,bytecode,storage,address):
    self.n=         nonce       # number of txs sent or contract creations
    self.b=         balance     # number of wei
    self.s=         storageRoot # root hash of self.state
    self.c=         codeHash    # KEC of bytecode
    # the rest are not in the spec, but we need it
    self.bytecode=  bytecode    # bytecode executed when this account gets a message call, where bytecode is empty for non-contract account
    self.storage=   storage     # instance of StateTree, mapping mapping 256-bit keys -> 256-bit values
    self.address=   address     # 20-byte address

# a generic collapse function
def L_I(k,v):
  return KEC(k),RLP(v)

# collapse function for a 
def Lstar(func,keyvalpairs):
  ret = {}
  for key,val in keyvalpairs.items():
    pair = func(key,val)
    ret[pair[0]] = pair[1]
  return ret

# e.g. Lstar(L_I,sigma)

# simple account ("non-contract account") has codeHash of empty bytecode
# emptyset ("∅","non-existent") denotes when account address is not in the world state, which is different from EMPTY() below

# this is unused, instead implemented in appx D using functions BE, RLP, TRIE
def p(a,sigma):
  # note: maybe members .s and .c should have default values for non-contract account
  return KEC(a), RLP( (sigma[a].n, sigma[a].b, sigma[a].s, sigma[a].c) )

# world state collapse function
# this function seems useless
# the name "L_S" has a name collision with a function in appendix F, but we don't use this one so we let that one overwrite this one
def L_S(sigma):
  return {p(a) for a in sigma}

# account validity function
def v(x):
  if type(x.n)==int and 0<=x.n and x.n<2**256 and \
     type(x.b)==int and 0<=x.b and x.b<2**258 and \
     type(x.s)==bytes and len(x.s)==32 and \
     type(x.b)==bytes and len(x.b)==32:
    return True
  else:
    return False

# empty account
# note: contract accounts may have empty account state
def EMPTY(sigma,a):
  if sigma[a].c == KEC(b'') and sigma[a].n==0 and sigma[a].b==0:
    return True
  else:
    return False

# dead account
def DEAD(sigma,a):
  if a not in sigma or EMPTY(sigma,a):
    return True
  else:
    return False


#####################
# 4.2 The Transaction

# two types of txs: message call and contract creation

# T denotes an instance of Transaction
class Transaction:
  def __init__(self,nonce,gasPrice,gasLimit,to,value,v,r,s,init,data):
    self.n=     nonce       # number of txs send by the sender
    self.p=     gasPrice    # number of wei to pay per unit of gas
    self.g=     gasLimit    # maximum gas for this tx
    self.t=     to          # address of message call recipient, or empty bytearray for contract creation
    self.v=     value       # number of wei to be transferred to message call's recipient, or endowment of contract creation
    self.w=     v           # signature stuff, see appx F
    self.r=     r           # signature stuff, see appx F
    self.s=     s           # signature stuff, see appx F
    self.i=     init        # EVM bytecode for account initialisation procedure and returns the account code; arbitrarily long; empty for message call
    self.d=     data        # byte array specifying input data for message call; arbitrarily long; empty for contract creation
    # the following is not in spec, but referenced in spec
    self.o=     None        # original transactor




