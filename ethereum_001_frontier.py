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

# contract's code can execute from a message call or from internal execution
# sender address can be recovered from a tx, see appendix F function S(T)

# transaction collapse function
# prepare tx for RLP
def L_T(T):
  if not T.t:
    return (T.n, T.p, T.g, T.t, T.v, T.i, T.w, T.r, T.s)
  else:
    return (T.n, T.p, T.g, T.t, T.v, T.d, T.w, T.r, T.s)

# transaction validity function
# this function name is not given in the yellowpaper, so we call it valid_transaction()
def valid_transaction(T):
  if type(T.n)==int and 0<=T.n and T.n<2**256 and \
     type(T.v)==int and 0<=T.v and T.v<2**256 and \
     type(T.p)==int and 0<=T.p and T.p<2**256 and \
     type(T.g)==int and 0<=T.g and T.g<2**256 and \
     type(T.w)==int and 0<=T.w and T.w<2**5 and \
     type(T.r)==int and 0<=T.r and T.r<2**256 and \
     type(T.s)==int and 0<=T.s and T.s<2**256 and \
     type(T.t)==bytes and (len(T.t)==0 or len(T.t)==20) and \
     type(T.i)==bytes and type(T.d)==bytes:     # no length restrictions on T.i and T.d
    return True
  else:
    return False


###############
# 4.3 The Block

# H denotes block header
# T denotes list of transactions
# U denotes ommers, but book's definition in section 4.3 is too strict, use 11.3

# H denotes an instance of BlockHeader
class BlockHeader:
  def __init__(self, parentHash, ommersHash, beneficiary, stateRoot, transactionsRoot, receiptsRoot, logsBloom, difficulty, number, gasLimit, gasUsed, timestamp, extraData, mixHash, nonce):
    self.p=     parentHash      # KEC(parent's block header)
    self.o=     ommersHash      # KEC(uncle block header list)
    self.c=     beneficiary     # miner's address
    self.r=     stateRoot       # world state root hash
    self.t=     transactionsRoot    # root hash of trie of txs
    self.e=     receiptsRoot    # root hash of trie of receipts
    self.b=     logsBloom       # bloom filter of logs, see below
    self.d=     difficulty      # integer difficulty of this block
    self.i=     number          # number of ancestor blocks, including genesis
    self.l=     gasLimit        # current gas limit for a block
    self.g=     gasUsed         # total gas used in this block
    self.s=     timestamp       # unix time()
    self.x=     extraData       # arbitrary 32 bytes
    self.m=     mixHash         # 32 byte proof of work
    self.n=     nonce           # 8 byte value used for mining

# B will be used as an instance of Block
class Block:
  def __init__(self, header, transactions, ommers, receipts, totalDifficulty):
    self.H=     header          # instance of BlockHeader
    self.T=     transactions    # list of transactions
    self.U=     ommers          # list of ommer headers
    # rest is not in the spec, but later associated with the block
    self.R=     receipts        # list of receipts, indexed by corresponding tx index
    self.t=     totalDifficulty # total difficulty, which is sum of difficulties from genesis, needed in section 10


# 4.3.1 Transaction receipt

# B.R denotes block B's tx reciepts
# B.R[i] denotes the ith tx receipt
# receipts hash root is from index-keyed trie of reciepts

# R denotes an instance of Receipt
class Receipt:
  def __init__(self, cumulativeGasUsed, bloomFilterFromLogs, logs, statusCode, preRoot):
    self.u=     cumulativeGasUsed       # cumulative gas used in block after this tx
    self.b=     bloomFilterFromLogs     # bloom filter for logs
    self.l=     logs                    # sequence of instances of Log (see below) from execution of this tx 
    self.z=     statusCode              # status code returned by this tx
    # rest is not in the spec, but later associated with the receipt, at least for frontier
    self.preRoot=   preRoot             # state root after the end of previous tx

# receipt collapse function
# prepare receipt for RLP
def L_R(R):
  return (R.preRoot, R.u, R.b, R.l) # TODO: in a later hardfork, first element is bytes([0]*32)

# this function name is not in the yellowpaper
def receipt_validity(R):
  if type(R.z)==int and 0<=R.z and \
     type(R.u)==int and 0<=R.u and \
     type(R.b)==bytes and len(R.b)==256 and\
     type(R.l) in {list, tuple} and validity_logs(R.l):
    return True
  else:
    return False


# O denotes an instance of Log
class Log():
  def __init__(self):
    self.a=     loggersAddress
    self.t=     topicsList
    self.d=     dataBytes

def validity_logs(O):
  return True # TODO see yellowpaper

# bloom filter function over logs
# note: name collision with function in appx H.1 involving EVM memory
def M(O):
  ret=bytes([0]*256)
  for x in {O.a}+O.t:
    ret = ret | M3_2048(x) #TODO what is bitwise or?
  return ret

def M3_2048(x):
  y='0'*2048
  for i in [0,2,4]:
    y[B(x,i)]=1
  return y.bytes() #TODO a guess

def B(x,i,y):
  return m(x,i)

def m(x,i):
  return int(KEC(x)[i,i+1]) % 2048


# 4.3.2 Holistic Validity

# TODO

# explains values for H.r, H.o, H.t, H.e, H.b
# e.g. H.r = TRIE(L_S(Pi(sigma,B)))

# note: the function p has name collision with section 4.1


# 4.3.3 Serialization

# header collapse function
# prepare receipt for RLP
def L_H(H):
  # TODO
  return ()

# block collapse function
# prepare block for RLP
def L_B(B):
  # TODO
  return ()

# TODO: more stuff like header types

# 4.3.4 Block Header Validity

# TODO
def V(H):
  return True




######################
# 5. Gas and Payment #
######################





############################
# 6. Transaction Execution #
############################

# Upsilon (greek letter 𝚼) is the state transition function, defines the execution of a tx

# initial tx validity tests:
# (1) tx is well-formed RLP (no trailing bytes)
# (2) valid signature
# (3) valid nonce
# (4) gas limit >= initial used gas
# (5) sender's balance >= up-front payment v_0


# 6.1 Substate

# transaction execution accrues info which is acted upon immediately following the tx

# accrued transaction substate
# A denotes an instance
class AccruedSubstate:
  def __init__(self,self_destruct_set,log_series,touched_accounts,refund_balance):
    self.s = self_destruct_set  # accounts which will be discarded following tx's completion
    self.l = log_series         # series of indexed checkpoints in VM code execution
    self.t = touched_accounts   # set of touched accts, empty ones will be deleted, not in frontier
    self.r = refund_balance     # from SSTORE to set from nonzero to zero, partially offsets the execution cost

# empty accrued substate
def A0():
  return AccruedSubstate(set(),[],set(),0)


# 6.2 Execution

# g_0 is the intrnisic gas, required to be paid before execution
def g_0(T):
  ret = 0
  #print("g_0",T.i,T.d,T.i+T.d)
  for i in T.i+T.d:
    if i==0:
      ret += G["txdatazero"]
    else:
      ret += G["txdatanonzero"]
  if not T.t:
    #ret += G["txcreate"]              # not in frontier
    pass
  ret += G["transaction"]
  return ret

# up-front cost
def v_0(T):
  return T.g*T.p+T.v

def transaction_validity(sigma,B,T):
  # return values: whether tx is valid, and also senderaddy (which is expensive to recover so we do it once)
  ST = S(T)     # recover sender address
  if (ST and
      ST in sigma and
      T.n == sigma[ST].n and        # nonce mismatch
      g_0(T) <= T.g and          # intrinsic gas (tx + creation + calldata cost) <= tx gas limit
      v_0(T) <= sigma[ST].b and     # up-front cost unavailable
      T.g <= B.H.l-l(B.R).u):    # tx gas limit <= block gas limit - gas used so far in this block
    return True, ST
  else:
    return False, ST

debug_Upsilon = 1
# execute a tx, both message call and contract creation
def Upsilon(sigma,
            B,      # current block, not in spec for frontier
            T,      # current tx
            recentblocks): # not in spec, dictionary with 256 recent blocks used by BLOCKHASH
  if verbose: print("Upsilon()")
  #print("Upsilon()")
  #print(L_T(T))
  #print("price,limit,to,value",T.p,T.g,T.t.hex(),T.v)

  # 1. tx validity, including recovering sender which is expensive
  valid, senderaddy = transaction_validity(sigma,B,T)
  if not valid:
    print("Upsilon() ERROR transaction invalid")
    return sigma, 0, [], 2, A0()  # TODO: fourth val is error code for invalid sig

  # there can't be invalid tx after this point, but can be errors like OOG

  #if 1:
  if debug_Upsilon:
    print("Upsilon() Balances before:")
    from_ = senderaddy
    to = T.t
    print("Upsilon() from",from_.hex(), sigma[from_].b, sigma[from_].n)
    print("Upsilon() to", to.hex(), end="")
    if to in sigma:
      print(" ",sigma[to].b)
    else:
      print(" 0")
    print("Upsilon() miner", B.H.c.hex(), end="")
    if B.H.c in sigma:
      print(" ",sigma[B.H.c].b)
    else:
      print(" 0")
    print("Upsilon() up-front cost", T.g*T.p)

  # 2. gas and tx stuff
  T.o = senderaddy # original transactor
  # in yellowpaper, sigma_0, sigmastar, sigmaprime are the "checkpoint states". But earlier states are never needed again, so there is no need to checkpoint. So we just rename the variable sigma. Reversion checkpoints are needed inside Lambda() and Omega().
  sigma_0 = sigma
  # update nonce and balance
  sigma_0[senderaddy].n += 1 # increment nonce
  sigma_0[senderaddy].b -= T.g*T.p # pay up-front costs
  g = T.g-g_0(T) # gas remaining for this tx
  print("Upsilon() gas remaining after up-front costs",g)

  # 3. execute transaction to get provisional state sigma_p, remaining gas gprime, accrued substate A, status code z
  if not T.t: # contract creation, bool arg not in frontier, z retrun not in frontier
    sigma_P,gprime,A,z,_ = Lambda(sigma_0,senderaddy,T.o,g,T.p,T.v,T.i,0,True,B.H,recentblocks)
    #print("ret from Lambda",sigma_P=={},gprime,A,z)
    #sigma_P,gprime,A,z = sigma_0,max(0,g-G["txcreate"]),A0(),1
    #print("ret from Lambda",sigma_P=={},gprime,A,z)
  else: # message call, bool arg not in frontier, z return not in frontier, one of the T.v not in frontier I think
    sigma_P,gprime,A,z,_ = Omega(sigma_0,senderaddy,T.o,T.t,T.t,g,T.p,T.v,T.v,T.d,0,True,B.H,recentblocks)
  # ignore the fifth return value, which is output bytearray which is not needed here

  # 4. handle gas payment and refund
  # increment refund counter for self-destructed accounts
  #A_rprime = A.r
  #for i in A.s:
  #  A_rprime += R["selfdestruct"]   # in frontier, this is done in function SUICIDE
  # determine gas refund gstar, capped by half of the total amount used T.g-gprime
  #gstar = gprime + min((T.g-gprime)//2,A_rprime)
  print("Upsilon (T.g-gprime)//2, A.r",(T.g-gprime)//2,A.r)
  gstar = gprime + min((T.g-gprime)//2,A.r)
  # checkpoint, but we don't checkpoint, just shallow copy
  sigmastar = sigma_P
  # apply gas payment to create pre-final state
  sigmastar[senderaddy].b += gstar*T.p
  m = B.H.c # miner's address
  if m not in sigmastar:
    sigmastar[m] = Account(0,0,TRIE({}),KEC(b''),b'',StateTree(),m)
  sigmastar[m].b += (T.g-gstar)*T.p
  print("miner gets",(T.g-gstar)*T.p)

  # 5. create final state sigmaprime by deleting all accounts in the self-destruct set A.s or that are touched and empty
  sigmaprime = sigmastar
  for addy in A.s:  # self-destruct set                 # note: if miner is in self-destruct set, then delete it too, this could be an edge-case for bugs
    #print("deleting",addy.hex())
    del sigmaprime[addy]
  # dead stuff is not in frontier
  #for addy in A.t:  # touched accts
  #  if DEAD(sigmaprime, addy): # check touched accts for being dead
  #    if addy in sigmaprime:
  #      sigmaprime.removed.add(addy)
  #      del sigmaprime[addy]
  # note: this stuff is supposedly needed later for receipts, state validation, and nonce validation. So just append it to the output, and append A too
  Upsilong = T.g-gstar  # total gas used in tx
  Upsilonl = A.l        # log items from tx
  Upsilonz = z          # status codes from tx, not in frontier

  #if 1: #debug_Upsilon:
  if debug_Upsilon:
    print("Upsilon() gas","g_0(T)",g_0(T),"g",g,"T.g,T.p,T.g*T.p",T.g,T.p,T.g*T.p,"gprime",gprime,"gstar",gstar,"Upsilong",Upsilong)

    print("Upsilon() Balances after:")
    print("Upsilon() from_",from_.hex())
    if from_.hex()[0:2]=="3d":  # debugging 49018
      print("Upsilon() from",sigmaprime[from_].b)
      #sigmaprime[from_].b = 0x43d67c65ceb4a82e
      #print("Upsilon() from",sigmaprime[from_].b)
    print("Upsilon() from",from_.hex(), sigmaprime[from_].b, sigmaprime[from_].n)
    print("Upsilon() to", to.hex(), end="")
    if to in sigmaprime:
      print("  ",sigmaprime[to].b)
    else:
      print("  -")
    print("Upsilon() miner", B.H.c.hex(), end="")
    if B.H.c in sigmaprime:
      print(" ",sigmaprime[B.H.c].b)
    else:
      print(" 0")


  return sigmaprime, Upsilong, Upsilonl, Upsilonz, A




########################
# 7. Contract Creation #
########################

debug_Lambda = 1

# Lambda (i.e. greek letter 𝚲) is the contract creation function
# note: spec has typo, we return five values
def Lambda(sigma,   # snapshot state and temporary state
           s,       # sender address
           o,       # original transactor
           g,       # available gas
           p,       # gas price
           v,       # endowment
           i,       # EVM init code bytearray
           e,       # present depth of message-call/contract-creation stack
           w,       # permission to modify the state, not in frontier
           H,       # not in spec, block header info for opcodes COINBASE, TIMESTAMP, NUMBER, DIFFICULTY, GASLIMIT
           recentblocks): # not in spec, dictionary with 256 recent blocks used by BLOCKHASH
  # returns: new state sigmaprime, remaining gas gprime, accrued substate A, error codes z, and output bytearray o_, but z is not part of frontier, not sure about o_
  if verbose: print("Lambda()",g,v,p)
  #print("Lambda()")
  if debug_Lambda:
    print("Lambda()",g,p,v)

  # 1. compute address of new contract
  sender = sigma[s]
  a = KEC(RLP((s,sender.n-1)))[12:32]
  if debug_Lambda:
    print("Lambda() created address",a.hex())
    print("Lambda() created address already in state",a in sigma)

  # 2. get account's pre-existing balance, if any
  #   note: the new address can have preexisting value, e.g precompute where contract will be created, then send money there, then create the account, but the account should have nonce 0 unless there is a hash collision
  if a in sigma:
    vprime = sigma[a].b
  else:
    vprime = 0

  # 3. create mutated state sigmastar as a deepcopy of sigma (we deviate from spec and deepcopy only the active state)

  # 4. increment/decrement receiver's/sender's balances by value sent
  # create/wipe account at new address
  sigma[a] = Account(0, v+vprime, TRIE({}), KEC(b''),b'',StateTree(),a)     # nonce changes to 1 in homestead
  #acct = sigmastar[a]
  #print("new contract",acct.n,acct.b,acct.s,acct.c)
  #print(v,vprime,type(v),type(vprime),v+vprime)
  # note: if there is an existing account at a, will overwrite it here or when applying checkpoint state
  # decrement sender balance, overwrite previous in preparation for revert
  sigma[s].b -= v #= Account(sender.n,sender.b-v,sender.s,sender.c,sender.bytecode,sender.storage,sender.address)
  """ not in frontier
  if s not in sigmastar and v==0:
    # note: when is this possible? The case of both s not in state and v!=0 is impossible? Anyway, if account at s missing, then it is already empty. This may be a source of edge cases and bugs.
    pass
  else:
    #sender = sigmastar[s]
    astar = Account(sender.n,sender.b,sender.s,sender.c,sender.bytecode,sender.storage,sender.address)
    astar.b -= v
  """

  sigmastar = sigma.copy() #.checkpoint()  # TODO: checkpoint

  # 5. Execute init code
  #print("code",i.hex())
  I = ExecutionEnvironment(a,o,p,b'',s,v,i,H,e,w,recentblocks)  # different in frontier
  sigmastarstar,gstarstar,A,o_ = Xi(sigmastar,g,I,(s,a))         # (s,a) not in frontier
  # returns state, remaining gas, accrued substate, bytecode
  print("Xi() output",sigmastarstar=={},gstarstar,A,o_.hex())

  # 6. fill in rest of account
  #print("Lambda() code",o_)
  #print("Lambda() ok",len(sigmastarstar))
  #sigmastarstar[a].c = KEC(o_)
  #sigmastarstar[a].bytecode = o_


  # 7. prepare return values based on whether there was an exception
  #   if exception, then the operation should have no effect on sigma leaving it how it was prior to attempting creation
  #   if no exception, then remaining gas is refunded, and now-altered state is allowed to persist. note: I think refund is just returning it.
  c = G["codedeposit"]*len(o_)  # code deposit cost
  print("Xi()",c,gstarstar)
  if not sigmastarstar:
    gprime = 0
  elif gstarstar<c:     # not enough gas to pay for code
    gprime = gstarstar
  else:
    gprime = gstarstar - c

  #gprime = gstarstar    # debugging
  print("Lambda() gprime c",gprime,c)
  if not sigmastarstar:
    print("Lambda() not sigmastarstar")
    sigmaprime = sigma
    #print("account:",a.hex(),sigmaprime[a].storage,sigmaprime[a].c.hex(),sigmaprime[a].bytecode.hex())
    #print("account n b s c bytecode storage address:",sigmaprime[a].n, sigmaprime[a].b, sigmaprime[a].s.hex(), sigmaprime[a].c.hex(),sigmaprime[a].bytecode.hex(),sigmaprime[a].storage,sigmaprime[a].address.hex())
    # in block 46402, create an account, but it runs out of gas, so delete it, this is for frontier
    print("Lambda()",a in sigmaprime)
    if a in sigmaprime:     # added at 46402
      del sigmaprime[a]     # added at 46402
      sigma[s].b += v       # added at 48511 or 48512
    if 0:   # for debugging
      sigmaprime[a].n = 0
      sigmaprime[a].c = KEC(o_)
      sigmaprime[a].bytecode = o_
      sigmaprime[a].storage = StateTree()
  elif gstarstar<c:     # not enough gas to pay for code
    print("Lambda() gstarstar<c")
    sigmaprime = sigmastar
    o_=bytearray([])      # added at 49018
    sigmaprime[a].c = KEC(o_)
    sigmaprime[a].bytecode = o_
    #sigmaprime[a].n = 1
    #sigmaprime[a].storage = StateTree()
    print("Lambda() new addy:",a.hex())
    print("  nonce balance code",sigmaprime[a].n, sigmaprime[a].b, sigmaprime[a].c.hex())
    print("  storage",{k.hex():sigmaprime[a].storage[k].hex() for k in sigmaprime[a].storage})
  else:
    sigmaprime = sigmastarstar
    sigmaprime[a].c = KEC(o_)
    sigmaprime[a].bytecode = o_

  #print("Lambda",[(k.hex(),v.hex()) for k,v in sigmaprime[a].storage.items()])

  if debug_Lambda:
    if a in sigmaprime:
      print("New account:")
      acct = sigmaprime[a]
      print("",a.hex(), acct.b, acct.n, acct.s.hex(), acct.c.hex(), acct.bytecode.hex())

  """ different in frontier
  F = ((not sigmastarstar) and o_==b'') or gstarstar<c or len(o_)>24576     # TODO: I think that 24576 was introduced in spurious dragon
  gprime = 0 if F else gstarstar-c      # final gas remaining
  if F:
    sigmaprime = sigma      # recover with deep-copy
  elif DEAD(sigmastarstar,a):
    sigmaprime = sigmastarstar
    if a in sigmaprime:  # is this possible?
      del sigmaprime[a]
  else:
    sigmaprime = sigmastarstar
    sigmaprime[a].c = KEC(o_)
    sigmaprime[a].bytecode = o_
  """

  
  z = 0 if (not sigmastarstar) or gstarstar<c else 1  # status code, including whether OOG, note: why not use F?, z not in frontier
  return sigmaprime, gprime, A, z, o_    # z not in frontier

