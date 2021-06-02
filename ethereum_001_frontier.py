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


# 7.1 Subtleties

# while init is executing, new address exist but with no code
# - EXTCODESIZE should return 0, and CODESIZE should return len(i)
# - message calls to address should execute no code
# - SELFDESTRUCT in init, then account is deleted before tx is completed
# - STOP or returns empty, then account is zombie (no code, balance locked)


###################
# 8. Message Call #
###################

def Omega(sigma,# state 
          s,    # sender
          o,    # transaction originator
          r,    # recipient
          c,    # code's account address
          g,    # available gas
          p,    # gas price
          v,    # value to be transferred
          vtilde,   # value apparent in the execution context for the DELEGATECALL instruction, not in frontier
          d,    # input data, arbitrary length
          e,    # depth of message-call/contract-creation stack
          w,    # permission to modify state, not in frontier
          H,    # not in spec, block header info for opcodes COINBASE, TIMESTAMP, NUMBER, DIFFICULTY, GASLIMIT
          recentblocks): # not in spec, dictionary with 256 recent blocks used by BLOCKHASH
  # returns: new state sigmaprime, remaining gas gprime, accrued substate A, error codes z (not in frontier), and output bytearray o_
  if verbose: print("Omega()")
  #print("Omega()")

  # 1. checkpoint state in preparation for revert
  sigma_1prime = sigma.copy() #.checkpoint()
  #for a,b in zip(sigma,sigma_1prime):
  #  if a != b:
  #    print(a.hex,b.hex())
  #print("shallow copy",len(sigma_1prime),len(sigma))
  #print(TRIE(y(sigma)).hex(),TRIE(y(sigma_1prime)).hex())

  # 2. receiver update
  if s!=r:
    if r not in sigma_1prime: # note: if v==0 (e.g. in block 46382), should create account with balance 0, but this case is disallowed after frontier
      # create new acct
      a_1prime = Account(0,v,TRIE({}),KEC(b''),b'',StateTree(),r)
      sigma_1prime[r] = a_1prime
      #print("ok",r.hex(),sigma_1prime[r].b)
      #  elif r not in sigma and v==0:  # TODO: see a few lines above
      #  # receiver acct remains empty
      #  pass
    else:
      a_1prime = sigma_1prime[r]
      a_1prime = Account(a_1prime.n,a_1prime.b+v,a_1prime.s,a_1prime.c,a_1prime.bytecode,a_1prime.storage,a_1prime.address)
      sigma_1prime[r] = a_1prime
      #sigma_1prime[r].b += v

  #a = Account(0,v,TRIE({}),KEC(b''),b'',StateTree(),r)
  #sigma[r] = a_1prime
  #print(TRIE(y(sigma)).hex(),TRIE(y(sigma_1prime)).hex())

  # 3. sender update
  sigma_1 = sigma_1prime    # sigma_1 is "first transition state"
  if s!=r:
    #if s not in sigma_1 and v==0:
    #  pass #del sigma[s] but it already was not there
    #else:
    #  # note that sender must be in state
    # above comments not in frontier
    a_1prime = sigma_1[s]
    a_1prime = Account(a_1prime.n,a_1prime.b-v,a_1prime.s,a_1prime.c,a_1prime.bytecode,a_1prime.storage,a_1prime.address)
    sigma_1[s] = a_1prime
    #sigma_1[s].b -= v

  # 4. execute code, if any
  if c in sigma_1:
    code = sigma_1[c].bytecode
  else:
    code = b''
  I = ExecutionEnvironment(r,o,p,d,s,vtilde,code,H,e,w,recentblocks)
  t = (s,r) # this is not in frontier, also not in each call to Xi* below
  # execute!
  r_ = int.from_bytes(r,'big')
  if r_>4 or r_==0:
    sigmastarstar, gstarstar, A, o_ = Xi(sigma_1,g,I,t) # note: in frontier, A is suicide list s, but s gets subsumed int A later
  else:
    # call precompile, see appx E
    if r_==1:
      sigmastarstar, gstarstar, A, o_ = XiECREC(sigma_1,g,I,t)
    elif r_==2:
      sigmastarstar, gstarstar, A, o_ = XiSHA256(sigma_1,g,I,t)
    elif r_==3:
      sigmastarstar, gstarstar, A, o_ = XiRIP160(sigma_1,g,I,t)
    elif r_==4:
      sigmastarstar, gstarstar, A, o_ = XiID(sigma_1,g,I,t)
  #else:
  #  sigmastarstar, gstarstar, A, o_ = sigma_1, g, A0(), b''


  # 5. prepare return values
  #   if exception (exhausted gas, stack underflow, invalid jumpdest, invalid instruction) then no gas is refunded to caller and state is reverted to sigma
  #   if no exception, then gas refunded
  if not sigmastarstar:
    sigmaprime = sigma
  else:
    sigmaprime = sigmastarstar
  if not sigmastarstar: # and o_==b''   commented part not in frontier
    gprime = 0
  else:
    gprime = gstarstar

  z = 0 if sigmastarstar=={} else 1     # z is not in frontier

  #print("Omega() gas",g,gstarstar,gprime)
  #print("okok",s.hex(),sigmaprime[s].b)
  #print("okok",r.hex(),sigmaprime[r].b)

  return sigmaprime, gprime, A, z, o_


def XiECREC(sigma,g,I,t):
  print("XiECREC()")
  return sigma,g,AO(),bytes()

def XiSHA256(sigma,g,I,t):
  print("XiSHA256()")
  return sigma,g,AO(),bytes()

def XiRIP160(sigma,g,I,t):
  print("XiRIP160()")
  return sigma,g,AO(),bytes()

def XiID(sigma,g,I,t):
  print("XiID()")
  return sigma,g,AO(),bytes()





######################
# 9. Execution Model #
######################



############
# 9.1 Basics
  
# EVM
# stack of 256-bit items, 1024 max depth
# memory is byte-array addressed by 256-bit words
# storage is 256-bit words, each indexed by a 256-bit key, all initialized to zero
# bytecode in a ROM, readable through special opcodes
# exceptions for stack underflow, invalid instructions, out-of-gas, etc
#   halt, don't write state, send error to the spawning execution environment to handle


###################
# 9.2 Fees Overview

# Fees for three distinct circumstances, all prerequisites to operation:
# 1) to execute opcode, see appx G
# 2) payment for subordinate CREATE, CALL, CALLCODE
# 3) to increase memory usage
#    fee is proportional to range of memory used, to the smallest multiple of 32 bytes, paid just-in-time

# gas for rezeroing storage entry is free and given a qualified refund

# see appx H for gas costs


###########################
# 9.3 Execution Environment

# I denotes an instance of ExecutionEnvironment
class ExecutionEnvironment:
  def __init__(self, a, o, p, d, s, v, b, H, e, w, recentblocks):
    self.a = a  # code owner address
    self.o = o  # original sender address
    self.p = p  # gas price of original tx
    self.d = d  # input data
    self.s = s  # address which caused this execution
    self.v = v  # wei
    self.b = b  # bytecode being executed
    self.H = H  # block header, or at least what is needed for opcodes BLOCKHASH, COINBASE, TIMESTAMP, NUMBER, DIFFICULTY, GASLIMIT
    self.e = e  # depth of calls and creations before can execute the present
    self.w = w  # permission to modify state, not in frontier
    # the following are not in the spec, but we need it
    self.recentblocks = recentblocks    # dictionary with 256 recent blocks, used only by BLOCKHASH with 256 recent block headers, dictionary is indexed by blockhash

# note: after frontier, Xi should also have arg t and return z. In frontier, it returns s,l,r but we just return A for now
# def Xi(sigma, g, I):
#   return sigmaprime, gprime, A, o


########################
# 9.4 Execution Overview

# sigma (i.e. greek letter 𝝈) denotes system state
# mu (i.e. greek letter 𝛍) denotes machine state

# this section defines Xi() (i.e. greek letter Ξ)
# yellowpaper defines Xi() recursively
#   with function X()
#   and iterator function O() which defines a single cycle of the state machine
#   and function Z() which determines exceptional halting
#   and function H() which specifies the output data iff normal halting states
# yellowpaper suggests that a fast implementations of Xi() may be an iterative progression of sigma and mu

# notation: empty sequence () is different from emptyset. H outputs emptyset when execution is to continue and a sequence, possibly (), when execution halts

# Ξ in the yellowpaper, Xi is how this Greek letter is written in ASCII
def Xi(sigma, 
       g,       # available gas
       I,       # execution environment
       T):      # tuple (sender address, contract address), not in frontier
  if verbose: print("Xi()")
  #print("Xi()")
  #print("code", I.b.hex())
  mu = MachineState(g,0,bytearray([]),0,[],bytearray([]))   # note: MachineState is defined in 9.4.1
  sigmaprime,muprime,A,I,o = X_loop(sigma,mu,A0(),I)
  return sigmaprime, muprime.g, A, o


debug_X = 0
def X(sigma,mu,A,I):
  if debug_X: print("X()")
  #print("X()",mu.pc)
  # this function recurses until exception, REVERT, or there is an output
  o = H(mu,I)   # check whether we reached a non-exception halting opcode
  w_ = w(mu,I)  # get next opcode
  if debug_X: print("w_",w_,I.b.hex())
  if Z(sigma,mu,I): # exception
    if debug_X: print("X() exception Z()")
    #print("X() exception Z()")
    sigmaprime,muprime,A,I,o = {},mu,A0(),I,b''
    #elif w_==0xfd:    # REVERT     REVERT is not in frontier
    #if debug: print("X() REVERT")
    #print("X() REVERT")
    #muprime = mu
    #muprime.g = mu.g-C(sigma,mu,I)
    #sigmaprime,muprime,A,I,o = None,muprime,A0(),I,o
  elif o!=None:     # halt after this opcode
    if debug_X: print("X() halt after this opcode")
    #print("X() halt after this opcode")
    sigmaprime,muprime,A,I = O(sigma,mu,A,I) # execution cycle
    o = mu.o # this is awkward, call it again after O() now that mu.o is updated
    #print("X() code",o.hex())
  else:             # recurse 
    #print("w_",w_,"mu.pc",mu.pc,"I.b",I.b.hex(),"I.b[mu.pc]",I.b[mu.pc])
    if debug_X: print("X() recurse")
    #print("X() recurse")
    sigmaprime,muprime,A,I,o = X(*O(sigma,mu,A,I))
  return sigmaprime, muprime, A, I, o


# the book suggests doing X() in a loop, so implement that too, since recursion with long-running programs may exceed system limits, I think that python has limit recursion depth 500
def X_loop(sigma,mu,A,I):
  if debug_X: print("X_loop()")
  while 1:
    if debug_X: print("X_loop() iter",mu.g)
    o = H(mu,I)   # check whether we reached a non-exception halting opcode
    w_ = w(mu,I)  # get next opcode
    if Z(sigma,mu,I): # excepton
      print("X_loop() exception")
      sigma,mu,A,I,o = {},mu,A0(),I,b''
      break
    #elif w_==0xfd:    # REVERT     # not in frontier
    #  muprime = mu
    #  muprime.g = mu.g-C(sigma,mu,I)
    #  sigmaprime,muprime,A,I,o = None,muprime,A0(),I,o
    #  break
    elif o!=None:     # halt after this halting opcode
      sigma,mu,A,I = O(sigma,mu,A,I) # execution cycle
      o = mu.o     # this is awkward, call it again after O() so that mu.o is updated
      break
    else:
      sigma,mu,A,I = O(sigma,mu,A,I)
  return sigma, mu, A, I, o


# 9.4.1 Machine State.

# mu denotes an instance of MachineState
class MachineState:
  def __init__(self,g,pc,m,i,s,o):
    self.g =    g   # gas available
    self.pc =   pc  # program counter
    self.m =    m   # memory contents up to zero padding until size 2^256
    self.i =    i   # number of active words in memory, counting continuously from position 0
    self.s =    s   # stack contents
    # the rest are not officially in machine state, but the spec treats them as if they are
    self.o =    o   # return data, should be empty bytearray by default

# w is current instruction to be executed
def w(mu,I):
  if mu.pc<len(I.b):
    return I.b[mu.pc]
  else:
    return 0x00     # STOP


# 9.4.2 Exceptional Halting

# the exceptional halting function
debug_Z = 0
def Z(sigma, mu, I):
  if debug_Z: print("Z()")
  w_ = w(mu,I)
  if debug_Z:
    print("Z() w_",w_)
    print("Z() gas",mu.g)
    if w_ in EVM_opcodes:
      print("Z()",len(mu.s),EVM_opcodes[w_]["delta"],len(mu.s)<EVM_opcodes[w_]["delta"])
      print("Z()",len(mu.s),EVM_opcodes[w_]["delta"],)
    else:
      print("Z()",w_,"is an invalid opcode")
  if((w_ not in EVM_opcodes) or   # instruction is invalid (in spec, they check if delta_w is undefined)
     len(mu.s)<EVM_opcodes[w_]["delta"] or  # insufficient stack items 
     mu.g<C(sigma,mu,I) or      # insufficient gas, typo in yp, this goes after checking for insufficient stack items which C() depends on
     ( w_==0x56 and             # opcode is "JUMP", need JUMPDEST
       mu.s[-1] not in D_loop(I.b) ) or  # D(), defined below, is the set of valid jump destinations
     ( w_==0x57 and             # similar for JUMPI
       mu.s[-2] != 0 and 
       mu.s[-1] not in D_loop(I.b) ) or
     len(mu.s) - EVM_opcodes[w_]["delta"] + EVM_opcodes[w_]["alpha"] > 1024):    #or  # stack size > 1024
    # the following are not in frontier
    #( w_==0x3e and             # RETURNDATACOPY
    #  mu.s[-2] + mu.s[-3] > len(mu.o) ) or 
    #( ( not I.w ) and W(w_,mu) ) ):   # state modification attempted during static call
    if debug_Z: print("Z() returning True")
    if debug_Z: print("Z() val",mu.g<C(sigma,mu,I),mu.g,C(sigma,mu,I))

    return True
  else:
    if debug_Z: print("Z() returning False")
    return False

# W() is not in frontier
# check if this opcode does state modification
def W(w_,mu):
  if(w_ in {0xf0,0x55,0xff} or    # CREATE, SSTORE, SELFDESTRUCT
     ( 0xa0 <= w_ and w_ <= 0xa4 ) or  # LOG0 to LOG4; note: typo in yellowpaper gives ambiguous precedence of and
     ( w_ in {0xf1,0xf2} and mu.s[-3]!=0 ) ):   # CALL or CALLCODE with nonzero value transferred
    return True
  else:
    return False

# claim: if Z() returns False, then execution of instruction can't cause an exceptional halt
# I.e. there are no undefined exceptional halts. This needs proof.


# 9.4.3 Jump Destination Validity

# valid jump destinations are positions of JUMPDEST instruction
#   must not be in immediates of PUSH
#   must be in "explicitly" defined portion of code, not "implicitly" defined STOP operations that trail it

# TODO: do this at contract creation, store it with code

# return set of valid jump destinations
def D(c):
  return D_J(c,0)

# recursive helper of D
def D_J(c,i):
  if i >= len(c):
    return set()
  elif c[i] == 0x5b:    # JUMPDEST
    return set([i]).union(D_J(c,N(i,c[i])))
  else:
    return D_J(c,N(i,c[i]))

# get the next valid instruction position, skipping PUSH* immediates
def N(i,w_):
  #print("N()",i,hex(w_))
  if 0x60<=w_ and w_<=0x7f:   # PUSH1,PUSH2,...,PUSH32
    return i+w_-0x60+2
  else:
    return i+1

# Note: above D() is recursive, and python exceeds recursion here at depth 1000, so do it in a loop. Both versions seem to work, but D_loop() can handle >1000 jumpdests.
def D_loop(c):
  jumpdests = set()
  pc = 0
  while pc < len(c):
    if c[pc] == 0x5b:    # JUMPDEST
      jumpdests.add(pc)
    pc = N(pc,c[pc])
  return jumpdests


# 9.4.4 Normal Halting

# the normal halting function
def H(mu,I):
  w_ = w(mu,I)
  #print("H()",w_)
  if w_ in {0xf3}: #,0xfd}:      # RETURN, since 0xfd REVERT is not in frontier
    #print("H() RETURN")
    return mu.o              # H_RETURN(mu) is defined in appx H, opcode RETURN. We hard-code mu.o here which may be empty string since H() is called before RETURN opcode
  elif w_ in {0x00,0xff}:    # STOP,SELFDESTRUCT
    #print("H() STOP or SELFDESTRUCT")
    return bytearray([])
  else:
    return None


#########################
# 9.5 The Execution Cycle


# iterator function, defines single cycle of the state machine
debug_O = 1
counter = 0
def O(sigma, mu, A, I):
  global counter
  if debug_O:
    #print("O() counter",counter)
    pass
  counter+=1

  #print("O() gas begin",mu.g)

  # 1. get opcode
  w_ = w(mu,I)

  # 2. check stack, making sure that stack pops/pushes items with low index first then shifts indices
  # there is several stack assertions, which we omit because EVM does precisely what these assertions check
  # note: we must reduce gas, execute opcode, then adjust pc, in the following order, otherwise opcodes GAS and PC will break
  if debug_O:
    #print("full stack",mu.s)
    #print("full mem",mu.m.hex())
    #print("mem len",len(mu.m))
    #print("full mem",mu.m.hex())
    print(hex(w_)[2:],EVM_opcodes[w_]["mnemonic"],"\tstack,gas:",[mu.s[-1*i] for i in range(EVM_opcodes[w_]["delta"],0,-1)],"\t",mu.g,"\t->",end="")

  # 3. reduce gas; note: some opcodes reduce it further
  #print("O() gas before decrement",mu.g)
  mu.g = mu.g - C(sigma, mu, I) # note: this is repeated in 9.4
  #print("O() gas after decrement",mu.g)
  if mu.g<0:
    return {}, mu, A, I     # out-of-gas error

  # 4. execute opcode
  # execute opcode
  #input("Press Enter to continue...")
  #input()
  #print("O()",EVM_opcodes[w_]["description"],sigma,mu,A,I)
  sigmaprime,muprime,Aprime,I = EVM_opcodes[w_]["description"](sigma,mu,A,I)
  #print(" ",EVM_opcodes[w_]["mnemonic"],"mu.s:",[mu.s[-1*i] for i in range(1,1+EVM_opcodes[w_]["alpha"])])
  if debug_O:
    #print("O() stack",mu.s)
    if sigmaprime != {}:
      print("\t",[mu.s[-1*i] for i in range(EVM_opcodes[w_]["alpha"],0,-1)],mu.g)

  # note: if sigmaprime=={}, then there was an exception

  # 5. adjust program counter
  if w_ not in {0x56,0x57}: # if not JUMP or JUMPI
    muprime.pc = N(mu.pc,w_)
  else: 
    # JUMP and JUMPI already adjusted it
    pass

  #print("O() gas end",mu.g)

  return sigmaprime, muprime, Aprime, I



###################
# 10. Blockchaian # 
###################


# get total difficulty of the chain up to this block
# walks back and recursively sums difficulties
def total_difficulty(B,         # a block
                     blocks):   # this is not in the yellowpaper, but we need a dictionary of blocks
  Bprime = P(B.H,blocks)
  B_t = B.H.d + total_difficulty(Bprime,blocks)     # note: yellowpaper abuses notation, since B.t and B.d are not a part of a block, we assume B.d looks up difficulty from the header
  return B_t

# get parent block from this block header
# we give it an extra arg Blocks which is a dictionary
def P(H,            # a block header
      blocks):      # this is not in the yellowpaper, but we need a dictionary of blocks indexed by hash
  parent = blocks[H.p]
  return parent




##########################
# 11. Block Finalization #
##########################

def finalize_block(sigma,   # state
                   B,       # the block to validate
                   blocks): # dictionary:blockhash->block, need recent 8(6?) blocks to validate ommers, and up to 256 to execute BLOCKHASH
  # 1. validate ommers
  if not validate_ommers(B,blocks):
    return False
  # 2. validate transactions
  if not validate_transactions(B):
    return False
  # 3. apply rewards
  sigma = Omega_(B,sigma)  # apply block rewards, note: yellowpaper uses ntn l(sigma) to mean final state, which is bad notation
  # 4. verify state and nonce
  return sigma



#########################
# 11.1 Ommer Validation

def validate_ommers(B,          # the block to validate
                    blocks):    # not in spec, a hash-indexed dictionary with blocks needed to access parents of blocks
  return True   # TODO: delete this line when ready
  if(len(B.U)<=2 and   # max 2 uncles per block
     V(B.U) and        # V(H) is the header validity function in 4.3.4 TODO: unimplemented
     k(B.U,P(B.H,blocks).H,6) ): # is kin, note: P(H,blocks) returns parent
    return True
  else:
    return False

# the is-kin function
def k(U,H,n,blocks):    # extra arg blocks is dictionary:blockhash->block
  if n==0:
    return False
  else:
    return s(U,H,blocks) or k(U,P(H,blocks).H,n-1)

# the is-sibling function
def s(U,H,blocks):
  if(P(H,blocks)==P(U,blocks) and    # same parent
     H!=U and            # not equal TODO: should check each field
     U not in B(H).U):   # not an uncle already, TODO: should check each field. NOTE: this is ineffective, need separate rule to check whether the uncle is not already there.
    return True
  else:
    return False

# get block from header
def B(H,blocks):
  blockhash = KEC(RLP(L_H(H)))  # compute block hash TODO: test this
  return blocks[blockhash]


#############################
# 11.2 Transaction Validation

def validate_transactions(B):
  return True   # TODO: delete this line when ready
  if B.H.g == l(B.R).u:     # total gas used in header equals accumulated gas in last receipt
    return True
  else:
    return False


#########################
# 11.3 Reward Application

# block miner reward
R_block = 5*(10**18)    # 5000000000000000000 wei

# applies rewards
# note: collision with function Omega() in section 8 for message call
# this is called "block finalization function", but that is defined at the beginning of this section to call Omega_(), so yellowpaper should not call this the block finalization function.
def Omega_(B,sigma):
  sigmaprime = sigma
  #print("miner before block reward:",B.H.c.hex(), sigmaprime[B.H.c].b)
  if B.H.c not in sigma:
    aprime = Account(0,0,TRIE({}),KEC(b''),b'',StateTree(),B.H.c)
    sigmaprime[B.H.c] = aprime
  sigmaprime[B.H.c].b = sigma[B.H.c].b + int((1+len(B.U)/32)*R_block)   # TODO: does floating point ever screw up? Maybe should hard-code R_block/32
  #print("miner after block reward:",B.H.c.hex(), sigmaprime[B.H.c].b)
  for U in B.U:
    R = int((1+(U.i-B.H.i)/8)*R_block)  # TODO: does floating point ever screw up? Maybe should hard-code R_block/32
    if U.c not in sigmaprime and R==0:
      # don't think R==0 is possible after validate_ommers(), but anyway account at U.c is already empty so no need to remove it
      pass
    else:
      # must update U.c's balance
      # note: bug in yellowpaper, because it assumes U.c is in state already
      if U.c in sigmaprime:
        sigmaprime[U.c].b += R
      else:
        aprime = Account(0,R,TRIE({}),KEC(b''),b'',StateTree(),U.c)
        sigmaprime[U.c] = aprime
      #print("uncle reward",R,sigmaprime[U.c].b)
  return sigmaprime



###############################
# 11.4 State & Nonce Validation

# Gamma (i.e. Greek letter 𝚪) maps block to initiation state
# This function assumes we save the snapshot state before each block, which we don't save.
def Gamma(B):
  if P(B.H):
    # typo in yellowpaper, kern10pc should be removed
    sigma_0 = None  # TODO: I think this is the genesis state after genesis block 0
    return state_0
  else:
    roothash = P(B.H).H.r   # parent's state root hash
    sigma_i = None  # TODO: I think this is the state before block i
    return  sigma_i

# Phi (i.e. Greek letter 𝚽) is the block transition function, maps incomplete block B to complete block Bprime
# this function is useful only to mine a block, if fills in nonce, mixHash, stateRoot
def Phi(B):
  Bstar = B
  Bstar.H.r = r(Pi(Gamma(B),B))  # recall: H.r is stateroot, Pi is block-level state transiction function, I think that r(sigma) means root hash, TODO: implement Gamma()
  Bprime = B
  if not B.H.m: # if mixHash is missing, then mine one
    n=0
    while 1:
      x,m = PoW(Bstar_notH, n, d)
      if x<=(2**256)/H.d:  # recall: H.d is difficulty
        break
      n+=1
    Bprime.H.m = B.H.m   # recall: H.m is mixHash
    Bprime.H.n = n       # recall H.n is nonce
  return Bprime


# Pi (i.e. Greek letter 𝚷) is the block-level state-transition function (called "state-accumulation function" in section 4.3.2)
# this is the main function used to process a block
def Pi(sigma,B,recentblocks):
  # note: yellowpaper notation here is underspecified
  # Pi is sketched in section 2 to iterate over all transactions in the block, which we implement here
  # sigma_n = Gamma(B)  # we already have sigma, don't need Gamma(), yellowpaper is overconstrained
  # set up receipts
  R_u = 0   # cumulative gas used
  B.R.append(Receipt(R_u,b'',[],0,b'')) # dummy receipt before first tx, this shouldn't get merkleized?
  sigma_n = sigma
  for n in range(len(B.T)):
    T = B.T[n]
    preRoot = b'' # sigma_n.merkleize()   # TODO
    sigma_n, Upsilong, Upsilonl, Upsilonz, A = Upsilon(sigma_n,B,T,recentblocks)
    # where g is total gas used in tx, l_ is log items from tx, z is status code from tx
    #sigma_n.merkleize()
    R_u += Upsilong     # cumulative gas used
    logsBloomFilter = None # TODO: M(O) should be called, but this is not critical
    R = Receipt(R_u, logsBloomFilter, Upsilonl, Upsilonz, preRoot)
    B.R.append(R)   # the index is actually n+1, since we have a dummy recept before the first tx, must fix this before merkleize receipts
    # TODO: handle receipt wrt block B, either insert, compare, or ignore
  # finalize: validate ommers, validate txs, apply rewards, verify state and nonce
  finalize_block(sigma_n,B,recentblocks)
  # TODO: do PoW with Phi()
  #postRoot = sigma_n.merkleize()
  # TODO: handle postRoot wrt block B, either insert, compare, or ignore
  return sigma_n



#######################################
# Appendix B. Recursive Length Prefix #
#######################################


# main functions for encoding (RLP) and decoding (RLP_inv)
def RLP(x):
  if verbose: print("RLP(",x,")")
  if type(x) in {bytearray,bytes}:
    return R_b(x)
  elif type(x)==int:
    return RLP(BE(x))
  else: #list
    return R_l(x)

# binary encoding/decoding
def R_b(x):
  if verbose: print("R_b(",x,")")
  if len(x)==1 and x[0]<128:
    return x #bytearray([x[0] + 0x80])
  elif len(x)<56:
    return bytearray([128+len(x)])+x
  else:
    return bytearray([ 183+len(BE(len(x))) ]) + BE(len(x))  + x

# int to big-endian byte array
def BE(x):
  if verbose: print("BE(",x,")")
  if x==0:
    return bytearray([])
  ret = bytearray([])
  while x>0:
    ret = bytearray([x%256]) + ret
    x=x//256
  return ret

# list encoding/decoding
def R_l(x):
  if verbose: print("R_l(",x,")")
  sx=s(x)
  if len(sx)<56:
    return bytearray([192+len(sx)]) + sx
  else:
    return bytearray([ 247+len(BE(len(sx)))]) + BE(len(sx)) + sx

# for a list, recursively call RLP or RLP_inv
def s(x):
  if verbose: print("s(",x,")")
  sx = bytearray([])
  for xi in x:
    sx+=RLP(xi)
  return sx


# inverses of above

def RLP_inv(b):
  if verbose: print("RLP_inv(",b.hex(),")")
  if len(b)==0:
    return bytearray([0x80])
  if b[0]<0xc0 : # bytes
    return R_b_inv(b)
  else:
    return R_l_inv(b)

def R_b_inv(b):
  if verbose: print("R_b_inv(",b.hex(),")")
  if len(b)==1 and b[0]<0x80:
    return b #bytearray([b[0]-0x80])
  elif b[0]<=0xb7:
    return b[1:1+b[0]-0x80]
  else:
    len_BElenx = b[0] - 183
    lenx = BE_inv(b[1:len_BElenx+1]) #TODO lenx unused
    return b[len_BElenx+1:len_BElenx+1+lenx]

def BE_inv(b):
  if verbose: print("BE_inv(",b.hex(),")")
  x=0
  for n in range(len(b)):
    #x+=b[n]*2**(len(b)-1-n)
    x+=b[n]*2**(8*(len(b)-1-n))
  return x

def R_l_inv(b):
  if verbose: print("R_l_inv(",b.hex(),")")
  if b[0] <= 0xf7:
    lensx = b[0]-0xc0
    sx = b[1:1+lensx]
  else:
    len_lensx = b[0] - 247
    lensx = BE_inv(b[1:1+len_lensx])
    sx = b[1+len_lensx : 1+len_lensx+lensx]
  return s_inv(sx)

def s_inv(b):
  if verbose: print("s_inv(",b.hex(),")")
  x=[]
  i=0
  len_=len(b)
  while i<len_:
    len_cur, len_len_cur = decode_length(b[i:])
    x += [RLP_inv(b[i:i+len_len_cur+len_cur])]
    i += len_cur + len_len_cur
    if debug: print("  s_inv() returning",x)
  if debug: print("  s_inv() returning",x)
  return x

# this is a helper function not described in the spec
# but the spec does not discuss the inverse to he RLP function, so never has the opportunity to discuss this
# returns the length of an encoded rlp object
def decode_length(b):
  if verbose: print("length_inv(",b.hex(),")")
  if len(b)==0:
    return 0,0 # TODO: this may be an error
  length_length=0
  first_rlp_byte = b[0]
  if first_rlp_byte < 0x80:
    rlp_length=1
    return rlp_length, length_length
  elif first_rlp_byte <= 0xb7:
    rlp_length = first_rlp_byte - 0x80
  elif first_rlp_byte <= 0xbf:
    length_length = first_rlp_byte - 0xb7
    rlp_length = BE_inv(b[1:1+length_length])
  elif first_rlp_byte <= 0xf7:
    rlp_length = first_rlp_byte - 0xc0
  elif first_rlp_byte <= 0xbf:
    length_length = first_rlp_byte - 0xb7
    rlp_length = BE_inv(b[1:1+length_length])
  return rlp_length, 1+length_length



###################################
# Appendix C. Hex Prefix Encoding #
###################################

def HP(x,t):
  # x is bytearray of values < 16
  # x is a byte array, will convert to a bytearray of values < 16
  # t is 0 or 1, or false or true
  if verbose: print("HP(",x,t,")")
  #x = bytes([int(d,16) for d in x.hex()])
  ret=bytearray()
  if len(x)%2==0: #ie even length
    ret.append(16*f(t))
    for i in range(0,len(x),2):
      ret.append(16*x[i]+x[i+1])
  else:
    ret.append(16*(f(t)+1)+x[0])
    for i in range(1,len(x),2):
      ret.append(16*x[i]+x[i+1])
  if debug: print("HP() returning", ret)
  return ret

def f(t):
  if t:
    return 2
  else:
    return 0

def HP_inv(bytes_):
  nibbles = ""
  odd_length = (bytes_[0]>>4)%2==1 #sixth lowest bit
  t = (bytes_[0]>>5)%2!=0 #fifth lowest bit
  if odd_length:
    nibbles += bytes_[0:1].hex()[1]
  for b in bytes_[1:]:
    nibbles += bytes([b]).hex()
  return nibbles, t



###########################################
# Appendix D. Modified Merkle Patricia Tree

#################################################
# build tree from account dict
# we follow the suggestion in including memoized tree structure and hashes
# the TRIE function is inefficient, only done once to build genesis tree from list of accounts

def y(J):
  yJ = {}
  for kn in J:
    kn_ = KEC(kn)
    knprime = bytearray(2*len(kn_))
    for i in range(2*len(kn_)):
      if i%2==0: # even
        knprime[i] = kn_[i//2]//16
      else:
        knprime[i] = kn_[i//2]%16
    #print(kn.hex(),kn_.hex(),knprime.hex())
    yJ[bytes(knprime)] = J[kn]
  return yJ
  #return {bytes([int(d,16) for d in KEC(k).hex()]):v for k,v in J.items()}

def TRIE(J):
  cJ0 = c(J,0)
  #print("cJ0",cJ0.hex())
  return KEC(cJ0)

# node composition function
def n(J,i):
  #print("n(",i,")")
  if len(J)==0:
    return b''
  cJi = c(J,i)
  if len(cJi)<32:
    return cJi
  else:
    #print("cJi,KEC(cJi)",cJi.hex(),KEC(cJi).hex())
    return KEC(cJi)

# structural composition function, used to patriciaize and merkleize a dictionary
# this function includes memoization of tree structure and hashes, as suggested in appx D.1
def c(J,i):
  #print("c(",J,i,")")
  #print("c(",i,")")

  if len(J)==0:
    return RLP(b'') # note: empty storage tree has merkle root: KEC(RLP(b'')) == 56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421
    # also, KEC(RLP(())) == 1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347, which is the sha3Unlces hash in block header for no uncles

  I_0 = next(iter(J))   # get first key, will reuse below

  # if leaf node
  if len(J) == 1:
    leaf = J[I_0]
    if type(leaf)==Account:
      I_1 = RLP((leaf.n,leaf.b,leaf.s,leaf.c))
    else:
      #I_1 = leaf
      I_1 = RLP(leaf)
      print("c() leaf",I_0.hex(),I_1.hex())
    #print(I_1.hex())
    rlp = RLP((HP(I_0[i:],1),I_1))
    #print("leaf rlp",rlp.hex(),KEC(rlp).hex())
    return rlp

  # prepare for extension node check by finding max j such that all keys I in J have the same I[i:j]
  l = I_0[:]
  j = len(l)
  for I_0 in J:
    j = min(j,len(I_0))
    l = l[:j]
    for x in range(i,j):
      if I_0[x] != l[x]:
        j = x
        l=l[:j]
        break
    if i==j:
      break

  # if extension node
  if i!=j:
    child = n(J,j)
    #print("extension,child",I_0[i:j].hex(),child.hex())
    rlp = RLP((HP(I_0[i:j],0),child))
    #print("extension rlp",rlp.hex(),KEC(rlp).hex())
    return rlp

  # otherwise branch node
  def u(j):
    #print("u(",j,")")
    #print([k.hex() for k in J.keys()])
    return n({I_0:I_1 for I_0,I_1 in J.items() if I_0[i]==j},i+1)
  v = b''
  for I_0 in J:
    if len(I_0)==i:
      v = J[I_0]
      break
  #print("v",v)
  rlp = RLP([u(k) for k in range(16)] + [v])
  #print("branch rlp",rlp.hex(),KEC(rlp).hex())
  return rlp



############
# Appendix F

# some global constants
secp256k1n = 115792089237316195423570985008687907852837564279074904382605163141518161494337
chainid = 0

def ECDSAPUBKEY(p_r):
  pass

def ECDSASIGN(e,p_r):
  pass

def ECDSARECOVER(e,v,r,s):
  # e is keccak hash of the tx
  # r is x-coordinate of curve point
  # v is recovery id, 27 for even y and 28 for odd y
  if v>28:
    v = v - (chainid*2+8) # special case, v=2*chainid+35 if y odd, otherwise v=2*chainid+36
  assert v==27 or v==28
  r_int  = int.from_bytes(r,"big")
  s_int  = int.from_bytes(s,"big")
  #r_int  = r
  #s_int  = s
  assert 0<r_int and r_int<secp256k1n
  #assert 0<s_int and s_int<(secp256k1n//2+1)     # TODO: this causes error starting in block 46169 (or 46170?), so just commented
  return crypto.secp256k1recover(r,s,v-27,e)

def A(p_r):
  return KEC(ECDSAPUBKEY(p_r))[12:32] # bits 96 to 256

def L_S(T):
  if not T.t:
    p = T.i
  else:
    p = T.d
  if T.w in {27,28}:
    return (T.n, T.p, T.g, T.t, T.v, p)
  else:
    return (T.n, T.p, T.g, T.t, T.v, p, chainid, (), ())

def h(T):
  return KEC(RLP(L_S(T))) # note: yellowpaper omits RLP()

# recover transaction sender
def S(T):
  return KEC(ECDSARECOVER(h(T),T.w,T.r,T.s))[12:32] 


def test_block_46147_transaction():
  print("ok 45147")
  Tjson = {"blockHash":"0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd","blockNumber":"0xb443","from":"0xa1e4380a3b1f749673e270229993ee55f35663b4","gas":"0x5208","gasPrice":"0x2d79883d2000","hash":"0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060","input":"0x","nonce":"0x0","r":"0x88ff6cf0fefd94db46111149ae4bfc179e9b94721fffd821d38d16464b3f71d0","s":"0x45e0aff800961cfce805daef7016b9b675c137a6a41a548f7b60a3484c06a33a","to":"0x5df9b87991262f6ba471f09758cde1c0fc1de734","transactionIndex":"0x0","v":"0x1c","value":"0x7a69"}
  nonce = int(Tjson["nonce"][2:],16)
  gasPrice = int(Tjson["gasPrice"][2:],16)
  gasLimit = int(Tjson["gas"][2:],16)
  to = bytes.fromhex(Tjson["to"][2:])
  value = int(Tjson["value"][2:],16)
  v = int(Tjson["v"][2:],16)
  r = bytes.fromhex(Tjson["r"][2:])
  s = bytes.fromhex(Tjson["s"][2:])
  data = bytes.fromhex(Tjson["input"][2:])
  init = bytes() if "init" not in Tjson else bytes.fromhex(Tjson["init"][2:])
  print("T",nonce,gasPrice,gasLimit,to,value,v,r,s,data,init)
  T = Transaction(nonce,gasPrice,gasLimit,to,value,v,r,s,init,data)
  sender = S(T)
  from_ = bytes.fromhex(Tjson["from"][2:])
  print(sender.hex(),from_.hex(),from_==sender) # SUCCEEDS!



##########################
# Appendix G. Fee Schedule

# G denotes fixed gas costs
G = {
  "zero":         0,        # nothing paid for ops of the set W["zero"]
  "base":         2,        # gas for ops in set W["base"]
  "verylow":      3,        #                    W["verylow"]
  "low":          5,        #                    W["low"]
  "mid":          8,        #                    W["mid"]
  "high":         10,       #                    W["high"]
  "ext":          20,       #                    W["ext"]
  #"balance":      400,      #         BALANCE
  "sload":        50,       #         SLOAD
  "jumpdest":     1,        #         JUMPDEST
  "sset":         20000,    #         SSTORE when change from zero to nonzero
  "sreset":       5000,     #         SSTORE when set to or remains zero
  "selfdestruct": 5000,     #         SELFDESTRUCT
  "create":       32000,    #         CREATE
  "codedeposit":  200,      #         CREATE per byte to put code in state
  "call":         40,       #         CALL
  "callvalue":    9000,     #         CALL for non-zero value transfer
  "callstipend":  2300,     # stipend for called contract subtracted from G["callvalue"] for nonzero value transfer
  "newaccount":   25000,    # gas for CALL or SELFDESTRUCT op which creates an account
  "exp":          10,       # partial payment for EXP
  "expbyte":      10,       #                     EXP when multiplied by ceil(log_256(exponent)) [?]
  "memory":       3,        # every additional word when expanding mem
  "txcreate":     32000,    # not in frontier?
  "txdatazero":   4,
  "txdatanonzero":68,
  "transaction":  21000,
  "log":          375,
  "logdata":      8,
  "logtopic":     375,
  "sha3":         30,
  "sha3word":     6,
  "copy":         3,
  #"blockhash":    20,
  #"quaddivisor":  20 
}

# R denotes gas refund amonuts
R = {
  "sclear":       15000,    # added to refund counter when storage is set from nonzero to zero
  "selfdestruct": 24000,    # added to refund counter when SELFDESTRUCT account
}



###########################################
# Appendix H. Virtual Machine Specification

# H.1 Gas Cost

# returns gas used by an opcode
# note: we deviate from the yellowpaper, we compute C_memory, C_SELFDESTRUCT, C_SSTORE inside the opcodes, where they can be readily computed.
def C(sigma, mu, I):
  # get opcode
  w_ = w(mu,I)
  # prepare return
  ret = 0 # C_memory(mu.iprime) - C_memory(mu.i)  # note: mu.iprime is available in the opcodes, so compute C_memory there
  if w_==0x55:   # SSTORE
    pass # this is done inside SSTORE
  elif w_==0x0a and mu.s[-2]==0:    # EXP
    ret += G["exp"]
  elif w_==0x0a and mu.s[-2]>0:     # EXP
    #print("C() exp ",mu.s[-2])
    ret += G["exp"] + G["expbyte"] * (1 + math.floor(math.log(mu.s[-2],256)))
  elif w_ in {0x37,0x39}:   # CALLDATACOPY, CODECOPY    #0x3c RETURNDATACOPY
    #print("C()",G["verylow"],G["copy"],len(mu.s))
    ret += G["verylow"] + G["copy"]*-1*((-1*mu.s[-3])//32)
  elif w_ == 0x3c:   # EXTCODECOPY
    ret += G["ext"] + G["copy"]*-1*((-1*mu.s[-4])//32)
  elif w_ == 0xa0:   # LOG0
    ret += G["log"] + G["logdata"]*mu.s[-2]
  elif w_ == 0xa1:   # LOG1
    ret += G["log"] + G["logdata"]*mu.s[-2] + G["logtopic"]
  elif w_ == 0xa2:   # LOG2
    ret += G["log"] + G["logdata"]*mu.s[-2] + 2*G["logtopic"]
  elif w_ == 0xa3:   # LOG3
    ret += G["log"] + G["logdata"]*mu.s[-2] + 3*G["logtopic"]
  elif w_ == 0xa4:   # LOG4
    ret += G["log"] + G["logdata"]*mu.s[-2] + 4*G["logtopic"]
  elif w_ in {0xf1,0xf2}:  # CALL, CALLCODE:
    ret += 0 # C_CALL(sigma,mu)  # note: C_CALL() is in appx H, compute it there
  #elif w_ == "SELFDESTRUCT":    # not in frontier
  #  ret += 0 # C_SELFDESTRUCT(sigma,mu)  # note: C_SELFDESTRUCT() is in appx H, compute it there
  elif w_ in {0xf1,0xf2}:  # CALL or CALLCODE
    # do this in the actual opcodes
    pass
  elif w_ == 0xf0:  # CREATE
    ret += G["create"]
  elif w_ == 0x20:  # SHA3
    ret += G["sha3"] + G["sha3word"]*(-1*(-1*mu.s[-2])//32)      # typo: s should be mu.s
  elif w_ == 0x5b:   # JUMPDEST
    ret += G["jumpdest"]
  elif w_ == 0x54:   # SLOAD
    ret += G["sload"]
  elif w_ in W["zero"]:
    ret += G["zero"]
  elif w_ in W["base"]:
    ret += G["base"]
  elif w_ in W["verylow"]:
    ret += G["verylow"]
  elif w_ in W["low"]:
    ret += G["low"]
  elif w_ in W["mid"]:
    ret += G["mid"]
  elif w_ in W["high"]:
    ret += G["high"]
  elif w_ in W["ext"]:
    ret += G["ext"]
  #elif w_ == "BALANCE":
  #  ret += G["balance"]
  #elif w_ == "BLOCKHASH":
  #  ret += G["blockhash"]
  return ret

def C_memory(a):
  return G["memory"]*a + (a**2)//512

W = {
  "zero":{0xfd,0xff,0xf3}, # STOP, SELFDESTRUCT, RETURN
  "base":{0x30,0x32,0x33,0x34,0x36,0x38,0x3a,0x41,0x42,0x43,0x44,0x45,0x50,0x58,0x59,0x5a}, # ADDRESS, ORIGIN, CALLER, CALLVALUE, CALLDATASIZE, CODESIZE, GASPRICE, COINBASE, TIMESTAMP, NUMBER, DIFFICULTY, GASLIMIT, POP, PC, MSIZE, GAS
  "verylow":{0x01,0x03,0x19,0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x1a,0x35,0x51,0x52,0x53,0x60,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6a,0x6b,0x6c,0x6d,0x6e,0x6f,0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7a,0x7b,0x7c,0x7d,0x7e,0x7f,0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f}, # ADD, SUB, NOT, LT, GT, SLT, SGT, EQ, ISZERO, AND, OR, XOR, BYTE, CALLDATALOAD, MLOAD, MSTORE, MSTORE8, PUSH*, DUP*, SWAP*},
  "low":{0x02,0x04,0x05,0x06,0x07,0x0b}, # MUL, DIV, SDIV, MOD, SMOD, SIGNEXTEND
  "mid":{0x08,0x09,0x56},  # ADDMOD, MULMOD, JUMP
  "high":{0x57}, # JUMPI
  "ext":{0x31,0x3b,0x40}  # BALANCE, EXTCODESIZE, BLOCKHASH
}
  
# memory expansion range function ("memory expansion function")
# note: name collision with chapter 4.3.1 involving logs, so call this one M_
def M_(s,f,l):
  # args are current numwords, proposed start byte, proposed length
  if l==0:
    return s
  else:
    return max(s,-1*((-1*(f+l))//32))

# not in frontier
# all but one 64th function
def L(n):
  return n-n//64



# H.2 Instruction Set

def STOP(sigma,mu,A,I):
  return sigma,mu,A,I

def ADD(sigma,mu,A,I):
  mu.s.append((mu.s.pop()+mu.s.pop())%2**256)
  return sigma,mu,A,I

def MUL(sigma,mu,A,I):
  mu.s.append((mu.s.pop()*mu.s.pop())%2**256)
  return sigma,mu,A,I

def SUB(sigma,mu,A,I):
  mu.s.append((mu.s.pop()-mu.s.pop())%2**256)
  return sigma,mu,A,I

def DIV(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  if mus1==0:
    mu.s.append(0)
  else:
    mu.s.append(mus0//mus1)
  return sigma,mu,A,I

def SDIV(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  # note: convert negative values to 2**256-value
  mus0_signed = mus0 if mus0<2**255 else mus0-2**256
  mus1_signed = mus1 if mus1<2**255 else mus1-2**256
  print("SDIV",mus0_signed,mus1_signed)
  if mus1==0:
    mu.s.append(0)
  elif mus0_signed==-1*2**255 and mus1_signed==-1:
    mu.s.append(mus0)
  else:
    sgn = -1 if mus0_signed*mus1_signed<0 else 1
    ret = sgn*(abs(mus0_signed)//abs(mus1_signed))
    if ret<0:
      ret = 2**256+ret
    mu.s.append(ret)
  return sigma,mu,A,I

def MOD(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  if mus1==0:
    mu.s.append(0)
  else:
    mu.s.append(mus0%mus1)
  return sigma,mu,A,I

def SMOD(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  mus0_signed = mus0 if mus0<2**255 else mus0-2**256
  mus1_signed = mus1 if mus1<2**255 else mus1-2**256
  if mus1==0:
    mu.s.append(0)
  else:
    sgn = 1 if mus0_signed>=0 else -1
    ret = sgn*(abs(mus0_signed)%abs(mus1_signed))
    if ret<0:
      ret = 2**256+ret
    mu.s.append(ret)
  return sigma,mu,A,I

def ADDMOD(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  mus2 = mu.s.pop()
  if mus2==0:
    mu.s.append(0)
  else:
    mu.s.append((mus0+mus1)%mus2)
  return sigma,mu,A,I

def MULMOD(sigma,mu,A,I):
  mus0 = mu.s.pop()     # a
  mus1 = mu.s.pop()     # b
  mus2 = mu.s.pop()     # modulus
  if mus2==0:
    mu.s.append(0)
  else:
    mu.s.append((mus0*mus1)%mus2)
    #print("MULMOD",mus0,mus1,mus2,(mus0*mus1)%mus2)
  return sigma,mu,A,I

def EXP(sigma,mu,A,I):
  mus0 = mu.s.pop()     # base
  mus1 = mu.s.pop()     # exponent
  #mu.s.append((mus0**mus1)%2**256)  # this is very slow for big mus1, so use the popular right-to-left binary method below
  base = mus0
  exponent = mus1
  base = base % 2**256
  result = 1
  while exponent > 0:
    if (exponent % 2 == 1):
      result = (result * base) % 2**256
    exponent = exponent >> 1
    base = (base * base) % 2**256
  mu.s.append(result)
  return sigma,mu,A,I

def SIGNEXTEND(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  # I think that mus0 is assumed unsigned, otherwise t can be >256 and we overflow
  # and mus1 is arbitrary, since two's complement
  mus1_bytes = mus1.to_bytes(256,"big")
  ret = 0
  t = 256-8*(mus0+1)    # takes value 0, 8, 16, ..., 248
  print("t",t)
  for i in range(256):
    if i<=t:
      ret += (mus1 & (1<<(255-t))) << (t-i)
      #print("ret1",ret,(mus1 & (1<<(255-t))),1 if mus1 & (1<<(255-t)) else 0)
    else:
      ret += (mus1 & (1<<(255-i)))
      #print("ret2",ret,1 if mus1 & (1<<(255-i)) else 0)
  mu.s.append(ret)
  return sigma,mu,A,I

def LT(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  if mus0<mus1:
    mu.s.append(1)
  else:
    mu.s.append(0)
  return sigma,mu,A,I

def GT(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  if mus0>mus1:
    mu.s.append(1)
  else:
    mu.s.append(0)
  return sigma,mu,A,I

def SLT(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  mus0_signed = mus0 if mus0<2**255 else mus0-2**256
  mus1_signed = mus1 if mus1<2**255 else mus1-2**256
  if mus0_signed<mus1_signed:
    mu.s.append(1)
  else:
    mu.s.append(0)
  return sigma,mu,A,I

def SGT(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  mus0_signed = mus0 if mus0<2**255 else mus0-2**256
  mus1_signed = mus1 if mus1<2**255 else mus1-2**256
  if mus0_signed>mus1_signed:
    mu.s.append(1)
  else:
    mu.s.append(0)
  return sigma,mu,A,I

def EQ(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  if mus0==mus1:
    mu.s.append(1)
  else:
    mu.s.append(0)
  return sigma,mu,A,I

def ISZERO(sigma,mu,A,I):
  mus0 = mu.s.pop()
  if mus0==0:
    mu.s.append(1)
  else:
    mu.s.append(0)
  return sigma,mu,A,I

def AND(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  mu.s.append(mus0 & mus1)
  return sigma,mu,A,I

def OR(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  mu.s.append(mus0 | mus1)
  return sigma,mu,A,I

def XOR(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  mu.s.append(mus0 ^ mus1)
  return sigma,mu,A,I

def NOT(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mu.s.append(2**256-1 - mus0)
  return sigma,mu,A,I

def BYTE(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  ret = 0
  for i in range(256):
    if i<8 and mus0<32:
      ret += (mus1 & 1<<(i+8*(31-mus0)))
  #ret >>= 8*(31-mus0)
  mu.s.append(ret)
  return sigma,mu,A,I

def SHA3(sigma,mu,A,I):
  mus0 = mu.s.pop()     # start offset
  mus1 = mu.s.pop()     # length
  # update memory if overflow
  mu_iprev = mu.i
  mu.i = M_(mu.i,mus0,mus1)
  print("SHA3",mu.i,mu_iprev)
  if mu_iprev<mu.i:
    mu.g = mu.g - (C_memory(mu.i)-C_memory(mu_iprev))
    if mu.g<0:
      return {}, mu, A, I     # halting exception
    mu.m.extend(bytes((mu.i-mu_iprev)*32))
  ret = KEC(mu.m[mus0:mus0+mus1])
  mu.s.append(int.from_bytes(ret,"big"))
  #mu.s.append(1)
  return sigma,mu,A,I

def ADDRESS(sigma,mu,A,I):
  mu.s.append(int.from_bytes(I.a,"big"))
  return sigma,mu,A,I

def BALANCE(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus0bytes20 = mus0.to_bytes(160,"big")  # note: maybe should be "little"
  if mus0bytes20 in sigma:
    mu.s.append(sigma[mus0bytes20].b)
  else:
    mu.s.append(0)
  return sigma,mu,A,I

def ORIGIN(sigma,mu,A,I):
  mu.s.append(int.from_bytes(I.o,"big"))
  return sigma,mu,A,I

def CALLER(sigma,mu,A,I):
  print(int.from_bytes(I.s,'big'))
  mu.s.append(int.from_bytes(I.s,'big'))
  return sigma,mu,A,I

def CALLVALUE(sigma,mu,A,I):
  mu.s.append(I.v)
  return sigma,mu,A,I

def CALLDATALOAD(sigma,mu,A,I):
  mus0 = mu.s.pop()
  if mus0>=len(I.d):
    mu.s.append(0)
  else:
    print("CALLDATALOAD",I.d[mus0:mus0+32].hex(), type(I.d[mus0:mus0+32]), type(mu.m))
    calldata = I.d[mus0:mus0+32]
    calldata += bytes(32-len(calldata))
    print("CALLDATALOAD",calldata)
    #mu.s.append(int.from_bytes(bytes(bytearray(I.d[mus0:mus0+32]).extend(32)),"big"))
    #mu.s.append(int.from_bytes(I.d[mus0:mus0+32],"big"))
    mu.s.append(int.from_bytes(calldata,"big"))
  return sigma,mu,A,I

def CALLDATASIZE(sigma,mu,A,I):
  mu.s.append(len(I.d))
  return sigma,mu,A,I

def CALLDATACOPY(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  mus2 = mu.s.pop()
  # extend memory if necessary
  mu_iprev = mu.i
  mu.i = M_(mu.i,mus0,mus2)
  if mu_iprev<mu.i:
    mu.g = mu.g - (C_memory(mu.i)-C_memory(mu_iprev))
    if mu.g<0:
      return {}, mu, A, I     # halting exception
    mu.m.extend(bytes((mu.i-mu_iprev)*32))
  for i in range(mus2):
    if mus1+i<len(I.d):
      mu.m[mus0+i] = I.d[mus1+i]
    else:
      mu.m[mus0+i] = 0
  return sigma,mu,A,I

def CODESIZE(sigma,mu,A,I):
  mu.s.append(len(I.b))
  return sigma,mu,A,I

def CODECOPY(sigma,mu,A,I):
  mus0 = mu.s.pop()     # memory location
  mus1 = mu.s.pop()     # code location
  mus2 = mu.s.pop()     # length
  # extend memory if necessary
  mu_iprev = mu.i
  mu.i = M_(mu.i,mus0,mus2)
  if mu_iprev<mu.i:
    mu.g = mu.g - (C_memory(mu.i)-C_memory(mu_iprev))
    if mu.g<0:
      return {}, mu, A, I     # halting exception
    mu.m.extend(bytes((mu.i-mu_iprev)*32))
  for i in range(mus2):
    if mus1+i<len(I.b):
      mu.m[mus0+i] = I.b[mus1+i]
    else:
      mu.m[mus0+i] = 0
  #print("CODECOPY",mu.m[mus0:mus0+mus2].hex())
  return sigma,mu,A,I

def GASPRICE(sigma,mu,A,I):
  mu.s.append(I.p)
  return sigma,mu,A,I

def EXTCODESIZE(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus0bytes20 = mus0.to_bytes(160,"big")  # note: maybe should be "little"
  if mus0bytes20 in sigma:
    mu.s.append(len(sigma[mus0bytes20].b))
  else:
    mu.s.append(0)
  return sigma,mu,A,I

def EXTCODECOPY(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  mus2 = mu.s.pop()
  mus3 = mu.s.pop()
  # extend memory if necessary
  mu_iprev = mu.i
  mu.i = M_(mu.i,mus1,mus3)
  if mu_iprev<mu.i:
    mu.g = mu.g - (C_memory(mu.i)-C_memory(mu_iprev))
    if mu.g<0:
      return {}, mu, A, I     # halting exception
    mu.m.extend(bytes((mu.i-mu_iprev)*32))
  # get code
  mus0bytes20 = mus0.to_bytes(160,"big")  # note: maybe should be "little"
  if mus0bytes20 in sigma:
    c = sigma[mus0bytes20].c
  else:
    c = bytes([])
  # copy code to mem
  for i in range(mus3):
    if mus2+i<len(c):
      mu.m[mus1+i] = c[mus2+i]
    else:
      assert 1==0     # STOP, note: find a nicer way to do this
  return sigma,mu,A,I
      
def RETURNDATASIZE(sigma,mu,A,I):
  mu.s.append(len(mu.o))
  return sigma,mu,A,I

def RETURNDATACOPY(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  mus2 = mu.s.pop()
  # extend memory if necessary
  mu_iprev = mu.i
  mu.i = M_(mu.i,mus0,mus2)
  if mu_iprev<mu.i:
    mu.g = mu.g - (C_memory(mu.i)-C_memory(mu_iprev))
    if mu.g<0:
      return {}, mu, A, I     # halting exception
    mu.m.extend(bytes((mu.i-mu_iprev)*32))
  # copy code to mem
  for i in range(mus2):
    if mus1+i<len(mu.o):
      mu.m[mus0+i] = mu.o[mus1+i]
    else:
      mu.m[mus0+i] = 0
  return sigma,mu,A,I

def BLOCKHASH(sigma,mu,A,I):
  # func P_ steps back over headers until it reaches the correct block number
  # note: name collision with func P() in section 10
  def P_(h,n,a):
    H = I.recentblocks[h].H         # get block header from block hash h
    if n>H.i or a==256 or h==0:     # recall: H.i is blocknumber
      return 0
    elif n==H.i:
      return h
    else:
      return P_(H.p,n,a+1)
  blockhash = P_(I.H.p,mus0,0)
  ret = int.from_bytes(blockhash,'big')
  mu.s.append(ret)
  return sigma,mu,A,I

def COINBASE(sigma,mu,A,I):
  mu.s.append(int.from_bytes(I.H.c,"big"))
  return sigma,mu,A,I

def TIMESTAMP(sigma,mu,A,I):
  mu.s.append(I.H.s)
  return sigma,mu,A,I

def NUMBER(sigma,mu,A,I):
  mu.s.append(I.H.i)
  return sigma,mu,A,I

def DIFFICULTY(sigma,mu,A,I):
  print("DIFFICULTY",I.H.d)
  mu.s.append(I.H.d)
  return sigma,mu,A,I

def GASLIMIT(sigma,mu,A,I):
  mu.s.append(I.H.l)
  return sigma,mu,A,I

def POP(sigma,mu,A,I):
  mu.s.pop()
  return sigma,mu,A,I

def MLOAD(sigma,mu,A,I):
  mus0 = mu.s.pop()
  # extend memory if necessary
  mu_iprev = mu.i
  mu.i = max(mu.i,-1*((-1*(mus0+32))//32))
  if mu_iprev<mu.i:
    mu.g = mu.g - (C_memory(mu.i)-C_memory(mu_iprev))
    if mu.g<0:
      return {}, mu, A, I     # halting exception
    mu.m.extend(bytes((mu.i-mu_iprev)*32))
  ret = int.from_bytes(mu.m[mus0:mus0+32],'big')
  #print("MLOAD",ret,mu.m[mus0:mus0+32].hex())
  mu.s.append(ret)
  return sigma,mu,A,I

def MSTORE(sigma,mu,A,I):
  mus0 = mu.s.pop()     # mem offset
  mus1 = mu.s.pop()     # word to store
  # extend memory if necessary
  mu_iprev = mu.i
  mu.i = max(mu.i,-1*((-1*(mus0+32))//32))
  if mu_iprev<mu.i:
    mu.g = mu.g - (C_memory(mu.i)-C_memory(mu_iprev))
    if mu.g<0:
      return {}, mu, A, I     # halting exception
    mu.m.extend(bytes((mu.i-mu_iprev)*32))
  mus1bytes = mus1.to_bytes(32,'big')
  #print("MSTORE",mus0,hex(mus1))
  mu.m[mus0:mus0+32] = mus1bytes
  return sigma,mu,A,I

def MSTORE8(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  # extend memory if necessary
  mu_iprev = mu.i
  mu.i = max(mu.i,-1*((-1*(mus0+1))//32))
  print("MSTORE8",mu.i,mu_iprev)
  if mu_iprev<mu.i:
    mu.g = mu.g - (C_memory(mu.i)-C_memory(mu_iprev))
    if mu.g<0:
      return {}, mu, A, I     # halting exception
    mu.m.extend(bytes((mu.i-mu_iprev)*32))
  mu.m[mus0] = mus1%256
  return sigma,mu,A,I

def SLOAD(sigma,mu,A,I):
  mus0 = mu.s.pop()
  mus0bytes = mus0.to_bytes(32,'big')
  if mus0bytes in sigma[I.a].storage:
    mu.s.append(int.from_bytes(sigma[I.a].storage[mus0bytes],'big'))
  else:
    mu.s.append(0)
  return sigma,mu,A,I
  
def SSTORE(sigma,mu,A,I):
  mus0 = mu.s.pop()     # key
  mus1 = mu.s.pop()     # value
  #print("SSTORE",mus0,mus1)
  mus0bytes = mus0.to_bytes(32,'big')
  mus1bytes = mus1.to_bytes(32,'big')
  print("SSTORE",mus0bytes.hex(),mus1bytes.hex())
  #print("SSTORE",sigma[I.a].storage)
  if mus0bytes in sigma[I.a].storage:
    oldval = int.from_bytes(sigma[I.a].storage[mus0bytes],'big')
  else:
    oldval = 0
  def C_SSTORE(sigma,mu):
    if mus1!=0 and oldval==0:
      return G["sset"]
    else:
      return G["sreset"]
  #print("SSTORE",C_SSTORE(sigma,mu))
  mu.g = mu.g - C_SSTORE(sigma,mu)
  if mu.g<0:
    return {}, mu, A, I     # out-of-gas exception
  if mus1==0 and oldval!=0:
    A.r += R["sclear"]
  #print(I.a,mus0bytes,mus1bytes)
  # if zero, then delete existing slot if exists
  if mus1!=0:
    sigma[I.a].storage[mus0bytes] = mus1bytes
  else:
    if mus0bytes in sigma[I.a].storage:
      del sigma[I.a].storage[mus0bytes]
  return sigma,mu,A,I
  
def JUMP(sigma,mu,A,I):
  def J_JUMP(mu):
    mus0 = mu.s.pop()
    mu.pc = mus0
  J_JUMP(mu)
  # note: JUMPDEST check done in Z()
  return sigma,mu,A,I

def JUMPI(sigma,mu,A,I):
  def J_JUMPI(mu):
    mus0 = mu.s.pop()
    mus1 = mu.s.pop()
    if mus1!=0:
      mu.pc = mus0
    else:
      mu.pc = mu.pc+1
  J_JUMPI(mu)
  # note: JUMPDEST check done in Z()
  return sigma,mu,A,I

def PC(sigma,mu,A,I):
  mu.s.append(mu.pc)
  return sigma,mu,A,I

def MSIZE(sigma,mu,A,I):
  mu.s.append(32*mu.i)
  return sigma,mu,A,I

def GAS(sigma,mu,A,I):
  mu.s.append(mu.g)
  return sigma,mu,A,I

def JUMPDEST(sigma,mu,A,I):
  # do nothing during execution
  return sigma,mu,A,I

def PUSHn(sigma,mu,A,I):
  # c() returns the immediates, or 0 if overflow code
  def c(x):
    if x<len(I.b):
      return I.b[x]
    else:
      return 0
  n = I.b[mu.pc]-0x60+1
  immediate = int.from_bytes(bytes([c(mu.pc+i+1) for i in range(n)]),'big')
  mu.s.append(immediate)
  # note: PC incremented by N()
  return sigma,mu,A,I

def DUPn(sigma,mu,A,I):
  n = I.b[mu.pc]-0x7f
  val = mu.s[-1*n]          # note: check for underflow done in Z() in section 9.4.2
  mu.s.append(val)
  return sigma,mu,A,I

def SWAPn(sigma,mu,A,I):
  n = I.b[mu.pc]-0x8e
  tmp = mu.s[-1]            # note: check for underflow done in Z() in section 9.4.2
  mu.s[-1] = mu.s[-1*n]     # note: check for underflow done in Z() in section 9.4.2
  mu.s[-1*n] = tmp
  return sigma,mu,A,I

def LOGn(sigma,mu,A,I):
  n = I.b[mu.pc]-0xa0
  mus0 = mu.s.pop()
  mus1 = mu.s.pop()
  # update memory if overflow
  mu_iprev = mu.i
  mu.i = M_(mu.i,mus0,mus1)
  if mu_iprev<mu.i:
    mu.g = mu.g - (C_memory(mu.i)-C_memory(mu_iprev))
    if mu.g<0:
      return {}, mu, A, I     # halting exception
    mu.m.extend(bytes((mu.i-mu_iprev)*32))
  bytes_to_append = I.a[:]
  for i in range(n):
    bytes_to_append += mu.s.pop().to_bytes(32,'big')
  bytes_to_append += mu.m[mus0:mus0+mus1]
  A.l += [bytes_to_append]
  return sigma,mu,A,I

def CREATE(sigma,mu,A,I):
  mus0 = mu.s.pop()     # value
  mus1 = mu.s.pop()     # input offset
  mus2 = mu.s.pop()     # input size
  # update memory if overflow
  mu_iprev = mu.i
  mu.i = M_(mu.i,mus1,mus2)
  if mu_iprev<mu.i:
    mu.g = mu.g - (C_memory(mu.i)-C_memory(mu_iprev))
    if mu.g<0:
      return {}, mu, A, I     # halting exception
    mu.m.extend(bytes((mu.i-mu_iprev)*32))
  # prepare calldata(?)
  i = mu.m[mus0:mus1+mus2]
  # create contract
  if mus0<=sigma[I.a].b and I.e<1024:
    sigmaprime, mu.g, Aplus, o = Lambda(sigma, I.a, I.o, L(mu.g), I.p, mus0, i, I.e+1, I.w, I.H, I.recentblocks)
  else:
    sigmaprime, mu.g, Aplus = sigma, mu.g, A0()
  # update A, the accrued transaction substate
  A.s = A.s.union(Aplus)
  A.l = A.l+Aplus.l
  A.t = A.t.union(Aplus.t)
  A.r += Aplus.r
  # push new acount's address x to stack, where x is defined as...
  if sigmaprime=={} or I.e==1024 or mus0>sigma[I.a].b: # note: are error conditions checked here or in Lambda?
    x = bytes([0]*20)
  else:
    nonce = sigmaprime[I.a].n
    x = KEC(RLP([I.a,nonce]))[12:32] #A(I.a + nonce.to_bytes(((nonce+7)/8,"big")) # note: this A() is implicitly defined and has a name collision with a function in appendix F.  check this, since in Lambda, address is 
  mu.s.append(int.from_bytes(x,"big"))
  # returndata mu.o is empty
  mu.o = bytearray([])
  return sigmaprime,mu,A,I

def CALL(sigma,mu,A,I):
  return _CALL(sigma,mu,A,I,"CALL")

def CALLCODE(sigma,mu,A,I,opcode):
  return _CALL(sigma,mu,A,I,"CALLCODE")

# this function _CALL is called by all CALL* opcodes. _CALL is not defined in the spec, but the idea that they mostly share code is in the definition of the CALL* opcodes.
def _CALL(sigma,mu,A,I,opcode):
  mus0 = mu.s.pop()   # used to compute C_GASCAP
  mus1 = mu.s.pop()   # to address  
  mus2 = mu.s.pop()   # value transfered
  mus3 = mu.s.pop()   # start of calldata in mem
  mus4 = mu.s.pop()   # length of calldata in mem
  mus5 = mu.s.pop()   # start of returndata in mem
  mus6 = mu.s.pop()   # length of returndata in mem

  # functions needed to compute gas
  def C_CALL(sigma,mu):
    return C_GASCAP(sigma,mu)+C_EXTRA(sigma,mu)
  def C_CALLGAS(sigma,mu):
    if mus2!=0:
      return C_GASCAP(sigma,mu)+G["callstipend"]
    else:
      return C_GASCAP(sigma,mu)
  def C_GASCAP(sigma,mu):
      if mu.g>=C_EXTRA(sigma,mu):
        return min(L(mu.g-C_EXTRA(sigma,mu)),a0)
      else:
        return a0
  def C_EXTRA(sigma,mu):
    return G["call"] + C_XFER(mu) + C_NEW(sigma,mu)
  def C_XFER(mu):
    if mus2!=0:
      return G["callvalue"]
    else:
      return 0
  def C_NEW(sigma,mu):
    if DEAD(sigma, (a1 % 2**160).to_bytes(20,'big')) and a2!=0:
      return G['newaccount']
    else:
      return 0
  
  # 1. check if out-of-gas
  mu_iprev = mu.i
  mu.i = M_(M_(mu.i,mus3,mus4),mus5,mus6)
  mu.g = mu.g - (C_memory(mu.i)-C_memory(mu_iprev)+C_CALL(sigma,mu))
  if mu.g<0:
    return {}, mu, A, I     # halting exception

  # 2. prepare to call
  # 2.1 update memory size if overflow
  if mu_iprev<mu.i:
    mu.m.extend(bytes((mu.i-mu_iprev)*32))
  # 2.2 calldata
  i = mu.m[mus3:mus3+mus4]
  # 2.3 recipient
  t = (mus1 % 2**160).to_bytes(20,'big')

  # 3. call
  if mus2<=sigma[I.a].b and I.e<1024:
    if opcode=='CALL':
      simgaprime, gprime, Aplus, o = Omega(sigma,I.a,I.o,t,t,C_CALLGAS(mu),I.p,a2,a2,i,I.e+1,I.w,I.H,I.recentblocks)
    elif opcode=='CALLCODE':
      simgaprime, gprime, Aplus, o = Omega(sigma,I.a,I.o,I.a,t,C_CALLGAS(mu),I.p,a2,a2,i,I.e+1,I.w,I.H,I.recentblocks)
  else:
    simgaprime, gprime, Aplus, o = sigma, g, A0(), bytearray([])

  # 4. finalize stuff
  # 4.1 write returndata to memory
  n = min(mus6,len(o))
  muprime.m[mus5:mus5+n] = o[0:n]
  # 4.2 get returndata to machine state
  muprime.o = o
  # 4.3 increment gas used
  muprime.g = mu.g+gprime   # note: maybe should check out-of-gas
  # 4.3 push return code to stack
  if simgaprime=={} or mus2>sigma[I.a].b or I.e==1024:  # note: maybe should also check for exceptional halting from 9.4.2
    x=0
  else:
    x=1
  mu.s.append(x)
  # 4.4 update accrued transaction substate
  Aprime = A0()
  Aprime.s = A.s.union(Aplus)
  Aprime.l = A.l+Aplus.l
  Aprime.t = A.t.union(Aplus.t)
  Aprime.r += Aplus.r
  return sigmaprime,muprime,Aprime,I

def RETURN(sigma,mu,A,I):
  mus0 = mu.s.pop()     # memory offset
  mus1 = mu.s.pop()     # length
  # update memory if overflow
  mu_iprev = mu.i
  mu.i = M_(mu.i,mus0,mus1)
  if mu_iprev<mu.i:
    mu.g = mu.g - (C_memory(mu.i)-C_memory(mu_iprev))
    if mu.g<0:
      return {}, mu, A, I     # halting exception
    mu.m.extend(bytes((mu.i-mu_iprev)*32))
  def H_RETURN(mu):
    return mu.m[mus0:mus0+mus1]
  mu.o = H_RETURN(mu)   # set mu.o here, since H() is called before RETURN opcode is executed
  #print("RETURN",mu.o.hex())
  return sigma,mu,A,I

# not in frontier
def REVERT(sigma,mu,A,I):
  mus0 = mu.s.pop()     # memory offset
  mus1 = mu.s.pop()     # length
  # update memory if overflow
  mu_iprev = mu.i
  mu.i = M_(mu.i,mus0,mus1)
  if mu_iprev<mu.i:
    mu.g = mu.g - (C_memory(mu.i)-C_memory(mu_iprev))
    if mu.g<0:
      return {}, mu, A, I     # halting exception
    mu.m.extend(bytes((mu.i-mu_iprev)*32))
  mu.o = mu.m[mus0:mus0+mus1]   # H_RETURN(mu) in yellowpaper
  return sigma,mu,A,I

# not in frontier
def INVALID(sigma,mu,A,I):
  return sigma,mu,A,I

"""
7f ff10112233445566778899aabbccddeeff00112233445566778899aabbccddee
ff
60 03
55
"""

def SELFDESTRUCT(sigma,mu,A,I):
  mus0 = mu.s.pop()     # address that gets remaining balance
  r = (mus0%2**160).to_bytes(20,'big')

  if I.a not in A.s:
    A.r += R["selfdestruct"]   # in a later fork, this is done in function Upsilon

  A.s = A.s.union(I.a)

  if r in sigma:
    sigma[r] = Account(sigma[r].n, sigma[r].b+sigma[I.a].b, sigma[r].s, sigma[r].c, b'', StateTree(), r)
  else:
    sigma[r] = Account(0, sigma[I.a].b, TRIE({}), KEC(b''), b'', StateTree(), r)

  print("SELFDESTRUCT", I.a.hex())
  del sigma[I.a]
  #sigma[I.a].b = 0

  return sigma,mu,A,I
  
  """ this is a newer version, untested
  # check gas
  def C_SELFDESTRUCT(sigma,mu):
    n=DEAD(sigma,r)
    ret=G["selfdestruct"]
    if n:
      ret+=G["newaccount"]
    return ret
  mu.g = mu.g - C_SELFDESTRUCT(sigma,mu)
  if mu.g<0:
    return {}, mu, A, I     # error
  # done checking gas
  A.s = A.s.union(I.a)
  sigmaprime = sigma
  if r not in sigma and sigma[I.a].b==0:
    del sigmaprime[r]
  elif r!=I.a:
    sigmaprime[r] = Account(sigma[r].n, sigma[r].b+sigma[I.a].b, sigma[r].s, sigma[r].c, b'', StateTree(), r)
  else:
    sigmaprime[r] = Account(sigma[r].n, 0, sigma[r].s, sigma[r].c, b'', StateTree(), r)
  sigmaprime[I.a].b=0
  return sigma,mu,A,I
  """


EVM_opcodes = {
  0x00:{"mnemonic":'STOP',           'delta':0, 'alpha':0, 'description':STOP},
  0x01:{"mnemonic":'ADD',            'delta':2, 'alpha':1, 'description':ADD},
  0x02:{"mnemonic":'MUL',            'delta':2, 'alpha':1, 'description':MUL},
  0x03:{"mnemonic":'SUB',            'delta':2, 'alpha':1, 'description':SUB},
  0x04:{"mnemonic":'DIV',            'delta':2, 'alpha':1, 'description':DIV},
  0x05:{"mnemonic":'SDIV',           'delta':2, 'alpha':1, 'description':SDIV},
  0x06:{"mnemonic":'MOD',            'delta':2, 'alpha':1, 'description':MOD},
  0x07:{"mnemonic":'SMOD',           'delta':2, 'alpha':1, 'description':SMOD},
  0x08:{"mnemonic":'ADDMOD',         'delta':3, 'alpha':1, 'description':ADDMOD},
  0x09:{"mnemonic":'MULMOD',         'delta':3, 'alpha':1, 'description':MULMOD},
  0x0a:{"mnemonic":'EXP',            'delta':2, 'alpha':1, 'description':EXP},
  0x0b:{"mnemonic":'SIGNEXTEND',     'delta':2, 'alpha':1, 'description':SIGNEXTEND},
  0x10:{"mnemonic":'LT',             'delta':2, 'alpha':1, 'description':LT},
  0x11:{"mnemonic":'GT',             'delta':2, 'alpha':1, 'description':GT},
  0x12:{"mnemonic":'SLT',            'delta':2, 'alpha':1, 'description':SLT},
  0x13:{"mnemonic":'SGT',            'delta':2, 'alpha':1, 'description':SGT},
  0x14:{"mnemonic":'EQ',             'delta':2, 'alpha':1, 'description':EQ},
  0x15:{"mnemonic":'ISZERO',         'delta':1, 'alpha':1, 'description':ISZERO},
  0x16:{"mnemonic":'AND',            'delta':2, 'alpha':1, 'description':AND},
  0x17:{"mnemonic":'OR',             'delta':2, 'alpha':1, 'description':OR},
  0x18:{"mnemonic":'XOR',            'delta':2, 'alpha':1, 'description':XOR},
  0x19:{"mnemonic":'NOT',            'delta':1, 'alpha':1, 'description':NOT},
  0x1a:{"mnemonic":'BYTE',           'delta':2, 'alpha':1, 'description':BYTE},
  0x20:{"mnemonic":'SHA3',           'delta':2, 'alpha':1, 'description':SHA3},
  0x30:{"mnemonic":'ADDRESS',        'delta':0, 'alpha':1, 'description':ADDRESS},
  0x31:{"mnemonic":'BALANCE',        'delta':1, 'alpha':1, 'description':BALANCE},
  0x32:{"mnemonic":'ORIGIN',         'delta':0, 'alpha':1, 'description':ORIGIN},
  0x33:{"mnemonic":'CALLER',         'delta':0, 'alpha':1, 'description':CALLER},
  0x34:{"mnemonic":'CALLVALUE',      'delta':0, 'alpha':1, 'description':CALLVALUE},
  0x35:{"mnemonic":'CALLDATALOAD',   'delta':1, 'alpha':1, 'description':CALLDATALOAD},
  0x36:{"mnemonic":'CALLDATASIZE',   'delta':0, 'alpha':1, 'description':CALLDATASIZE},
  0x37:{"mnemonic":'CALLDATACOPY',   'delta':3, 'alpha':0, 'description':CALLDATACOPY},
  0x38:{"mnemonic":'CODESIZE',       'delta':0, 'alpha':1, 'description':CODESIZE},
  0x39:{"mnemonic":'CODECOPY',       'delta':3, 'alpha':0, 'description':CODECOPY},
  0x3a:{"mnemonic":'GASPRICE',       'delta':0, 'alpha':1, 'description':GASPRICE},
  0x3b:{"mnemonic":'EXTCODESIZE',    'delta':1, 'alpha':1, 'description':EXTCODESIZE},
  0x3c:{"mnemonic":'EXTCODECOPY',    'delta':4, 'alpha':0, 'description':EXTCODECOPY},
  0x3d:{"mnemonic":'RETURNDATASIZE', 'delta':0, 'alpha':1, 'description':RETURNDATASIZE},
  0x3e:{"mnemonic":'RETURNDATACOPY', 'delta':3, 'alpha':0, 'description':RETURNDATACOPY},
  0x40:{"mnemonic":'BLOCKHASH',      'delta':1, 'alpha':1, 'description':BLOCKHASH},
  0x41:{"mnemonic":'COINBASE',       'delta':0, 'alpha':1, 'description':COINBASE},
  0x42:{"mnemonic":'TIMESTAMP',      'delta':0, 'alpha':1, 'description':TIMESTAMP},
  0x43:{"mnemonic":'NUMBER',         'delta':0, 'alpha':1, 'description':NUMBER},
  0x44:{"mnemonic":'DIFFICULTY',     'delta':0, 'alpha':1, 'description':DIFFICULTY},
  0x45:{"mnemonic":'GASLIMIT',       'delta':0, 'alpha':1, 'description':GASLIMIT},
  0x50:{"mnemonic":'POP',            'delta':1, 'alpha':0, 'description':POP},
  0x51:{"mnemonic":'MLOAD',          'delta':1, 'alpha':1, 'description':MLOAD},
  0x52:{"mnemonic":'MSTORE',         'delta':2, 'alpha':0, 'description':MSTORE},
  0x53:{"mnemonic":'MSTORE8',        'delta':2, 'alpha':0, 'description':MSTORE8},
  0x54:{"mnemonic":'SLOAD',          'delta':1, 'alpha':1, 'description':SLOAD},
  0x55:{"mnemonic":'SSTORE',         'delta':2, 'alpha':0, 'description':SSTORE},
  0x56:{"mnemonic":'JUMP',           'delta':1, 'alpha':0, 'description':JUMP},
  0x57:{"mnemonic":'JUMPI',          'delta':2, 'alpha':0, 'description':JUMPI},
  0x58:{"mnemonic":'PC',             'delta':0, 'alpha':1, 'description':PC},
  0x59:{"mnemonic":'MSIZE',          'delta':0, 'alpha':1, 'description':MSIZE},
  0x5a:{"mnemonic":'GAS',            'delta':0, 'alpha':1, 'description':GAS},
  0x5b:{"mnemonic":'JUMPDEST',       'delta':0, 'alpha':0, 'description':JUMPDEST},
  0x60:{"mnemonic":'PUSH1',          'delta':0, 'alpha':1, 'description':PUSHn},
  0x61:{"mnemonic":'PUSH2',          'delta':0, 'alpha':1, 'description':PUSHn},
  0x62:{"mnemonic":'PUSH3',          'delta':0, 'alpha':1, 'description':PUSHn},
  0x63:{"mnemonic":'PUSH4',          'delta':0, 'alpha':1, 'description':PUSHn},
  0x64:{"mnemonic":'PUSH5',          'delta':0, 'alpha':1, 'description':PUSHn},
  0x65:{"mnemonic":'PUSH6',          'delta':0, 'alpha':1, 'description':PUSHn},
  0x66:{"mnemonic":'PUSH7',          'delta':0, 'alpha':1, 'description':PUSHn},
  0x67:{"mnemonic":'PUSH8',          'delta':0, 'alpha':1, 'description':PUSHn},
  0x68:{"mnemonic":'PUSH9',          'delta':0, 'alpha':1, 'description':PUSHn},
  0x69:{"mnemonic":'PUSH10',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x6a:{"mnemonic":'PUSH11',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x6b:{"mnemonic":'PUSH12',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x6c:{"mnemonic":'PUSH13',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x6d:{"mnemonic":'PUSH14',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x6e:{"mnemonic":'PUSH15',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x6f:{"mnemonic":'PUSH16',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x70:{"mnemonic":'PUSH17',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x71:{"mnemonic":'PUSH18',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x72:{"mnemonic":'PUSH19',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x73:{"mnemonic":'PUSH20',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x74:{"mnemonic":'PUSH21',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x75:{"mnemonic":'PUSH22',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x76:{"mnemonic":'PUSH23',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x77:{"mnemonic":'PUSH24',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x78:{"mnemonic":'PUSH25',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x79:{"mnemonic":'PUSH26',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x7a:{"mnemonic":'PUSH27',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x7b:{"mnemonic":'PUSH28',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x7c:{"mnemonic":'PUSH29',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x7d:{"mnemonic":'PUSH30',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x7e:{"mnemonic":'PUSH31',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x7f:{"mnemonic":'PUSH32',         'delta':0, 'alpha':1, 'description':PUSHn},
  0x80:{"mnemonic":'DUP1',           'delta':1, 'alpha':2, 'description':DUPn},
  0x81:{"mnemonic":'DUP2',           'delta':2, 'alpha':3, 'description':DUPn},
  0x82:{"mnemonic":'DUP3',           'delta':3, 'alpha':4, 'description':DUPn},
  0x83:{"mnemonic":'DUP4',           'delta':4, 'alpha':5, 'description':DUPn},
  0x84:{"mnemonic":'DUP5',           'delta':5, 'alpha':6, 'description':DUPn},
  0x85:{"mnemonic":'DUP6',           'delta':6, 'alpha':7, 'description':DUPn},
  0x86:{"mnemonic":'DUP7',           'delta':7, 'alpha':8, 'description':DUPn},
  0x87:{"mnemonic":'DUP8',           'delta':8, 'alpha':9, 'description':DUPn},
  0x88:{"mnemonic":'DUP9',           'delta':9, 'alpha':10, 'description':DUPn},
  0x89:{"mnemonic":'DUP10',          'delta':10, 'alpha':11, 'description':DUPn},
  0x8a:{"mnemonic":'DUP11',          'delta':11, 'alpha':12, 'description':DUPn},
  0x8b:{"mnemonic":'DUP12',          'delta':12, 'alpha':13, 'description':DUPn},
  0x8c:{"mnemonic":'DUP13',          'delta':13, 'alpha':14, 'description':DUPn},
  0x8d:{"mnemonic":'DUP14',          'delta':14, 'alpha':15, 'description':DUPn},
  0x8e:{"mnemonic":'DUP15',          'delta':15, 'alpha':16, 'description':DUPn},
  0x8f:{"mnemonic":'DUP16',          'delta':16, 'alpha':17, 'description':DUPn},
  0x90:{"mnemonic":'SWAP1',          'delta':2, 'alpha':2, 'description':SWAPn},
  0x91:{"mnemonic":'SWAP2',          'delta':3, 'alpha':3, 'description':SWAPn},
  0x92:{"mnemonic":'SWAP3',          'delta':4, 'alpha':4, 'description':SWAPn},
  0x93:{"mnemonic":'SWAP4',          'delta':5, 'alpha':5, 'description':SWAPn},
  0x94:{"mnemonic":'SWAP5',          'delta':6, 'alpha':6, 'description':SWAPn},
  0x95:{"mnemonic":'SWAP6',          'delta':7, 'alpha':7, 'description':SWAPn},
  0x96:{"mnemonic":'SWAP7',          'delta':8, 'alpha':8, 'description':SWAPn},
  0x97:{"mnemonic":'SWAP8',          'delta':9, 'alpha':9, 'description':SWAPn},
  0x98:{"mnemonic":'SWAP9',          'delta':10, 'alpha':10, 'description':SWAPn},
  0x99:{"mnemonic":'SWAP10',         'delta':11, 'alpha':11, 'description':SWAPn},
  0x9a:{"mnemonic":'SWAP11',         'delta':12, 'alpha':12, 'description':SWAPn},
  0x9b:{"mnemonic":'SWAP12',         'delta':13, 'alpha':13, 'description':SWAPn},
  0x9c:{"mnemonic":'SWAP13',         'delta':14, 'alpha':14, 'description':SWAPn},
  0x9d:{"mnemonic":'SWAP14',         'delta':15, 'alpha':15, 'description':SWAPn},
  0x9e:{"mnemonic":'SWAP15',         'delta':16, 'alpha':16, 'description':SWAPn},
  0x9f:{"mnemonic":'SWAP16',         'delta':17, 'alpha':17, 'description':SWAPn},
  0xa0:{"mnemonic":'LOG0',           'delta':2, 'alpha':0, 'description':LOGn},
  0xa1:{"mnemonic":'LOG1',           'delta':3, 'alpha':0, 'description':LOGn},
  0xa2:{"mnemonic":'LOG2',           'delta':4, 'alpha':0, 'description':LOGn},
  0xa3:{"mnemonic":'LOG3',           'delta':5, 'alpha':0, 'description':LOGn},
  0xa4:{"mnemonic":'LOG4',           'delta':6, 'alpha':0, 'description':LOGn},
  0xf0:{"mnemonic":'CREATE',         'delta':3, 'alpha':1, 'description':CREATE},
  0xf1:{"mnemonic":'CALL',           'delta':7, 'alpha':1, 'description':CALL},
  0xf2:{"mnemonic":'CALLCODE',       'delta':7, 'alpha':1, 'description':CALLCODE},
  0xf3:{"mnemonic":'RETURN',         'delta':2, 'alpha':0, 'description':RETURN},
  #0xfd:{"mnemonic":'REVERT',         'delta':2, 'alpha':0, 'description':REVERT},
  #0xfe:{"mnemonic":'INVALID',        'delta':0, 'alpha':0, 'description':INVALID},
  0xff:{"mnemonic":'SELFDESTRUCT',   'delta':1, 'alpha':0, 'description':SELFDESTRUCT},
}


###########################
# Appendix I. Genesis Block

def genesis_block_and_state(filename,state):
  stream = open(filename, 'r')
  accts = json.loads(stream.read())
  stream.close()
  accts = accts["alloc"]
  for addyhex in accts:
    balance = int(accts[addyhex]["balance"])
    account = Account(0, #nonce
                      balance,
                      bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"), # empty state tree root
                      bytes.fromhex("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"), # empty code codeHash
                      bytes([]),
                      None,
                      bytes.fromhex(addyhex))
    #print(addyhex,account.b)
    #state[KEC(bytes.fromhex(addyhex))] = account
    state[bytes.fromhex(addyhex)] = account
  #stateRoot = state.merkleize()
  genesis_block = None #Block(bytes([0]*32),KEC(RLP(())),bytes([0]*20),stateRoot,0,0,bytes([0])*256,2**17,0,0,3141592,0,0,bytes([0]*32),KEC(bytes([42]),(),()))
  # note: not sure how values () will RLP-ize
  return state,genesis_block
  


