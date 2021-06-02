#!/usr/bin/env python3 

#import devp2p				# p2p for communicating with other nodes


import json
import pickle
import sys

import ethereum_001_frontier as e1
#import ethereum_001_frontier_works2_on_46402 as e1



"""
606060405261010a806100136000396000f30060606040526000357c0100000000000000000000000000000000000000000000000000000000900480630f59f83a1461003957610037565b005b6100446004506100b2565b60405180806020018281038252838181518152602001915080519060200190808383829060006004602084601f0104600302600f01f150905090810190601f1680156100a45780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b6020604051908101604052806000815260200150604060405190810160405280600381526020017f65746800000000000000000000000000000000000000000000000000000000008152602001509050610107565b9056
"""


####################
# input/output files

def get_block(num):
  #dir_ = str((blocknum//100000)*100000).zfill(8)+"/"
  #dir_ = ""
  dir_ = "./blocks00000000/"
  filename = str(num).zfill(8)+".json"
  stream = open(dir_+filename, 'r')
  block = json.loads(stream.read())
  #print(num)
  #print(json.dumps(block, indent=1))
  stream.close()
  block = block["result"]
  blockheader = e1.BlockHeader(
          bytes.fromhex(block["parentHash"][2:]),
          bytes.fromhex(block["sha3Uncles"][2:]),
          bytes.fromhex(block["miner"][2:]),
          bytes.fromhex(block["stateRoot"][2:]),
          bytes.fromhex(block["transactionsRoot"][2:]),
          bytes.fromhex(block["receiptsRoot"][2:]),
          bytes.fromhex(block["logsBloom"][2:]),
          int(block["difficulty"][2:],16),
          int(block["number"][2:],16),
          int(block["gasLimit"][2:],16),
          int(block["gasUsed"][2:],16),
          int(block["timestamp"][2:],16),
          bytes.fromhex(block["extraData"][2:]),
          bytes.fromhex(block["mixHash"][2:]),
          int(block["nonce"][2:],16),
          )
  transactions = []
  for T in block["transactions"]:
    if T["to"]==None:
      init = bytes.fromhex(T["input"][2:])
      data = bytes()
    else:
      init = bytes()
      data = bytes.fromhex(T["input"][2:])
    #if T["to"]==None:   # infura sent blocks with to field: '0x' or null (starting block 46402)
    #   T["to"] = "0x"
    transactions.append(e1.Transaction(
        int(T["nonce"][2:],16),
        int(T["gasPrice"][2:],16),
        int(T["gas"][2:],16),
        bytes.fromhex(T["to"][2:]) if T["to"] else b'',     # None for contract creation
        int(T["value"][2:],16),
        int(T["v"][2:],16),
        bytes.fromhex(T["r"][2:].zfill(64)),
        bytes.fromhex(T["s"][2:].zfill(64)),
        #int(T["r"][2:],16),
        #int(T["s"][2:],16),
        init,
        data
        ))
  ommers = []
  for o in block["uncles"]:
    ommers.append(get_uncle(num,len(ommers)))
  receipts = [] # this doesn't come with the block, must fill it in separately
  totalDifficulty = int(block["totalDifficulty"][2:],16),
  block = e1.Block(blockheader,transactions,ommers,receipts,totalDifficulty)
  return block


def get_uncle(blocknum,idx):
  #dir_ = "uncles_"+str((blocknum//100000)*100000).zfill(8)+"/"
  #dir_ = ""
  dir_ = "./uncles_00000000/"
  filename = "uncle_"+str(blocknum).zfill(8)+"_"+str(idx)+".json"
  stream = open(dir_+filename, 'r')
  block = json.loads(stream.read())
  stream.close()
  block = block["result"]
  blockheader = e1.BlockHeader(
          bytes.fromhex(block["parentHash"][2:]),
          bytes.fromhex(block["sha3Uncles"][2:]),
          bytes.fromhex(block["miner"][2:]),
          bytes.fromhex(block["stateRoot"][2:]),
          bytes.fromhex(block["transactionsRoot"][2:]),
          bytes.fromhex(block["receiptsRoot"][2:]),
          bytes.fromhex(block["logsBloom"][2:]),
          int(block["difficulty"][2:],16),
          int(block["number"][2:],16),
          int(block["gasLimit"][2:],16),
          int(block["gasUsed"][2:],16),
          bytes.fromhex(block["timestamp"][2:]),
          bytes.fromhex(block["extraData"][2:]),
          bytes.fromhex(block["mixHash"][2:]),
          int(block["nonce"][2:],16),
          )
  return blockheader

def save_state_to_pickle_file(state, filename):
  with open(filename+'.pkl', 'wb') as f:
    pickle.dump(state, f, pickle.HIGHEST_PROTOCOL)

def load_state_from_pickle_file(filename):
  with open(filename + '.pkl', 'rb') as f:
    return pickle.load(f)


def save_state_to_json_file(state, filename):
  with open(filename+'.json', 'w') as f:
    f.write("{\n")
    comma_flag=0
    for s in state:
      if comma_flag:
        f.write(",\n")
      comma_flag=1
      #f.write("\n")
      f.write("\"0x"+s.hex()+"\":{\n")
      f.write(" \"balance\": \""+hex(state[s].b)+"\",\n")
      f.write(" \"code\": \"0x"+state[s].bytecode.hex()+"\",\n")
      f.write(" \"nonce\": \""+hex(state[s].n)+"\",\n")
      if state[s].storage:
        f.write(" \"storage\": {\n") 
        comma_flag2=0
        for l in state[s].storage:
          if comma_flag2:
            f.write(",\n")
          comma_flag2=1
          f.write("  \"0x"+l.hex()+":\""+state[s].storage[l].hex()+"\"") 
        f.write(" }\n")
      else:
        f.write(" \"storage\":{}\n") 
      f.write("}")
    f.write("\n}")
    f.close()

def load_state_from_json_file(filename):
  f = open(filename, 'r')
  accts = json.loads(f.read())
  f.close()
  #print("load_state_from_json_file()",accts)
  if "alloc" in accts:
    accts = accts["alloc"]
  state = e1.StateTree()
  for addyhex in accts:
    nonce = 0
    if "nonce" in accts[addyhex]:
      print(accts[addyhex]["nonce"])
      nonce_str = accts[addyhex]["nonce"]
      nonce = int(nonce_str[2:] if nonce_str.startswith("0x") else nonce_str,16)
    balance = 0
    if "balance" in accts[addyhex]:
      #balance = int(accts[addyhex]["balance"])
      balance_str = accts[addyhex]["balance"]
      balance = int(balance_str[2:] if balance_str.startswith("0x") else balance_str,16)
    bytecode = bytearray([])
    if "bytecode" in accts[addyhex]:
      bytecode = bytes.fromhex(accts[addyhex]["bytecode"])
    storage = {}
    if "storage" in accts[addyhex]:
      for k in accts[addyhex]["storage"]:
        storage[bytes.fromhex(k)] = bytes.fromhex(accts[addyhex]["storage"][k])
    addy = bytes.fromhex(addyhex[2:])
    account = e1.Account(nonce,
                      balance,
                      e1.StateTree_merkleize(storage),
                      e1.KEC(bytecode),
                      bytecode,
                      storage,
                      addy)
    state[addy] = account
  return state

def load_txs_json_and_env_json_to_block(txs_filename,env_filename):

  stream = open(txs_filename, 'r')
  txs_json = json.loads(stream.read())
  stream.close()
  txs = []
  for tx in txs_json:
    gas = 0
    if "gas" in txs:
      gas = int(txs_json["gas"][2:],16)
    gasPrice = 0
    if "gasPrice" in txs_json:
      gasPrice = int(txs_json["gasPrice"][2:],16)
    hash_ = bytearray([0]*32)
    if "hash" in txs_json:
      hash_ = bytes.fromhex(txs_json["hash"][2:],16)
    input_ = bytearray([])
    if "input" in txs_json:
      input_ = bytes.fromhex(txs_json["input"][2:])
    nonce=0
    if "nonce" in txs_json:
      nonce = int(txs_json["nonce"][2:],16)
    r = bytearray([0]*32)
    if "r" in txs_json:
      r = bytes.fromhex(txs_json["r"][2:])
    s = bytearray([0]*32)
    if "s" in txs_json:
      s = bytes.fromhex(txs_json["s"][2:])
    to = bytearray([])
    if "to" in txs_json:
      to = bytes.fromhex(txs_json["to"][2:])
    v = 27
    if "v" in txs_json:
      v = int(txs_json["v"][2:],16)
    value = 0
    if "value" in txs_json:
      value = int(txs_json["value"][2:],16)
    # change if message call or contract creation
    if to:
      init=input_
      data=bytes([])
    else:
      init=bytes([])
      data=input_
    txs.append(e1.Transaction(nonce,gasPrice,gas,to,value,v,r,s,init,data))

  stream = open(env_filename, 'r')
  env = json.loads(stream.read())
  stream.close()
  coinbase = "0x"+"0"*40
  if "currentCoinbase" in env:
    coinbase = env["currentCoinbase"]
  difficulty = 1
  if "currentDifficulty" in env:
    difficulty = int(env["currentDifficulty"][2:],16)
  gasLimit = 10000000000000
  if "currentGasLimit" in env:
    gasLimit = int(env["currentGasLimit"][2:],16)
  number = 1
  if "currentNumber" in env:
    number = int(env["currentNumber"])
  timestamp = 1
  if "currentTimestamp" in env:
    timestamp = int(env["currentTimestamp"][2:],16)
  recent_block_hashes = {}
  if "blockHashes" in env:
    for idx,hash_ in enumerate(env["blockHashes"]):
      recent_block_hashes[int(idx)] = bytes.fromhex(hash_[2:])
  ommers = []
  if "ommers" in env:
    for ommer in env["ommers"]:
      ommers.append(ommer)
      # each ommer looks like: {"delta":  1, "address": "0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" }

  # create header and block
  parentHash = bytes([0]*32)
  ommerHash = bytes([0]*32)
  stateRoot = bytes([0]*32)
  txsRoot = bytes([0]*32)
  rcptsRoot = bytes([0]*32)
  logsBloom = bytes([0]*32)
  gasUsed = 0
  extraData = bytes([])
  mixHash = bytes([0]*32)
  blockNonce = 0
  header = e1.BlockHeader(parentHash,ommerHash,coinbase,stateRoot,txsRoot,rcptsRoot,logsBloom,difficulty,number,gasLimit,gasUsed,timestamp,extraData,mixHash,blockNonce)
  receipts = []
  block = e1.Block(header,txs,ommers,receipts,difficulty)

  return block,recent_block_hashes


##############################################################
# loop over blocks, reading them from file, and executing them

def sync(block_num_end):

  # Start networking process.
  # Because of the asynchronous nature of networking, we create a new process.
  #p2p = devp2p.start()

  # Setup data directory, parse blockchain/account data if available.
  #with open("genesis.json", 'rb') as f:
  #  genesis_json = json(f)
  #  accounts.set_from_json(genesis_json)
  #  blocks.set_from_json(genesis_json)
  #  block_number = blocks.get_block_number_from_json(genesis_json);

  # init state from genesis
  state = e1.StateTree()
  state, genesis_block = e1.genesis_block_and_state("genesis_frontier.json",state)
  #for a in state:
  #  acct = state[a]
  #  print(acct.address.hex(),acct.b)

  # first block is special: no coinbase reward
  if 1:
    block = get_block(0)
    root_hash = e1.TRIE(e1.y(state))
    print("block 0 root_hash",root_hash.hex())
    if root_hash.hex()!="d7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544":
      print("error with genesis state root")
      return
    blocknum = 1
  else:
    #blocknum = 46146   # just before first transaction
    #blocknum = 46211
    #blocknum = 46346
    #blocknum = 46400
    #blocknum = 47200
    blocknum = 48600
    blocknum = 48642
    blocknum = 48679

    #blocknum = 46402
    #blocknum = 40000
    blocknum = 46400
    #blocknum = 48500
    blocknum = 49000
    state = load_state_from_pickle_file("snapshot_"+str(blocknum))

  #for a in state:
  #  acct = state[a]
  #  print(acct.address.hex(),acct.b)

  # loop for frontier
  #frontier_last_blocknum = block_num_end
  frontier_last_blocknum = blocknum+1000000
  recentblocks = {}
  try:
    while blocknum < frontier_last_blocknum:
      #if blocknum==49018:
      #  save_state_to_json_file(state, "49018_prestate")
      #if blocknum==46382:
      if blocknum%1000==0: #46146:
        #pass
        save_state_to_pickle_file(state, "snapshot_"+str(blocknum))
      block = get_block(blocknum)
      recentblocks[blocknum] = block
      state = e1.Pi(state,block,recentblocks)
      root_hash = e1.StateTree_merkleize(state) #e1.TRIE(e1.y(state))
      #root_hash = e1.TRIE(e1.y(state))
      if block.H.r != root_hash:
        print("error root_hash",blocknum,block.H.r.hex(), root_hash.hex())
        #save_state_to_pickle_file(state, "snapshot_"+str(blocknum))
        return
      print("block",blocknum,"root_hash",root_hash.hex())
      blocknum+=1
  except KeyboardInterrupt:
    pass
    # keyboard interrupt gets us out of main loop

  if 0:
    save_state_to_pickle_file(state,"snapshot_"+str(blocknum))


"""
  # loop for homestead
  while block_number < 100:
    # get block
    block = p2p.download_block()
    while p2p.waiting:
      miner.mine_block(mine_flag, p2p.difficulty)
    block = p2p.current_block

    # execute block
    evm.execute_block(block, accounts, blocks)

    # apply changes to state
    accounts.apply(block)

    block_number+=1

  
  # loop after dao fork
  while block_number < 200:
    # get block

    # execute block

    # apply changes to state
 

  # loop after anti-dos fork
  while block_number < 300:
    # get block

    # execute block

    # apply changes to state


  # loop after spurious dragon fork
  while block_number < 400:
    # get block

    # execute block

    # apply changes to state


  # loop after byzantium fork
  while block_number < 500:
    # get block

    # execute block

    # apply changes to state


  # loop after constantinople fork
  while block_number < 600:
    # get block

    # execute block

    # apply changes to state

  
  # 
"""




"""
if 1==1 and \   "ok"
   0==0:    # second case
   print(1)

if (1==1 and # ok
   0==0):    # second case
   print(1)
"""

# this mimics geth's t8n interface for retesteth
def t8n():
  print("t8n()")
  state_filename = ""
  env_filename = ""
  txs_filename = ""
  for arg in sys.argv:
    if arg[:14] == "--input.alloc=":
      state_filename = arg[14:]
    if arg[:12] == "--input.env=":
      env_filename = arg[12:]
    if arg[:12] == "--input.txs=":
      txs_filename = arg[12:]
  if state_filename and txs_filename and env_filename:
    print("ok")
    state = load_state_from_json_file(state_filename)
    block,recent_block_hashes = load_txs_json_and_env_json_to_block(txs_filename,env_filename)
    recentblocks = {}
    print("block number",block.H.i)
    recentblocks[block.H.i] = block
    state = e1.Pi(state,block,recentblocks)
    root_hash = e1.StateTree_merkleize(state)
    print(root_hash)
  """
BLOCK=49018
PATH_TO_JSON=../go-ethereum/pauls_tests/$BLOCK
python3 main.py t8n --input.alloc=$PATH_TO_JSON/alloc_full.json --input.txs=$PATH_TO_JSON/txs.json --input.env=$PATH_TO_JSON/env.json
  """


if __name__ == "__main__":
  if len(sys.argv)>1 and sys.argv[1] == "t8n": 
    t8n()
  else: # start executing from genesis
    #end_block = 46147   # until first transaction
    end_block = 100000
    sync(end_block) 


