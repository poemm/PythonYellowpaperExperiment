


  


#######################
## Keccak

# pip install pysha3
import sha3

def keccak256(bytes_):
  return sha3.keccak_256(bytes_).digest()

def keccak512(bytes_):
  return sha3.keccak_512(bytes_).digest()



#######################
## secp256k1

# pip install coincurve
from coincurve.ecdsa import deserialize_recoverable, recover
from coincurve.keys import PublicKey

import coincurve

def secp256k1sign(msgbytes_,privkey):
  pass

def secp256k1recover(r,s,v,msg_hash):
  #print("secp256k1recover",r,s,v,msg_hash)
  sig = bytearray([0]*65)
  sig[32-len(r):32] = r
  sig[64-len(s):64] = s
  sig[64] = v
  sig = bytes(sig)
  #print("sig,msg_hash:",sig.hex(),msg_hash.hex())
  pub = coincurve.PublicKey.from_signature_and_message(sig,msg_hash,hasher=None)
  #print("pub",pub)
  pub = pub.format(compressed=False)[1:]
  #pub = pub.format(compressed=False)
  #pub = pub.format()
  #print("pub formatted",pub)
  return pub
  #deserialized_sig = deserialize_recoverable(serialized_sig)
  #print(deserialized_sig)
  #recovered_pubkey = PublicKey(recover(msg_hash,deserialized_sig)).format()
  #print(recovered_pubkey)
  #return recovered_pubkey
  #sig = empty.ecdsa_recoverable_deserialize(serialized_sig, v-27)
  #empty.pubkey = empty.ecdsa_recover(hash_,sig,raw=True)
  #recovered_pubkey = empty.serialize(compressed=False)[1:]

