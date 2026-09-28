"""Smoke test: BLS12-381 via the Lean-backed spec, cross-checked against py_ecc."""
from eth_cryptography_specs import bls
from py_ecc.bls import G2ProofOfPossession as ref

SKS = [
    0x263dbd792f5b1be47ed85f8938c0f29586af0d3ac7b977f21c278fe1462040e3,
    0x47b8192d77bf871b62e87859d653922725724a5c031afeabc60bcef5ff665138,
    0x328388aff0d4a5b7dc9205abd374e7e98f3cd9f3418edb4eafda5fb16473d216,
]
MSG = b"\x12" * 32

pks  = [ref.SkToPk(sk) for sk in SKS]
sigs = [ref.Sign(sk, MSG) for sk in SKS]
agg_sig = ref.Aggregate(sigs)

print("BYTES_PER_PUBKEY   :", bls.BYTES_PER_PUBKEY)
print("BYTES_PER_SIGNATURE:", bls.BYTES_PER_SIGNATURE)

# 1. aggregate pubkeys through the Lean spec, compare with py_ecc
lean_apk = bls.eth_aggregate_pubkeys(pks)
ref_apk  = ref._AggregatePKs(pks)
print("\neth_aggregate_pubkeys ->", lean_apk.hex())
print("py_ecc  _AggregatePKs ->", ref_apk.hex())
print("match:", lean_apk == ref_apk)

# 2. verify the aggregate signature through the Lean spec
ok = bls.eth_fast_aggregate_verify(pks, MSG, agg_sig)
print("\neth_fast_aggregate_verify (valid sig)   :", ok)

# 3. negative case: tamper with the message
bad = bls.eth_fast_aggregate_verify(pks, b"\x13" * 32, agg_sig)
print("eth_fast_aggregate_verify (wrong msg)   :", bad)

# 4. edge case from the spec: empty pubkeys + G2 infinity signature -> True
inf_sig = b"\xc0" + b"\x00" * 95
print("eth_fast_aggregate_verify ([], inf sig) :",
      bls.eth_fast_aggregate_verify([], MSG, inf_sig))

assert lean_apk == ref_apk and ok and not bad
print("\nALL CHECKS PASSED")
