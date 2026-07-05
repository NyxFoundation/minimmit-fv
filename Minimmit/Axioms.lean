import Minimmit.Basic

set_option autoImplicit false

namespace Minimmit

/-- Idealized digital signatures (EUF-CMA), declared as an axiom (Barrier 1).
    Sound relative to the signature scheme being unforgeable; the negligible
    forgery probability is abstracted away here. Guarded by `ValidExecution` so
    it constrains only real protocol executions (without the guard, an
    adversarial `Execution` value would let this axiom prove `False`).
    Source: arXiv:2508.10862 §5 — the quorum-counting arguments rely on "`k`
    messages each signed by a different processor", i.e. on equating a valid
    signed message with its signer. This is a **permanent** idealized
    assumption; there is no Phase-2 follow-up. -/
axiom signature_unforgeable {n : Nat} (e : Execution n) :
    ValidExecution e → SignatureUnforgeable e

end Minimmit
