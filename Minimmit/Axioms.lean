import Minimmit.Basic
import Minimmit.Protocol

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

/-- Idealized collision-resistant hashing, declared as an axiom (Barrier 1):
    on valid states the hash parent-link is functional. Sound relative to the
    collision resistance of `H` — the hash component of `b = (v, Tr, h)`
    determines the parent uniquely, since two distinct parents with hash `h`
    would exhibit a collision; the negligible collision probability is
    abstracted away here. Guarded by `ValidStateView` exactly as
    `signature_unforgeable` is guarded by `ValidExecution` (an adversarial
    `StateView` with a genuinely relational `parentLink` would otherwise
    prove `False`). Source: arXiv:2508.10862 §2 — `H` is collision-resistant,
    giving each block a unique ancestor chain and a well-defined `b.Tr*`;
    this powers the log-level Consistency reading
    (`Minimmit.consistency_logs`). This is a **permanent** idealized
    assumption; there is no Phase-2 follow-up. -/
axiom collision_resistant {n : Nat} (sv : StateView n) :
    ValidStateView sv → sv.ParentFunctional

end Minimmit
