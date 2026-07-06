import Minimmit.Liveness.Lemma5_7
import Minimmit.Responsiveness.Lemma5_10

set_option autoImplicit false

namespace Minimmit

/-!
# The concrete round-robin leader schedule (§4)

`lead(v) = p_{j+1}` with `j = v mod n`, under the 0-indexed labelling
`p_{i+1} := (i : Fin n)`: view `v` is led by processor `v % n`. Discharges the
two rotation hypotheses threaded through Tracks B/C — `hrot` (`lemma_5_7`) and
`hrr` (`lemma_5_10`) — as theorems about this schedule, and packages the
resulting corollaries. `StateView.lead` stays abstract, so custom schedules
remain supported; this is the canonical instance.
-/

/-- The §4 round-robin schedule: view `v` is led by processor `v % n`
    (the paper's `p_{j+1}`, `j = v mod n`, relabelled 0-indexed). -/
def roundRobin (n : Nat) (hn : 0 < n) : View → Processor n :=
  fun v => ⟨v % n, Nat.mod_lt v hn⟩

/-- Every processor leads cofinally many views — the `hrot` hypothesis of
    `lemma_5_7`, discharged for `roundRobin`. Witness: the first multiple of
    `n` past `v₀`, offset by `p`. -/
theorem roundRobin_rotates {n : Nat} (hn : 0 < n) :
    ∀ (p : Processor n) (v₀ : View), ∃ v, v₀ ≤ v ∧ roundRobin n hn v = p := by
  intro p v₀
  refine ⟨n * (v₀ / n + 1) + p.val, ?_, ?_⟩
  · have hdm := Nat.div_add_mod v₀ n
    have hlt := Nat.mod_lt v₀ hn
    have hexp : n * (v₀ / n + 1) = n * (v₀ / n) + n := by ring
    omega
  · apply Fin.ext
    show (n * (v₀ / n + 1) + p.val) % n = p.val
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]

/-- Within any window of `n` consecutive views the round-robin leaders are
    pairwise distinct — the `hrr` hypothesis of `lemma_5_10`, discharged for
    `roundRobin`. Equal residues with `|v − w| < n` force `v = w`. -/
theorem roundRobin_inj_window {n : Nat} (hn : 0 < n) :
    ∀ v w : View, v ≠ w → v < w + n → w < v + n →
      roundRobin n hn v ≠ roundRobin n hn w := by
  intro v w hne hvw hwv heq
  have hmod : v % n = w % n := congrArg Fin.val heq
  have hv := Nat.div_add_mod v n
  have hw := Nat.div_add_mod w n
  have hdv : n * (v / n + 1) = n * (v / n) + n := by ring
  have hdw : n * (w / n + 1) = n * (w / n) + n := by ring
  have h1 : v / n < w / n + 1 :=
    Nat.lt_of_mul_lt_mul_left (a := n) (by omega)
  have h2 : w / n < v / n + 1 :=
    Nat.lt_of_mul_lt_mul_left (a := n) (by omega)
  have hdd : v / n = w / n := by omega
  have hnn : n * (v / n) = n * (w / n) := by rw [hdd]
  omega

/-- **Lemma 5.7 (Liveness), round-robin form.** `lemma_5_7` with the concrete
    §4 schedule; the rotation hypothesis is discharged by
    `roundRobin_rotates`. -/
theorem lemma_5_7_roundRobin {n f : Nat} {GST Δ : Time} (sv : StateView n)
    (e : Execution n) (hd : sv.VoteDiscipline e)
    (hrd : sv.ReceiptDiscipline e) (hvd : sv.ViewDiscipline e f)
    (hnw : sv.NetworkDiscipline e f) (hld : sv.LeaderDiscipline e f)
    (hdd : sv.DeliveryDiscipline e f GST Δ)
    (htd : sv.TimerDiscipline e f Δ) (htx : sv.TxDiscipline e f)
    (hnf : 5 * f + 1 ≤ n) (hfb : e.FaultBound f)
    (hn : 0 < n) (hlead : sv.lead = roundRobin n hn)
    {tr : Tx} {pᵢ : Processor n} {t₀ : Time}
    (hpc : e.Correct pᵢ) (hrecv : sv.receivedTx pᵢ t₀ tr) :
    ∀ p, e.Correct p → ∃ t', sv.inLog p t' tr :=
  lemma_5_7 sv e hd hrd hvd hnw hld hdd htd htx hnf hfb
    (by rw [hlead]; exact roundRobin_rotates hn) hpc hrecv

/-- **Lemma 5.10 (optimistic responsiveness), round-robin form.**
    `lemma_5_10` with the concrete §4 schedule; the window-injectivity
    hypothesis is discharged by `roundRobin_inj_window`. -/
theorem lemma_5_10_roundRobin {n f fa : Nat} {GST Δ δ : Time}
    (sv : StateView n) (e : Execution n) (hd : sv.VoteDiscipline e)
    (hrd : sv.ReceiptDiscipline e) (hvd : sv.ViewDiscipline e f)
    (hnw : sv.NetworkDiscipline e f) (hld : sv.LeaderDiscipline e f)
    (hdd : sv.DeliveryDiscipline e f GST δ) (htd : sv.TimerDiscipline e f Δ)
    (hδΔ : δ ≤ Δ) (hfd : sv.FinalityDiscipline e f)
    (htx : sv.TxDiscipline e f)
    (hnf : 5 * f + 1 ≤ n) (hfa : e.FaultBound fa) (hfaf : fa ≤ f)
    (hn : 0 < n) (hlead : sv.lead = roundRobin n hn)
    {tr : Tx} {pᵢ : Processor n} {t : Time}
    (hpc : e.Correct pᵢ) (hGST : GST ≤ t) (hrecv : sv.receivedTx pᵢ t tr) :
    ∀ p, e.Correct p →
      ∃ t' ≤ t + 2 * δ + (fa + 1) * (2 * Δ + 2 * δ + 1) + 4 * δ,
        sv.inLog p t' tr :=
  lemma_5_10 sv e hd hrd hvd hnw hld hdd htd hδΔ hfd htx hnf hfa hfaf
    (by rw [hlead]; exact roundRobin_inj_window hn) hpc hGST hrecv

end Minimmit
