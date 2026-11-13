/- GID: D5/S0/Automata/CanonicalDFAOKernel
   generality: G
   mirror-B: D5/B/S0/Automata/CanonicalDFAOKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordinary finite DFAOs correct only on canonical most-significant-first expansions have finite arithmetic kernels, including the independently read zero term. -/

import D5.S0.Automata.FiniteKernelDFAO
import D5.S0.Automata.DFAOStateLowerBound

/-! Canonical MSDF machines are connected to the adopted arithmetic kernel.
The n=0 kernel value is kept separately; no padding hypothesis is imposed. -/

namespace D5.S1.Recurrence.AntiRecurrenceAutomaticity

/-- Standard base-b digits, most significant first. The remainder operation is
only a total coercion into Fin b; standard digits already lie below b. -/
def msfDigits (b : ℕ) (hb : 0 < b) (n : ℕ) : List (Fin b) := (Nat.digits b n).reverse.map (fun d => ⟨d % b, Nat.mod_lt d hb⟩)

end D5.S1.Recurrence.AntiRecurrenceAutomaticity

namespace D5.S0.Automata.CanonicalDFAOKernel

open D5.S0.Automata.DFAOStateLowerBound
open D5.S0.Automata.FiniteKernelDFAO
open D5.S1.Recurrence.AntiRecurrenceAutomaticity (msfDigits)

/-- An ordinary finite output machine correct on positive canonical MSDF
expansions. Its output at zero is unconstrained. This includes either the
empty-word or single-zero convention, without assuming leading-zero tolerance. -/
def CanonicalAutomatic {B : Type*} (k : ℕ) (hk : 2 ≤ k) (a : ℕ → B) : Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, ∃ M : DFAO (Fin k) B Q,
    ∀ n, 0 < n → M.evalOutput (msfDigits k (by omega) n) = a n

private theorem canonical_append (k : ℕ) (hk : 2 ≤ k) (e r n : ℕ)
    (hr : r < k ^ e) (hn : 0 < n) :
    msfDigits k (by omega) (k ^ e * n + r) =
      msfDigits k (by omega) n ++
        ((Nat.digits k r ++ List.replicate (e - (Nat.digits k r).length) 0).reverse.map
          (fun d => (⟨d % k, Nat.mod_lt d (by omega)⟩ : Fin k))) := by
  have hlen := (Nat.digits_length_le_iff (by omega : 1 < k) r).mpr hr
  have hd := Nat.digits_append_zeroes_append_digits (b := k)
    (k := e - (Nat.digits k r).length) (m := n) (n := r) (by omega) hn
  rw [Nat.add_sub_cancel' hlen] at hd
  rw [show r + k ^ e * n = k ^ e * n + r by omega] at hd
  simp only [msfDigits, ← hd, List.reverse_append, List.map_append]

/-- Every canonical-MSDF DFAO has finite arithmetic kernel. This handles
canonical zero separately and therefore needs no assumption on zero transitions. -/
theorem canonical_finite_kernel {B : Type*} (k : ℕ) (hk : 2 ≤ k)
    (a : ℕ → B) (ha : CanonicalAutomatic k hk a) : Finite ↥(kKernel k a) := by
  classical
  obtain ⟨Q, hQ, M, hM⟩ := ha
  letI : Fintype Q := hQ
  let decode : Option Q × (Q → Q) → ℕ → B := fun p n =>
    if n = 0 then match p.1 with
      | none => a 0
      | some q => M.output q
    else M.output (p.2 (M.toDFA.eval (msfDigits k (by omega) n)))
  have hfin : (Set.range decode).Finite := Set.finite_range _
  rw [Set.finite_coe_iff]
  apply hfin.subset
  intro b hb
  obtain ⟨e, r, hr, rfl⟩ := hb
  let suffix :=
    (Nat.digits k r ++ List.replicate (e - (Nat.digits k r).length) 0).reverse.map
      (fun d => (⟨d % k, Nat.mod_lt d (by omega)⟩ : Fin k))
  refine ⟨⟨if r = 0 then none else some (M.toDFA.eval (msfDigits k (by omega) r)),
    fun q => M.toDFA.evalFrom q suffix⟩, ?_⟩
  funext n
  by_cases hn : n = 0
  · by_cases hr0 : r = 0
    · simp [decode, hn, hr0]
    · simpa only [decode, hn, hr0, ↓reduceIte, mul_zero, zero_add, DFAO.evalOutput]
        using hM r (by omega)
  · have hnpos : 0 < n := by omega
    dsimp [decode]
    have hv : 0 < k ^ e * n + r := by positivity
    rw [if_neg hn, ← hM _ hv, canonical_append k hk e r n hr hnpos]
    simp only [DFAO.evalOutput, DFA.eval, DFA.evalFrom_of_append, suffix]

end D5.S0.Automata.CanonicalDFAOKernel
