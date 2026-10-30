/- GID: D5/S1/Dynamics/Shadowing/ReturnDistanceSubshift
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/ReturnDistanceSubshift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact binary return-distance subshifts and their exact-length word language. -/

import D5.S1.Dynamics.Shadowing.ReturnDistanceSupport
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-! Return distances count the step between successive ones; distance one is allowed
when one belongs to D. Finite supports and the zero configuration are included. -/

open Set Function SymbolicDynamics.FullShift
open scoped PiCountable

namespace D5.S1.Dynamics.Shadowing

/-- A binary finite alphabet with its inherited discrete metric. -/
abbrev ReturnBit := ↥(Finset.range 2)
def returnZero : ReturnBit := ⟨0, by decide⟩
def returnOne : ReturnBit := ⟨1, by decide⟩

noncomputable instance returnConfigurationMetric : MetricSpace (ℤ → ReturnBit) :=
  PiCountable.metricSpace

@[simp] theorem return_zero_ne_one : returnZero ≠ returnOne := by decide

/-- The set of one coordinates of an actual two-sided configuration. -/
def oneSupport (x : ℤ → ReturnBit) : Set ℤ := {i | x i = returnOne}

def ReturnLegal (D : Set ℤ) (x : ℤ → ReturnBit) : Prop :=
  ∀ p q, SupportAdjacent (oneSupport x) p q → q - p ∈ D

/-- The local consecutive-pair condition is closed in the genuine product topology. -/
theorem return_legal_closed (D : Set ℤ) : IsClosed {x | ReturnLegal D x} := by
  have hopen (p q : ℤ) : IsOpen {x : ℤ → ReturnBit |
      SupportAdjacent (oneSupport x) p q} := by
    by_cases hpq : p < q
    · have he (i : ℤ) : IsOpen {x : ℤ → ReturnBit | x i = returnOne} := by
        simpa only [Set.preimage, Set.mem_singleton_iff] using
          (continuous_apply i : Continuous (fun x : ℤ → ReturnBit => x i)).isOpen_preimage
            ({returnOne} : Set ReturnBit) (isOpen_discrete _)
      have hn (i : ℤ) : IsOpen {x : ℤ → ReturnBit | x i ≠ returnOne} := by
        simpa only [Set.preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using
          (continuous_apply i : Continuous (fun x : ℤ → ReturnBit => x i)).isOpen_preimage
            ({returnOne}ᶜ : Set ReturnBit) (isOpen_discrete _)
      have hh := (Set.finite_Ioo p q).isOpen_biInter (fun i _ => hn i)
      convert (he p).inter ((he q).inter hh) using 1
      ext x
      simp [SupportAdjacent, oneSupport, hpq, and_assoc]
    · simp [SupportAdjacent, hpq]
  unfold ReturnLegal
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro p
  apply isClosed_iInter
  intro q
  apply isClosed_imp (hopen p q)
  by_cases hd : q - p ∈ D <;> simp [hd]

/-- All integer shifts preserve the same consecutive return distances. -/
theorem return_legal_shift {D : Set ℤ} {x : ℤ → ReturnBit}
    (hx : ReturnLegal D x) (g : ℤ) : ReturnLegal D (shift g x) := by
  intro p q hpq
  have hpqlt := hpq.2.2.1
  have hpair : SupportAdjacent (oneSupport x) (g + p) (g + q) := by
    refine ⟨hpq.1, hpq.2.1, by omega, ?_⟩
    intro t hpt htq ht
    apply hpq.2.2.2 (t - g) (by omega) (by omega)
    change x (g + (t - g)) = returnOne
    simpa [oneSupport] using ht
  have hd := hx (g + p) (g + q) hpair
  simpa using hd

/-- Bundled Mathlib subshift on a finite alphabet and integer coordinates. -/
def returnDistanceSubshift (D : Set ℤ) : SymbolicDynamics.FullShift.Subshift ReturnBit ℤ where
  carrier := {x | ReturnLegal D x}
  isClosed := return_legal_closed D
  mapsTo := fun g _ hx => return_legal_shift hx g

abbrev ReturnPoint (D : Set ℤ) := {x : ℤ → ReturnBit // ReturnLegal D x}

instance returnPointCompact (D : Set ℤ) : CompactSpace (ReturnPoint D) :=
  isCompact_iff_compactSpace.mp (return_legal_closed D).isCompact

/-- The actual shift by one on the subshift. -/
def returnShift (D : Set ℤ) (x : ReturnPoint D) : ReturnPoint D :=
  ⟨shift 1 x.1, return_legal_shift x.2 1⟩

theorem return_shift_continuous (D : Set ℤ) : Continuous (returnShift D) :=
  ((continuous_shift 1).comp continuous_subtype_val).subtype_mk _

/-- A support determines a binary configuration, with no finiteness assumption. -/
noncomputable def supportPoint (P : Set ℤ) : ℤ → ReturnBit := by
  classical
  exact fun i => if i ∈ P then returnOne else returnZero

@[simp] theorem one_support_point (P : Set ℤ) : oneSupport (supportPoint P) = P := by
  classical
  ext i
  simp [oneSupport, supportPoint]

/-- A configuration with at most one one is legal for every return-distance set. -/
theorem singleton_support_legal (D : Set ℤ) (s : ℤ) :
    ReturnLegal D (supportPoint {s}) := by
  intro p q hpq
  rw [one_support_point] at hpq
  have hp : p = s := hpq.1
  have hq : q = s := hpq.2.1
  have := hpq.2.2.1
  omega

/-- A finite word occurs in an actual subshift point at an integer coordinate. -/
def ReturnWordOccurs (w : List ReturnBit) (x : ℤ → ReturnBit) (t : ℤ) : Prop :=
  ∀ j : Fin w.length, x (t + (j : ℕ)) = w[j]

/-- The ordinary finite-word language of the bundled two-sided subshift. -/
def ReturnLanguage (D : Set ℤ) (w : List ReturnBit) : Prop :=
  ∃ x : ReturnPoint D, ∃ t : ℤ, ReturnWordOccurs w x.1 t

/-- Original exact-length quasi-finite type: the replacement has length exactly n. -/
def ReturnQuasiFiniteType (D : Set ℤ) : Prop :=
  ∃ M : ℕ, ∀ n : ℕ, M ≤ n → ∀ u v : List ReturnBit,
    ReturnLanguage D u → ReturnLanguage D v →
    (∃ w : List ReturnBit, w.length = n ∧ ReturnLanguage D w ∧
      ReturnLanguage D (u ++ w) ∧ ReturnLanguage D (w ++ v)) →
    ∃ z : List ReturnBit, z.length = n ∧ ReturnLanguage D z ∧
      ReturnLanguage D (u ++ z ++ v)

/-- A word with a prescribed single possible one occurs in a singleton-support point. -/
theorem singleton_word_language (D : Set ℤ) (w : List ReturnBit) (s : ℤ)
    (hw : ∀ j : Fin w.length,
      w[j] = if (j : ℤ) = s then returnOne else returnZero) : ReturnLanguage D w := by
  classical
  refine ⟨⟨supportPoint {s}, singleton_support_legal D s⟩, 0, ?_⟩
  intro j
  simpa [supportPoint] using (hw j).symm

private theorem zero_word_language (D : Set ℤ) (n : ℕ) :
    ReturnLanguage D (List.replicate n returnZero) := by
  apply singleton_word_language D _ (-1)
  intro j
  have hj : (j : ℤ) ≠ -1 := by omega
  simp [hj]

private theorem one_zero_word_language (D : Set ℤ) (n : ℕ) :
    ReturnLanguage D (returnOne :: List.replicate n returnZero) := by
  apply singleton_word_language D _ 0
  intro j
  by_cases hj : j.val = 0
  · simp [hj]
  · have hjz : (j : ℤ) ≠ 0 := by omega
    simp [List.getElem_cons, hj, hjz]

private theorem zero_one_word_language (D : Set ℤ) (n : ℕ) :
    ReturnLanguage D (List.replicate n returnZero ++ [returnOne]) := by
  apply singleton_word_language D _ n
  intro j
  have hj := j.isLt
  simp only [List.length_append, List.length_replicate, List.length_singleton] at hj
  by_cases hjn : j.val < n
  · have hne : (j : ℤ) ≠ n := by omega
    simp [List.getElem_append, hjn, hne]
  · have he : j.val = n := by omega
    simp [List.getElem_append, he]

/-- A bounded interval of forbidden first-return distances obstructs any legal point
with a leading one, a zero block, and a terminal one. -/
theorem forbidden_return_interval {D : Set ℤ} {x : ℤ → ReturnBit}
    (hx : ReturnLegal D x) (t : ℤ) (H N : ℕ) (hN : 0 < N)
    (hstart : x t = returnOne) (hend : x (t + N) = returnOne)
    (hzero : ∀ d : ℕ, 0 < d → d ≤ H → x (t + d) ≠ returnOne)
    (hforbid : ∀ d : ℕ, H < d → d ≤ N → (d : ℤ) ∉ D) : False := by
  classical
  have hex : ∃ d : ℕ, 0 < d ∧ x (t + d) = returnOne := ⟨N, hN, hend⟩
  let d := Nat.find hex
  have hd : 0 < d ∧ x (t + d) = returnOne := Nat.find_spec hex
  have hdN : d ≤ N := Nat.find_min' hex ⟨hN, hend⟩
  have hHd : H < d := by
    by_contra! hle
    exact hzero d hd.1 hle hd.2
  have hadj : SupportAdjacent (oneSupport x) t (t + d) := by
    refine ⟨hstart, hd.2, by omega, ?_⟩
    intro s hts hsd hs
    have hnat : ((s - t).toNat : ℤ) = s - t := by omega
    have hlt : (s - t).toNat < d := by omega
    have hmin := Nat.find_min hex hlt
    apply hmin
    refine ⟨by omega, ?_⟩
    change x (t + (s - t).toNat) = returnOne
    have he : t + ((s - t).toNat : ℤ) = s := by omega
    rw [he]
    exact hs
  have hallowed := hx t (t + d) hadj
  exact hforbid d hHd hdN (by simpa using hallowed)

/-- Arbitrarily long forbidden intervals contradict the source's exact-length QFT
condition on the actual language of the two-sided compact subshift. -/
theorem forbidden_intervals_not_quasi_finite_type {D : Set ℤ}
    (hinterval : ∀ n : ℕ, ∃ H : ℕ, ∀ d : ℕ,
      H < d → d ≤ H + n + 1 → (d : ℤ) ∉ D) : ¬ ReturnQuasiFiniteType D := by
  rintro ⟨M, hM⟩
  let n := max M 1
  obtain ⟨H, hH⟩ := hinterval n
  let u := returnOne :: List.replicate H returnZero
  let w := List.replicate n returnZero
  let v := [returnOne]
  have hu : ReturnLanguage D u := one_zero_word_language D H
  have hv : ReturnLanguage D v := by simpa [v] using one_zero_word_language D 0
  have hw : ReturnLanguage D w := zero_word_language D n
  have huw : ReturnLanguage D (u ++ w) := by
    change ReturnLanguage D
      (returnOne :: (List.replicate H returnZero ++ List.replicate n returnZero))
    rw [← List.replicate_add]
    exact one_zero_word_language D (H + n)
  have hwv : ReturnLanguage D (w ++ v) := zero_one_word_language D n
  obtain ⟨z, hzn, _, x, t, hxt⟩ := hM n (by dsimp [n]; omega) u v hu hv
    ⟨w, by simp [w], hw, huw, hwv⟩
  have hlen : (u ++ z ++ v).length = H + n + 2 := by simp [u, v, hzn]; omega
  have hstart : x.1 t = returnOne := by
    have he := hxt ⟨0, by rw [hlen]; omega⟩
    simpa [u, v] using he
  have hend : x.1 (t + (H + n + 1 : ℕ)) = returnOne := by
    have he := hxt ⟨H + n + 1, by rw [hlen]; omega⟩
    simpa [u, v, List.getElem_append, hzn, Nat.not_lt.mpr (by omega : H + 1 + n ≤ H + n + 1)] using he
  have hzero : ∀ d : ℕ, 0 < d → d ≤ H → x.1 (t + d) ≠ returnOne := by
    intro d hd hdH
    have he := hxt ⟨d, by rw [hlen]; omega⟩
    have he0 : x.1 (t + d) = returnZero := by
      simpa [u, v, List.getElem_append, List.getElem_cons, hd.ne',
        show d - 1 < H by omega,
        show d < H + 1 by omega, show d < H + 1 + n by omega] using he
    rw [he0]
    exact return_zero_ne_one
  exact forbidden_return_interval x.2 t H (H + n + 1) (by omega) hstart hend hzero hH

#print axioms forbidden_intervals_not_quasi_finite_type
#print axioms return_legal_closed
#print axioms return_shift_continuous

end D5.S1.Dynamics.Shadowing
