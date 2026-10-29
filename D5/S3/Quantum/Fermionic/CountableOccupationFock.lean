/- GID: D5/S3/Quantum/Fermionic/CountableOccupationFock
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/CountableOccupationFock
   mirror-E: none(waiver:algebraic-countable-fock)
   anchors: []
   utility: none
   digest: Signed finite occupations intertwine the finite Jordan-Wigner action. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
import D5.S3.Quantum.Fermionic.FockMajoranaCarrier
import D5.S3.Quantum.FermionicCorrelationalBound.CompletedCorrelationalBound
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! Algebraic finite-excitation states and transport of the finite Jordan–Wigner action. -/

open scoped BigOperators Matrix
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression (fullC_entry)
open D5.S3.Quantum.FermionicCorrelationalBound.CompletedCorrelationalBound
open private mem_occupationSet occupationSet_injective occupationSet_ofSet from
  D5.S3.Quantum.FermionicCorrelationalBound.CompletedCorrelationalBound
open PredictiveThermodynamic.Physical (Assignment)

noncomputable section
namespace D5.S3.Quantum.Fermionic.CountableOccupationFock

abbrev Fock := (Finset ℕ) →₀ ℂ

def ket (S : Finset ℕ) : Fock := Finsupp.single S 1

def vacuum : Fock := ket ∅

def lowerCount (j : ℕ) (S : Finset ℕ) : ℕ := (S.filter (· < j)).card

def phase (j : ℕ) (S : Finset ℕ) : ℂ := (-1 : ℂ) ^ lowerCount j S

def annihilate (j : ℕ) : Module.End ℂ Fock :=
  Finsupp.lsum ℂ fun S => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight
    (if j ∈ S then phase j S • ket (S.erase j) else 0)

def create (j : ℕ) : Module.End ℂ Fock :=
  Finsupp.lsum ℂ fun S => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight
    (if j ∈ S then 0 else phase j S • ket (insert j S))

def parity : Module.End ℂ Fock :=
  Finsupp.lsum ℂ fun S => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight
    ((-1 : ℂ) ^ S.card • ket S)

def prefixEmbed (N : ℕ) : (Assignment N → ℂ) →ₗ[ℂ] Fock :=
  ∑ t : Assignment N, (LinearMap.proj t).smulRight (ket (occupationSet t))

@[simp] private theorem annihilate_ket (j : ℕ) (S : Finset ℕ) :
    annihilate j (ket S) = if j ∈ S then phase j S • ket (S.erase j) else 0 := by
  simp only [annihilate, ket, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_apply, one_smul]

@[simp] private theorem create_ket (j : ℕ) (S : Finset ℕ) :
    create j (ket S) = if j ∈ S then 0 else phase j S • ket (insert j S) := by
  simp only [create, ket, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_apply, one_smul]

@[simp] private theorem parity_ket (S : Finset ℕ) :
    parity (ket S) = (-1 : ℂ) ^ S.card • ket S := by
  simp only [parity, ket, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_apply, one_smul]

private theorem end_ext {T U : Module.End ℂ Fock}
    (h : ∀ S, T (ket S) = U (ket S)) : T = U := by
  apply Finsupp.lhom_ext
  intro S a
  have hs : Finsupp.single S a = a • ket S := by simp [ket]
  simp only [hs, map_smul, h]

private theorem occupation_below {N : ℕ} (t : Assignment N) :
    ∀ i ∈ occupationSet t, i < N := by
  intro i hi
  obtain ⟨k, _, hk⟩ := Finset.mem_map.mp hi
  exact (show k.val = i from hk) ▸ k.isLt

private theorem occupation_update {N : ℕ} (t : Assignment N) (j : Fin N) (b : Bool) :
    occupationSet (Function.update t j b) =
      if b then insert j.val (occupationSet t) else (occupationSet t).erase j.val := by
  classical
  ext n
  by_cases hn : n < N
  · let i : Fin N := ⟨n, hn⟩
    have hmem (u : Assignment N) : n ∈ occupationSet u ↔ u i = true :=
      mem_occupationSet u i
    by_cases he : i = j
    · have hnj : n = j.val := congrArg Fin.val he
      subst n
      cases b <;> simp [hmem, he]
    · have hnj : n ≠ j.val := fun h => he (Fin.ext h)
      cases b <;> simp [hmem, he, hnj, Ne.symm hnj]
  · have hnj : n ≠ j.val := by intro h; subst n; exact hn j.isLt
    have hnot (u : Assignment N) : n ∉ occupationSet u :=
      fun h => hn (occupation_below u n h)
    cases b <;> simp [hnot, hnj, Ne.symm hnj]

private theorem occupation_prefix {N : ℕ} (t : Assignment N) (j : Fin N) :
    lowerCount j.val (occupationSet t) = prefixCount t j := by
  classical
  unfold lowerCount occupationSet prefixCount
  rw [Finset.filter_map]
  simp only [Finset.card_map]
  congr 1
  ext i
  simp only [occupiedModes, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, ← Fin.lt_def]
  tauto

@[simp] private theorem prefixEmbed_apply (N : ℕ) (v : Assignment N → ℂ) :
    prefixEmbed N v = ∑ t : Assignment N, v t • ket (occupationSet t) := by
  simp [prefixEmbed, LinearMap.sum_apply]

@[simp] private theorem prefixEmbed_single (N : ℕ) (t : Assignment N) (a : ℂ) :
    prefixEmbed N (Pi.single t a) = a • ket (occupationSet t) := by
  classical
  simp [prefixEmbed_apply, Pi.single_apply]

private theorem prefixEmbed_coefficient (N : ℕ) (v : Assignment N → ℂ) (t : Assignment N) :
    prefixEmbed N v (occupationSet t) = v t := by
  classical
  simp [prefixEmbed_apply, ket, Finsupp.single_apply, (occupationSet_injective N).eq_iff]

theorem prefixEmbed_injective (N : ℕ) : Function.Injective (prefixEmbed N) := by
  intro v w h
  funext t
  simpa only [prefixEmbed_coefficient] using congrArg (fun f : Fock => f (occupationSet t)) h

private theorem finite_annihilate_column {N : ℕ} (j : Fin N) (t : Assignment N) :
    (fullC j).mulVec (Pi.single t 1) =
      if t j = true then (-1 : ℂ) ^ prefixCount t j •
        Pi.single (Function.update t j false) 1 else 0 := by
  classical
  ext s
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, fullC_entry]
  by_cases ht : t j = true
  · simp [ht, Pi.single_apply, eq_comm]
  · simp [ht]

private theorem finite_create_column {N : ℕ} (j : Fin N) (t : Assignment N) :
    ((fullC j)ᴴ).mulVec (Pi.single t 1) =
      if t j = false then (-1 : ℂ) ^ prefixCount t j •
        Pi.single (Function.update t j true) 1 else 0 := by
  classical
  ext s
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.conjTranspose_apply,
    fullC_entry]
  by_cases ht : t j = false
  · have hc : (s j = true ∧ t = Function.update s j false) ↔
        s = Function.update t j true := by
      constructor
      · rintro ⟨hs, he⟩
        rw [he]
        simp [hs]
      · intro he
        simp [he, ht]
    rw [if_pos ht]
    by_cases hs : s = Function.update t j true
    · subst s
      have hp : prefixCount (Function.update t j true) j = prefixCount t j := by
        rw [← occupation_prefix, occupation_update, ← occupation_prefix]
        simp [lowerCount, Finset.filter_insert]
      simp [hc, hp, ht]
    · simp [hc, hs, Pi.single_apply, Ne.symm hs]
  · have htt : t j = true := Bool.eq_true_of_not_eq_false ht
    have hc : ¬(s j = true ∧ t = Function.update s j false) := by
      rintro ⟨_, he⟩
      have := congrFun he j
      simp [htt] at this
    simp [ht, hc]

private theorem pi_ext_one {N : ℕ} {f g : (Assignment N → ℂ) →ₗ[ℂ] Fock}
    (h : ∀ t, f (Pi.single t 1) = g (Pi.single t 1)) : f = g := by
  apply LinearMap.pi_ext
  intro t a
  have ha : Pi.single t a = a • Pi.single t (1 : ℂ) := by
    ext u
    by_cases h : u = t <;> simp [Pi.single_apply, h, eq_comm]
  simp only [ha, map_smul, h]

theorem jw_annihilate_intertwining (N : ℕ) (j : Fin N) (v : Assignment N → ℂ) :
    annihilate j.val (prefixEmbed N v) = prefixEmbed N ((fullC j).mulVec v) := by
  have h : (annihilate j.val).comp (prefixEmbed N) =
      (prefixEmbed N).comp (Matrix.mulVecLin (fullC j)) := by
    apply pi_ext_one
    intro t
    simp only [LinearMap.comp_apply, prefixEmbed_single, one_smul, annihilate_ket,
      Matrix.mulVecLin_apply, finite_annihilate_column]
    classical
    simp only [mem_occupationSet]
    split_ifs with ht
    · simp [phase, occupation_prefix, occupation_update]
    · simp
  exact LinearMap.congr_fun h v

theorem jw_create_intertwining (N : ℕ) (j : Fin N) (v : Assignment N → ℂ) :
    create j.val (prefixEmbed N v) = prefixEmbed N (((fullC j)ᴴ).mulVec v) := by
  have h : (create j.val).comp (prefixEmbed N) =
      (prefixEmbed N).comp (Matrix.mulVecLin ((fullC j)ᴴ)) := by
    apply pi_ext_one
    intro t
    simp only [LinearMap.comp_apply, prefixEmbed_single, one_smul, create_ket,
      Matrix.mulVecLin_apply, finite_create_column]
    classical
    simp only [mem_occupationSet]
    cases ht : t j <;> simp [ht, phase, occupation_prefix, occupation_update]
  exact LinearMap.congr_fun h v

/-- Extension by empty sites, expressed in the original Boolean coordinates. -/
def prefixExtend (N M : ℕ) : (Assignment N → ℂ) →ₗ[ℂ] (Assignment M → ℂ) :=
  ∑ t : Assignment N, (LinearMap.proj t).smulRight
    (Pi.single (occupationOfSet M (occupationSet t)) 1)

@[simp] private theorem prefixExtend_single (N M : ℕ) (t : Assignment N) (a : ℂ) :
    prefixExtend N M (Pi.single t a) =
      a • Pi.single (occupationOfSet M (occupationSet t)) 1 := by
  classical
  simp [prefixExtend, LinearMap.sum_apply, Pi.single_apply]

theorem prefix_coherence (N M : ℕ) (hNM : N ≤ M) (v : Assignment N → ℂ) :
    prefixEmbed M (prefixExtend N M v) = prefixEmbed N v := by
  have h : (prefixEmbed M).comp (prefixExtend N M) = prefixEmbed N := by
    apply pi_ext_one
    intro t
    simp only [LinearMap.comp_apply, prefixExtend_single, one_smul, prefixEmbed_single]
    rw [occupationSet_ofSet M (occupationSet t)
      (fun i hi => lt_of_lt_of_le (occupation_below t i hi) hNM)]
  exact LinearMap.congr_fun h v

theorem cutoff_annihilate_coherence (N M : ℕ) (hNM : N ≤ M)
    (j : Fin N) (v : Assignment N → ℂ) :
    (fullC ⟨j.val, lt_of_lt_of_le j.isLt hNM⟩).mulVec (prefixExtend N M v) =
      prefixExtend N M ((fullC j).mulVec v) := by
  apply prefixEmbed_injective M
  rw [← jw_annihilate_intertwining, prefix_coherence N M hNM]
  change annihilate j.val (prefixEmbed N v) = _
  rw [jw_annihilate_intertwining N j v, prefix_coherence N M hNM]

theorem cutoff_create_coherence (N M : ℕ) (hNM : N ≤ M)
    (j : Fin N) (v : Assignment N → ℂ) :
    ((fullC ⟨j.val, lt_of_lt_of_le j.isLt hNM⟩)ᴴ).mulVec (prefixExtend N M v) =
      prefixExtend N M (((fullC j)ᴴ).mulVec v) := by
  apply prefixEmbed_injective M
  rw [← jw_create_intertwining, prefix_coherence N M hNM]
  change create j.val (prefixEmbed N v) = _
  rw [jw_create_intertwining N j v, prefix_coherence N M hNM]

/-- A single prefix captures a vector and any specified finite collection of modes. -/
theorem finite_capture (v : Fock) (J : Finset ℕ) :
    ∃ N : ℕ, (∀ j ∈ J, j < N) ∧ ∃ w : Assignment N → ℂ, prefixEmbed N w = v := by
  classical
  let B := v.support.biUnion id ∪ J
  let N := B.sup id + 1
  have hB (j : ℕ) (hj : j ∈ B) : j < N :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
  refine ⟨N, (fun j hj => hB j (Finset.mem_union_right _ hj)), ?_⟩
  have hS (S : Finset ℕ) (hS : S ∈ v.support) : ∀ j ∈ S, j < N := by
    intro j hj
    exact hB j (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨S, hS, hj⟩))
  have hv : v.sum (fun S a => Finsupp.single S a) ∈ LinearMap.range (prefixEmbed N) := by
    apply Submodule.sum_mem
    intro S hSv
    refine ⟨Pi.single (occupationOfSet N S) (v S), ?_⟩
    rw [prefixEmbed_single, occupationSet_ofSet N S (hS S hSv)]
    simp [ket]
  simpa only [Finsupp.sum_single, LinearMap.mem_range] using hv

def mode (j : ℕ) (creator : Bool) : Module.End ℂ Fock :=
  if creator then create j else annihilate j

def finiteMode {N : ℕ} (j : Fin N) (creator : Bool) : FullOperator N :=
  if creator then (fullC j)ᴴ else fullC j

/-- Products act from right to left, including the empty word. -/
def word : List (ℕ × Bool) → Module.End ℂ Fock
  | [] => 1
  | p :: w => mode p.1 p.2 * word w

def finiteWord {N : ℕ} : List (Fin N × Bool) → FullOperator N
  | [] => 1
  | p :: w => finiteMode p.1 p.2 * finiteWord w

theorem word_intertwining (N : ℕ) (w : List (Fin N × Bool)) (v : Assignment N → ℂ) :
    word (w.map (fun p => (p.1.val, p.2))) (prefixEmbed N v) =
      prefixEmbed N ((finiteWord w).mulVec v) := by
  induction w with
  | nil => simp [word, finiteWord]
  | cons p w ih =>
    simp only [List.map_cons, word, Module.End.mul_apply, ih, finiteWord,
      ← Matrix.mulVec_mulVec]
    rcases p with ⟨j, b⟩
    cases b
    · exact jw_annihilate_intertwining N j _
    · exact jw_create_intertwining N j _

private theorem finite_nilpotent {N : ℕ} (j : Fin N) : fullC j * fullC j = 0 := by
  classical
  let x := D5.S3.Quantum.Fermionic.FockMajoranaCarrier.majorana j false
  let y := D5.S3.Quantum.Fermionic.FockMajoranaCarrier.majorana j true
  have hc := (D5.S3.Quantum.Fermionic.FockMajoranaCarrier.majorana_clifford_and_parity N).2.2.2.1
  have hx2 : (2 : ℂ) • (x * x) = (2 : ℂ) • (1 : FullOperator N) := by
    simpa only [two_smul, ite_true] using hc (j, false) (j, false)
  have hy2 : (2 : ℂ) • (y * y) = (2 : ℂ) • (1 : FullOperator N) := by
    simpa only [two_smul, ite_true] using hc (j, true) (j, true)
  have hx : x * x = 1 := by
    simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
      using congrArg (fun z => (2 : ℂ)⁻¹ • z) hx2
  have hy : y * y = 1 := by
    simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
      using congrArg (fun z => (2 : ℂ)⁻¹ • z) hy2
  have hxy : x * y + y * x = 0 := by
    simpa using hc (j, false) (j, true)
  have hfour : (4 : ℂ) • (fullC j * fullC j) = 0 := by
    calc
      _ = x * x - y * y - Complex.I • (x * y + y * x) := by
        simp only [x, y, D5.S3.Quantum.Fermionic.FockMajoranaCarrier.majorana,
          Bool.false_eq_true, ite_false, ite_true, add_mul, mul_add, sub_mul, mul_sub,
          smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I,
          neg_one_smul, smul_add, smul_sub]
        module
      _ = 0 := by rw [hx, hy, hxy]; simp
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (4 : ℂ) ≠ 0), one_smul,
    smul_zero] using congrArg (fun z => (4 : ℂ)⁻¹ • z) hfour

private theorem finite_aa {N : ℕ} (i j : Fin N) :
    fullC i * fullC j + fullC j * fullC i = 0 := by
  rcases lt_trichotomy i j with h | h | h
  · exact fullC_anticomm_of_lt i j h
  · subst j; rw [finite_nilpotent]; simp
  · simpa only [add_comm] using fullC_anticomm_of_lt j i h

private theorem finite_cc {N : ℕ} (i j : Fin N) :
    (fullC i)ᴴ * (fullC j)ᴴ + (fullC j)ᴴ * (fullC i)ᴴ = 0 := by
  simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_zero, add_comm] using congrArg Matrix.conjTranspose (finite_aa i j)

private theorem finite_ac {N : ℕ} (i j : Fin N) :
    fullC i * (fullC j)ᴴ + (fullC j)ᴴ * fullC i = if i = j then 1 else 0 := by
  classical
  rcases lt_trichotomy i j with h | h | h
  · simpa only [if_neg (ne_of_lt h)] using fullC_mixed_anticomm_of_lt i j h
  · subst j; simpa using fullC_CAR i
  · have ht := congrArg Matrix.conjTranspose (fullC_mixed_anticomm_of_lt j i h)
    simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero,
      if_neg (ne_of_gt h)] using ht

private theorem finite_car {N : ℕ} (i j : Fin N) (a b : Bool) :
    finiteMode i a * finiteMode j b + finiteMode j b * finiteMode i a =
      if i = j ∧ a ≠ b then 1 else 0 := by
  classical
  cases a <;> cases b
  · simpa [finiteMode] using finite_aa i j
  · simpa [finiteMode] using finite_ac i j
  · simpa [finiteMode, eq_comm, add_comm] using finite_ac j i
  · simpa [finiteMode] using finite_cc i j

/-- Universal CAR on the algebraic, countably indexed carrier. -/
theorem car (i j : ℕ) (a b : Bool) :
    mode i a * mode j b + mode j b * mode i a =
      if i = j ∧ a ≠ b then (1 : Module.End ℂ Fock) else 0 := by
  classical
  apply LinearMap.ext
  intro v
  obtain ⟨N, hN, w, rfl⟩ := finite_capture v {i, j}
  let iN : Fin N := ⟨i, hN i (by simp)⟩
  let jN : Fin N := ⟨j, hN j (by simp)⟩
  have hi := word_intertwining N [(iN, a), (jN, b)] w
  have hj := word_intertwining N [(jN, b), (iN, a)] w
  simp only [List.map_cons, List.map_nil, word, finiteWord, mul_one,
    Module.End.mul_apply] at hi hj
  change mode i a (mode j b (prefixEmbed N w)) +
    mode j b (mode i a (prefixEmbed N w)) = _
  rw [hi, hj, ← map_add, ← Matrix.add_mulVec, finite_car]
  have he : (iN = jN) ↔ i = j := Fin.ext_iff
  by_cases h : i = j ∧ a ≠ b
  · simp [h, he]
  · simp [h, he]

theorem annihilate_vacuum (j : ℕ) : annihilate j vacuum = 0 := by
  simp [vacuum]

theorem parity_involution : parity * parity = (1 : Module.End ℂ Fock) := by
  apply end_ext
  intro S
  simp only [Module.End.mul_apply, parity_ket, map_smul, smul_smul,
    ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, Module.End.one_apply]

theorem parity_odd (j : ℕ) (b : Bool) :
    parity * mode j b + mode j b * parity = 0 := by
  apply end_ext
  intro S
  cases b <;> by_cases hj : j ∈ S
  all_goals simp only [mode, Bool.false_eq_true, ite_false, ite_true,
    LinearMap.add_apply, Module.End.mul_apply, parity_ket, map_smul,
    annihilate_ket, create_ket, hj, ite_false, ite_true, map_zero, smul_zero,
    LinearMap.zero_apply, add_zero, zero_add]
  · rw [Finset.card_erase_of_mem hj]
    have hc : S.card - 1 + 1 = S.card := Nat.sub_add_cancel (Finset.card_pos.mpr ⟨j, hj⟩)
    have hp : (-1 : ℂ) ^ S.card = -((-1 : ℂ) ^ (S.card - 1)) := by
      conv_lhs => rw [← hc]
      rw [pow_succ]; ring
    rw [hp]
    module
  · rw [Finset.card_insert_of_notMem hj, pow_succ]
    module

theorem create_vacuum (j : ℕ) : create j vacuum = ket {j} := by
  simp [vacuum, phase, lowerCount]

private theorem creator_basis (S : Finset ℕ) :
    ∃ w : List ℕ, ∃ z : ℂ, z ≠ 0 ∧
      word (w.map (fun j => (j, true))) vacuum = z • ket S := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨[], 1, one_ne_zero, by simp [word, vacuum]⟩
  | @insert j S hj ih =>
    obtain ⟨w, z, hz, hw⟩ := ih
    refine ⟨j :: w, z * phase j S, mul_ne_zero hz (pow_ne_zero _ (by norm_num)), ?_⟩
    simp only [List.map_cons, word, Module.End.mul_apply, mode, ite_true, hw,
      map_smul, create_ket, if_neg hj, smul_smul]

/-- Every finite-excitation state is a finite linear combination of creator words. -/
theorem creator_spanning :
    Submodule.span ℂ (Set.range (fun w : List ℕ =>
      word (w.map (fun j => (j, true))) vacuum)) = ⊤ := by
  classical
  apply top_unique
  suffices hall : ∀ v : Fock, v ∈ Submodule.span ℂ (Set.range (fun w : List ℕ =>
      word (w.map (fun j => (j, true))) vacuum)) by
    intro v _
    exact hall v
  intro v
  induction v using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add f g hf hg => exact Submodule.add_mem _ hf hg
  | single S a =>
    obtain ⟨w, z, hz, hw⟩ := creator_basis S
    have hword : word (w.map (fun j => (j, true))) vacuum ∈
        Submodule.span ℂ (Set.range (fun w : List ℕ =>
          word (w.map (fun j => (j, true))) vacuum)) :=
      Submodule.subset_span ⟨w, rfl⟩
    have he : Finsupp.single S a = (a / z) • (z • ket S) := by
      rw [smul_smul, div_mul_cancel₀ _ hz]
      simp [ket]
    rw [he, ← hw]
    exact Submodule.smul_mem _ _ hword


/-- An occupied coefficient is recovered from the coefficient after deleting its site. -/
private theorem annihilate_coefficient (j : ℕ) (v : Fock) (S : Finset ℕ) (hj : j ∈ S) :
    annihilate j v (S.erase j) = phase j S * v S := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finsupp.add_apply, hf, hg]
    ring
  | single T a =>
    have hs : Finsupp.single T a = a • ket T := by simp [ket]
    rw [hs, map_smul, annihilate_ket]
    by_cases hjT : j ∈ T
    · rw [if_pos hjT]
      by_cases hTS : T = S
      · subst T
        simp [ket, smul_smul, mul_comm]
      · have he : T.erase j ≠ S.erase j := by
          intro he
          apply hTS
          calc
            T = insert j (T.erase j) := (Finset.insert_erase hjT).symm
            _ = insert j (S.erase j) := congrArg (insert j) he
            _ = S := Finset.insert_erase hj
        simp [ket, he, hTS, eq_comm]
    · have hTS : T ≠ S := by rintro rfl; exact hjT hj
      simp [hjT, ket, hTS, eq_comm]

/-- The simultaneous kernel of all actual annihilators is precisely the vacuum line. -/
theorem common_annihilator_kernel (v : Fock) :
    (∀ j : ℕ, annihilate j v = 0) ↔ ∃ α : ℂ, v = α • vacuum := by
  classical
  constructor
  · intro h
    refine ⟨v ∅, ?_⟩
    ext S
    by_cases hS : S = ∅
    · subst S
      simp [vacuum, ket]
    · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have hz : phase j S * v S = 0 := by
        rw [← annihilate_coefficient j v S hj, h j]
        rfl
      have hv : v S = 0 := (mul_eq_zero.mp hz).resolve_left
        (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))
      simp [hv, vacuum, ket, hS]
  · rintro ⟨α, rfl⟩ j
    rw [map_smul, annihilate_vacuum, smul_zero]

/-- Creator spanning extends a scalar vacuum value to the entire actual carrier. -/
theorem eq_scalar_of_creator_commutation (A : Module.End ℂ Fock) (α : ℂ)
    (hvac : A vacuum = α • vacuum)
    (hc : ∀ j : ℕ, A * create j = create j * A) :
    A = α • (1 : Module.End ℂ Fock) := by
  apply LinearMap.ext_on_range creator_spanning
  intro w
  have hw : ∀ w : List ℕ,
      A (word (w.map (fun j => (j, true))) vacuum) =
        α • word (w.map (fun j => (j, true))) vacuum := by
    intro w
    induction w with
    | nil => simpa [word] using hvac
    | cons j w ih =>
      have hj (v : Fock) : A (create j v) = create j (A v) :=
        LinearMap.congr_fun (hc j) v
      simpa only [List.map_cons, word, Module.End.mul_apply, mode, ite_true,
        hj, ih, map_smul]
  exact hw w

end D5.S3.Quantum.Fermionic.CountableOccupationFock
