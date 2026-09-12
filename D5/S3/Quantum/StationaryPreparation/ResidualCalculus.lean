/- GID: D5/S3/Quantum/StationaryPreparation/ResidualCalculus
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/ResidualCalculus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Last-tail multiplicities and local residual transitions determine normalized coefficients of a fixed-unitary circuit. -/

import D5.S3.Quantum.StationaryPreparation.PaddingMemory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.StationaryPreparation.ResidualCalculus

open D5.S3.Quantum.StationaryPreparation.PaddingMemory
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors


section LastTailMass

open D5.S3.Quantum.Entanglement.OccupancyWordSectors

variable {A : Type*} [Fintype A] [DecidableEq A]

def tailCount (head : A) (b : Multiset A) : ℕ :=
  ∑ i : {i : A // i ≠ head}, b.count i.val

theorem head_add_tail_count (head : A) (b : Multiset A) :
    b.count head + tailCount head b = b.card := by
  unfold tailCount
  rw [← Fintype.sum_eq_add_sum_subtype_ne b.count head]
  exact Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)

theorem tail_count_erase_head (head : A) (b : Multiset A) :
    tailCount head (b.erase head) = tailCount head b := by
  apply Finset.sum_congr rfl
  intro i _
  exact Multiset.count_erase_of_ne i.property b

theorem tail_count_erase_tail (head : A) (b : Multiset A) (i : A)
    (hi : i ≠ head) (hib : i ∈ b) :
    tailCount head (b.erase i) + 1 = tailCount head b := by
  have h1 := head_add_tail_count head b
  have h2 := head_add_tail_count head (b.erase i)
  have hc : (b.erase i).count head = b.count head :=
    Multiset.count_erase_of_ne (Ne.symm hi) b
  have hn : (b.erase i).card + 1 = b.card := by
    simpa using congrArg Multiset.card (Multiset.cons_erase hib)
  omega

/-- The ordinary last-tail weight, expressed using actual occupation-word multiplicity. -/
def lastTailMass (head : A) (b : Multiset A) : ℝ :=
  (tailCount head b : ℝ) * (multiplicity b.card b : ℝ) / (b.card : ℝ)

theorem last_tail_mass_nonneg (head : A) (b : Multiset A) : 0 ≤ lastTailMass head b := by
  unfold lastTailMass
  positivity

theorem last_tail_mass_pos (head : A) (b : Multiset A) (hR : 0 < tailCount head b) :
    0 < lastTailMass head b := by
  have hn : 0 < b.card := by have := head_add_tail_count head b; omega
  unfold lastTailMass
  exact div_pos (mul_pos (by exact_mod_cast hR)
    (by exact_mod_cast multiplicity_pos b rfl)) (by exact_mod_cast hn)

theorem erase_multiplicity_real (b : Multiset A) (i : A) (hi : i ∈ b) :
    (b.card : ℝ) * (multiplicity (b.erase i).card (b.erase i) : ℝ) =
      (b.count i : ℝ) * (multiplicity b.card b : ℝ) := by
  have hn : (b.erase i).card + 1 = b.card := by
    simpa using congrArg Multiset.card (Multiset.cons_erase hi)
  have hm := multiplicity_erase_mul (n := (b.erase i).card) hn.symm i hi
  rw [hn] at hm
  exact_mod_cast hm

theorem last_tail_mass_erase_head (head : A) (b : Multiset A)
    (hi : head ∈ b) (hR : 0 < tailCount head b) :
    lastTailMass head (b.erase head) =
      headProbability (b.count head) (tailCount head b) * lastTailMass head b := by
  have hsum := head_add_tail_count head b
  have hc : (b.erase head).card + 1 = b.card := by
    simpa using congrArg Multiset.card (Multiset.cons_erase hi)
  have hb : 0 < b.count head := Multiset.count_pos.mpr hi
  have hn : (0 : ℝ) < b.card := by exact_mod_cast (by omega : 0 < b.card)
  have he : (0 : ℝ) < (b.erase head).card := by
    exact_mod_cast (by omega : 0 < (b.erase head).card)
  have hcR : ((b.erase head).card : ℝ) + 1 = b.card := by exact_mod_cast hc
  have hsR : (b.count head : ℝ) + tailCount head b = b.card := by exact_mod_cast hsum
  have hm := erase_multiplicity_real b head hi
  unfold lastTailMass headProbability
  rw [tail_count_erase_head]
  have hd : (b.count head : ℝ) + tailCount head b - 1 = (b.erase head).card := by linarith
  rw [hd]
  field_simp [hn.ne', he.ne']
  nlinarith [congrArg (fun x : ℝ => (tailCount head b : ℝ) * x) hm]

theorem last_tail_mass_erase_tail (head : A) (b : Multiset A) (i : A)
    (hi : i ≠ head) (hib : i ∈ b) (hR : 2 ≤ tailCount head b) :
    lastTailMass head (b.erase i) =
      tailProbability (b.count head) (tailCount head b) (b.count i) * lastTailMass head b := by
  have hsum := head_add_tail_count head b
  have hc : (b.erase i).card + 1 = b.card := by
    simpa using congrArg Multiset.card (Multiset.cons_erase hib)
  have ht := tail_count_erase_tail head b i hi hib
  have hn : (0 : ℝ) < b.card := by exact_mod_cast (by omega : 0 < b.card)
  have he : (0 : ℝ) < (b.erase i).card := by
    exact_mod_cast (by omega : 0 < (b.erase i).card)
  have hr : (0 : ℝ) < tailCount head b := by exact_mod_cast (by omega : 0 < tailCount head b)
  have hcR : ((b.erase i).card : ℝ) + 1 = b.card := by exact_mod_cast hc
  have hsR : (b.count head : ℝ) + tailCount head b = b.card := by exact_mod_cast hsum
  have htR : (tailCount head (b.erase i) : ℝ) + 1 = tailCount head b := by exact_mod_cast ht
  have hm := erase_multiplicity_real b i hib
  unfold lastTailMass tailProbability
  have hd : (b.count head : ℝ) + tailCount head b - 1 = (b.erase i).card := by linarith
  rw [hd, show (tailCount head (b.erase i) : ℝ) = tailCount head b - 1 by linarith]
  field_simp [hn.ne', he.ne', hr.ne']
  nlinarith [congrArg (fun x : ℝ => ((tailCount head b : ℝ) - 1) * x) hm]

theorem last_tail_mass_singleton (head i : A) (hi : i ≠ head) :
    lastTailMass head ({i} : Multiset A) = 1 := by
  have hs := head_add_tail_count head ({i} : Multiset A)
  have ht : tailCount head ({i} : Multiset A) = 1 := by simpa [hi, Ne.symm hi] using hs
  have hm : multiplicity ({i} : Multiset A).card ({i} : Multiset A) = 1 := by
    rw [multiplicity_eq_factorial _ rfl]
    have hp : (∏ z : A, (({i} : Multiset A).count z).factorial) = 1 := by
      apply Finset.prod_eq_one
      intro z _
      by_cases hz : z = i <;> simp [hz]
    simp [hp]
  unfold lastTailMass
  rw [ht, hm]
  simp

theorem last_tail_mass_one (head : A) (b : Multiset A)
    (hR : tailCount head b = 1) : lastTailMass head b = 1 := by
  induction hn : b.card using Nat.strong_induction_on generalizing b with
  | h n ih =>
    by_cases hh : head ∈ b
    · have he : (b.erase head).card < n := by
        rw [Multiset.card_erase_of_mem hh, hn]
        have : b.card ≠ 0 := by
          intro hz
          have hb := Multiset.card_eq_zero.mp hz
          simpa [hb] using hh
        exact Nat.pred_lt (by simpa [hn] using this)
      have hr : tailCount head (b.erase head) = 1 := by
        rw [tail_count_erase_head, hR]
      have hm := ih _ he (b.erase head) hr rfl
      have hp : headProbability (b.count head) (tailCount head b) = 1 := by
        have hc : (b.count head : ℝ) ≠ 0 := by
          exact_mod_cast (Multiset.count_pos.mpr hh).ne'
        simp [headProbability, hR, hc]
      rw [last_tail_mass_erase_head head b hh (by omega), hp, one_mul] at hm
      exact hm
    · have hc : b.card = 1 := by
        simpa [Multiset.count_eq_zero.mpr hh, hR] using
          (head_add_tail_count head b).symm
      obtain ⟨i, rfl⟩ := Multiset.card_eq_one.mp hc
      apply last_tail_mass_singleton
      simpa [eq_comm] using hh

theorem last_tail_head_amplitude (head : A) (b : Multiset A)
    (hi : head ∈ b) (hR : 0 < tailCount head b) :
    (Real.sqrt (headProbability (b.count head) (tailCount head b)) : ℂ) *
      (Real.sqrt (lastTailMass head b) : ℂ) =
      (Real.sqrt (lastTailMass head (b.erase head)) : ℂ) := by
  have hr : (1 : ℝ) ≤ tailCount head b := by exact_mod_cast hR
  have hp : 0 ≤ headProbability (b.count head) (tailCount head b) := by
    unfold headProbability
    exact div_nonneg (Nat.cast_nonneg _) (by linarith [Nat.cast_nonneg (α := ℝ) (b.count head)])
  rw [last_tail_mass_erase_head head b hi hR, Real.sqrt_mul hp, Complex.ofReal_mul]

theorem last_tail_tail_amplitude (head : A) (b : Multiset A) (i : A)
    (hi : i ≠ head) (hib : i ∈ b) (hR : 2 ≤ tailCount head b) :
    (Real.sqrt (tailProbability (b.count head) (tailCount head b) (b.count i)) : ℂ) *
      (Real.sqrt (lastTailMass head b) : ℂ) =
      (Real.sqrt (lastTailMass head (b.erase i)) : ℂ) := by
  have hr : (2 : ℝ) ≤ tailCount head b := by exact_mod_cast hR
  have hp : 0 ≤ tailProbability (b.count head) (tailCount head b) (b.count i) := by
    unfold tailProbability
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    · exact mul_nonneg (Nat.cast_nonneg _)
        (by linarith [Nat.cast_nonneg (α := ℝ) (b.count head)])
  rw [last_tail_mass_erase_tail head b i hi hib hR, Real.sqrt_mul hp, Complex.ofReal_mul]

end LastTailMass

section CircuitOutput

open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors

variable {A K : Type*} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]

def blankMemory (blank : A) : Space K →ₗᵢ[ℂ] Space (A × K) :=
  coordinateEmbedding (blankInjection blank (Function.Embedding.refl K))

theorem blank_memory_apply (blank : A) (x : Space K) (i : A) (k : K) :
    blankMemory blank x (i, k) = if i = blank then x k else 0 := by
  by_cases hi : i = blank
  · subst i
    simpa [blankMemory, blankInjection] using
      (coordinate_embedding_apply (blankInjection blank (Function.Embedding.refl K)) x k)
  · rw [if_neg hi]
    apply coordinate_embedding_off_range
    rintro ⟨j, hj⟩
    exact hi (congrArg Prod.fst hj).symm

theorem initialized_apply_all (blank : A) (n : ℕ) (x : Space K)
    (w : Fin n → A) (k : K) :
    initialized blank n x (w, k) = if w = (fun _ => blank) then x k else 0 := by
  classical
  conv_lhs => rw [basis_expansion x]
  simp only [map_sum, map_smul, initialize_basis]
  by_cases hw : w = (fun _ => blank) <;>
    simp [blankState, basis_apply, Prod.mk.injEq, hw]

theorem first_gate_initialized (blank : A) (n : ℕ) (U : Unitary (A × K))
    (x : Space K) (w : Fin (n + 1) → A) (k : K) :
    firstGate n U (initialized blank (n + 1) x) (w, k) =
      if Fin.tail w = (fun _ => blank) then U (blankMemory blank x) (w 0, k) else 0 := by
  rw [first_gate_apply]
  have hc (i : A) (u : Fin n → A) :
      Fin.cons i u = (fun _ => blank) ↔ i = blank ∧ u = (fun _ => blank) := by
    simp [funext_iff, Fin.forall_fin_succ]
  have hv : (WithLp.toLp 2 (fun p : A × K =>
      initialized blank (n + 1) x (Fin.cons p.1 (Fin.tail w), p.2))) =
      if Fin.tail w = (fun _ => blank) then blankMemory blank x else 0 := by
    ext p
    rcases p with ⟨i, j⟩
    by_cases ht : Fin.tail w = (fun _ => blank) <;>
      simp [initialized_apply_all, hc, ht, blank_memory_apply]
  rw [hv]
  split <;> simp_all

/-- Actual unitary circuit recursion on an arbitrary pure initial memory. -/
theorem circuit_initialized_step (blank : A) (U : ℕ → Unitary (A × K))
    (n t : ℕ) (x : Space K) (w : Fin (n + 1) → A) (k : K) :
    circuit U (n + 1) t (initialized blank (n + 1) x) (w, k) =
      circuit U n (t + 1)
        (initialized blank n (WithLp.toLp 2
          (fun j : K => U t (blankMemory blank x) (w 0, j)))) (Fin.tail w, k) := by
  simp only [circuit, LinearIsometryEquiv.trans_apply, tail_gate_apply]
  have hv : (WithLp.toLp 2 (fun p : Register A K n =>
      firstGate n (U t) (initialized blank (n + 1) x) (Fin.cons (w 0) p.1, p.2))) =
      initialized blank n (WithLp.toLp 2
        (fun j : K => U t (blankMemory blank x) (w 0, j))) := by
    ext p
    rcases p with ⟨u, j⟩
    simp [first_gate_initialized, initialized_apply_all]
  rw [hv]

theorem occupation_cons_eq {n : ℕ} (i : A) (w : Word A n) :
    occupation (Fin.cons i w) = i ::ₘ occupation w := by
  simp only [occupation, List.ofFn_cons]
  rfl

theorem occupation_head_tail_iff {n : ℕ} (w : Word A (n + 1)) (b : Multiset A) :
    occupation w = b ↔ w 0 ∈ b ∧ occupation (Fin.tail w) = b.erase (w 0) := by
  conv_lhs => rw [← Fin.cons_self_tail w, occupation_cons_eq]
  rw [← Multiset.singleton_add, add_comm ({w 0} : Multiset A),
    Multiset.add_singleton_eq_iff]

/-- Local residual equations imply every coefficient of the actual repeated circuit.
The local equations are construction obligations, not an assumed output theorem. -/
theorem circuit_output_of_residuals (blank : A) (U : Unitary (A × K))
    (a : Multiset A) (r : Multiset A → Space K) (f : Space K)
    (hzero : r 0 = f)
    (hstep : ∀ b, b ≤ a → b ≠ 0 → ∀ i k,
      U (blankMemory blank (r b)) (i, k) = if i ∈ b then r (b.erase i) k else 0) :
    ∀ n t b, b.card = n → b ≤ a → ∀ (w : Word A n) k,
      circuit (fun _ => U) n t (initialized blank n (r b)) (w, k) =
        if occupation w = b then f k else 0 := by
  intro n
  induction n with
  | zero =>
    intro t b hb hba w k
    have hb0 : b = 0 := Multiset.card_eq_zero.mp hb
    subst b
    have hw : w = (fun _ => blank) := Subsingleton.elim _ _
    simp [circuit, initialized_apply_all, hzero, hw, occupation]
  | succ n ih =>
    intro t b hb hba w k
    have hb0 : b ≠ 0 := by intro hz; simp [hz] at hb
    rw [circuit_initialized_step]
    have hv : (WithLp.toLp 2
        (fun j : K => U (blankMemory blank (r b)) (w 0, j))) =
        if w 0 ∈ b then r (b.erase (w 0)) else 0 := by
      ext j
      by_cases hi : w 0 ∈ b <;> simp [hstep b hba hb0, hi]
    rw [hv]
    by_cases hi : w 0 ∈ b
    · rw [if_pos hi]
      have hcard : (b.erase (w 0)).card = n := by
        simp [Multiset.card_erase_of_mem hi, hb]
      rw [ih (t + 1) (b.erase (w 0)) hcard ((Multiset.erase_le _ _).trans hba)]
      simp only [occupation_head_tail_iff w b, hi, true_and]
    · have hw : occupation w ≠ b := fun h => hi ((occupation_head_tail_iff w b).mp h).1
      simp [hi, hw]

theorem normalized_output_of_residuals (blank : A) (U : Unitary (A × K))
    (a : Multiset A) (r : Multiset A → Space K) (f : Space K)
    (hzero : r 0 = f)
    (hstep : ∀ b, b ≤ a → b ≠ 0 → ∀ i k,
      U (blankMemory blank (r b)) (i, k) = if i ∈ b then r (b.erase i) k else 0) :
    ∀ w k, circuit (fun _ => U) a.card 0
      (initialized blank a.card ((Real.sqrt (multiplicity a.card a : ℝ) : ℂ)⁻¹ • r a))
      (w, k) = sectorVector a.card a w * f k := by
  intro w k
  simp only [map_smul]
  change (Real.sqrt (multiplicity a.card a : ℝ) : ℂ)⁻¹ *
    circuit (fun _ => U) a.card 0 (initialized blank a.card (r a)) (w, k) = _
  rw [circuit_output_of_residuals blank U a r f hzero hstep a.card 0 a rfl le_rfl]
  by_cases hw : occupation w = a <;> simp [sectorVector, sectorWords, hw]

end CircuitOutput

end D5.S3.Quantum.StationaryPreparation.ResidualCalculus
