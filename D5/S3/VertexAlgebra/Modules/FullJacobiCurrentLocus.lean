/- GID: D5/S3/VertexAlgebra/Modules/FullJacobiCurrentLocus
   generality: I
   mirror-B: none(source-only-candidate)
   mirror-E: none(source-only-candidate)
   anchors: []
   utility: Pascal power formula and all-source stability of the genuine locus.
   status: UNCOMPILED source candidate.
-/
import D5.S3.VertexAlgebra.Modules.FullJacobiCurrentVacuum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.Modules.FullJacobiCurrentLocus
open FullJacobiCurrentTransport FullJacobiCurrentNilpotence
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeAllStateField
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section
universe u
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Finite Pascal reindexing; both edge coefficients are retained. -/
private theorem pascal_sum (N : ℕ) (w : ℕ → Module.End ℂ M) :
    (∑ j ∈ Finset.range (N + 2), (Nat.choose (N + 1) j : ℂ) • w j) =
      (∑ j ∈ Finset.range (N + 1), (Nat.choose N j : ℂ) • w j) +
      (∑ j ∈ Finset.range (N + 1), (Nat.choose N j : ℂ) • w (j + 1)) := by
  have hedge : (∑ j ∈ Finset.range (N + 1), (Nat.choose N j : ℂ) • w j) =
      (∑ j ∈ Finset.range (N + 1), (Nat.choose N (j + 1) : ℂ) • w (j + 1)) + w 0 := by
    calc
      _ = ∑ j ∈ Finset.range (N + 2), (Nat.choose N j : ℂ) • w j := by
        symm
        rw [Finset.sum_range_succ]
        simp
      _ = _ := by rw [Finset.sum_range_succ']; simp
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_smul,
    Finset.sum_add_distrib, Nat.choose_zero_right, Nat.cast_one, one_smul]
  rw [hedge]
  abel

/-- The preserved proposition now has an explicit finite Pascal induction. -/
theorem current_exp_power_formula (J : FullJacobiLatticeModule D M)
    (i : Fin D.rank) (β : Charge D) (n m : ℤ) (N : ℕ) :
    currentExpPowerFormulaStatement J i β n m N := by
  classical
  let T := current J i n
  let c : ℂ := bilinear D (unitCharge D i) β
  change T ^ N * mode J (exponentialState β) m =
    ∑ j ∈ Finset.range (N + 1), ((Nat.choose N j : ℂ) * c^j) •
      mode J (exponentialState β) (m + (j : ℤ) * n) * T ^ (N - j)
  induction N with
  | zero => simp
  | succ N ih =>
    let w : ℕ → Module.End ℂ M := fun j =>
      c^j • mode J (exponentialState β) (m + (j : ℤ) * n) * T ^ (N + 1 - j)
    have hterm (j : ℕ) (hj : j ∈ Finset.range (N + 1)) :
        T * (((Nat.choose N j : ℂ) * c^j) •
          mode J (exponentialState β) (m + (j : ℤ) * n) * T ^ (N - j)) =
        (Nat.choose N j : ℂ) • w j + (Nat.choose N j : ℂ) • w (j + 1) := by
      have hjN : j ≤ N := by have hjlt := Finset.mem_range.mp hj; omega
      have hc : T * mode J (exponentialState β) (m + (j : ℤ) * n) =
          mode J (exponentialState β) (m + (j : ℤ) * n) * T +
            c • mode J (exponentialState β) (n + (m + (j : ℤ) * n)) :=
        sub_eq_iff_eq_add'.mp (module_current_exponential J i β n (m + (j : ℤ) * n))
      have hp : T * T ^ (N - j) = T ^ (N + 1 - j) := by
        rw [← pow_succ']
        congr 1
        omega
      have hs : n + (m + (j : ℤ) * n) = m + ((j + 1 : ℕ) : ℤ) * n := by
        push_cast
        ring
      have hd : N + 1 - (j + 1) = N - j := by omega
      calc
        _ = ((Nat.choose N j : ℂ) * c^j) •
            (mode J (exponentialState β) (m + (j : ℤ) * n) * T ^ (N + 1 - j)) +
            (((Nat.choose N j : ℂ) * c^j) * c) •
              (mode J (exponentialState β) (m + ((j + 1 : ℕ) : ℤ) * n) * T ^ (N - j)) := by
          rw [← mul_assoc, mul_smul_comm, hc, smul_add, add_mul]
          simp only [smul_mul_assoc, mul_assoc, hp, hs, smul_smul]
        _ = _ := by simp only [w, smul_mul_assoc, smul_smul, pow_succ, hd, mul_assoc]
    calc
      T ^ (N + 1) * mode J (exponentialState β) m =
          T * (T ^ N * mode J (exponentialState β) m) := by
        rw [pow_succ', mul_assoc]
      _ = ∑ j ∈ Finset.range (N + 1),
          ((Nat.choose N j : ℂ) • w j + (Nat.choose N j : ℂ) • w (j + 1)) := by
        rw [ih, Finset.mul_sum]
        exact Finset.sum_congr rfl hterm
      _ = ∑ j ∈ Finset.range (N + 2), (Nat.choose (N + 1) j : ℂ) • w j := by
        rw [Finset.sum_add_distrib]
        exact (pascal_sum N w).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [w, smul_mul_assoc, smul_smul]

/-- Common truncation is taken over exactly K concrete vectors, never all of M. -/
theorem common_exponential_truncation (J : FullJacobiLatticeModule D M)
    (β : Charge D) (T : Module.End ℂ M) (K : ℕ) (v : M) :
    ∃ R : ℤ, 0 ≤ R ∧ ∀ t : ℕ, t < K → ∀ s : ℤ,
      R ≤ s → mode J (exponentialState β) s ((T ^ t) v) = 0 := by
  classical
  choose B hB using (fun t : Fin K =>
    module_truncation J (exponentialState β) ((T ^ t.val) v))
  let R : ℕ := Finset.univ.sup (fun t : Fin K => (B t).toNat)
  refine ⟨R, Int.natCast_nonneg _, ?_⟩
  intro t ht s hs
  have hb : (B ⟨t,ht⟩).toNat ≤ R := Finset.le_sup (f := fun t : Fin K => (B t).toNat)
    (Finset.mem_univ (⟨t,ht⟩ : Fin K))
  exact hB ⟨t,ht⟩ s (by omega)

/-- Exponential stability with the explicit common bound K+max(0,R-m). -/
theorem exponential_mode_stable (J : FullJacobiLatticeModule D M)
    (i : Fin D.rank) (n : ℤ) (hn : 0 < n) (β : Charge D) (m : ℤ)
    (v : M) (hv : v ∈ powerNilpotenceSubmodule (current J i n)) :
    mode J (exponentialState β) m v ∈ powerNilpotenceSubmodule (current J i n) := by
  classical
  obtain ⟨K, hK, hvK⟩ := hv
  let T := current J i n
  obtain ⟨R, hR, hcut⟩ := common_exponential_truncation J β T K v
  dsimp only [T] at hcut
  let N : ℕ := K + (R - m).toNat
  have hNpos : 0 < N := by dsimp [N]; omega
  have hNexact : (N : ℤ) = (K : ℤ) + max 0 (R - m) := by dsimp [N]; omega
  refine ⟨N, hNpos, ?_⟩
  have hformula := LinearMap.congr_fun (current_exp_power_formula J i β n m N) v
  change (T ^ N) (mode J (exponentialState β) m v) = _ at hformula
  rw [hformula]
  simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hjK : K ≤ N - j
  · have hz : (current J i n ^ (N - j)) v = 0 := pow_map_zero_of_le T hjK hvK
    simp [hz]
  · have ht : N - j < K := by omega
    have hjN : j ≤ N := by have hjlt := Finset.mem_range.mp hj; omega
    have hjlarge : (R - m).toNat < j := by dsimp [N] at *; omega
    have hprod : (j : ℤ) ≤ (j : ℤ) * n := by
      have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
      have hn1 : (1 : ℤ) ≤ n := by omega
      nlinarith
    have hindex : R ≤ m + (j : ℤ) * n := by omega
    simp [hcut (N - j) ht _ hindex]

/-- The literal preserving-state set of the predecessor is a source submodule. -/
def preservingStates (J : FullJacobiLatticeModule D M) (N : Submodule ℂ M) :
    Submodule ℂ (Carrier D) where
  carrier := sourceModeStable J N
  zero_mem' := by intro s v hv; simpa [mode] using N.zero_mem
  add_mem' := by
    intro a b ha hb s v hv
    simpa [mode] using N.add_mem (ha s v hv) (hb s v hv)
  smul_mem' := by
    intro c a ha s v hv
    simpa [mode] using N.smul_mem c (ha s v hv)

/-- Both independently finite iterate sums lie in N, term by term. -/
theorem preservingStates_product (J : FullJacobiLatticeModule D M)
    (N : Submodule ℂ M) (a b : Carrier D)
    (ha : a ∈ preservingStates J N) (hb : b ∈ preservingStates J N) (r : ℤ) :
    sourceProduct D a r b ∈ preservingStates J N := by
  classical
  intro s v hv
  obtain ⟨hF, hS, h⟩ := module_iterate J a b v r s
  rw [h]
  apply N.sub_mem
  · rw [finsum_eq_sum_of_support_subset _ hF.coe_toFinset.ge]
    apply N.sum_mem
    intro j hj
    exact N.smul_mem _ (ha _ _ (hb _ v hv))
  · rw [finsum_eq_sum_of_support_subset _ hS.coe_toFinset.ge]
    apply N.sum_mem
    intro j hj
    exact N.smul_mem _ (N.smul_mem _ (hb _ _ (ha _ v hv)))

/-- Source negative-word generation is consumed literally, including charged generators. -/
theorem all_source_modes_stable (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin D.rank) (n : ℤ) (hn : 0 < n)
    (a : Carrier D) (s : ℤ) (v : M)
    (hv : v ∈ powerNilpotenceSubmodule (current J i n)) :
    mode J a s v ∈ powerNilpotenceSubmodule (current J i n) := by
  classical
  let N := powerNilpotenceSubmodule (current J i n)
  let S := preservingStates J N
  have hcurrent (h : Fin D.rank) : currentState D h ∈ S := by
    intro t u hu
    exact current_mode_stable J i h n t u hu
  have hexp (β : Charge D) : exponentialState β ∈ S := by
    intro t u hu
    exact exponential_mode_stable J i n hn β t u hu
  obtain ⟨B, hB⟩ := finite_negative_generation D hD
  have hword (w : List (Generator D B × ℕ)) : negativeWord D B w ∈ S := by
    induction w with
    | nil => simpa [negativeWord, exponentialState] using hexp 0
    | cons x w ih =>
      rcases x with ⟨g,k⟩
      cases g with
      | inl h =>
        have hm := preservingStates_product J N _ _ (hcurrent h) ih (-(k : ℤ) - 1)
        simpa only [negativeWord, generatingField, sourceProduct, current_state_field] using hm
      | inr β =>
        have hm := preservingStates_product J N _ _ (hexp β.val) ih (-(k : ℤ) - 1)
        simpa only [negativeWord, generatingField, sourceProduct, source_exponential_stateField] using hm
  have hspan : negativeWordSpan D B ≤ S := Submodule.span_le.mpr (by
    rintro u ⟨w, rfl⟩
    exact hword w)
  have ha : a ∈ S := hspan (by rw [hB]; trivial)
  exact ha s v hv

/-- The algebraic injectivity mechanism: no quotient or vacuum hypothesis enters. -/
theorem current_preimage_locus (J : FullJacobiLatticeModule D M)
    (i : Fin D.rank) (n : ℤ) (v : M)
    (hv : current J i n v ∈ powerNilpotenceSubmodule (current J i n)) :
    v ∈ powerNilpotenceSubmodule (current J i n) := by
  obtain ⟨K, hK, hzero⟩ := hv
  refine ⟨K + 1, Nat.succ_pos _, ?_⟩
  simpa only [pow_succ, Module.End.mul_apply] using hzero

end
end D5.S3.VertexAlgebra.Modules.FullJacobiCurrentLocus
