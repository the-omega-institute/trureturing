import D5.S3.Quantum.Fermionic.CountableOccupationFock
import Mathlib.InformationTheory.Hamming
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false

open scoped BigOperators InnerProductSpace Matrix Classical
open PredictiveThermodynamic.Physical (Assignment)
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner (FullOperator fullC)
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression (fullC_entry)
open D5.S3.Quantum.FermionicCorrelationalBound.CompletedCorrelationalBound (occupiedModes)
open D5.S3.Quantum.Fermionic.CountableOccupationFock
  (finiteMode mode prefixEmbed jw_annihilate_intertwining jw_create_intertwining)

namespace D5.S3.Quantum.Semigroups.WuCubicMultimodeCrossing
noncomputable section

/-- The squared norm of the odd-occupation component. -/
def oddMass {N : ℕ} (x : Assignment N → ℂ) : ℝ :=
  ∑ u, (if (occupiedModes u).card % 2 = 1 then (1 : ℝ) else 0) * Complex.normSq (x u)

private theorem hammingDist_update_le_one {N : ℕ} (v : Assignment N) (j : Fin N)
    (b : Bool) : hammingDist (Function.update v j b) v ≤ 1 := by
  have hsub : (Finset.univ.filter (fun i => Function.update v j b i ≠ v i)) ⊆
      ({j} : Finset (Fin N)) := by
    intro i hi
    simp only [Finset.mem_singleton]
    by_contra hne
    exact (Finset.mem_filter.mp hi).2 (Function.update_of_ne hne b v)
  simpa only [hammingDist, Finset.card_singleton] using Finset.card_le_card hsub

private theorem annihilation_entry_eq_zero {N : ℕ} (j : Fin N) {u v : Assignment N}
    (h : 2 ≤ hammingDist u v) : fullC j u v = 0 := by
  have hnot : ¬ (v j = true ∧ u = Function.update v j false) := by
    rintro ⟨_, rfl⟩
    have hle := hammingDist_update_le_one v j false
    omega
  rw [fullC_entry, if_neg hnot]

private theorem mode_entry_eq_zero {N : ℕ} (j : Fin N) (creator : Bool)
    {u v : Assignment N} (h : 2 ≤ hammingDist u v) : finiteMode j creator u v = 0 := by
  cases creator
  · exact annihilation_entry_eq_zero j h
  · change ((fullC j)ᴴ) u v = 0
    have h' : 2 ≤ hammingDist v u := by rwa [hammingDist_comm v u]
    rw [Matrix.conjTranspose_apply, annihilation_entry_eq_zero j h', star_zero]

private theorem inner_mulVec_eq_zero_of_entries {N : ℕ} (A : FullOperator N)
    {S T : Set (Assignment N)} {x y : Assignment N → ℂ}
    (hx : Function.support x ⊆ S) (hy : Function.support y ⊆ T)
    (hA : ∀ u ∈ S, ∀ v ∈ T, A u v = 0) :
    ⟪WithLp.toLp 2 x, WithLp.toLp 2 (A.mulVec y)⟫_ℂ = 0 := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Pi.star_apply]
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  by_cases hu : x u = 0
  · simp [hu]
  by_cases hv : y v = 0
  · simp [hv]
  rw [hA u (hx hu) v (hy hv), zero_mul, zero_mul]

/-- Two coordinate subspaces at mutual Hamming distance at least two are orthogonal
and have zero crossing under each signed CAR annihilator and creator. -/
theorem support_separated {N : ℕ} {S T : Set (Assignment N)} {x y : Assignment N → ℂ}
    (hx : Function.support x ⊆ S) (hy : Function.support y ⊆ T)
    (hsep : ∀ u ∈ S, ∀ v ∈ T, 2 ≤ hammingDist u v) :
    ⟪WithLp.toLp 2 x, WithLp.toLp 2 y⟫_ℂ = 0 ∧
      ∀ (j : Fin N) (creator : Bool),
        ⟪WithLp.toLp 2 x, WithLp.toLp 2 ((finiteMode j creator).mulVec y)⟫_ℂ = 0 := by
  constructor
  · have hA : ∀ u ∈ S, ∀ v ∈ T, (1 : FullOperator N) u v = 0 := by
      intro u hu v hv
      apply Matrix.one_apply_ne
      rintro rfl
      have h := hsep u hu u hv
      rw [hammingDist_self] at h
      omega
    simpa only [Matrix.one_mulVec] using inner_mulVec_eq_zero_of_entries 1 hx hy hA
  · intro j creator
    exact inner_mulVec_eq_zero_of_entries (finiteMode j creator) hx hy
      (fun u hu v hv => mode_entry_eq_zero j creator (hsep u hu v hv))

/-- The countable CAR image of a prefix state has a finite representative with
zero pairing against the other support. -/
theorem support_separated_prefix {N : ℕ} {S T : Set (Assignment N)}
    {x y : Assignment N → ℂ}
    (hx : Function.support x ⊆ S) (hy : Function.support y ⊆ T)
    (hsep : ∀ u ∈ S, ∀ v ∈ T, 2 ≤ hammingDist u v)
    (j : Fin N) (creator : Bool) :
    ∃ z : Assignment N → ℂ,
      mode j.val creator (prefixEmbed N y) = prefixEmbed N z ∧
        ⟪WithLp.toLp 2 x, WithLp.toLp 2 z⟫_ℂ = 0 := by
  refine ⟨(finiteMode j creator).mulVec y, ?_, (support_separated hx hy hsep).2 j creator⟩
  cases creator
  · exact jw_annihilate_intertwining N j y
  · exact jw_create_intertwining N j y

private def occupationSymbol {N : ℕ} (S : Finset (Fin N)) : Assignment N :=
  fun i => decide (i ∈ S)

@[simp] private theorem occupiedModes_symbol {N : ℕ} (S : Finset (Fin N)) :
    occupiedModes (occupationSymbol S) = S := by
  ext i
  simp [occupiedModes, occupationSymbol]

private def mix {N : ℕ} (e o : Assignment N) (r : ℝ) : Assignment N → ℂ :=
  fun u => (if u = e then (Real.sqrt (1 - r) : ℂ) else 0) +
    (if u = o then (Real.sqrt r : ℂ) else 0)

private theorem mix_support {N : ℕ} (e o : Assignment N) (r : ℝ) :
    Function.support (mix e o r) ⊆ ({e, o} : Set (Assignment N)) := by
  intro u hu
  by_contra h
  have hn : u ≠ e ∧ u ≠ o := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or] using h
  exact hu (by simp [mix, hn.1, hn.2])

private theorem mix_weighted_mass {N : ℕ} {e o : Assignment N} {r : ℝ}
    (heo : e ≠ o) (hr : r ∈ Set.Icc (0 : ℝ) 1) (w : Assignment N → ℝ) :
    (∑ u, w u * Complex.normSq (mix e o r u)) = w e * (1 - r) + w o * r := by
  have hpoint (u : Assignment N) :
      w u * Complex.normSq (mix e o r u) =
        (if u = e then w e * (1 - r) else 0) + (if u = o then w o * r else 0) := by
    by_cases he : u = e
    · subst u
      simp [mix, heo, Complex.normSq_ofReal, Real.mul_self_sqrt (sub_nonneg.mpr hr.2)]
    · by_cases ho : u = o
      · subst u
        simp [mix, heo.symm, Complex.normSq_ofReal, Real.mul_self_sqrt hr.1]
      · simp [mix, he, ho]
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem mix_norm {N : ℕ} {e o : Assignment N} {r : ℝ}
    (heo : e ≠ o) (hr : r ∈ Set.Icc (0 : ℝ) 1) : ‖WithLp.toLp 2 (mix e o r)‖ = 1 := by
  have h := mix_weighted_mass heo hr (fun _ => 1)
  simp only [one_mul, sub_add_cancel] at h
  rw [EuclideanSpace.norm_eq]
  change Real.sqrt (∑ u, ‖mix e o r u‖ ^ 2) = 1
  simp_rw [← Complex.normSq_eq_norm_sq]
  rw [h, Real.sqrt_one]

private theorem mix_oddMass {N : ℕ} {e o : Assignment N} {r : ℝ}
    (heo : e ≠ o) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (he : (occupiedModes e).card % 2 = 0) (ho : (occupiedModes o).card % 2 = 1) :
    oddMass (mix e o r) = r := by
  rw [oddMass, mix_weighted_mass heo hr
    (fun u => if (occupiedModes u).card % 2 = 1 then (1 : ℝ) else 0)]
  simp [he, ho]

/-- The witnesses mix the occupation symbols 000 and 001, and 110 and 111,
with every later mode vacant. Each signed single jump has zero crossing
in both directions. -/
theorem exists_orthogonal_with_oddMass_zero_crossing {N : ℕ} (hN : 3 ≤ N)
    {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∃ x y : Assignment N → ℂ,
      ‖WithLp.toLp 2 x‖ = 1 ∧ ‖WithLp.toLp 2 y‖ = 1 ∧
      ⟪WithLp.toLp 2 x, WithLp.toLp 2 y⟫_ℂ = 0 ∧
      oddMass x = t ∧ oddMass y = s ∧
      ∀ (j : Fin N) (creator : Bool),
        ⟪WithLp.toLp 2 x, WithLp.toLp 2 ((finiteMode j creator).mulVec y)⟫_ℂ = 0 ∧
        ⟪WithLp.toLp 2 y, WithLp.toLp 2 ((finiteMode j creator).mulVec x)⟫_ℂ = 0 := by
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨1, by omega⟩
  let k : Fin N := ⟨2, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hval : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have hik : i ≠ k := by
    intro h
    have hval : (0 : ℕ) = 2 := congrArg Fin.val h
    omega
  have hjk : j ≠ k := by
    intro h
    have hval : (1 : ℕ) = 2 := congrArg Fin.val h
    omega
  let a₀ := occupationSymbol (∅ : Finset (Fin N))
  let a₁ := occupationSymbol ({k} : Finset (Fin N))
  let b₀ := occupationSymbol ({i, j} : Finset (Fin N))
  let b₁ := occupationSymbol ({i, j, k} : Finset (Fin N))
  have ca₀ : (occupiedModes a₀).card = 0 := by simp [a₀]
  have ca₁ : (occupiedModes a₁).card = 1 := by simp [a₁]
  have cb₀ : (occupiedModes b₀).card = 2 := by simp [b₀, Finset.card_pair_eq_two_iff, hij]
  have cb₁ : (occupiedModes b₁).card = 3 := by
    simp [b₁, Finset.card_insert_of_notMem, hij, hik, hjk]
  have ha : a₀ ≠ a₁ := by
    intro h
    have hc := congrArg (fun u => (occupiedModes u).card) h
    rw [ca₀, ca₁] at hc
    omega
  have hb : b₀ ≠ b₁ := by
    intro h
    have hc := congrArg (fun u => (occupiedModes u).card) h
    rw [cb₀, cb₁] at hc
    omega
  have hleft : ∀ u ∈ ({a₀, a₁} : Set (Assignment N)), u i = false ∧ u j = false := by
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · simp [a₀, occupationSymbol]
    · rw [Set.mem_singleton_iff.mp hu]
      simp [a₁, occupationSymbol, hik, hjk]
  have hright : ∀ v ∈ ({b₀, b₁} : Set (Assignment N)), v i = true ∧ v j = true := by
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · simp [b₀, occupationSymbol]
    · rw [Set.mem_singleton_iff.mp hv]
      simp [b₁, occupationSymbol]
  have hsep : ∀ u ∈ ({a₀, a₁} : Set (Assignment N)),
      ∀ v ∈ ({b₀, b₁} : Set (Assignment N)), 2 ≤ hammingDist u v := by
    intro u hu v hv
    obtain ⟨hui, huj⟩ := hleft u hu
    obtain ⟨hvi, hvj⟩ := hright v hv
    change 1 < (Finset.univ.filter (fun l => u l ≠ v l)).card
    exact Finset.one_lt_card.mpr ⟨i, by simp [hui, hvi], j, by simp [huj, hvj], hij⟩
  have hxy := support_separated (mix_support a₀ a₁ t) (mix_support b₀ b₁ s) hsep
  have hyx := support_separated (mix_support b₀ b₁ s) (mix_support a₀ a₁ t)
    (fun v hv u hu => by simpa only [hammingDist_comm u v] using hsep u hu v hv)
  refine ⟨mix a₀ a₁ t, mix b₀ b₁ s, mix_norm ha ht, mix_norm hb hs, hxy.1,
    mix_oddMass ha ht (by rw [ca₀]) (by rw [ca₁]),
    mix_oddMass hb hs (by rw [cb₀]) (by rw [cb₁]), ?_⟩
  exact fun l creator => ⟨hxy.2 l creator, hyx.2 l creator⟩

run_cmd do
  for theoremName in #[``support_separated, ``support_separated_prefix,
      ``exists_orthogonal_with_oddMass_zero_crossing] do
    for axiomName in ← Lean.collectAxioms theoremName do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom for {theoremName}: {axiomName}"

end
end D5.S3.Quantum.Semigroups.WuCubicMultimodeCrossing
