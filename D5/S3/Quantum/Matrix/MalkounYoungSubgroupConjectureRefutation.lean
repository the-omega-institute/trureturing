/- GID: D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.claim; result=D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.result; claim=D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.claim
   digest: Fifteen Gram blocks refute the class-preserving permutation inequality. -/

import D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation

/-! # Conjecture D fails for class-preserving permutation groups -/

open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Matrix.MalkounYoungSubgroupConjectureRefutation

open D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation (crossSum diagonal_product_eq_real)

noncomputable section

/-- The source's group of permutations preserving every equivalence class. -/
def classPreserving {n : ℕ} (r : Setoid (Fin n)) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ i, r (σ i) i}
  one_mem' := fun i => r.refl i
  mul_mem' := fun hσ hτ i => r.trans (hσ _) (hτ i)
  inv_mem' := by
    intro σ hσ i
    have h := r.symm (hσ (σ.symm i))
    rw [σ.apply_symm_apply] at h
    exact h

/-- Conjecture D for arbitrary dimension and both arbitrary equivalence relations. -/
def claim : Prop :=
  ∀ (n : ℕ) (r₁ r₂ : Setoid (Fin n)) (h : Matrix (Fin n) (Fin n) ℂ),
    h.IsHermitian → h.PosSemidef →
      (Nat.card ↥(classPreserving r₁ ⊓ classPreserving r₂) : ℝ) *
        (∏ i, (h i i).re) ≤ (crossSum (classPreserving r₁) (classPreserving r₂) h).re

private def coords (m : ℕ) : Fin (m * 3) ≃ Fin m × Fin 3 := finProdFinEquiv.symm

private def blockRelation (m : ℕ) (r : Setoid (Fin 3)) : Setoid (Fin (m * 3)) where
  r i k := (coords m i).1 = (coords m k).1 ∧ r (coords m i).2 (coords m k).2
  iseqv := ⟨fun _ => ⟨rfl, r.refl _⟩,
    fun h => ⟨h.1.symm, r.symm h.2⟩,
    fun h k => ⟨h.1.trans k.1, r.trans h.2 k.2⟩⟩

private def seedRelation (t : Fin 3) : Setoid (Fin 3) :=
  Setoid.ker (fun s : Fin 3 => s == t)

private def blockMatrix (m : ℕ) (a : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin (m * 3)) (Fin (m * 3)) ℂ :=
  (Matrix.blockDiagonal (fun _ : Fin m => a)).submatrix
    (fun i => ((coords m i).2, (coords m i).1))
    (fun i => ((coords m i).2, (coords m i).1))

private def v : Matrix (Fin 2) (Fin 3) ℂ := !![1, 1, 1; 0, 1, Complex.I]

private def seed : Matrix (Fin 3) (Fin 3) ℂ := v.conjTranspose * v

private theorem block_posSemidef (m : ℕ) : (blockMatrix m seed).PosSemidef := by
  rw [blockMatrix.eq_1, seed.eq_1]
  rw [Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_conjTranspose]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).submatrix _

private def blockPermutation (m : ℕ) (f : Fin m → Equiv.Perm (Fin 3)) :
    Equiv.Perm (Fin (m * 3)) :=
  (coords m).symm.permCongr (Equiv.prodCongrRight f)

private def blockLift (m : ℕ) (r : Setoid (Fin 3)) (f : Fin m → classPreserving r) :
    classPreserving (blockRelation m r) :=
  ⟨blockPermutation m (fun j => (f j).val), by
    intro i
    change (coords m _).1 = (coords m i).1 ∧ r (coords m _).2 (coords m i).2
    rw [blockPermutation.eq_1]
    simp only [Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
    exact ⟨rfl, (f _).property _⟩⟩

private theorem blockLift_apply (m : ℕ) (r : Setoid (Fin 3))
    (f : Fin m → classPreserving r) (j : Fin m) (i : Fin 3) :
    coords m ((blockLift m r f).val ((coords m).symm (j, i))) = (j, (f j).val i) := by
  rw [blockLift.eq_1]
  change coords m (blockPermutation m (fun j => (f j).val) ((coords m).symm (j, i))) = _
  rw [blockPermutation.eq_1]
  simp only [Equiv.permCongr_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply, Equiv.prodCongrRight_apply]

private def fiberPermutation (m : ℕ) (σ : Equiv.Perm (Fin (m * 3)))
    (hσ : ∀ i, (coords m (σ i)).1 = (coords m i).1) (j : Fin m) :
    Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (fun s => (coords m (σ ((coords m).symm (j, s)))).2) (by
    constructor
    · intro a b hab
      have he : coords m (σ ((coords m).symm (j, a))) =
          coords m (σ ((coords m).symm (j, b))) := by
        apply Prod.ext
        · simp only [hσ, Equiv.apply_symm_apply]
        · exact hab
      exact congrArg Prod.snd ((coords m).symm.injective (σ.injective
        ((coords m).injective he)))
    · intro b
      let x := coords m (σ.symm ((coords m).symm (j, b)))
      have hx : x.1 = j := by
        have h := hσ (σ.symm ((coords m).symm (j, b)))
        simpa only [Equiv.apply_symm_apply] using h.symm
      refine ⟨x.2, ?_⟩
      have he : (coords m).symm (j, x.2) = σ.symm ((coords m).symm (j, b)) := by
        apply (coords m).injective
        simp only [Equiv.apply_symm_apply]
        exact Prod.ext hx.symm rfl
      simp only [he, Equiv.apply_symm_apply])

private def blockEquiv (m : ℕ) (r : Setoid (Fin 3)) :
    (Fin m → classPreserving r) ≃ classPreserving (blockRelation m r) :=
  Equiv.ofBijective (blockLift m r) (by
    constructor
    · intro f g h
      funext j
      apply Subtype.ext
      apply Equiv.ext
      intro i
      have he := congrArg (fun σ => (coords m (σ.val ((coords m).symm (j, i)))).2) h
      simpa only [blockLift_apply] using he
    · intro σ
      let f : Fin m → classPreserving r := fun j =>
        ⟨fiberPermutation m σ.val (fun i => (σ.property i).1) j, by
          intro i
          change r (coords m (σ.val ((coords m).symm (j, i)))).2 i
          simpa only [Equiv.apply_symm_apply] using
            (σ.property ((coords m).symm (j, i))).2⟩
      refine ⟨f, ?_⟩
      apply Subtype.ext
      apply Equiv.ext
      intro i
      apply (coords m).injective
      have hi : (coords m).symm ((coords m i).1, (coords m i).2) = i :=
        (coords m).symm_apply_apply i
      rw [← hi, blockLift_apply]
      apply Prod.ext
      · simpa only [Equiv.apply_symm_apply] using
          ((σ.property ((coords m).symm ((coords m i).1, (coords m i).2))).1).symm
      · rfl)

private theorem block_factorization (m : ℕ) (r s : Setoid (Fin 3))
    (a : Matrix (Fin 3) (Fin 3) ℂ) :
    crossSum (classPreserving (blockRelation m r))
      (classPreserving (blockRelation m s)) (blockMatrix m a) =
      (crossSum (classPreserving r) (classPreserving s) a) ^ m := by
  classical
  have hterm (f : Fin m → classPreserving r) (g : Fin m → classPreserving s) :
      (∏ i, blockMatrix m a ((blockLift m r f).val i) ((blockLift m s g).val i)) =
        ∏ j, ∏ i, a ((f j).val i) ((g j).val i) := by
    rw [← (coords m).symm.prod_comp (fun i =>
      blockMatrix m a ((blockLift m r f).val i) ((blockLift m s g).val i))]
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro i _
    simp only [blockMatrix, Matrix.submatrix_apply, blockLift_apply,
      Matrix.blockDiagonal_apply, ite_true]
  have hsum :
      crossSum (classPreserving (blockRelation m r))
        (classPreserving (blockRelation m s)) (blockMatrix m a) =
      ∑ f : Fin m → classPreserving r, ∑ g : Fin m → classPreserving s,
        ∏ j, ∏ i, a ((f j).val i) ((g j).val i) := by
    change (∑ σ : classPreserving (blockRelation m r),
      ∑ τ : classPreserving (blockRelation m s), ∏ i, blockMatrix m a (σ.val i) (τ.val i)) = _
    rw [← (blockEquiv m r).sum_comp]
    apply Finset.sum_congr rfl
    intro f _
    rw [← (blockEquiv m s).sum_comp]
    apply Finset.sum_congr rfl
    intro g _
    exact hterm f g
  rw [hsum]
  calc
    _ = ∑ f : Fin m → classPreserving r,
        ∏ j, ∑ τ : classPreserving s, ∏ i, a ((f j).val i) (τ.val i) := by
      apply Finset.sum_congr rfl
      intro f _
      exact (Fintype.prod_sum (fun j (τ : classPreserving s) =>
        ∏ i, a ((f j).val i) (τ.val i))).symm
    _ = ∏ _ : Fin m, ∑ σ : classPreserving r,
        ∑ τ : classPreserving s, ∏ i, a (σ.val i) (τ.val i) :=
      (Fintype.prod_sum (fun _ (σ : classPreserving r) =>
        ∑ τ : classPreserving s, ∏ i, a (σ.val i) (τ.val i))).symm
    _ = _ := by simp only [crossSum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private def seedEquiv (t : Fin 3) (p : Equiv.Perm (Fin 3))
    (hp : ∀ i, seedRelation t (p i) i)
    (hclass : ∀ σ : Equiv.Perm (Fin 3), (∀ i, seedRelation t (σ i) i) → σ = 1 ∨ σ = p)
    (hne : p ≠ 1) : Bool ≃ classPreserving (seedRelation t) :=
  Equiv.ofBijective (fun b => ⟨if b then p else 1, by
    cases b
    · exact fun i => (seedRelation t).refl i
    · exact hp⟩) (by
    constructor
    · intro a b h
      have hv := congrArg Subtype.val h
      cases a <;> cases b
      · rfl
      · exact (hne hv.symm).elim
      · exact (hne hv).elim
      · rfl
    · intro σ
      rcases hclass σ.val σ.property with h | h
      · exact ⟨false, Subtype.ext h.symm⟩
      · exact ⟨true, Subtype.ext h.symm⟩)

private theorem seed_crossSum :
    crossSum (classPreserving (seedRelation 2)) (classPreserving (seedRelation 0)) seed =
      9 - Complex.I := by
  classical
  have hp : ∀ i : Fin 3, seedRelation 2 (Equiv.swap 0 1 i) i := by
    change ∀ i : Fin 3, (Equiv.swap 0 1 i == 2) = (i == 2)
    decide
  have hq : ∀ i : Fin 3, seedRelation 0 (Equiv.swap 1 2 i) i := by
    change ∀ i : Fin 3, (Equiv.swap 1 2 i == 0) = (i == 0)
    decide
  have hc : ∀ σ : Equiv.Perm (Fin 3), (∀ i, seedRelation 2 (σ i) i) →
      σ = 1 ∨ σ = Equiv.swap 0 1 := by
    change ∀ σ : Equiv.Perm (Fin 3), (∀ i, (σ i == 2) = (i == 2)) →
      σ = 1 ∨ σ = Equiv.swap 0 1
    decide +kernel
  have hd : ∀ σ : Equiv.Perm (Fin 3), (∀ i, seedRelation 0 (σ i) i) →
      σ = 1 ∨ σ = Equiv.swap 1 2 := by
    change ∀ σ : Equiv.Perm (Fin 3), (∀ i, (σ i == 0) = (i == 0)) →
      σ = 1 ∨ σ = Equiv.swap 1 2
    decide +kernel
  let e := seedEquiv 2 (Equiv.swap 0 1) hp hc (by decide)
  let f := seedEquiv 0 (Equiv.swap 1 2) hq hd (by decide)
  change (∑ σ : classPreserving (seedRelation 2),
    ∑ τ : classPreserving (seedRelation 0), ∏ i, seed (σ.val i) (τ.val i)) = _
  rw [← e.sum_comp]
  simp_rw [← f.sum_comp]
  change (∑ b : Bool, ∑ c : Bool, ∏ i, seed
    ((if b then Equiv.swap 0 1 else 1) i) ((if c then Equiv.swap 1 2 else 1) i)) = _
  rw [seed.eq_1, v.eq_1]
  norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ, Fin.prod_univ_succ, map_ofNat, Fintype.sum_bool, Equiv.swap_apply_def]
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]

private theorem block_intersection (m : ℕ) :
    classPreserving (blockRelation m (seedRelation 2)) ⊓
      classPreserving (blockRelation m (seedRelation 0)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro σ hσ
  apply Subgroup.mem_bot.mpr
  apply Equiv.ext
  intro i
  apply (coords m).injective
  apply Prod.ext
  · exact (hσ.1 i).1
  · have hseed : ∀ a b : Fin 3, seedRelation 2 a b → seedRelation 0 a b → a = b := by
      change ∀ a b : Fin 3, (a == 2) = (b == 2) → (a == 0) = (b == 0) → a = b
      decide
    exact hseed _ _ (hσ.1 i).2 (hσ.2 i).2

private theorem block_diagonal (m : ℕ) :
    (∏ i, ((blockMatrix m seed) i i).re) = 4 ^ m := by
  apply Complex.ofReal_injective
  rw [← diagonal_product_eq_real _ (block_posSemidef m).1]
  have hp : (∏ i, (blockMatrix m seed) i i) = (∏ s, seed s s) ^ m := by
    calc
      _ = ∏ p : Fin m × Fin 3, seed p.2 p.2 := by
        apply Fintype.prod_equiv (coords m)
        intro i
        simp only [blockMatrix, Matrix.submatrix_apply, Matrix.blockDiagonal_apply, ite_true]
      _ = _ := by simp [Fintype.prod_prod_type]
  rw [hp]
  norm_num [seed, v, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ, Fin.prod_univ_succ, map_ofNat]

private theorem power_value : (9 - Complex.I) ^ 15 =
    -20078071648128 - 224842906547072 * Complex.I := by
  norm_num [Complex.ext_iff, pow_succ, Complex.mul_re, Complex.mul_im]

/-- Conjecture D fails for fifteen copies of the three-column Gram matrix. -/
theorem result : ¬ claim := by
  intro h
  have hb := h 45 (blockRelation 15 (seedRelation 2))
    (blockRelation 15 (seedRelation 0)) (blockMatrix 15 seed)
    (block_posSemidef 15).1 (block_posSemidef 15)
  rw [block_intersection 15, block_diagonal 15, block_factorization 15,
    seed_crossSum, power_value] at hb
  norm_num at hb

end

end D5.S3.Quantum.Matrix.MalkounYoungSubgroupConjectureRefutation
