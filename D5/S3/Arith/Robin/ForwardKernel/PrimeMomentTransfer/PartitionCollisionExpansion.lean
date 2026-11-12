/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic moments have degree-sensitive collision expansions. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticMomentDefs
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.ArithmeticTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CollisionComponentFactor
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.MergedLabelMomentBounds

/-! Grouping by equality partitions is the classical fiber decomposition of a finite sum
(equivalently, the set-partition expansion of power sums). The quadratic reduction below
extends the finite-order algebraic moment identities to arbitrary order. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]

/-- Coefficients of the remainder of `X^m` modulo `X^2 - a*X - b`.
The initial value also handles the empty product. -/
def quadraticPowerCoeffs (a b : ℝ) (m : ℕ) : ℝ × ℝ :=
  let z := (QuadraticAlgebra.omega : QuadraticAlgebra ℝ b a) ^ m
  (z.im, z.re)

private theorem quadraticPowerCoeffs_succ (a b : ℝ) (m : ℕ) :
    quadraticPowerCoeffs a b (m + 1) =
      (a * (quadraticPowerCoeffs a b m).1 + (quadraticPowerCoeffs a b m).2,
        b * (quadraticPowerCoeffs a b m).1) := by
  simp only [quadraticPowerCoeffs]
  rw [pow_succ', ← QuadraticAlgebra.mk_eta
    ((QuadraticAlgebra.omega : QuadraticAlgebra ℝ b a) ^ m), QuadraticAlgebra.omega_mul_mk]
  apply Prod.ext <;> dsimp only <;> ring

/-- The quadratic relation reduces every power in any commutative real algebra. -/
theorem quadraticPowerCoeffs_pow (a b : ℝ) (y : A)
    (hy : y ^ 2 = a • y + b • (1 : A)) (m : ℕ) :
    y ^ m = (quadraticPowerCoeffs a b m).1 • y +
      (quadraticPowerCoeffs a b m).2 • (1 : A) := by
  let φ : QuadraticAlgebra ℝ b a →ₐ[ℝ] A :=
    QuadraticAlgebra.lift ⟨y, by simpa [sq, add_comm] using hy⟩
  have h := map_pow φ (QuadraticAlgebra.omega : QuadraticAlgebra ℝ b a) m
  simpa [φ, QuadraticAlgebra.lift, quadraticPowerCoeffs, add_comm] using h.symm

/-- Both reduction coefficients have the degree-sensitive bound used for collision grading. -/
theorem quadraticPowerCoeffs_bound (a b C L : ℝ) (hC : 1 ≤ C) (hL : 1 ≤ L)
    (ha : |a| ≤ C * L) (hb : |b| ≤ C * L) (m : ℕ) (hm : 1 ≤ m) :
    |(quadraticPowerCoeffs a b m).1| ≤ ((C + 1) * L) ^ (m - 1) ∧
    |(quadraticPowerCoeffs a b m).2| ≤ ((C + 1) * L) ^ (m - 1) := by
  let M := (C + 1) * L
  have hM : 0 ≤ M := mul_nonneg (by linarith) (by linarith)
  have hCL : 0 ≤ C * L := mul_nonneg (by linarith) (by linarith)
  have hstep : C * L + 1 ≤ M := by dsimp [M]; nlinarith
  have haux (n : ℕ) :
      |(quadraticPowerCoeffs a b (n + 1)).1| ≤ M ^ n ∧
      |(quadraticPowerCoeffs a b (n + 1)).2| ≤ M ^ n := by
    induction n with
    | zero => simp [quadraticPowerCoeffs]
    | succ n ih =>
      rw [quadraticPowerCoeffs_succ]
      dsimp only
      constructor
      · calc
          |a * (quadraticPowerCoeffs a b (n + 1)).1 +
              (quadraticPowerCoeffs a b (n + 1)).2| ≤
              |a| * |(quadraticPowerCoeffs a b (n + 1)).1| +
                |(quadraticPowerCoeffs a b (n + 1)).2| := by
                  simpa only [abs_mul] using abs_add_le
                    (a * (quadraticPowerCoeffs a b (n + 1)).1)
                    (quadraticPowerCoeffs a b (n + 1)).2
          _ ≤ (C * L) * M ^ n + M ^ n :=
            add_le_add (mul_le_mul ha ih.1 (abs_nonneg _) hCL) ih.2
          _ = (C * L + 1) * M ^ n := by ring
          _ ≤ M ^ (n + 1) := by
            rw [pow_succ']; exact mul_le_mul_of_nonneg_right hstep (pow_nonneg hM _)
      · calc
          |b * (quadraticPowerCoeffs a b (n + 1)).1| =
              |b| * |(quadraticPowerCoeffs a b (n + 1)).1| := abs_mul _ _
          _ ≤ (C * L) * M ^ n := mul_le_mul hb ih.1 (abs_nonneg _) hCL
          _ ≤ M ^ (n + 1) := by
            rw [pow_succ']; exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hM _)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using haux n

/-- Equality patterns realized by tuples of the given order and index type.
Omitted partitions have no index assignments and hence contribute zero. -/
def tupleKernelPatterns (k : ℕ) (ι : Type*) [Fintype ι] : Finset (Setoid (Fin k)) :=
  Finset.univ.image (fun d : Fin k → ι => Setoid.ker d)

/-- Mathlib's fiber sum, specialized to the kernel partition of a tuple. -/
theorem sum_eq_tupleKernel_sums {k : ℕ} {M : Type*} [AddCommMonoid M]
    (F : (Fin k → ι) → M) :
    (∑ d, F d) = ∑ σ ∈ tupleKernelPatterns k ι,
      ∑ d : Fin k → ι with Setoid.ker d = σ, F d := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun d _ => Finset.mem_image.mpr
    ⟨d, Finset.mem_univ _, rfl⟩) F

omit [Fintype ι] [Algebra ℝ A] in
private theorem tuple_product_eq_block_powers {k : ℕ} (σ : Setoid (Fin k))
    (d : Fin k → ι) (hd : Setoid.ker d = σ) (Y : ι → A) :
    (∏ i, Y (d i)) = ∏ B : Quotient σ, Y (d B.out) ^ mult (Quotient.mk σ) B := by
  have hout (i : Fin k) : d i = d (Quotient.mk σ i).out := by
    change (Setoid.ker d) i (Quotient.mk σ i).out
    rw [hd]
    exact Quotient.exact (Quotient.out_eq (Quotient.mk σ i)).symm
  have himage : Finset.univ.image (Quotient.mk σ) = Finset.univ := by
    ext B
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact ⟨B.out, Quotient.out_eq B⟩
  calc
    _ = ∏ i : Fin k, Y (d (Quotient.mk σ i).out) :=
      Finset.prod_congr rfl (fun i _ => congrArg Y (hout i))
    _ = _ := by
      simpa only [himage, mult] using
        (Finset.prod_comp (s := Finset.univ) (fun B : Quotient σ => Y (d B.out))
          (Quotient.mk σ))

omit [Fintype ι] in
private theorem tuple_quadratic_reduction {k : ℕ} (σ : Setoid (Fin k))
    (d : Fin k → ι) (hd : Setoid.ker d = σ)
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (hquad : ∀ e, Y e ^ 2 = a • Y e + b • (1 : A)) :
    ℓ (∏ i, Y (d i)) = ∑ S : Finset (Quotient σ),
      ((∏ B ∈ S, (quadraticPowerCoeffs a b (mult (Quotient.mk σ) B)).1) *
       (∏ B ∈ Sᶜ, (quadraticPowerCoeffs a b (mult (Quotient.mk σ) B)).2)) *
      ℓ (∏ B ∈ S, Y (d B.out)) := by
  rw [tuple_product_eq_block_powers σ d hd Y]
  simp_rw [quadraticPowerCoeffs_pow a b _ (hquad _) _]
  rw [Fintype.prod_add, map_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.prod_smul, Finset.prod_smul]
  simp only [Finset.prod_const_one, smul_mul_smul_comm, mul_one, map_smul, smul_eq_mul]

/-- The residual moment for a fixed equality pattern and a set of retained blocks.
The exact-kernel condition is the block-injectivity condition: values agree within each
block and differ between distinct blocks. The positional weight product equals the
product of the aggregated weights over the blocks. -/
def kernelDistinctMoment {k : ℕ} (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A)
    (f : Fin k → ι → ℝ) (σ : Setoid (Fin k)) (S : Finset (Quotient σ)) : ℝ :=
  ∑ d : Fin k → ι with Setoid.ker d = σ,
    (∏ i, f i (d i)) * ℓ (∏ B ∈ S, Y (d B.out))

/-- At every order, each collision block contributes either its linear coefficient
and one algebra element, or its constant coefficient. No centering, normalization,
positivity, or independence is required. Empty index types and order zero are included. -/
theorem quadratic_moment_eq_partition_expansion {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (hquad : ∀ d, Y d ^ 2 = a • Y d + b • (1 : A))
    (f : Fin k → ι → ℝ) :
    quadraticFamilyMoment ℓ Y f =
      ∑ σ ∈ tupleKernelPatterns k ι, ∑ S : Finset (Quotient σ),
        ((∏ B ∈ S, (quadraticPowerCoeffs a b (mult (Quotient.mk σ) B)).1) *
         (∏ B ∈ Sᶜ, (quadraticPowerCoeffs a b (mult (Quotient.mk σ) B)).2)) *
        kernelDistinctMoment ℓ Y f σ S := by
  rw [quadraticFamilyMoment_eq_tuple_sum, sum_eq_tupleKernel_sums]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [kernelDistinctMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [tuple_quadratic_reduction σ d (Finset.mem_filter.mp hd).2 ℓ Y a b hquad,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  ring

theorem quotient_mult_pos {k : ℕ} (σ : Setoid (Fin k)) (B : Quotient σ) :
    1 ≤ mult (Quotient.mk σ) B := by
  apply Finset.card_pos.mpr
  exact ⟨B.out, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Quotient.out_eq B⟩⟩

/-- The positive block multiplicities account for every original label once. -/
theorem sum_quotient_multiplicities {k : ℕ} (σ : Setoid (Fin k)) :
    (∑ B : Quotient σ, mult (Quotient.mk σ) B) = k := by
  simpa only [mult, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin k)))
      (t := (Finset.univ : Finset (Quotient σ))) (f := Quotient.mk σ)
      (fun _ _ => Finset.mem_univ _)).symm

private theorem sum_quotient_mult_sub_one {k : ℕ} (σ : Setoid (Fin k)) :
    (∑ B : Quotient σ, (mult (Quotient.mk σ) B - 1)) =
      k - Fintype.card (Quotient σ) := by
  rw [Finset.sum_tsub_distrib _ (fun B _ => quotient_mult_pos σ B)]
  simp [sum_quotient_multiplicities σ]

theorem partition_coefficient_bound {k : ℕ} (σ : Setoid (Fin k))
    (S : Finset (Quotient σ)) (a b C L : ℝ) (hC : 1 ≤ C) (hL : 1 ≤ L)
    (ha : |a| ≤ C * L) (hb : |b| ≤ C * L) :
    |(∏ B ∈ S, (quadraticPowerCoeffs a b (mult (Quotient.mk σ) B)).1) *
      (∏ B ∈ Sᶜ, (quadraticPowerCoeffs a b (mult (Quotient.mk σ) B)).2)| ≤
        ((C + 1) * L) ^ (k - Fintype.card (Quotient σ)) := by
  let M := (C + 1) * L
  have hM : 0 ≤ M := mul_nonneg (by linarith) (by linarith)
  rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
  calc
    _ ≤ (∏ B ∈ S, M ^ (mult (Quotient.mk σ) B - 1)) *
        (∏ B ∈ Sᶜ, M ^ (mult (Quotient.mk σ) B - 1)) := by
      apply mul_le_mul
      · exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun B _ =>
          (quadraticPowerCoeffs_bound a b C L hC hL ha hb _ (quotient_mult_pos σ B)).1)
      · exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun B _ =>
          (quadraticPowerCoeffs_bound a b C L hC hL ha hb _ (quotient_mult_pos σ B)).2)
      · exact Finset.prod_nonneg (fun _ _ => abs_nonneg _)
      · exact Finset.prod_nonneg (fun _ _ => pow_nonneg hM _)
    _ = ∏ B : Quotient σ, M ^ (mult (Quotient.mk σ) B - 1) := by
      rw [mul_comm, Finset.prod_compl_mul_prod]
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, sum_quotient_mult_sub_one]

/-- Ordered collision tests with at least one unretained endpoint.
Using both orientations changes only the finite expansion, not its indicator. -/
def collisionEdges {B : Type*} [Fintype B] [DecidableEq B] (S : Finset B) : Finset (B × B) :=
  Finset.univ.filter fun e => e.1 ≠ e.2 ∧ (e.1 ∉ S ∨ e.2 ∉ S)

private theorem injective_indicator_edge_expansion {B : Type*} [Fintype B] [DecidableEq B]
    (S : Finset B) (φ : B → ι) :
    (if Function.Injective φ then (1 : ℝ) else 0) =
      (if Set.InjOn φ (S : Set B) then (1 : ℝ) else 0) *
        ∑ G ∈ (collisionEdges S).powerset,
          (-1 : ℝ) ^ G.card * (if ∀ e ∈ G, φ e.1 = φ e.2 then 1 else 0) := by
  have hexpand :
      (∏ e ∈ collisionEdges S, (1 - if φ e.1 = φ e.2 then (1 : ℝ) else 0)) =
        ∑ G ∈ (collisionEdges S).powerset,
          (-1 : ℝ) ^ G.card * (if ∀ e ∈ G, φ e.1 = φ e.2 then 1 else 0) := by
    rw [Finset.prod_sub]
    simp only [Finset.prod_const_one, mul_one]
    apply Finset.sum_congr rfl
    intro G hG
    rw [Finset.prod_boole]
    split_ifs <;> rfl
  rw [← hexpand]
  by_cases hφ : Function.Injective φ
  · simp only [hφ, ite_true, hφ.injOn, one_mul]
    apply (Finset.prod_eq_one ?_).symm
    intro e he
    have hne := (Finset.mem_filter.mp he).2.1
    simp [show φ e.1 ≠ φ e.2 from fun h => hne (hφ h)]
  · simp only [hφ, ite_false]
    by_cases hS : Set.InjOn φ (S : Set B)
    · simp only [hS, ite_true, one_mul]
      obtain ⟨x, y, hxy, hne⟩ : ∃ x y, φ x = φ y ∧ x ≠ y := by
        by_contra hn
        apply hφ
        intro x y hxy
        by_contra hne
        exact hn ⟨x, y, hxy, hne⟩
      have he : (x,y) ∈ collisionEdges S := by
        simp only [collisionEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hne, ?_⟩
        by_cases hx : x ∈ S
        · exact Or.inr (fun hy => hne (hS hx hy hxy))
        · exact Or.inl hx
      exact (Finset.prod_eq_zero he (by simp [hxy])).symm
    · simp [hS]

private theorem sum_injective_eq_edge_expansion {B : Type*} [Fintype B] [DecidableEq B]
    (S : Finset B) (F : (B → ι) → ℝ) :
    (∑ φ : B → ι with Function.Injective φ, F φ) =
      ∑ G ∈ (collisionEdges S).powerset, (-1 : ℝ) ^ G.card *
        ∑ φ : B → ι with Set.InjOn φ (S : Set B) ∧
          (∀ e ∈ G, φ e.1 = φ e.2), F φ := by
  simp only [Finset.sum_filter]
  have hpoint (φ : B → ι) :
      (if Function.Injective φ then F φ else 0) =
        (if Function.Injective φ then (1 : ℝ) else 0) * F φ := by
    split <;> simp_all
  simp_rw [hpoint, injective_indicator_edge_expansion S]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro φ hφ
  by_cases hS : Set.InjOn φ (S : Set B) <;>
    by_cases hG : ∀ e ∈ G, φ e.1 = φ e.2 <;> simp [hS, hG, mul_assoc, mul_comm]

theorem kernelDistinctMoment_eq_block_assignments {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (σ : Setoid (Fin k)) (S : Finset (Quotient σ)) :
    kernelDistinctMoment ℓ Y f σ S =
      ∑ φ : Quotient σ → ι with Function.Injective φ,
        (∏ i, f i (φ (Quotient.mk σ i))) * ℓ (∏ B ∈ S, Y (φ B)) := by
  symm
  apply Finset.sum_bij (fun φ _ => φ ∘ Quotient.mk σ)
  · intro φ hφ
    have hinj := (Finset.mem_filter.mp hφ).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext i j
    exact ⟨fun h => Quotient.exact (hinj h), fun h => congrArg φ (Quotient.sound h)⟩
  · intro φ hφ ψ hψ h
    funext B
    have hh := congrFun h B.out
    simpa only [Function.comp_apply, Quotient.out_eq] using hh
  · intro d hd
    have hd' := (Finset.mem_filter.mp hd).2
    have hker (i j : Fin k) : (Setoid.ker d) i j ↔ σ i j := by rw [hd']
    refine ⟨fun B => d B.out, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro B C h
      have hrel : σ B.out C.out := (hker _ _).mp h
      simpa only [Quotient.out_eq] using (Quotient.sound hrel :
        Quotient.mk σ B.out = Quotient.mk σ C.out)
    · funext i
      change d (Quotient.mk σ i).out = d i
      have hrel := Quotient.exact (Quotient.out_eq (Quotient.mk σ i))
      exact (hker _ _).mpr hrel
  · intro φ hφ
    simp only [Function.comp_apply, Quotient.out_eq]

/-- Removing only collisions involving unretained blocks gives an exact finite
edge-subset expansion. The retained distinct-index sum stays signed. -/
theorem kernelDistinctMoment_eq_edge_expansion {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (σ : Setoid (Fin k)) (S : Finset (Quotient σ)) :
    kernelDistinctMoment ℓ Y f σ S =
      ∑ G ∈ (collisionEdges S).powerset, (-1 : ℝ) ^ G.card *
        ∑ φ : Quotient σ → ι with Set.InjOn φ (S : Set (Quotient σ)) ∧
          (∀ e ∈ G, φ e.1 = φ e.2),
          (∏ i, f i (φ (Quotient.mk σ i))) * ℓ (∏ B ∈ S, Y (φ B)) := by
  rw [kernelDistinctMoment_eq_block_assignments]
  exact sum_injective_eq_edge_expansion (B := Quotient σ) S
    (fun φ => (∏ i, f i (φ (Quotient.mk σ i))) * ℓ (∏ B ∈ S, Y (φ B)))

/-- Connected collision components, expressed as the equivalence closure of the edges. -/
def collisionComponents {B : Type*} (G : Finset (B × B)) : Setoid B :=
  Relation.EqvGen.setoid (fun x y => (x, y) ∈ G)

private theorem collisionComponents_le_ker_iff {B : Type*} (G : Finset (B × B))
    (φ : B → ι) :
    collisionComponents G ≤ Setoid.ker φ ↔ ∀ e ∈ G, φ e.1 = φ e.2 := by
  constructor
  · intro h e he
    exact h (Relation.EqvGen.rel _ _ he)
  · intro h
    exact Setoid.eqvGen_le (fun x y hxy => h (x, y) hxy)

private theorem positional_weight_eq_block_weight {k : ℕ}
    (σ : Setoid (Fin k)) (f : Fin k → ι → ℝ) (φ : Quotient σ → ι) :
    (∏ i, f i (φ (Quotient.mk σ i))) =
      ∏ B : Quotient σ, collisionComponentWeight σ f B (φ B) := by
  symm
  unfold collisionComponentWeight
  calc
    _ = ∏ B : Quotient σ, ∏ i : Fin k with Quotient.mk σ i = B,
        f i (φ (Quotient.mk σ i)) := by
      apply Finset.prod_congr rfl
      intro B hB
      apply Finset.prod_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.prod_fiberwise Finset.univ (Quotient.mk σ) _

private theorem collision_free_card_le {B : Type*} [Fintype B] [DecidableEq B]
    (S : Finset B) (G : Finset (B × B))
    (hS : Set.InjOn (Quotient.mk (collisionComponents G)) S) :
    (S.image (Quotient.mk (collisionComponents G)))ᶜ.card ≤ Sᶜ.card := by
  rw [Finset.card_compl, Finset.card_compl, Finset.card_image_iff.mpr hS]
  exact Nat.sub_le_sub_right (Fintype.card_quotient_le _) _

private theorem collision_free_card_lt {B : Type*} [Fintype B] [DecidableEq B]
    (S : Finset B) (G : Finset (B × B)) (hGE : G ⊆ collisionEdges S)
    (hG : G.Nonempty) (hS : Set.InjOn (Quotient.mk (collisionComponents G)) S) :
    (S.image (Quotient.mk (collisionComponents G)))ᶜ.card < Sᶜ.card := by
  have hstrict : Fintype.card (Quotient (collisionComponents G)) < Fintype.card B := by
    apply Fintype.card_lt_of_surjective_not_injective (Quotient.mk (collisionComponents G))
      Quotient.mk_surjective
    intro hinj
    obtain ⟨e, he⟩ := hG
    have hne := (Finset.mem_filter.mp (hGE he)).2.1
    exact hne (hinj (Quotient.sound (Relation.EqvGen.rel _ _ he)))
  rw [Finset.card_compl, Finset.card_compl, Finset.card_image_iff.mpr hS]
  have hsle : S.card ≤ Fintype.card (Quotient (collisionComponents G)) := by
    rw [← Finset.card_image_iff.mpr hS]
    exact Finset.card_le_univ _
  omega

private theorem collision_edge_subsum_abs_le {B : Type*} [Fintype B] [DecidableEq B]
    (S : Finset B) (E : Finset (Finset (B × B)))
    (hE : E ⊆ (collisionEdges S).powerset)
    (F : Finset (B × B) → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ G ∈ E, |F G| ≤ M) :
    |∑ G ∈ E, (-1 : ℝ) ^ G.card * F G| ≤
      (2 : ℝ) ^ (Fintype.card B * Fintype.card B) * M := by
  have hcard : E.card ≤ 2 ^ (Fintype.card B * Fintype.card B) := by
    calc
      E.card ≤ (collisionEdges S).powerset.card := Finset.card_le_card hE
      _ = 2 ^ (collisionEdges S).card := Finset.card_powerset _
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by omega)
        simpa only [Fintype.card_prod] using Finset.card_le_univ (collisionEdges S)
  calc
    _ ≤ ∑ G ∈ E, |(-1 : ℝ) ^ G.card * F G| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _G ∈ E, M := by
      apply Finset.sum_le_sum
      intro G hG
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hF G hG
    _ = (E.card : ℝ) * M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM

/-- A retained-injective assignment subject to a finite set of collision equalities. -/
def collisionAssignmentMoment {B : Type*} [Fintype B] [DecidableEq B]
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (w : B → ι → ℝ)
    (S : Finset B) (G : Finset (B × B)) : ℝ :=
  ∑ φ : B → ι with Set.InjOn φ S ∧ (∀ e ∈ G, φ e.1 = φ e.2),
    (∏ B, w B (φ B)) * ℓ (∏ B ∈ S, Y (φ B))

private theorem collisionAssignmentMoment_eq_quotient_sum {B : Type*} [Fintype B] [DecidableEq B]
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (w : B → ι → ℝ)
    (S : Finset B) (G : Finset (B × B)) :
    collisionAssignmentMoment ℓ Y w S G =
      ∑ φ : B → ι with collisionComponents G ≤ Setoid.ker φ ∧ Set.InjOn φ S,
        (∏ B, w B (φ B)) * ℓ (∏ B ∈ S, Y (φ B)) := by
  unfold collisionAssignmentMoment
  apply Finset.sum_congr
  · ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      collisionComponents_le_ker_iff, and_comm]
  · intro φ hφ
    rfl

theorem kernelDistinctMoment_eq_collision_assignment_sum {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (σ : Setoid (Fin k)) (S : Finset (Quotient σ)) :
    kernelDistinctMoment ℓ Y f σ S =
      ∑ G ∈ (collisionEdges S).powerset, (-1 : ℝ) ^ G.card *
        collisionAssignmentMoment ℓ Y (collisionComponentWeight σ f) S G := by
  rw [kernelDistinctMoment_eq_edge_expansion]
  apply Finset.sum_congr rfl
  intro G hG
  congr 1
  apply Finset.sum_congr rfl
  intro φ hφ
  rw [positional_weight_eq_block_weight]

theorem collisionAssignmentMoment_empty {B : Type*} [Fintype B] [DecidableEq B]
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (w : B → ι → ℝ) (S : Finset B) :
    collisionAssignmentMoment ℓ Y w S ∅ =
      (∏ B ∈ Sᶜ, ∑ d, w B d) * distinctIndexMoment ℓ Y
        (fun i : Fin (Fintype.card S) => w ((Fintype.equivFin S).symm i)) := by
  rw [← component_assignment_factorization ℓ Y S w]
  unfold collisionAssignmentMoment
  apply Finset.sum_congr
  · ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, _⟩ b c hbc
      exact Subtype.ext (h b.property c.property hbc)
    · intro h
      constructor
      · intro b hb c hc hbc
        exact congrArg Subtype.val (h (a₁ := ⟨b, hb⟩) (a₂ := ⟨c, hc⟩) hbc)
      · simp
  · intro φ hφ
    rfl

/-- The collision-removal bounds preserve the signed retained moment. The first
bound uses at most q free components, and each nonempty edge set saves one. -/
theorem kernelDistinctMoment_collision_estimates {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (σ : Setoid (Fin k)) (S : Finset (Quotient σ))
    (C H s : ℝ) (hC : 1 ≤ C) (hH : 1 ≤ H) (hs : 0 ≤ s)
    (hunit : ℓ 1 = 1) (hcenter : ∀ d, ℓ (Y d) = 0)
    (hD : (Fintype.card ι : ℝ) ≤ C * H) (hf : ∀ i d, |f i d| ≤ 1)
    (hR : DisjointLabelMomentBound ℓ Y f C s) (hrk : S.card < k) :
    |kernelDistinctMoment ℓ Y f σ S| ≤
      (2 : ℝ) ^ (Fintype.card (Quotient σ) * Fintype.card (Quotient σ)) *
        C ^ (Sᶜ.card + 1) * H ^ Sᶜ.card * s ^ S.card ∧
    (1 ≤ Sᶜ.card →
      |kernelDistinctMoment ℓ Y f σ S -
        (∏ B ∈ Sᶜ, ∑ d, collisionComponentWeight σ f B d) *
          distinctIndexMoment ℓ Y (fun i : Fin (Fintype.card S) =>
            collisionComponentWeight σ f ((Fintype.equivFin S).symm i))| ≤
        (2 : ℝ) ^ (Fintype.card (Quotient σ) * Fintype.card (Quotient σ)) *
          C ^ Sᶜ.card * H ^ (Sᶜ.card - 1) * s ^ S.card) := by
  let J := collisionAssignmentMoment ℓ Y (collisionComponentWeight σ f) S
  have hJG (G : Finset (Quotient σ × Quotient σ)) (q : ℕ)
      (hq : Set.InjOn (Quotient.mk (collisionComponents G)) S →
        (S.image (Quotient.mk (collisionComponents G)))ᶜ.card ≤ q) :
      |J G| ≤ C ^ (q + 1) * H ^ q * s ^ S.card := by
    dsimp only [J]
    rw [collisionAssignmentMoment_eq_quotient_sum]
    by_cases hS : Set.InjOn (Quotient.mk (collisionComponents G)) S
    · exact quotient_merged_assignment_abs_le ℓ Y f σ (collisionComponents G) S
        C H s q hC hH hs hunit hcenter hD hf hR hrk (hq hS)
    · rw [quotient_assignment_zero_of_retained_collision ℓ Y (collisionComponents G) S
        (collisionComponentWeight σ f) hS, abs_zero]
      positivity
  have hJE : kernelDistinctMoment ℓ Y f σ S =
      ∑ G ∈ (collisionEdges S).powerset, (-1 : ℝ) ^ G.card * J G :=
    kernelDistinctMoment_eq_collision_assignment_sum ℓ Y f σ S
  constructor
  · rw [hJE]
    have hb := collision_edge_subsum_abs_le S (collisionEdges S).powerset
      (fun _ h => h) J (C ^ (Sᶜ.card + 1) * H ^ Sᶜ.card * s ^ S.card)
      (by positivity) (fun G hG => hJG G Sᶜ.card (collision_free_card_le S G))
    simpa only [mul_assoc] using hb
  · intro hq
    have hmem : (∅ : Finset (Quotient σ × Quotient σ)) ∈ (collisionEdges S).powerset :=
      Finset.empty_mem_powerset _
    have herr : kernelDistinctMoment ℓ Y f σ S - J ∅ =
        ∑ G ∈ (collisionEdges S).powerset.erase ∅, (-1 : ℝ) ^ G.card * J G := by
      rw [hJE, ← Finset.sum_erase_add _ _ hmem]
      simp
    rw [← collisionAssignmentMoment_empty ℓ Y (collisionComponentWeight σ f) S]
    change |kernelDistinctMoment ℓ Y f σ S - J ∅| ≤ _
    rw [herr]
    have hb := collision_edge_subsum_abs_le S ((collisionEdges S).powerset.erase ∅)
      (Finset.erase_subset _ _) J (C ^ Sᶜ.card * H ^ (Sᶜ.card - 1) * s ^ S.card)
      (by positivity) ?_
    · simpa only [mul_assoc] using hb
    · intro G hG
      have hG' := Finset.mem_erase.mp hG
      have hlt := collision_free_card_lt S G
        (Finset.mem_powerset.mp hG'.2) (Finset.nonempty_iff_ne_empty.mpr hG'.1)
      have hm := hJG G (Sᶜ.card - 1) (fun hS => by have := hlt hS; omega)
      simpa only [Nat.sub_add_cancel hq] using hm

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
