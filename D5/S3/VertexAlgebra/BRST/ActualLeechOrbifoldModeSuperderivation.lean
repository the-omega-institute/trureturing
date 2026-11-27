/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldModeSuperderivation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldModeSuperderivation
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Fixed-first zero-mode commutator and the original BRST superderivation. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBorcherds

/-!
# The BRST zero-mode commutator on the native Leech tensor field

The two finite portions of the commutator account for the nonnegative and negative
indices of the inner tensor mode. The fixed first Leech input supplies the four
orbifold Borcherds identities used by both terms of the BRST current.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open StateField.BorcherdsPermutations
open StateFieldResidueReconstruction (integerBinomial epsilon)

section FiniteShuffle

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- The coefficient Borcherds law on one ordered triple with a prescribed sign. -/
private def SignedLaw (μ : Modes A) (e : ℂ) (a w c : A) : Prop :=
  ∀ p q r : ℤ, iterate μ a w c p q r =
    ∑ᶠ t : ℕ, (((-1 : ℂ)^t) * integerBinomial r t) •
      (μ (p + r - t) a (μ (q + t) w c) -
        (epsilon r * e) • μ (q + r - t) w (μ (p + t) a c))

private theorem zero_binomial_sum (f : ℕ → A) :
    (∑ᶠ t : ℕ, integerBinomial 0 t • f t) = f 0 := by
  rw [finsum_eq_single _ 0]
  · simp [integerBinomial]
  · intro t ht
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero ht)]

private theorem commutator_of_law {μ : Modes A} {e : ℂ} {a w c : A}
    (h : SignedLaw μ e a w c) (i r : ℤ) :
    μ i a (μ r w c) - e • μ r w (μ i a c) =
      ∑ᶠ k : ℕ, integerBinomial i k • μ (i + r - k) (μ k a w) c := by
  -- The factor (-1)^t is immaterial in the sole surviving summand.
  have collapse (f : ℕ → A) :
      (∑ᶠ t : ℕ, ((-1 : ℂ)^t * integerBinomial 0 t) • f t) = f 0 := by
    rw [finsum_eq_single _ 0]
    · simp [integerBinomial]
    · intro t ht
      simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero ht)]
  -- Use the unexpanded law so the coefficient is in the form used by collapse.
  have law := h i r 0
  rw [collapse] at law
  simpa only [iterate, add_zero, zero_add, Nat.cast_zero, sub_zero, epsilon, zpow_zero, one_mul]
    using law.symm

omit [Module ℂ A] in
private theorem finite_interval {f : ℤ → A} (lo hi : ℤ)
    (h : ∀ i, i < lo ∨ hi < i → f i = 0) : Function.HasFiniteSupport f := by
  apply (Finset.Icc lo hi).finite_toSet.subset
  intro i hi'
  by_contra hn
  apply hi'
  apply h
  simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using hn

private theorem finite_offset {μ : Modes A} (h : LowerTruncated μ) (a w : A) (r : ℤ) :
    Function.HasFiniteSupport (fun t : ℕ => μ (r + t) a w) := by
  obtain ⟨N, hN⟩ := h a w
  apply (Finset.range (N - r).toNat).finite_toSet.subset
  intro t ht
  apply Finset.mem_range.mpr
  by_contra hn
  exact ht (hN _ (by omega))

private theorem finite_rows {I J W : Type*} [Zero W] {f : I × J → W}
    {s : Set I} (hs : s.Finite) (rows : ∀ i, Function.HasFiniteSupport (fun j => f (i, j)))
    (outside : ∀ i ∉ s, ∀ j, f (i, j) = 0) : Function.HasFiniteSupport f := by
  classical
  apply (hs.biUnion (fun i _ => (rows i).image (fun j => (i,j)))).subset
  rintro ⟨i,j⟩ hij
  apply Set.mem_iUnion₂.mpr
  refine ⟨i, ?_, ⟨j, hij, rfl⟩⟩
  by_contra hn
  exact hij (outside i hn j)

private theorem finite_fiber {I J W : Type*} [Zero W] {f : I × J → W}
    (h : Function.HasFiniteSupport f) (i : I) :
    Function.HasFiniteSupport (fun j => f (i,j)) := by
  exact Set.Finite.preimage (fun j _ k _ eq => congrArg Prod.snd eq) h

private theorem finite_row_sums {I J W : Type*} [AddCommMonoid W] {f : I × J → W}
    (h : Function.HasFiniteSupport f) : Function.HasFiniteSupport (fun i => ∑ᶠ j, f (i,j)) := by
  apply (h.image Prod.fst).subset
  intro i hi
  by_contra hn
  apply hi
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  by_contra hj
  exact hn ⟨(i,j), hj, rfl⟩

private theorem finite_reindex {I J W : Type*} [Zero W] {f : J → W}
    (h : Function.HasFiniteSupport f) (e : I ≃ J) :
    Function.HasFiniteSupport (fun i => f (e i)) :=
  Set.Finite.preimage e.injective.injOn h

private theorem finite_convolution (f : ℤ → A) (g : ℤ → B) (d M N : ℤ)
    (hf : ∀ i ≥ M, f i = 0) (hg : ∀ j ≥ N, g j = 0) :
    Function.HasFiniteSupport (fun i => f i ⊗ₜ[ℂ] g (d - i)) := by
  refine finite_interval (d - N + 1) (M - 1) ?_
  intro i hi
  rcases hi with hi | hi
  · rw [hg _ (by omega), TensorProduct.tmul_zero]
  · rw [hf _ (by omega), TensorProduct.zero_tmul]

private theorem choose_nat (m k : ℕ) :
    integerBinomial (m : ℤ) k = (m.choose k : ℂ) := by
  rw [show integerBinomial (m : ℤ) k = Ring.choose ((m : ℤ) : ℂ) k from
    Ring.map_choose (Int.castRingHom ℂ) (m : ℤ) k, Int.cast_natCast, Ring.choose_natCast]

private theorem choose_neg (t k : ℕ) :
    integerBinomial (-(t : ℤ) - 1) k = (-1 : ℂ)^k * ((t+k).choose k : ℂ) := by
  rw [show integerBinomial (-(t : ℤ) - 1) k =
    Ring.choose ((-(t : ℤ) - 1 : ℤ) : ℂ) k from
      Ring.map_choose (Int.castRingHom ℂ) _ _, Int.cast_sub, Int.cast_neg,
      Int.cast_natCast, Int.cast_one,
      show -(t : ℂ) - 1 = -((t : ℂ) + 1) by ring, ← Nat.cast_succ, Ring.choose_neg]
  have arg : ((t + 1 : ℕ) : ℂ) + k - 1 = ((t+k : ℕ) : ℂ) := by push_cast; ring
  rw [arg, Ring.choose_natCast]
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_negOnePow_natCast, smul_eq_mul]

private theorem choose_iterate (k t : ℕ) :
    (-1 : ℂ)^t * integerBinomial (-(k : ℤ) - 1) t = ((k+t).choose t : ℂ) := by
  rw [choose_neg, ← mul_assoc, ← mul_pow]
  norm_num

private theorem epsilon_neg_succ (k : ℕ) :
    epsilon (-(k : ℤ) - 1) = -((-1 : ℂ)^k) := by
  rw [epsilon, show -(k : ℤ) - 1 = -((k : ℤ) + 1) by omega, zpow_neg,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast, zpow_one,
    mul_neg_one, inv_neg, ← inv_pow]
  norm_num

private def crossed (ν : Modes B) (e : ℂ) (b x y : B) (i s : ℤ) : B :=
  if 0 ≤ i then ν (-1-i) b (ν s x y)
  else e • ν s x (ν (-1-i) b y)

private theorem crossed_finite {ν : Modes B} (trunc : LowerTruncated ν)
    (e : ℂ) (b x y : B) (k : ℕ) (q : ℤ) :
    Function.HasFiniteSupport (fun i : ℤ =>
      integerBinomial i k • crossed ν e b x y i (q+i-k)) := by
  obtain ⟨X, hX⟩ := trunc x y
  obtain ⟨Y, hY⟩ := trunc b y
  refine finite_interval (min 0 (-Y)) (max (-1) (X - q + k - 1)) ?_
  intro i hi
  by_cases ip : 0 ≤ i
  · have tail : X ≤ q + i - k := by omega
    simp [crossed, ip, hX _ tail]
  · have tail : Y ≤ -1-i := by omega
    simp [crossed, ip, hY _ tail]

omit [Module ℂ B] in
private theorem finsum_two_ranges {f : ℤ → B} (hf : Function.HasFiniteSupport f)
    {pos neg : ℕ → ℤ} (hp : Function.Injective pos) (hn : Function.Injective neg)
    (disj : Disjoint (Set.range pos) (Set.range neg))
    (outside : Function.support f ⊆ Set.range pos ∪ Set.range neg) :
    (∑ᶠ i : ℤ, f i) = (∑ᶠ t : ℕ, f (pos t)) + ∑ᶠ t : ℕ, f (neg t) := by
  classical
  calc
    _ = ∑ᶠ i ∈ Set.range pos ∪ Set.range neg, f i := by
      have hfilter : ∀ i, (Set.range pos ∪ Set.range neg).indicator f i = f i := by
        intro i
        by_cases hi : i ∈ Set.range pos ∪ Set.range neg
        · simp [hi]
        · have hz : f i = 0 := by
            by_contra h
            exact hi (outside h)
          simp [hi, hz]
      simp only [finsum_mem_def, hfilter]
    _ = (∑ᶠ t : ℕ, f (pos t)) + ∑ᶠ t : ℕ, f (neg t) := by
      rw [finsum_mem_union' disj (hf.inter_of_right _) (hf.inter_of_right _),
        finsum_mem_range hp, finsum_mem_range hn]

private theorem crossed_iterate {ν : Modes B} {e : ℂ} {b x y : B}
    (trunc : LowerTruncated ν) (law : SignedLaw ν e b x y) (k : ℕ) (q : ℤ) :
    (∑ᶠ i : ℤ, integerBinomial i k • crossed ν e b x y i (q+i-k)) =
      ν q (ν (-1-k) b x) y := by
  classical
  let f : ℤ → B := fun i => integerBinomial i k • crossed ν e b x y i (q+i-k)
  let pos : ℕ → ℤ := fun t => (k : ℤ) + t
  let neg : ℕ → ℤ := fun t => -1 - (t : ℤ)
  have hp : Function.Injective pos := by intro a b h; dsimp [pos] at h; omega
  have hn : Function.Injective neg := by intro a b h; dsimp [neg] at h; omega
  have outside : Function.support f ⊆ Set.range pos ∪ Set.range neg := by
    intro i hi
    by_cases hneg : i < 0
    · exact Or.inr ⟨(-1-i).toNat, by dsimp [neg]; omega⟩
    by_cases hpos : (k : ℤ) ≤ i
    · exact Or.inl ⟨(i-k).toNat, by dsimp [pos]; omega⟩
    exfalso
    apply hi
    have hz : integerBinomial i k = 0 := calc
      _ = integerBinomial (i.toNat : ℤ) k := congrArg (fun j => integerBinomial j k) (by omega)
      _ = 0 := by rw [choose_nat, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    simp [f, hz]
  have hf : Function.HasFiniteSupport f := crossed_finite trunc e b x y k q
  have disj : Disjoint (Set.range pos) (Set.range neg) := by
    refine Set.disjoint_left.mpr ?_
    rintro i ⟨t, ht⟩ ⟨u, hu⟩
    dsimp [pos] at ht
    dsimp [neg] at hu
    omega
  change (∑ᶠ i, f i) = _
  rw [finsum_two_ranges hf hp hn disj outside]
  let F : ℕ → B := fun t => f (pos t)
  let R : ℕ → B := fun t => f (neg t)
  have hF : Function.HasFiniteSupport F := Set.Finite.preimage hp.injOn hf
  have hR : Function.HasFiniteSupport R := Set.Finite.preimage hn.injOn hf
  change (∑ᶠ t, F t) + (∑ᶠ t, R t) = _
  have single : iterate ν b x y 0 q (-(k : ℤ)-1) = ν q (ν (-1-k) b x) y := by
    simpa only [iterate, zero_add, add_zero, Nat.cast_zero, sub_zero,
      show -(k : ℤ)-1 = -1-k by omega] using
      zero_binomial_sum (fun t : ℕ => ν (q-t) (ν (-(k : ℤ)-1+t) b x) y)
  rw [← finsum_add_distrib hF hR, ← single, law]
  apply finsum_congr
  intro t
  have ht : 0 ≤ (k : ℤ) + t := by omega
  have hl : ¬ 0 ≤ -1 - (t : ℤ) := by omega
  have positiveChoose : integerBinomial ((k : ℤ) + t) k = ((k+t).choose t : ℂ) := by
    rw [← Nat.cast_add, choose_nat, Nat.choose_symm_add (a := k) (b := t)]
  have negativeChoose : integerBinomial (-1 - (t : ℤ)) k =
      (-1 : ℂ)^k * ((k+t).choose t : ℂ) := by
    rw [show -1 - (t : ℤ) = -(t : ℤ) - 1 by omega, choose_neg, Nat.add_comm t k,
      Nat.choose_symm_add (a := k) (b := t)]
  change f (pos t) + f (neg t) = _
  simp only [f, pos, neg, crossed, ite_eq_left ht, ite_eq_right hl, zero_add, positiveChoose,
    negativeChoose, choose_iterate, epsilon_neg_succ,
    show q + ((k : ℤ) + t) - k = q + t by omega,
    show -1 - (-1 - (t : ℤ)) = t by omega,
    show q + (-1 - (t : ℤ)) - k = q + (-(k : ℤ)-1) - t by omega,
    show -1 - ((k : ℤ) + t) = -(k : ℤ)-1-t by omega]
  module


private def commutator (μ : Modes A) (e : ℂ) (a w c : A) (i r : ℤ) : A :=
  μ i a (μ r w c) - e • μ r w (μ i a c)

private def firstPiece (μ : Modes A) (ν : Modes B) (e f : ℂ)
    (a w c : A) (b x y : B) (n : ℤ) (ir : ℤ × ℤ) : A ⊗[ℂ] B :=
  commutator μ e a w c ir.1 ir.2 ⊗ₜ[ℂ] crossed ν f b x y ir.1 (n-1-ir.2)

private def weightedPiece (μ : Modes A) (ν : Modes B) (e : ℂ)
    (a w c : A) (b x y : B) (n : ℤ) (kip : ℕ × ℤ × ℤ) : A ⊗[ℂ] B :=
  let (k,i,p) := kip
  integerBinomial i k •
    (μ p (μ k a w) c ⊗ₜ[ℂ] crossed ν e b x y i (n-1-p+i-k))

private theorem weighted_finite {μ : Modes A} {ν : Modes B}
    (hμ : LowerTruncated μ) (hν : LowerTruncated ν) (e : ℂ)
    (a w c : A) (b x y : B) (n : ℤ) :
    Function.HasFiniteSupport (weightedPiece μ ν e a w c b x y n) := by
  obtain ⟨X, hX⟩ := hν x y
  obtain ⟨Y, hY⟩ := hν b y
  apply finite_rows (finite_offset hμ a w 0)
  · intro k
    obtain ⟨P, hP⟩ := hμ (μ k a w) c
    apply finite_rows (Finset.Icc (min 0 (-Y)) (max (-1) (X - n + P + k))).finite_toSet
    · intro i
      by_cases ip : 0 ≤ i
      · refine finite_interval (n-1+i-k-X+1) (P-1) ?_
        intro p hp
        rcases hp with hp | hp
        · have tail : X ≤ n-1-p+i-k := by omega
          simp [weightedPiece, crossed, ip, hX _ tail]
        · simp [weightedPiece, hP _ (by omega : P ≤ p)]
      · obtain ⟨G, hG⟩ := hν x (ν (-1-i) b y)
        refine finite_interval (n-1+i-k-G+1) (P-1) ?_
        intro p hp
        rcases hp with hp | hp
        · have tail : G ≤ n-1-p+i-k := by omega
          simp [weightedPiece, crossed, ip, hG _ tail]
        · simp [weightedPiece, hP _ (by omega : P ≤ p)]
    · intro i hi p
      have hi' : i < min 0 (-Y) ∨ max (-1) (X-n+P+k) < i := by
        simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using hi
      by_cases hp : P ≤ p
      · simp [weightedPiece, hP _ hp]
      by_cases ip : 0 ≤ i
      · have tail : X ≤ n-1-p+i-k := by omega
        simp [weightedPiece, crossed, ip, hX _ tail]
      · have tail : Y ≤ -1-i := by omega
        simp [weightedPiece, crossed, ip, hY _ tail]
  · rintro k hk ⟨i,p⟩
    have hz : μ k a w = 0 := by
      simpa only [Function.mem_support, not_not, zero_add] using hk
    simp [weightedPiece, hz]

private def shuffleIndices : ((ℤ × ℤ) × ℕ) ≃ (ℕ × ℤ × ℤ) where
  toFun v := (v.2, v.1.1, v.1.1 + v.1.2 - v.2)
  invFun v := ((v.2.1, v.2.2 + v.1 - v.2.1), v.1)
  left_inv := by
    rintro ⟨⟨i,r⟩,k⟩
    change ((i, (i+r-k)+k-i), k) = ((i,r),k)
    rw [show (i+r-k)+k-i = r by omega]
  right_inv := by
    rintro ⟨k,i,p⟩
    change (k, i, i+(p+k-i)-k) = (k,i,p)
    rw [show i+(p+k-i)-k = p by omega]

/-- One commutator contribution, including the finite support of the crossed terms. -/
private theorem first_piece_sum {μ : Modes A} {ν : Modes B}
    (hμ : LowerTruncated μ) (hν : LowerTruncated ν)
    {e f : ℂ} {a w c : A} {b x y : B}
    (lawA : SignedLaw μ e a w c) (lawB : SignedLaw ν f b x y) (n : ℤ) :
    Function.HasFiniteSupport (firstPiece μ ν e f a w c b x y n) ∧
      (∑ᶠ ir, firstPiece μ ν e f a w c b x y n ir) =
        ∑ᶠ k : ℕ, ∑ᶠ p : ℤ, μ p (μ k a w) c ⊗ₜ[ℂ] ν (n-1-p) (ν (-1-k) b x) y := by
  let F := weightedPiece μ ν f a w c b x y n
  let G : (ℤ × ℤ) × ℕ → A ⊗[ℂ] B := fun v => F (shuffleIndices v)
  have hF : Function.HasFiniteSupport F := weighted_finite hμ hν f a w c b x y n
  have hG : Function.HasFiniteSupport G := finite_reindex hF shuffleIndices
  have expand (ir : ℤ × ℤ) : firstPiece μ ν e f a w c b x y n ir = ∑ᶠ k, G (ir,k) := by
    obtain ⟨i,r⟩ := ir
    let T : A →ₗ[ℂ] A ⊗[ℂ] B :=
      (TensorProduct.mk ℂ A B).flip (crossed ν f b x y i (n-1-r))
    change T (commutator μ e a w c i r) = _
    rw [commutator, commutator_of_law lawA]
    have hk : Function.HasFiniteSupport (fun k : ℕ =>
        integerBinomial i k • μ (i+r-k) (μ k a w) c) := by
      apply (finite_offset hμ a w 0).subset
      intro k h
      by_contra hn
      have hz : μ k a w = 0 := by
        simpa only [Function.mem_support, not_not, zero_add] using hn
      exact h (by simp [hz])
    rw [map_finsum T hk]
    apply finsum_congr
    intro k
    simp only [G, F, shuffleIndices, Equiv.coe_fn_mk, weightedPiece,
      map_smul, T, LinearMap.flip_apply, TensorProduct.mk_apply]
    rw [show n-1-(i+r-k)+i-k = n-1-r by omega]
  have hExpand : firstPiece μ ν e f a w c b x y n = fun ir => ∑ᶠ k, G (ir,k) :=
    funext expand
  refine ⟨hExpand ▸ finite_row_sums hG, ?_⟩
  calc
    _ = ∑ᶠ v, G v := by rw [finsum_curry G hG]; exact finsum_congr expand
    _ = ∑ᶠ v, F v := finsum_comp_equiv shuffleIndices (f := F)
    _ = ∑ᶠ k : ℕ, ∑ᶠ p : ℤ, ∑ᶠ i : ℤ, F (k,i,p) := by
      let swap : (ℕ × ℤ × ℤ) ≃ (ℕ × ℤ × ℤ) :=
        Equiv.prodCongr (Equiv.refl ℕ) (Equiv.prodComm ℤ ℤ)
      let H : ℕ × ℤ × ℤ → A ⊗[ℂ] B := fun v => F (swap v)
      calc
        _ = ∑ᶠ v, H v := (finsum_comp_equiv swap (f := F)).symm
        _ = _ := finsum_curry₃ H (finite_reindex hF swap)
    _ = _ := by
      apply finsum_congr
      intro k
      apply finsum_congr
      intro p
      let T : B →ₗ[ℂ] A ⊗[ℂ] B := TensorProduct.mk ℂ A B (μ p (μ k a w) c)
      let h := crossed_finite hν f b x y k (n-1-p)
      calc
        _ = T (∑ᶠ i : ℤ, integerBinomial i k •
            crossed ν f b x y i (n-1-p+i-k)) := by
          rw [map_finsum T h]
          exact finsum_congr (fun i => by simp [F, weightedPiece, T])
        _ = _ := by rw [crossed_iterate hν lawB]; rfl


private def convolution (μ : Modes A) (ν : Modes B) (a w : A) (b x : B)
    (n i : ℤ) : A ⊗[ℂ] B :=
  μ i a w ⊗ₜ[ℂ] ν (n-1-i) b x

private theorem convolution_finite {μ : Modes A} {ν : Modes B}
    (hμ : LowerTruncated μ) (hν : LowerTruncated ν) (a w : A) (b x : B) (n : ℤ) :
    Function.HasFiniteSupport (convolution μ ν a w b x n) := by
  obtain ⟨M, hM⟩ := hμ a w
  obtain ⟨N, hN⟩ := hν b x
  exact finite_convolution _ _ (n-1) M N hM hN

private def productTerm (μ : Modes A) (ν : Modes B) (a w c : A) (b x y : B)
    (m n : ℤ) (ir : ℤ × ℤ) : A ⊗[ℂ] B :=
  convolution μ ν a (μ ir.2 w c) b (ν (n-1-ir.2) x y) m ir.1

private theorem product_finite {μ : Modes A} {ν : Modes B}
    (hμ : LowerTruncated μ) (hν : LowerTruncated ν)
    (a w c : A) (b x y : B) (m n : ℤ) :
    Function.HasFiniteSupport (productTerm μ ν a w c b x y m n) := by
  obtain ⟨M, hM⟩ := hμ w c
  obtain ⟨N, hN⟩ := hν x y
  have h : Function.HasFiniteSupport
      (fun ri : ℤ × ℤ => productTerm μ ν a w c b x y m n (ri.2,ri.1)) := by
    apply finite_rows (Finset.Icc (n-N) (M-1)).finite_toSet
    · intro r
      exact convolution_finite hμ hν a (μ r w c) b (ν (n-1-r) x y) m
    · intro r hr i
      have tail : r < n-N ∨ M-1 < r := by
        simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using hr
      rcases tail with tail | tail
      · simp [productTerm, convolution, hN _ (by omega : N ≤ n-1-r)]
      · simp [productTerm, convolution, hM _ (by omega : M ≤ r)]
  exact finite_reindex h (Equiv.prodComm ℤ ℤ)

variable {μ : Modes A} {ν : Modes B} {T : Modes (A ⊗[ℂ] B)}

private theorem composed_tmul (hμ : LowerTruncated μ) (hν : LowerTruncated ν)
    (conv : ∀ n a w b x, T n (a ⊗ₜ[ℂ] b) (w ⊗ₜ[ℂ] x) =
      ∑ᶠ i, convolution μ ν a w b x n i)
    (a w c : A) (b x y : B) (m n : ℤ) :
    T m (a ⊗ₜ[ℂ] b) (T n (w ⊗ₜ[ℂ] x) (c ⊗ₜ[ℂ] y)) =
      ∑ᶠ ir, productTerm μ ν a w c b x y m n ir := by
  rw [conv n w c x y, map_finsum _ (convolution_finite hμ hν w c x y n)]
  let P := productTerm μ ν a w c b x y m n
  let e := Equiv.prodComm ℤ ℤ
  let G : ℤ × ℤ → A ⊗[ℂ] B := fun ri => P (e ri)
  calc
    _ = ∑ᶠ ri, G ri := by
      rw [finsum_curry G (finite_reindex (product_finite hμ hν a w c b x y m n) e)]
      apply finsum_congr
      intro r
      exact conv m a (μ r w c) b (ν (n-1-r) x y)
    _ = _ := finsum_comp_equiv e (f := P)

private def iterateTerm (μ : Modes A) (ν : Modes B)
    (a w c : A) (b x y : B) (n : ℤ) (kp : ℤ × ℤ) : A ⊗[ℂ] B :=
  convolution μ ν (μ kp.1 a w) c (ν (-1-kp.1) b x) y n kp.2

private theorem iterate_finite (hμ : LowerTruncated μ) (hν : LowerTruncated ν)
    (a w c : A) (b x y : B) (n : ℤ) :
    Function.HasFiniteSupport (iterateTerm μ ν a w c b x y n) := by
  obtain ⟨M, hM⟩ := hμ a w
  obtain ⟨N, hN⟩ := hν b x
  apply finite_rows (Finset.Icc (-N) (M-1)).finite_toSet
  · intro k
    exact convolution_finite hμ hν (μ k a w) c (ν (-1-k) b x) y n
  · intro k hk p
    have tail : k < -N ∨ M-1 < k := by
      simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using hk
    rcases tail with tail | tail
    · simp [iterateTerm, convolution, hN _ (by omega : N ≤ -1-k)]
    · simp [iterateTerm, convolution, hM _ (by omega : M ≤ k)]

private def complement (d : ℤ) : ℤ ≃ ℤ where
  toFun i := d-i
  invFun i := d-i
  left_inv i := by dsimp; omega
  right_inv i := by dsimp; omega

private theorem tensor_zero_mode (hμ : LowerTruncated μ) (hν : LowerTruncated ν)
    (conv : ∀ n a w b x, T n (a ⊗ₜ[ℂ] b) (w ⊗ₜ[ℂ] x) =
      ∑ᶠ i, convolution μ ν a w b x n i)
    {a w c : A} {b x y : B} {e : ℂ}
    (lawA : SignedLaw μ 1 a w c) (lawB : SignedLaw ν e b x y) (n : ℤ) :
    T 0 (a ⊗ₜ[ℂ] b) (T n (w ⊗ₜ[ℂ] x) (c ⊗ₜ[ℂ] y)) -
      e • T n (w ⊗ₜ[ℂ] x) (T 0 (a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] y)) =
      T n (T 0 (a ⊗ₜ[ℂ] b) (w ⊗ₜ[ℂ] x)) (c ⊗ₜ[ℂ] y) := by
  let F := productTerm μ ν a w c b x y 0 n
  let R : ℤ × ℤ → A ⊗[ℂ] B := fun ir => productTerm μ ν w a c x b y n 0 (ir.2,ir.1)
  let U := firstPiece μ ν 1 e a w c b x y n
  let W := firstPiece ν μ e 1 b x y a w c n
  let swap := TensorProduct.comm ℂ B A
  let indices := Equiv.prodCongr (complement (-1)) (complement (n-1))
  let V : ℤ × ℤ → A ⊗[ℂ] B := fun ir => swap (W (indices ir))
  let I : ℤ × ℤ → A ⊗[ℂ] B := iterateTerm μ ν a w c b x y n
  have hF : Function.HasFiniteSupport F := product_finite hμ hν a w c b x y 0 n
  have hR : Function.HasFiniteSupport R :=
    finite_reindex (product_finite hμ hν w a c x b y n 0) (Equiv.prodComm ℤ ℤ)
  have hU := first_piece_sum hμ hν lawA lawB n
  have hW := first_piece_sum hν hμ lawB lawA n
  have hV : Function.HasFiniteSupport V := by
    apply (finite_reindex hW.1 indices).subset
    intro ir hir
    by_contra hn
    have hz : W (indices ir) = 0 := not_not.mp hn
    exact hir (by simp [V, hz])
  have hI : Function.HasFiniteSupport I := iterate_finite hμ hν a w c b x y n
  have forward := composed_tmul hμ hν conv a w c b x y 0 n
  have reverse : T n (w ⊗ₜ[ℂ] x) (T 0 (a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] y)) = ∑ᶠ ir, R ir :=
    (composed_tmul hμ hν conv w a c x b y n 0).trans
      (finsum_comp_equiv (Equiv.prodComm ℤ ℤ)).symm
  have iter : T n (T 0 (a ⊗ₜ[ℂ] b) (w ⊗ₜ[ℂ] x)) (c ⊗ₜ[ℂ] y) =
      ∑ᶠ k : ℤ, ∑ᶠ p : ℤ, I (k,p) := by
    rw [conv 0 a w b x]
    change ((T n).flip (c ⊗ₜ[ℂ] y)) (∑ᶠ k, convolution μ ν a w b x 0 k) = _
    rw [map_finsum _ (convolution_finite hμ hν a w b x 0)]
    apply finsum_congr
    intro k
    exact conv n (μ k a w) c (ν (-1-k) b x) y
  have split (ir : ℤ × ℤ) : F ir - e • R ir = U ir + V ir := by
    obtain ⟨i,r⟩ := ir
    have indices_apply : indices (i,r) = (-1-i,n-1-r) := rfl
    have j : -1 - (-1-i) = i := by omega
    have s : n-1-(n-1-r) = r := by omega
    have sign : 0 ≤ -1-i ↔ ¬ 0 ≤ i := by omega
    by_cases ip : 0 ≤ i
    · simp only [F, R, U, V, W, firstPiece, commutator, productTerm, convolution,
        indices_apply, crossed, sign, ip, swap,
        ite_true, ite_false, not_true_eq_false, one_smul, map_sub,
        TensorProduct.sub_tmul, TensorProduct.tmul_smul,
        TensorProduct.comm_tmul, j, s, zero_sub]
      abel
    · simp only [F, R, U, V, W, firstPiece, commutator, productTerm, convolution,
        indices_apply, crossed, sign, ip, swap,
        ite_true, ite_false, not_false_eq_true, one_smul, map_sub,
        TensorProduct.sub_tmul, TensorProduct.tmul_smul,
        TensorProduct.comm_tmul, j, s, zero_sub]
      simp only [smul_sub]
      abel
  have second : (∑ᶠ ir, V ir) = ∑ᶠ l : ℕ, ∑ᶠ p : ℤ, I (-1-l,p) := by
    let J := iterateTerm ν μ b x y a w c n
    have hJ : Function.HasFiniteSupport J := iterate_finite hν hμ b x y a w c n
    let cast : ℕ → ℤ := fun l => l
    have hRows : Function.HasFiniteSupport (fun l : ℕ => ∑ᶠ q : ℤ, J (cast l,q)) :=
      Set.Finite.preimage (show Function.Injective cast by intro i j h; dsimp [cast] at h; omega).injOn
        (finite_row_sums hJ)
    calc
      _ = swap (∑ᶠ ir, W (indices ir)) :=
        (map_finsum swap.toLinearMap (finite_reindex (show Function.HasFiniteSupport W
          from hW.1) indices)).symm
      _ = swap (∑ᶠ ir, W ir) := congrArg swap (finsum_comp_equiv indices (f := W))
      _ = swap (∑ᶠ l : ℕ, ∑ᶠ q : ℤ, J (cast l,q)) := congrArg swap hW.2
      _ = _ := by
        change swap.toLinearMap (∑ᶠ l : ℕ, ∑ᶠ q : ℤ, J (cast l,q)) = _
        rw [map_finsum swap.toLinearMap hRows]
        apply finsum_congr
        intro l
        rw [← finsum_comp_equiv (complement (n-1)) (f := fun q => J (cast l,q)),
          map_finsum swap.toLinearMap (finite_reindex (finite_fiber hJ (cast l)) _)]
        apply finsum_congr
        intro p
        simp only [J, I, iterateTerm, convolution, cast, complement, Equiv.coe_fn_mk, swap,
          LinearEquiv.coe_coe, TensorProduct.comm_tmul,
          show -1-(-1-(l : ℤ)) = l by omega,
          show n-1-(n-1-p) = p by omega]
  rw [forward, reverse, iter]
  change (∑ᶠ ir, F ir) - e • (∑ᶠ ir, R ir) = _
  have hScaled : Function.HasFiniteSupport (fun ir => e • R ir) :=
    hR.smul_right (fun _ => e)
  have sumSplit := finsum_sub_distrib hF hScaled
  simp only [split] at sumSplit
  rw [smul_finsum' e hR, ← sumSplit, finsum_add_distrib
    (show Function.HasFiniteSupport U from hU.1) hV, hU.2, second]
  let pos : ℕ → ℤ := fun k => k
  let neg : ℕ → ℤ := fun k => -1-(k : ℤ)
  symm
  exact finsum_two_ranges (finite_row_sums hI) (pos := pos) (neg := neg)
    (by intro i j h; dsimp [pos] at h; omega)
    (by intro i j h; dsimp [neg] at h; omega)
    (by
      refine Set.disjoint_left.mpr ?_
      rintro i ⟨k, hk⟩ ⟨l, hl⟩
      dsimp [pos] at hk
      dsimp [neg] at hl
      omega)
    (by
      intro i _
      by_cases h : 0 ≤ i
      · exact Or.inl ⟨i.toNat, by dsimp [pos]; omega⟩
      · exact Or.inr ⟨(-1-i).toNat, by dsimp [neg]; omega⟩)


end FiniteShuffle

open ActualLeechHyperbolic (leechData leech_spec)
open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef)
open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeSugawaraCurrents (gramComplex)
open TwistedGround.Orbifold
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock (ket)
open private mode_vv sum_v smul_v from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi
open private assocY_tmul reassoc_parity from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes
open private rightLift_tmul from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
open private parity_square current_odd from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBRSTDerivation
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

private abbrev FixedLeech := LatticeInvolution.FixedCarrier leechData
private abbrev TwistedLeech :=
  HalfFock.LatticeHalfFockParityField.paritySpace leechData leechUnit (-1)
private abbrev PlaneGhost := LatticeMatterGhostCoupling.State hyperbolicPlane

local notation "inV" => (LinearMap.inl ℂ FixedLeech TwistedLeech)
local notation "inM" => (LinearMap.inr ℂ FixedLeech TwistedLeech)
local notation "orb" => modesOfStateField (OriginalOrbifoldField.Y leechData leechUnit leechPosDef)
local notation "plane" => modesOfStateField (LatticeMatterGhostStateField.Y hyperbolicPlane)
local notation "tensor" => modesOfStateField assocY
local notation "par" => LatticeMatterGhostStateField.parity hyperbolicPlane
local notation "tensorPar" => rightLift par

section Linearity

variable {A : Type*} [AddCommGroup A] [Module ℂ A] {μ : Modes A}

private theorem iter_support (trunc : LowerTruncated μ) (a w c : A) (p q r : ℤ) :
    Function.HasFiniteSupport (fun t : ℕ =>
      integerBinomial p t • μ (p+q-t) (μ (r+t) a w) c) := by
  apply (finite_offset trunc a w r).subset
  intro t ht
  by_contra h
  have hz : μ (r+t) a w = 0 := not_not.mp h
  exact ht (by simp [hz])

private theorem prod_support (trunc : LowerTruncated μ) (e : ℂ) (a w c : A) (p q r : ℤ) :
    Function.HasFiniteSupport (fun t : ℕ => ((-1 : ℂ)^t * integerBinomial r t) •
      (μ (p+r-t) a (μ (q+t) w c) -
        (epsilon r * e) • μ (q+r-t) w (μ (p+t) a c))) := by
  have forward : Function.HasFiniteSupport
      (fun t : ℕ => μ (p+r-t) a (μ (q+t) w c)) := by
    apply (finite_offset trunc w c q).subset
    intro t ht
    by_contra h
    have hz : μ (q+t) w c = 0 := not_not.mp h
    exact ht (by simp [hz])
  have reverse : Function.HasFiniteSupport
      (fun t : ℕ => μ (q+r-t) w (μ (p+t) a c)) := by
    apply (finite_offset trunc a c p).subset
    intro t ht
    by_contra h
    have hz : μ (p+t) a c = 0 := not_not.mp h
    exact ht (by simp [hz])
  exact (forward.sub (reverse.smul_right (fun _ => epsilon r * e))).smul_right
    (fun t => (-1 : ℂ)^t * integerBinomial r t)

private theorem law_add_middle (trunc : LowerTruncated μ) {e : ℂ} {a u v c : A}
    (hu : SignedLaw μ e a u c) (hv : SignedLaw μ e a v c) :
    SignedLaw μ e a (u+v) c := by
  intro p q r
  have iterAdd : iterate μ a (u+v) c p q r =
      iterate μ a u c p q r + iterate μ a v c p q r := by
    simp only [iterate, map_add, LinearMap.add_apply, smul_add]
    exact finsum_add_distrib (iter_support trunc a u c p q r) (iter_support trunc a v c p q r)
  rw [iterAdd, hu p q r, hv p q r,
    ← finsum_add_distrib (prod_support trunc e a u c p q r) (prod_support trunc e a v c p q r)]
  apply finsum_congr
  intro t
  simp only [map_add, LinearMap.add_apply, smul_add, smul_sub]
  abel

private theorem law_add_last (trunc : LowerTruncated μ) {e : ℂ} {a w u v : A}
    (hu : SignedLaw μ e a w u) (hv : SignedLaw μ e a w v) :
    SignedLaw μ e a w (u+v) := by
  intro p q r
  have iterAdd : iterate μ a w (u+v) p q r =
      iterate μ a w u p q r + iterate μ a w v p q r := by
    simp only [iterate, map_add, smul_add]
    exact finsum_add_distrib (iter_support trunc a w u p q r) (iter_support trunc a w v p q r)
  rw [iterAdd, hu p q r, hv p q r,
    ← finsum_add_distrib (prod_support trunc e a w u p q r) (prod_support trunc e a w v p q r)]
  apply finsum_congr
  intro t
  simp only [map_add, smul_add, smul_sub]
  abel

end Linearity

private theorem orb_fixed_law (a : FixedLeech) (w c : Orbifold) :
    SignedLaw orb 1 (inV a) w c := by
  have trunc : LowerTruncated orb := lowerTruncated_modesOfStateField _
  have fromDefect (u v : Orbifold)
      (h : ∀ p q r : ℤ, defect orb (inV a) u v p q r = 0) :
      SignedLaw orb 1 (inV a) u v := by
    intro p q r
    have h' := ((defect_eq_zero_iff_borcherds orb trunc (inV a) u v p q r).mp
      (h p q r)).2.2.2
    simpa only [iterate, mul_one] using h'
  have vvv (b d : FixedLeech) : SignedLaw orb 1 (inV a) (inV b) (inV d) := by
    intro p q r
    have h := congrArg inV ((LatticeInvolution.fixed_borcherds leechData a b d p q r).2.2.2)
    have fixedCoeff (z : FixedLeech) (m : ℤ) :
        ((LatticeInvolution.fixedY leechData z)[[m]]) = LatticeInvolution.fixedMode leechData z m :=
      LatticeInvolution.fixedField_ncoeff leechData z m
    simpa only [iterate, mul_one, mode_vv, ← smul_v, sum_v, map_sub, fixedCoeff]
      using h
  have vvm (b : FixedLeech) (d : TwistedLeech) : SignedLaw orb 1 (inV a) (inV b) (inM d) :=
    fromDefect _ _ (OriginalOrbifoldJacobi.defect_vvm leechPosDef a b d)
  have vmv (b : TwistedLeech) (d : FixedLeech) : SignedLaw orb 1 (inV a) (inM b) (inV d) :=
    fromDefect _ _ (OriginalOrbifoldJacobi.defect_vmv leechPosDef leech_spec.1 a d b)
  have vmm (b d : TwistedLeech) : SignedLaw orb 1 (inV a) (inM b) (inM d) :=
    fromDefect _ _ (OriginalOrbifoldJacobi.defect_vmm leechPosDef leech_spec.1 a b d)
  have split (u : Orbifold) : inV u.1 + inM u.2 = u := by
    rcases u with ⟨u,v⟩
    change (u + 0, 0 + v) = (u,v)
    simp only [add_zero, zero_add]
  have h := law_add_middle trunc
    (law_add_last trunc (vvv w.1 c.1) (vvm w.1 c.2))
    (law_add_last trunc (vmv w.2 c.1) (vmm w.2 c.2))
  rwa [split w, split c] at h

private theorem plane_law (b x y : PlaneGhost) (e : ℂ) (isOdd : Bool)
    (hb : par b = (if isOdd then -b else b)) (hx : par x = e • x) :
    SignedLaw plane (if isOdd then e else 1) b x y := by
  intro p q r
  have h := (LatticeMatterGhostBorcherds.borcherds hyperbolicPlane b x y p q r).2.2.2.2
  change iterate plane b x y p q r = ∑ᶠ t : ℕ,
    (((-1 : ℂ)^t) * integerBinomial r t) •
      (plane (p+r-t) b (plane (q+t) x y) - epsilon r •
        (plane (q+r-t) x (plane (p+t) ((2 : ℂ)⁻¹ • (b + par b)) y) +
          plane (q+r-t) (par x) (plane (p+t) ((2 : ℂ)⁻¹ • (b - par b)) y))) at h
  cases isOdd
  · simp only [Bool.false_eq_true, ite_false] at hb ⊢
    have even : (2 : ℂ)⁻¹ • (b + par b) = b := by rw [hb]; module
    have odd : (2 : ℂ)⁻¹ • (b - par b) = 0 := by rw [hb, sub_self, smul_zero]
    simpa only [even, odd, map_zero, LinearMap.zero_apply, add_zero, mul_one] using h
  · simp only [ite_true] at hb ⊢
    have even : (2 : ℂ)⁻¹ • (b + par b) = 0 := by rw [hb, add_neg_cancel, smul_zero]
    have odd : (2 : ℂ)⁻¹ • (b - par b) = b := by rw [hb]; module
    simpa only [even, odd, hx, map_zero, LinearMap.zero_apply, zero_add, map_smul,
      LinearMap.smul_apply, smul_smul] using h

/-- The literal tensor zero-mode commutator for a fixed Leech first source
and homogeneous plane–ghost sources. The other Leech inputs are arbitrary. -/
theorem fixed_first_tensor_zero_mode (a : FixedLeech) (w c : Orbifold)
    (b x y : PlaneGhost) (e : ℂ) (isOdd : Bool)
    (hb : par b = (if isOdd then -b else b)) (hx : par x = e • x) (n : ℤ) :
    tensor 0 (inV a ⊗ₜ[ℂ] b) (tensor n (w ⊗ₜ[ℂ] x) (c ⊗ₜ[ℂ] y)) -
      (if isOdd then e else 1) •
        tensor n (w ⊗ₜ[ℂ] x) (tensor 0 (inV a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] y)) =
      tensor n (tensor 0 (inV a ⊗ₜ[ℂ] b) (w ⊗ₜ[ℂ] x)) (c ⊗ₜ[ℂ] y) :=
  tensor_zero_mode (lowerTruncated_modesOfStateField _) (lowerTruncated_modesOfStateField _)
    assocY_tmul (orb_fixed_law a w c) (plane_law b x y e isOdd hb hx) n

private theorem fixed_odd_derivation (a : FixedLeech) (b : PlaneGhost) (hb : par b = -b)
    (n : ℤ) (s v : AssocState) :
    tensor 0 (inV a ⊗ₜ[ℂ] b) (tensor n s v) =
      tensor n (tensor 0 (inV a ⊗ₜ[ℂ] b) s) v +
        tensor n (tensorPar s) (tensor 0 (inV a ⊗ₜ[ℂ] b) v) := by
  induction s using TensorProduct.inductionOn with
  | tmul w x =>
    have homogeneous (z : PlaneGhost) (e : ℂ) (hz : par z = e • z) :
        tensor 0 (inV a ⊗ₜ[ℂ] b) (tensor n (w ⊗ₜ[ℂ] z) v) =
          tensor n (tensor 0 (inV a ⊗ₜ[ℂ] b) (w ⊗ₜ[ℂ] z)) v +
            tensor n (tensorPar (w ⊗ₜ[ℂ] z)) (tensor 0 (inV a ⊗ₜ[ℂ] b) v) := by
      induction v using TensorProduct.inductionOn with
      | tmul c y =>
        have h := sub_eq_iff_eq_add.mp
          (fixed_first_tensor_zero_mode a w c b z y e true (by simpa using hb) hz n)
        simpa only [rightLift_tmul, hz, TensorProduct.tmul_smul, map_smul, Bool.true_eq, ite_true,
          LinearMap.smul_apply] using h
      | add v₁ v₂ h₁ h₂ =>
        simp only [map_add, h₁, h₂]
        abel
    let even := (2 : ℂ)⁻¹ • (x + par x)
    let odd := (2 : ℂ)⁻¹ • (x - par x)
    have he : par even = (1 : ℂ) • even := by
      dsimp only [even]
      rw [map_smul, map_add, parity_square, one_smul, add_comm (par x)]
    have ho : par odd = (-1 : ℂ) • odd := by
      simp only [odd, map_smul, map_sub, parity_square]
      module
    have split : w ⊗ₜ[ℂ] x = w ⊗ₜ[ℂ] even + w ⊗ₜ[ℂ] odd := by
      rw [← TensorProduct.tmul_add]
      congr 1
      dsimp [even, odd]
      module
    rw [split]
    simp only [map_add, LinearMap.add_apply, homogeneous even 1 he, homogeneous odd (-1) ho]
    abel
  | add s₁ s₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, h₁, h₂]
    abel

private theorem assocQ_mode_superderivation (n : ℤ) (s v : AssocState) :
    assocQ (tensor n s v) = tensor n (assocQ s) v + tensor n (tensorPar s) (assocQ v) := by
  have hc : par (LatticeAllStateField.vacuum hyperbolicPlane ⊗ₜ[ℂ] ket {1}) =
      -(LatticeAllStateField.vacuum hyperbolicPlane ⊗ₜ[ℂ] ket {1}) := by
    simp [LatticeMatterGhostStateField.parity, TensorProduct.map_tmul, parity_ket,
      TensorProduct.tmul_neg]
  have hj : par (LatticeMatterGhostStateField.Jtot hyperbolicPlane (gramComplex hyperbolicPlane)) =
      -LatticeMatterGhostStateField.Jtot hyperbolicPlane (gramComplex hyperbolicPlane) := by
    simpa only [pow_one, neg_one_smul] using
      current_odd hyperbolicPlane (gramComplex hyperbolicPlane)
  have h₁ := fixed_odd_derivation ActualLeechOrbifoldMatter.omega.1 _ hc n s v
  have h₂ := fixed_odd_derivation (LatticeInvolution.fixedVacuum leechData) _ hj n s v
  have current : assocBRSTCurrent =
      inV ActualLeechOrbifoldMatter.omega.1 ⊗ₜ[ℂ]
        (LatticeAllStateField.vacuum hyperbolicPlane ⊗ₜ[ℂ] ket {1}) +
      inV (LatticeInvolution.fixedVacuum leechData) ⊗ₜ[ℂ]
        LatticeMatterGhostStateField.Jtot hyperbolicPlane (gramComplex hyperbolicPlane) := rfl
  have currentMode : tensor 0 assocBRSTCurrent = assocQ := assocQ_current_zero_mode
  rw [← currentMode, current]
  simp only [map_add, LinearMap.add_apply, h₁, h₂]
  abel

/-- The actual BRST charge superderives every original integer mode, with
its second term twisted by the native bc parity on the first input. -/
theorem actualQ_mode_superderivation (n : ℤ) (s v : ComplexState) :
    Q (originalMode n s v) =
      originalMode n (Q s) v + originalMode n (originalParity s) (Q v) := by
  have hQ (x : ComplexState) : reassoc (Q x) = assocQ (reassoc x) := by
    rw [← actualQ_current_zero_mode, reassoc_originalMode, actualBRSTCurrent,
      reassoc.apply_symm_apply, assocQ_current_zero_mode]
  apply reassoc.injective
  rw [map_add, hQ, reassoc_originalMode, reassoc_originalMode, reassoc_originalMode,
    hQ, hQ, reassoc_parity]
  exact assocQ_mode_superderivation n (reassoc s) (reassoc v)


end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
