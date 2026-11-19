/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTSuperJacobi
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTSuperJacobi
   mirror-E: none(waiver:algebraic-original-brst-super-jacobi)
   anchors: []
   utility: none
   digest: Signed integer residue closure and super-Borcherds for the original BRST field. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTFieldAxioms
import D5.S3.VertexAlgebra.SignedFields.SignedFieldResidueLocality

/-!
Signed residue closure follows from Dong locality and creative-field uniqueness,
as in `LatticeMatterGhostStateFieldIterate` and `LatticeMatterGhostBRSTDerivation`.
The coefficient argument uses the signed Pascal method of
`LatticeMatterGhostSignedBorcherds` on the original BRST carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTSuperJacobi

open OriginalOrbifoldCriticalMatter (Matter State vacuum)
open OriginalOrbifoldBRSTStateField (Y Y_truncation)
open OriginalOrbifoldBRSTSignedLocality (parity stateField_locality)
open OriginalOrbifoldBRSTFieldAxioms (translation translation_vacuum stateField_creation
  stateField_creativity stateField_covariance parity_involution homogeneous_mode_product)
open FieldNormalProductLocality (delta deltaEnd)
open SignedFieldNormalProductLocality (signedComm)
open SignedFieldResidueLocality
open StateFieldResidueReconstruction (integerBinomial epsilon deltaEnd_iterate_apply)

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private theorem local_sub (s : ℂ) (A B C : VertexOperator ℂ State)
    (ha : ∃ M : ℕ, delta^[M] (signedComm s A C) = 0)
    (hb : ∃ N : ℕ, delta^[N] (signedComm s B C) = 0) :
    ∃ K : ℕ, delta^[K] (signedComm s (A - B) C) = 0 := by
  obtain ⟨M, hm⟩ := ha
  obtain ⟨N, hn⟩ := hb
  have hm' := FiniteFieldLocality.monotone (signedComm s A C)
    M (max M N) (le_max_left _ _) hm
  have hn' := FiniteFieldLocality.monotone (signedComm s B C)
    N (max M N) (le_max_right _ _) hn
  have split : signedComm s (A - B) C = signedComm s A C - signedComm s B C := by
    funext i j
    simp only [signedComm, map_sub, Pi.sub_apply, mul_sub, sub_mul, smul_sub]
    abel
  refine ⟨max M N, ?_⟩
  funext i j
  rw [← deltaEnd_iterate_apply, split, map_sub]
  simp only [Pi.sub_apply, deltaEnd_iterate_apply, hm', hn', Pi.zero_apply, sub_self]

private theorem creative_unique (degree : ℕ) (F : VertexOperator ℂ State)
    (creative : ∀ n : ℤ, 0 ≤ n → (F[[n]]) vacuum = 0)
    (initial : (F[[-1]]) vacuum = 0)
    (covariant : ∀ n : ℤ, translation * (F[[n]]) - (F[[n]]) * translation =
      -(n : ℂ) • (F[[n - 1]]))
    (locality : ∀ (x : State) (q : ℕ), parity x = (-1 : ℂ) ^ q • x →
      ∃ N : ℕ, delta^[N] (signedComm ((-1 : ℂ) ^ (degree * q)) F (Y x)) = 0) :
    F = 0 := by
  have negative (k : ℕ) : (F[[-(k : ℤ) - 1]]) vacuum = 0 := by
    induction k with
    | zero => simpa using initial
    | succ k ih =>
      have h := LinearMap.congr_fun (covariant (-(k : ℤ) - 1)) vacuum
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        ih, translation_vacuum, map_zero, sub_self] at h
      rw [show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by omega] at h
      have scalar : -((-(k : ℤ) - 1 : ℤ) : ℂ) = (k : ℂ) + 1 := by
        push_cast
        ring
      rw [scalar] at h
      have nonzero : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      exact (smul_eq_zero.mp h.symm).resolve_left nonzero
  have vacuumZero (n : ℤ) : (F[[n]]) vacuum = 0 := by
    by_cases hn : 0 ≤ n
    · exact creative n hn
    · rw [show n = -(((-n - 1).toNat : ℕ) : ℤ) - 1 by omega]
      exact negative _
  have boundary (d : ℤ → ℤ → State) (h : ∀ i j : ℤ, 0 ≤ j → d i j = 0) (N : ℕ) :
      (∀ i j : ℤ, 0 ≤ j → (delta^[N] d) i j = 0) ∧
        (∀ i : ℤ, (delta^[N] d) i (-1) = d (i + N) (-1)) := by
    induction N with
    | zero => exact ⟨h, by simp⟩
    | succ N ih =>
      constructor
      · intro i j hj
        rw [Function.iterate_succ_apply']
        simp only [delta, ih.1 (i + 1) j hj, ih.1 i (j + 1) (by omega), sub_self]
      · intro i
        rw [Function.iterate_succ_apply']
        change (delta^[N] d) (i + 1) (-1) - (delta^[N] d) i 0 = _
        rw [ih.2, ih.1 i 0 (by omega), sub_zero]
        apply congrArg (fun k : ℤ => d k (-1))
        omega
  have homogeneousModes (n : ℤ) (x : State) (q : ℕ)
      (hx : parity x = (-1 : ℂ) ^ q • x) : (F[[n]]) x = 0 := by
    obtain ⟨N, killed⟩ := locality x q hx
    let comm := signedComm ((-1 : ℂ) ^ (degree * q)) F (Y x)
    change delta^[N] comm = 0 at killed
    let d : ℤ → ℤ → State := fun i j => comm i j vacuum
    have tail : ∀ i j : ℤ, 0 ≤ j → d i j = 0 := by
      intro i j hj
      simp only [d, comm, signedComm, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.mul_apply, stateField_creativity x j hj, vacuumZero, map_zero,
        smul_zero, sub_self]
    have hd : delta^[N] d = 0 := by
      rw [← BinomialKernelDelta.delta_evaluation comm vacuum N, killed]
      rfl
    have h := congrFun (congrFun hd (n - N)) (-1)
    rw [(boundary d tail N).2 (n - N)] at h
    simpa only [d, comm, signedComm, sub_add_cancel, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.mul_apply, vacuumZero, map_zero,
      smul_zero, sub_zero, stateField_creation, Pi.zero_apply] using h
  have paritySquare (x : State) : parity (parity x) = x :=
    LinearMap.congr_fun parity_involution x
  have allModes (n : ℤ) (x : State) : (F[[n]]) x = 0 := by
    let x0 := (2 : ℂ)⁻¹ • (x + parity x)
    let x1 := (2 : ℂ)⁻¹ • (x - parity x)
    have h0 : parity x0 = (-1 : ℂ) ^ 0 • x0 := by
      dsimp [x0]
      rw [map_smul, map_add, paritySquare]
      simp only [pow_zero, one_smul]
      congr 1
      abel
    have h1 : parity x1 = (-1 : ℂ) ^ 1 • x1 := by
      dsimp [x1]
      rw [map_smul, map_sub, paritySquare]
      norm_num only [pow_one]
      module
    have hx : x = x0 + x1 := by dsimp [x0, x1]; module
    rw [hx, map_add, homogeneousModes n x0 0 h0, homogeneousModes n x1 1 h1, add_zero]
  apply HVertexOperator.coeff_inj
  funext power
  apply LinearMap.ext
  intro x
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  simpa only [map_zero, Pi.zero_apply, LinearMap.zero_apply]
    using allModes (-power - 1) x

private theorem residue_creation (s : ℂ) (r : ℤ) (a b : State) :
    (((residueField s r (Y a) (Y b)).operator)[[-1]]) vacuum = ((Y a)[[r]]) b ∧
      ∀ n : ℤ, 0 ≤ n → (((residueField s r (Y a) (Y b)).operator)[[n]]) vacuum = 0 := by
  have rightZero (n : ℤ) : residueRight r n (Y a) (Y b) vacuum = 0 := by
    unfold residueRight
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    rw [stateField_creativity a i (by omega), map_zero, smul_zero]
  constructor
  · rw [(residueField s r (Y a) (Y b)).coefficient, residueCoefficient, rightZero,
      smul_zero, sub_zero]
    unfold residueLeft
    rw [finsum_eq_single _ 0]
    · simp [integerBinomial, stateField_creation]
    · intro i hi
      rw [stateField_creativity b (-1 + (i : ℤ)) (by omega), map_zero, smul_zero]
  · intro n hn
    rw [(residueField s r (Y a) (Y b)).coefficient, residueCoefficient, rightZero,
      smul_zero, sub_zero]
    unfold residueLeft
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    rw [stateField_creativity b (n + (i : ℤ)) (by omega), map_zero, smul_zero]

/-- The signed residue product of homogeneous fields is the actual field of their
integer mode product. -/
theorem residueClosure (a b : State) (pa pb : ℕ)
    (ha : parity a = (-1 : ℂ) ^ pa • a) (hb : parity b = (-1 : ℂ) ^ pb • b) (r : ℤ) :
    Y (((Y a)[[r]]) b) =
      (residueField ((-1 : ℂ) ^ (pa * pb)) r (Y a) (Y b)).operator := by
  let field := (residueField ((-1 : ℂ) ^ (pa * pb)) r (Y a) (Y b)).operator
  let product := ((Y a)[[r]]) b
  let difference := field - Y product
  have productParity := homogeneous_mode_product a b pa pb r ha hb
  have creation := residue_creation ((-1 : ℂ) ^ (pa * pb)) r a b
  have creativeDifference : ∀ n : ℤ, 0 ≤ n → (difference[[n]]) vacuum = 0 := by
    intro n hn
    simp only [difference, field, map_sub, Pi.sub_apply, LinearMap.sub_apply,
      creation.2 n hn, stateField_creativity product n hn, sub_self]
  have initial : (difference[[-1]]) vacuum = 0 := by
    simp only [difference, field, product, map_sub, Pi.sub_apply, LinearMap.sub_apply,
      creation.1, stateField_creation, sub_self]
  have covariance (n : ℤ) :
      translation * (difference[[n]]) - (difference[[n]]) * translation =
        -(n : ℂ) • (difference[[n - 1]]) := by
    simp only [difference, map_sub, Pi.sub_apply]
    calc
      _ = (translation * (field[[n]]) - (field[[n]]) * translation) -
        (translation * ((Y product)[[n]]) - ((Y product)[[n]]) * translation) := by
          simp only [mul_sub, sub_mul]
          abel
      _ = _ := by
        rw [residue_translation _ r (Y a) (Y b) translation
          (stateField_covariance a) (stateField_covariance b), stateField_covariance]
        module
  have crossLocality (c : State) (t : ℕ) (hc : parity c = (-1 : ℂ) ^ t • c) :
      ∃ N : ℕ, delta^[N] (signedComm ((-1 : ℂ) ^ ((pa + pb) * t)) difference (Y c)) = 0 := by
    have sign : ((-1 : ℂ) ^ (pa * t)) * ((-1 : ℂ) ^ (pb * t)) =
        (-1 : ℂ) ^ ((pa + pb) * t) := by rw [← pow_add, Nat.add_mul]
    have first := residue_locality ((-1 : ℂ) ^ (pa * pb)) ((-1 : ℂ) ^ (pa * t))
      ((-1 : ℂ) ^ (pb * t)) (Y a) (Y b) (Y c)
      (stateField_locality a c pa t ha hc) (stateField_locality b c pb t hb hc)
      (stateField_locality a b pa pb ha hb) r
    rw [sign] at first
    exact local_sub _ field (Y product) (Y c) first
      (stateField_locality product c (pa + pb) t productParity hc)
  exact (sub_eq_zero.mp (creative_unique (pa + pb) difference
    creativeDifference initial covariance crossLocality)).symm

open BinomialKernelDelta (chooseSign chooseSign_zero chooseSign_pascal finsum_split)

private abbrev mode (a : State) (n : ℤ) (b : State) : State := ((Y a)[[n]]) b

private def iterateTerm (a b c : State) (p q r : ℤ) (i : ℕ) : State :=
  integerBinomial p i • mode (mode a (r + i) b) (p + q - i) c

private def productTerm (a b c : State) (p q r : ℤ) (i : ℕ) : State :=
  chooseSign r i • mode a (p + r - i) (mode b (q + i) c)

private abbrev iterateSum (a b c : State) (p q r : ℤ) : State :=
  ∑ᶠ i : ℕ, iterateTerm a b c p q r i

private abbrev productSum (a b c : State) (p q r : ℤ) : State :=
  ∑ᶠ i : ℕ, productTerm a b c p q r i

private theorem offset_finite (a b : State) (n : ℤ) (f : ℕ → State → State)
    (zero : ∀ i, f i 0 = 0) :
    Function.HasFiniteSupport (fun i : ℕ => f i (mode a (n + i) b)) := by
  obtain ⟨cutoff, vanish⟩ := Y_truncation a b
  refine (Finset.range (cutoff - n).toNat).finite_toSet.subset ?_
  intro i hi
  apply Finset.mem_range.mpr
  by_contra! high
  apply hi
  change f i (mode a (n + i) b) = 0
  have hz : mode a (n + i) b = 0 := vanish _ (by omega)
  rw [hz, zero]

private theorem iterate_sequence_finite (a b c : State) (n r : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ => mode (mode a (r + i) b) (n - i) c) :=
  offset_finite a b r (fun i v => mode v (n - i) c) (by intro i; simp [mode])

private theorem product_sequence_finite (a b c : State) (n q : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ => mode a (n - i) (mode b (q + i) c)) :=
  offset_finite b c q (fun i v => mode a (n - i) v) (by intro i; simp [mode])

private theorem sum_pascal (n : ℤ) (f : ℕ → State) (finite : Function.HasFiniteSupport f) :
    (∑ᶠ i : ℕ, integerBinomial (n + 1) i • f i) =
      (∑ᶠ i : ℕ, integerBinomial n i • f i) +
        (∑ᶠ i : ℕ, integerBinomial n i • f (i + 1)) := by
  have tail := finite.fun_comp_of_injective (g := fun i : ℕ => i + 1)
    (fun _ _ h => Nat.add_right_cancel h)
  have chooseZero (m : ℤ) : integerBinomial m 0 = 1 := by simp [integerBinomial]
  have pascal (i : ℕ) :
      integerBinomial (n + 1) (i + 1) =
        integerBinomial n i + integerBinomial n (i + 1) := by
    unfold integerBinomial
    rw [Ring.choose_succ_succ, Int.cast_add]
  rw [finsum_split (fun i => integerBinomial (n + 1) i • f i)
      (finite.smul_right (integerBinomial (n + 1))),
    finsum_split (fun i => integerBinomial n i • f i)
      (finite.smul_right (integerBinomial n))]
  simp only [chooseZero, one_smul]
  simp_rw [pascal, add_smul]
  rw [finsum_add_distrib
    (f := fun i => integerBinomial n i • f (i + 1))
    (g := fun i => integerBinomial n (i + 1) • f (i + 1))
    (tail.smul_right (integerBinomial n))
    (tail.smul_right (fun i => integerBinomial n (i + 1)))]
  abel

private theorem signed_sum_pascal (n : ℤ) (f : ℕ → State) (finite : Function.HasFiniteSupport f) :
    (∑ᶠ i : ℕ, chooseSign (n + 1) i • f i) =
      (∑ᶠ i : ℕ, chooseSign n i • f i) -
        (∑ᶠ i : ℕ, chooseSign n i • f (i + 1)) := by
  have tail := finite.fun_comp_of_injective (g := fun i : ℕ => i + 1)
    (fun _ _ h => Nat.add_right_cancel h)
  rw [finsum_split (fun i => chooseSign (n + 1) i • f i)
      (finite.smul_right (chooseSign (n + 1))),
    finsum_split (fun i => chooseSign n i • f i)
      (finite.smul_right (chooseSign n))]
  simp only [chooseSign_zero, one_smul]
  simp_rw [chooseSign_pascal, sub_smul]
  rw [finsum_sub_distrib
    (f := fun i => chooseSign n (i + 1) • f (i + 1))
    (g := fun i => chooseSign n i • f (i + 1))
    (tail.smul_right (fun i => chooseSign n (i + 1)))
    (tail.smul_right (chooseSign n))]
  abel

private theorem iterate_pascal (a b c : State) (p q r : ℤ) :
    iterateSum a b c (p + 1) q r =
      iterateSum a b c p (q + 1) r + iterateSum a b c p q (r + 1) := by
  let f (i : ℕ) := mode (mode a (r + i) b) (p + 1 + q - i) c
  have law := sum_pascal p f (iterate_sequence_finite a b c (p + 1 + q) r)
  simpa only [iterateSum, iterateTerm, f, Nat.cast_add, Nat.cast_one,
    show p + (q + 1) = p + 1 + q by omega,
    show ∀ i : ℕ, r + ((i : ℤ) + 1) = r + 1 + i by intro i; omega,
    show ∀ i : ℕ, p + 1 + q - ((i : ℤ) + 1) = p + q - i by intro i; omega]
    using law

private theorem product_pascal (a b c : State) (p q r : ℤ) :
    productSum a b c p q (r + 1) =
      productSum a b c (p + 1) q r - productSum a b c p (q + 1) r := by
  let f (i : ℕ) := mode a (p + (r + 1) - i) (mode b (q + i) c)
  have law := signed_sum_pascal r f (product_sequence_finite a b c (p + (r + 1)) q)
  simpa only [productSum, productTerm, f, Nat.cast_add, Nat.cast_one,
    show p + (r + 1) = p + 1 + r by omega,
    show ∀ i : ℕ, p + 1 + r - ((i : ℤ) + 1) = p + r - i by intro i; omega,
    show ∀ i : ℕ, q + ((i : ℤ) + 1) = q + 1 + i by intro i; omega]
    using law

private theorem epsilon_succ (r : ℤ) : epsilon (r + 1) = -epsilon r := by
  rw [epsilon, epsilon, zpow_add₀ (by norm_num)]
  norm_num

private def defect (s : ℂ) (a b c : State) (p q r : ℤ) : State :=
  iterateSum a b c p q r -
    (productSum a b c p q r - (epsilon r * s) • productSum b a c q p r)

private theorem defect_pascal (s : ℂ) (a b c : State) (p q r : ℤ) :
    defect s a b c (p + 1) q r =
      defect s a b c p (q + 1) r + defect s a b c p q (r + 1) := by
  unfold defect
  rw [iterate_pascal, product_pascal a b c p q, product_pascal b a c q p, epsilon_succ]
  module

private theorem product_zero (a b c : State) (p q : ℤ) :
    productSum a b c p q 0 = mode a p (mode b q c) := by
  unfold productSum
  rw [finsum_eq_single _ 0]
  · simp [productTerm]
  · intro i hi
    simp [productTerm, chooseSign, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

/-- The signed product difference at a nonnegative parameter is one coefficient
of the corresponding finite power of the locality operator. -/
private theorem positive_product (s : ℂ) (a b c : State) (p q : ℤ) (r : ℕ) :
    productSum a b c p q r - (epsilon r * s) • productSum b a c q p r =
      (delta^[r] (signedComm s (Y a) (Y b))) p q c := by
  induction r generalizing p q with
  | zero =>
    simp only [Nat.cast_zero, product_zero, epsilon, zpow_zero, one_mul,
      Function.iterate_zero_apply, signedComm, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.mul_apply, mode]
  | succ r ih =>
    rw [Nat.cast_succ, product_pascal a b c p q, product_pascal b a c q p,
      epsilon_succ, Function.iterate_succ_apply']
    change _ = (delta^[r] (signedComm s (Y a) (Y b))) (p + 1) q c -
      (delta^[r] (signedComm s (Y a) (Y b))) p (q + 1) c
    rw [← ih (p + 1) q, ← ih p (q + 1)]
    module

/-- The full integer coefficient super-Borcherds identity for the native field.
All three coefficient families have finite support after evaluation on the
arbitrary third state. The modes are the normalized modes of the actual field. -/
theorem homogeneous_borcherds (a b c : State) (pa pb : ℕ)
    (ha : parity a = (-1 : ℂ) ^ pa • a) (hb : parity b = (-1 : ℂ) ^ pb • b) (p q r : ℤ) :
    let μ := fun (x : State) (n : ℤ) (y : State) => ((Y x)[[n]]) y
    let iterate := fun i : ℕ => integerBinomial p i • μ (μ a (r + i) b) (p + q - i) c
    let forward := fun i : ℕ =>
      ((-1 : ℂ) ^ i * integerBinomial r i) • μ a (p + r - i) (μ b (q + i) c)
    let reverse := fun i : ℕ =>
      ((-1 : ℂ) ^ i * integerBinomial r i) • μ b (q + r - i) (μ a (p + i) c)
    Function.HasFiniteSupport iterate ∧ Function.HasFiniteSupport forward ∧
      Function.HasFiniteSupport reverse ∧
      (∑ᶠ i : ℕ, iterate i) = (∑ᶠ i : ℕ, forward i) -
        (epsilon r * (-1 : ℂ) ^ (pa * pb)) • (∑ᶠ i : ℕ, reverse i) := by
  let s : ℂ := (-1 : ℂ) ^ (pa * pb)
  change Function.HasFiniteSupport (iterateTerm a b c p q r) ∧
    Function.HasFiniteSupport (productTerm a b c p q r) ∧
    Function.HasFiniteSupport (productTerm b a c q p r) ∧
    iterateSum a b c p q r = productSum a b c p q r - (epsilon r * s) • productSum b a c q p r
  refine ⟨(iterate_sequence_finite a b c (p + q) r).smul_right (integerBinomial p),
    (product_sequence_finite a b c (p + r) q).smul_right (chooseSign r),
    (product_sequence_finite b a c (q + r) p).smul_right (chooseSign r),
    sub_eq_zero.mp ?_⟩
  change defect s a b c p q r = 0
  have zeroSeed (n t : ℤ) : defect s a b c 0 n t = 0 := by
    have closure := residueClosure a b pa pb ha hb t
    have seed : mode (mode a t b) n c =
        productSum a b c 0 n t - (epsilon t * s) • productSum b a c n 0 t := by
      change ((Y (mode a t b))[[n]]) c = _
      rw [closure, (residueField s t (Y a) (Y b)).coefficient]
      simp only [residueCoefficient, residueLeft, residueRight, productSum, productTerm,
        chooseSign, integerBinomial, mode, zero_add, add_comm t n]
    unfold defect iterateSum
    rw [finsum_eq_single _ 0]
    · simpa [iterateTerm, integerBinomial] using sub_eq_zero.mpr seed
    · intro i hi
      simp [iterateTerm, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
  obtain ⟨localityOrder, killed⟩ := stateField_locality a b pa pb ha hb
  obtain ⟨modeCutoff, vanish⟩ := Y_truncation a b
  let cutoff : ℤ := max modeCutoff localityOrder
  have highSeed (m n t : ℤ) (ht : cutoff ≤ t) : defect s a b c m n t = 0 := by
    have hm : modeCutoff ≤ t := (le_max_left _ _).trans ht
    have hl : (localityOrder : ℤ) ≤ t := (le_max_right _ _).trans ht
    have iterateZero : iterateSum a b c m n t = 0 := by
      unfold iterateSum
      apply finsum_eq_zero_of_forall_eq_zero
      intro i
      unfold iterateTerm
      have hz : mode a (t + i) b = 0 := vanish _ (by omega)
      rw [hz]
      simp [mode]
    obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ t by omega)
    change delta^[localityOrder] (signedComm s (Y a) (Y b)) = 0 at killed
    have highLocal := FiniteFieldLocality.monotone (signedComm s (Y a) (Y b))
      localityOrder degree (by omega) killed
    simp only [defect, iterateZero, positive_product, highLocal, Pi.zero_apply,
      LinearMap.zero_apply, sub_zero]
  have positive (m : ℕ) : ∀ n t : ℤ, defect s a b c m n t = 0 := by
    induction m with
    | zero => exact zeroSeed
    | succ m ih =>
      intro n t
      rw [Nat.cast_succ, defect_pascal, ih, ih, add_zero]
  -- At each lower third index the induction on the first index keeps the
  -- second index universally quantified, since each backward step shifts it.
  have negative (d : ℕ) : ∀ (m : ℕ) (n : ℤ), defect s a b c (-(m : ℤ)) n (cutoff - d) = 0 := by
    induction d with
    | zero => intro m n; exact highSeed _ _ _ (by omega)
    | succ d outer =>
      intro m
      induction m with
      | zero => intro n; exact zeroSeed _ _
      | succ m inner =>
        intro n
        have step := defect_pascal s a b c (-((m + 1 : ℕ) : ℤ)) (n - 1)
          (cutoff - (d + 1 : ℕ))
        rw [show -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) by omega,
          show n - 1 + 1 = n by omega,
          show cutoff - (d + 1 : ℕ) + 1 = cutoff - d by omega,
          inner, outer, add_zero] at step
        exact step.symm
  by_cases hp : 0 ≤ p
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    exact positive m q r
  by_cases hr : cutoff ≤ r
  · exact highSeed p q r hr
  rw [show p = -((-p).toNat : ℤ) by omega,
    show r = cutoff - ((cutoff - r).toNat : ℤ) by omega]
  exact negative _ _ _

#print axioms residueClosure
#print axioms defect_pascal
#print axioms positive_product
#print axioms homogeneous_borcherds

end
end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTSuperJacobi
