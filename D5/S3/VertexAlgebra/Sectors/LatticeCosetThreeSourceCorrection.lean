/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetThreeSourceCorrection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetThreeSourceCorrection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact all-state native three-source Schur projection correction. -/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetOperatorCorrection

/-! Native transverse creation is retained through the middle field. All
convolutions are justified by statewise truncation before reindexing.
The native lattice convention is Bakalov--Kac, math/0402315v1, section 4.1. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeCosetThreeSourceCorrection

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeDiscriminantTheta
open LatticeCosetCompression LatticeCosetTransverse LatticeCosetSeparation
open LatticeCosetFieldSeparation LatticeCosetProjectedAction
open LatticeCosetCreationSeparation LatticeCosetOperatorCorrection MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

open private multiply_mul multiply_add multiply_C polynomialMode_monomial from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetProjectedAction
open private multiply_single from D5.S3.VertexAlgebra.Sectors.LatticeCosetSeparation
open private map_finsum_linear from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetFieldSeparation
open private reconstruction_finite mixed_injection from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetOperatorCorrection
open private derivative_map solution_unique from
  D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open private exponential_derivative from D5.S3.VertexAlgebra.LatticeSugawaraConformal

private def multiplyCoefficient (F : LatticeData) (v : Carrier F) :
    Oscillator F →ₗ[ℂ] Carrier F where
  toFun f := multiply F f v
  map_add' f g := multiply_add F f g v
  map_smul' s f := by
    rw [MvPolynomial.smul_eq_C_mul, multiply_mul, multiply_C]
    rfl

private def retainedMode (F : LatticeData) (A : ℤ → Carrier F) (m : ℤ) :
    Polynomial (Oscillator F) →ₗ[ℂ] Carrier F :=
  Polynomial.lsum (fun j => multiplyCoefficient F (A (m-j)))

private theorem retainedMode_monomial (F : LatticeData) (A : ℤ → Carrier F)
    (m : ℤ) (j : ℕ) (f : Oscillator F) :
    retainedMode F A m (Polynomial.monomial j f) = multiply F f (A (m-j)) := by
  change (Polynomial.monomial j f).sum (fun k g => multiply F g (A (m-k))) = _
  apply Polynomial.sum_monomial_index
  change multiplyCoefficient F (A (m-j)) 0 = 0
  exact map_zero _

private theorem retainedMode_C_mul (F : LatticeData) (A : ℤ → Carrier F)
    (m : ℤ) (f : Oscillator F) (q : Polynomial (Oscillator F)) :
    retainedMode F A m (Polynomial.C f * q) =
      multiply F f (retainedMode F A m q) := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => simp only [mul_add, map_add, hq, hr]
  | monomial j g =>
    rw [Polynomial.C_mul_monomial, retainedMode_monomial, retainedMode_monomial,
      multiply_mul]

private theorem retainedMode_X_pow (F : LatticeData) (A : ℤ → Carrier F)
    (m : ℤ) (r : ℕ) (q : Polynomial (Oscillator F)) :
    retainedMode F A m (Polynomial.X^r * q) = retainedMode F A (m-r) q := by
  induction q using Polynomial.induction_on' with
  | add q q' h h' => simp only [mul_add, map_add, h, h']
  | monomial d z =>
    rw [Polynomial.X_pow_mul_monomial, retainedMode_monomial, retainedMode_monomial]
    congr 2
    push_cast
    omega

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

private def retainedTranslation (a : Fin e → ℤ) :
    MvPolynomial (Fin e × ℕ) ℂ →ₐ[ℂ] Polynomial (Oscillator (ambient D e B C hC hCe)) :=
  aeval (fun x => Polynomial.C (transverse D B C hC hCe x.1 x.2) -
    Polynomial.C ((transversePair D B C a x.1 : ℂ) • 1) * Polynomial.X^(x.2+1))

private theorem retained_polynomial (hD : (gramReal D).PosDef)
    (a : Fin e → ℤ) (u : Carrier D) (h : MvPolynomial (Fin e × ℕ) ℂ) (m : ℤ)
    (v : Carrier (ambient D e B C hC hCe)) :
    ((Y (ambient D e B C hC hCe) (injection D B C hC hCe a u))[[m]])
        (multiply _ (transversePolynomial D B C hC hCe h) v) =
      retainedMode _ (fun t =>
        ((Y (ambient D e B C hC hCe) (injection D B C hC hCe a u))[[t]]) v) m
          (retainedTranslation D B C hC hCe a h) := by
  induction h using MvPolynomial.induction_on generalizing m v with
  | C z =>
    simp only [transversePolynomial, aeval_C, retainedTranslation]
    simp only [MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self]
    rw [multiply_C, map_smul]
    change _ = retainedMode _ _ m (Polynomial.monomial 0 (MvPolynomial.C z))
    rw [retainedMode_monomial, multiply_C]
    simp
  | add f g hf hg =>
    simp only [map_add, multiply_add, hf, hg]
  | mul_X f x hf =>
    have hx : multiply _ (transversePolynomial D B C hC hCe (f * X x)) v =
        multiply _ (transverse D B C hC hCe x.1 x.2)
          (multiply _ (transversePolynomial D B C hC hCe f) v) := by
      rw [map_mul]
      simp only [transversePolynomial, aeval_X]
      rw [mul_comm, multiply_mul]
    rw [hx, field_transverse_commutator D B C hC hCe hD, hf, hf]
    simp only [map_mul, retainedTranslation, aeval_X]
    rw [mul_comm _ (Polynomial.C _ - _), sub_mul, map_sub,
      retainedMode_C_mul, mul_assoc, retainedMode_C_mul, retainedMode_X_pow]
    rw [show ((transversePair D B C a x.1 : ℂ) •
      (1 : Oscillator (ambient D e B C hC hCe))) = MvPolynomial.C
        (transversePair D B C a x.1 : ℂ) by simp [MvPolynomial.smul_eq_C_mul], multiply_C]

private theorem retained_series (a b : Fin e → ℤ) :
    PowerSeries.map (retainedTranslation D B C hC hCe a).toRingHom
        (creationSeries (externalLattice C hC hCe) b) =
      PowerSeries.map ((Polynomial.CAlgHom.comp
        (transversePolynomial D B C hC hCe)).toRingHom)
          (creationSeries (externalLattice C hC hCe) b) +
      PowerSeries.map (((Polynomial.mapAlgHom (Algebra.ofId ℂ
        (Oscillator (ambient D e B C hC hCe)))).comp
          (scalarTranslation D B C a)).toRingHom)
            (creationSeries (externalLattice C hC hCe) b) := by
  classical
  apply PowerSeries.ext
  intro q
  rw [map_add, PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
  by_cases hq : q = 0
  · simp [creationSeries, hq]
  · simp only [creationSeries, PowerSeries.coeff_mk, dite_eq_right hq]
    change retainedTranslation D B C hC hCe a ((q : ℂ)⁻¹ • ∑ x : Fin e,
        (b x : ℂ) • X (x,q-1)) =
      (Polynomial.CAlgHom : Oscillator (ambient D e B C hC hCe) →ₐ[ℂ]
        Polynomial (Oscillator (ambient D e B C hC hCe))) (transversePolynomial D B C hC hCe
        ((q : ℂ)⁻¹ • ∑ x : Fin e, (b x : ℂ) • X (x,q-1))) +
      (Polynomial.mapAlgHom (Algebra.ofId ℂ (Oscillator (ambient D e B C hC hCe))))
        (scalarTranslation D B C a ((q : ℂ)⁻¹ • ∑ x : Fin e, (b x : ℂ) • X (x,q-1)))
    have hx (x : Fin e × ℕ) : retainedTranslation D B C hC hCe a (X x) =
        (Polynomial.CAlgHom : Oscillator (ambient D e B C hC hCe) →ₐ[ℂ]
          Polynomial (Oscillator (ambient D e B C hC hCe)))
            (transversePolynomial D B C hC hCe (X x)) +
        (Polynomial.mapAlgHom (Algebra.ofId ℂ (Oscillator (ambient D e B C hC hCe))))
          (scalarTranslation D B C a (X x)) := by
      simp [retainedTranslation, transversePolynomial, scalarTranslation,
        Polynomial.mapAlgHom, MvPolynomial.smul_eq_C_mul, sub_eq_add_neg]
    simp only [map_smul, map_sum, hx, smul_add, Finset.sum_add_distrib]

private theorem retained_exponential (a b : Fin e → ℤ) :
    PowerSeries.map (retainedTranslation D B C hC hCe a).toRingHom
        (creationExponential (externalLattice C hC hCe) b) =
      PowerSeries.map ((Polynomial.CAlgHom.comp
        (transversePolynomial D B C hC hCe)).toRingHom)
          (creationExponential (externalLattice C hC hCe) b) *
      PowerSeries.map (((Polynomial.mapAlgHom (Algebra.ofId ℂ
        (Oscillator (ambient D e B C hC hCe)))).comp
          (scalarTranslation D B C a)).toRingHom)
            (creationExponential (externalLattice C hC hCe) b) := by
  let : Algebra (Polynomial (Oscillator (ambient D e B C hC hCe)))
      (PowerSeries (Polynomial (Oscillator (ambient D e B C hC hCe)))) :=
    MvPowerSeries.instAlgebra
  let f := creationExponential (externalLattice C hC hCe) b
  let S := creationSeries (externalLattice C hC hCe) b
  let R := (retainedTranslation D B C hC hCe a).toRingHom
  let T := ((Polynomial.CAlgHom.comp (transversePolynomial D B C hC hCe)).toRingHom)
  let H := (((Polynomial.mapAlgHom (Algebra.ofId ℂ
    (Oscillator (ambient D e B C hC hCe)))).comp (scalarTranslation D B C a)).toRingHom)
  have hd := exponential_derivative (externalLattice C hC hCe) b
  have hr : PowerSeries.derivative (R := Polynomial (Oscillator (ambient D e B C hC hCe)))
      (f.map R) = f.map R * PowerSeries.derivative (S.map R) := by
    rw [derivative_map, hd, map_mul, derivative_map]
  have ht : PowerSeries.derivative (R := Polynomial (Oscillator (ambient D e B C hC hCe)))
      (f.map T) = f.map T * PowerSeries.derivative (S.map T) := by
    rw [derivative_map, hd, map_mul, derivative_map]
  have hh : PowerSeries.derivative (R := Polynomial (Oscillator (ambient D e B C hC hCe)))
      (f.map H) = f.map H * PowerSeries.derivative (S.map H) := by
    rw [derivative_map, hd, map_mul, derivative_map]
  have hs : S.map R = S.map T + S.map H := retained_series D B C hC hCe a b
  apply solution_unique (f.map R) (f.map T * f.map H)
    (PowerSeries.derivative (S.map R)) hr
  · have hp := (PowerSeries.derivative (R := Polynomial (Oscillator
        (ambient D e B C hC hCe)))).leibniz' (f.map T) (f.map H)
    change PowerSeries.derivative (R := Polynomial (Oscillator (ambient D e B C hC hCe)))
      (f.map T * f.map H) = f.map T * PowerSeries.derivative (f.map H) +
        f.map H * PowerSeries.derivative (f.map T) at hp
    rw [hp, ht, hh, hs, map_add]
    ring
  · have hc : PowerSeries.coeff 0 f = 1 :=
      LatticeSugawaraConformal.exponential_constant (externalLattice C hC hCe) b
    simp only [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton, PowerSeries.coeff_map, hc, map_one, one_mul]

private theorem retained_coefficient (hD : (gramReal D).PosDef)
    (a b : Fin e → ℤ) (n : ℕ) :
    retainedTranslation D B C hC hCe a
        (PowerSeries.coeff n (creationExponential (externalLattice C hC hCe) b)) =
      ∑ k ∈ Finset.range (n+1), correction D B C a b k •
        (Polynomial.C (transversePolynomial D B C hC hCe
          (PowerSeries.coeff (n-k) (creationExponential (externalLattice C hC hCe) b))) *
            Polynomial.X^k) := by
  have hn := congrArg (PowerSeries.coeff n) (retained_exponential D B C hC hCe a b)
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mul,
    ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hn
  change retainedTranslation D B C hC hCe a _ = _ at hn
  rw [hn]
  apply Finset.sum_congr rfl
  intro k hk
  change Polynomial.C (transversePolynomial D B C hC hCe
      (PowerSeries.coeff (n-k) (creationExponential (externalLattice C hC hCe) b))) *
    (Polynomial.mapAlgHom (Algebra.ofId ℂ (Oscillator (ambient D e B C hC hCe))))
      (scalarTranslation D B C a
        (PowerSeries.coeff k (creationExponential (externalLattice C hC hCe) b))) = _
  rw [transverse_creation_coefficient D B C hC hCe hD, map_smul]
  simp only [Polynomial.coe_mapAlgHom, Polynomial.map_pow, Polynomial.map_X,
    mul_smul_comm]

/-- Before projection, the complete native field retains every residual
transverse creation coefficient, on an arbitrary ambient target state. -/
theorem field_transverse_creation (hD : (gramReal D).PosDef)
    (a b : Fin e → ℤ) (u : Carrier D) (m : ℤ) (n : ℕ)
    (z : Carrier (ambient D e B C hC hCe)) :
    ((Y (ambient D e B C hC hCe) (injection D B C hC hCe a u))[[m]])
      (multiply _ (transversePolynomial D B C hC hCe
        (PowerSeries.coeff n (creationExponential (externalLattice C hC hCe) b))) z) =
      ∑ k ∈ Finset.range (n+1), correction D B C a b k •
        multiply _ (transversePolynomial D B C hC hCe
          (PowerSeries.coeff (n-k) (creationExponential (externalLattice C hC hCe) b)))
            (((Y (ambient D e B C hC hCe) (injection D B C hC hCe a u))[[m-k]]) z) := by
  rw [retained_polynomial D B C hC hCe hD, retained_coefficient D B C hC hCe hD,
    map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul, Polynomial.C_mul_X_pow_eq_monomial, retainedMode_monomial]

private theorem joint_cutoff (b c d : Fin e → ℤ)
    (v t w : Carrier D) (q r : ℤ) :
    ∃ N M : ℕ, ∀ i j k : ℕ,
      N ≤ j+k ∨ M ≤ i →
        compressed D B C hC hCe b (c+d) v (q+i-k)
          (compressed D B C hC hCe c d t (r+j+k) w) = 0 := by
  classical
  obtain ⟨N,hN⟩ := compressed_high_modes D B C hC hCe c d t w r
  have hmid (s : ℕ × ℕ) : ∃ M : ℕ, ∀ i : ℕ, M ≤ i →
      compressed D B C hC hCe b (c+d) v (q+i-s.2)
        (compressed D B C hC hCe c d t (r+s.1+s.2) w) = 0 := by
    obtain ⟨M,hM⟩ := compressed_high_modes D B C hC hCe b (c+d) v
      (compressed D B C hC hCe c d t (r+s.1+s.2) w) (q-s.2)
    refine ⟨M, fun i hi => ?_⟩
    simpa only [show q-(s.2 : ℤ)+i = q+i-s.2 by omega] using hM i hi
  choose M hM using hmid
  refine ⟨N, ((Finset.range N).product (Finset.range N)).sup M, ?_⟩
  intro i j k h
  by_cases hn : N ≤ j+k
  · have hz := hN (j+k) hn
    rw [Nat.cast_add, ← add_assoc] at hz
    rw [hz, map_zero]
  · apply hM (j,k) i
    exact le_trans (Finset.le_sup (f := M)
      (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩)) (h.resolve_left hn)

private theorem correction_joint_finite (a b c d : Fin e → ℤ)
    (u v t w : Carrier D) (p q r : ℤ) :
    Function.HasFiniteSupport (fun s : ℕ × ℕ × ℕ =>
      (correction D B C a b s.1 * correction D B C a c s.2.1 *
        correction D B C b c s.2.2) •
      compressed D B C hC hCe a (b+(c+d)) u (p-s.1-s.2.1)
        (compressed D B C hC hCe b (c+d) v (q+s.1-s.2.2)
          (compressed D B C hC hCe c d t (r+s.2.1+s.2.2) w))) := by
  classical
  obtain ⟨N,M,hNM⟩ := joint_cutoff D B C hC hCe b c d v t w q r
  apply (Finset.finite_toSet ((Finset.range M).product
    ((Finset.range N).product (Finset.range N)))).subset
  rintro ⟨i,j,k⟩ hs
  apply Finset.mem_product.mpr
  have hm : i < M := by
    by_contra hi
    exact hs (by dsimp only; rw [hNM i j k (Or.inr (by omega)), map_zero, smul_zero])
  have hn : j+k < N := by
    by_contra hjk
    exact hs (by dsimp only; rw [hNM i j k (Or.inl (by omega)), map_zero, smul_zero])
  change i ∈ Finset.range M ∧ (j,k) ∈ (Finset.range N).product (Finset.range N)
  exact ⟨Finset.mem_range.mpr hm, Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩

private theorem triangular_finsum {V : Type} [AddCommGroup V]
    (f : ℕ × ℕ × ℕ → V) (hf : Function.HasFiniteSupport f) :
    (∑ᶠ n : ℕ, ∑ k ∈ Finset.range (n+1), ∑ᶠ i : ℕ, f (i,n-k,k)) = ∑ᶠ s, f s := by
  classical
  let φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun s => (s.2.1+s.2.2,s.2.2,s.1)
  let g : ℕ × ℕ × ℕ → V := fun s => if s.2.1 ≤ s.1 then f (s.2.2,s.1-s.2.1,s.2.1) else 0
  have hφ : Function.Injective φ := by
    rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ hh
    simp only [φ, Prod.mk.injEq] at hh
    rcases hh with ⟨hn,hk,hi⟩
    have hj : j = j' := by omega
    simp [hi,hj,hk]
  have hget (s : ℕ × ℕ × ℕ) : g (φ s) = f s := by
    rcases s with ⟨i,j,k⟩
    simp [g,φ]
  have hs : Function.support g ⊆ φ '' Function.support f := by
    rintro ⟨n,k,i⟩ hh
    change (if k ≤ n then f (i,n-k,k) else 0) ≠ 0 at hh
    by_cases hkn : k ≤ n
    · refine ⟨(i,n-k,k), ?_, ?_⟩
      · simpa only [Function.mem_support, ite_eq_left hkn] using hh
      · dsimp only [φ]
        congr 1
        omega
    · exact (hh (ite_eq_right hkn)).elim
  have hg : Function.HasFiniteSupport g := (hf.image φ).subset hs
  have hr : (∑ᶠ s ∈ Set.range φ, g s) = ∑ᶠ s, g s := by
    rw [← finsum_mem_univ g]
    apply finsum_mem_inter_support_eq'
    intro s hh
    exact iff_of_true (by obtain ⟨x,hx,h⟩ := hs hh; exact ⟨x,h⟩) (Set.mem_univ s)
  calc
    _ = ∑ᶠ n : ℕ, ∑ᶠ k : ℕ, ∑ᶠ i : ℕ, g (n,k,i) := by
      apply finsum_congr
      intro n
      rw [finsum_eq_sum_of_support_subset (s := Finset.range (n+1)) _ (by
        intro k hk
        apply Finset.mem_range.mpr
        by_contra hn
        exact hk (by simp [g, show ¬ k ≤ n by omega]))]
      apply Finset.sum_congr rfl
      intro k hk
      apply finsum_congr
      intro i
      simp [g, show k ≤ n by have := Finset.mem_range.mp hk; omega]
    _ = ∑ᶠ s, g s := (finsum_curry₃ g hg).symm
    _ = ∑ᶠ s ∈ Set.range φ, g s := hr.symm
    _ = ∑ᶠ s, g (φ s) := finsum_mem_range hφ
    _ = _ := finsum_congr hget

local notation "E" => ambient D e B C hC hCe
local notation "J" => injection D B C hC hCe
local notation "P" => projection D B C hC hCe
local notation "I" => compressed D B C hC hCe
local notation "K" => correction D B C

/-- The exact native all-state three-source projection has all three pairwise
Schur factors. Its joint natural-index support is finite by inner truncation
and then middle truncation on each actual resulting inner state. -/
theorem three_source_projection_correction (hD : (gramReal D).PosDef)
    (a b c d : Fin e → ℤ) (u v t w : Carrier D) (p q r : ℤ) :
    Function.HasFiniteSupport (fun s : ℕ × ℕ × ℕ =>
      (K a b s.1 * K a c s.2.1 * K b c s.2.2) •
        I a (b+(c+d)) u (p-s.1-s.2.1)
          (I b (c+d) v (q+s.1-s.2.2) (I c d t (r+s.2.1+s.2.2) w))) ∧
    P (a+(b+(c+d)))
      (((Y E (J a u))[[p]])
        (((Y E (J b v))[[q]]) (((Y E (J c t))[[r]]) (J d w)))) =
      ∑ᶠ s : ℕ × ℕ × ℕ, (K a b s.1 * K a c s.2.1 * K b c s.2.2) •
        I a (b+(c+d)) u (p-s.1-s.2.1)
          (I b (c+d) v (q+s.1-s.2.2) (I c d t (r+s.2.1+s.2.2) w)) := by
  classical
  let f : ℕ × ℕ × ℕ → Carrier D := fun s =>
    (K a b s.1 * K a c s.2.1 * K b c s.2.2) •
      I a (b+(c+d)) u (p-s.1-s.2.1)
        (I b (c+d) v (q+s.1-s.2.2) (I c d t (r+s.2.1+s.2.2) w))
  have hf : Function.HasFiniteSupport f := correction_joint_finite D B C hC hCe a b c d u v t w p q r
  refine ⟨hf, ?_⟩
  change _ = ∑ᶠ s, f s
  rw [← triangular_finsum f hf, inner_creation_expansion D B C hC hCe hD c d t w r]
  let L := ((P (a+(b+(c+d)))).comp ((Y E (J a u))[[p]])).comp ((Y E (J b v))[[q]])
  change L (∑ᶠ n : ℕ, mixedState D B C hC hCe (c+d)
    (PowerSeries.coeff n (creationExponential (externalLattice C hC hCe) c))
      (I c d t (r+n) w)) = _
  rw [map_finsum_linear L _ (reconstruction_finite D B C hC hCe c d t w r)]
  apply finsum_congr
  intro n
  dsimp only [L, LinearMap.comp_apply]
  rw [mixed_injection D B C hC hCe,
    field_transverse_creation D B C hC hCe hD, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul, map_smul,
    projected_transverse_polynomial D B C hC hCe hD,
    transverse_creation_coefficient D B C hC hCe hD, map_smul,
    Polynomial.X_pow_eq_monomial, polynomialMode_monomial, one_smul]
  have he := intermediate_projection_correction D B C hC hCe hD a b (c+d) u v
    (I c d t (r+n) w) (p-(n-k : ℕ)) (q-k)
  rw [add_assoc] at he
  rw [he.2, smul_finsum' _ he.1]
  rw [smul_finsum' _ (he.1.fun_comp (smul_zero _))]
  apply finsum_congr
  intro i
  dsimp only [f, Prod.fst, Prod.snd]
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  have hc : r+(n-k : ℕ)+k = r+n := by omega
  have hp : p-(n-k : ℕ)-i = p-i-(n-k : ℕ) := by omega
  have hq : q-(k : ℤ)+i = q+i-k := by omega
  rw [hc,hp,hq]
  simp only [smul_smul]
  congr 1
  ring

end
end D5.S3.VertexAlgebra.LatticeCosetThreeSourceCorrection
