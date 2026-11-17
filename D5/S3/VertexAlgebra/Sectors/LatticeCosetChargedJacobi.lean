/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetChargedJacobi
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetChargedJacobi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual all-state charged Borcherds descent by finite triangular convolution. -/

/-
Delivery metadata: source-only semantic assessment, not a machine verdict.
proof_shape: charged_borcherds: content (semantic source assessment).
escape_witness: Projected all-state Jacobi with the actual source and product
corrections, combined by finite triangular convolution on vector tail cutoffs.
The consumed source_mixed/exact_source_probe chain retains the original
translation, full Schur correction, cocycle and signed modes.
admission_basis: escape-witness (proposed; no current acceptance claimed).
utility: none. These are general algebraic identities on arbitrary states and
ranks, not bounded enumeration, a checker, numeric reduction or a certified
finite instance. Bind-only normalization/cutoff helpers are genuinely consumed.
Attribution: supplied original source; source-contraction supplier
LatticeCosetSourceSkewProbe.lean, SHA256
73fa8b8332d3fa5e57ebe74d853682c869cf39031724cdc088191c004e5a84ce;
Bakalov--Kac math/0402315v1 section 4.1; native residue/Sugawara supplier
attributions remain with Scott Carnahan and Kalle Kytölä in their sources.

Both modules: preserve every original signature/quantifier, finite rank zero,
arbitrary integral B, symmetric even C, all original finite charge/oscillator
states, all signed modes/cutoffs, positive ORIGINAL G only, full Schur and
original epsilon. No analytic sewing, actual quotient F/exchange, scalar
polynomiality, categorical realization, string/AdS completion or literature
novelty claim.

Delivery status: metadata entries above are the supplied proposals for final
integration, not an admission, mirror generation, waiver approval or freeze.
The exact preserved native source suffix has supplied compiled evidence.
This metadata-modified candidate still requires real final integration checks;
the supplied native receipts do not validate these changed file bytes.
-/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetOperatorCorrection
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetVirasoro
import D5.S3.VertexAlgebra.StateField.SkewSymmetry
import D5.S3.VertexAlgebra.LatticeAllStateJacobi
import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
All-state charged Borcherds identity for the actual compressed lattice fields.
Only the ORIGINAL Gram form is positive definite. The ambient symmetric even
block form may be degenerate or indefinite; original and external rank zero
are included. This is an algebraic coefficient identity, not analytic sewing,
tensor-category coherence, CFT realization, or completion of the string goal.

Source-contraction proof attribution: LatticeCosetSourceSkewProbe.lean,
SHA256 73fa8b8332d3fa5e57ebe74d853682c869cf39031724cdc088191c004e5a84ce.
The source contraction has choose(S(a,c),n), with NO extra (-1)^n.

The new content is the finite triangular binomial convolution of these source
and product corrections with the actual ordinary all-state Jacobi identity.
Classical lattice conventions: Bakalov--Kac, math/0402315v1, section 4.1;
native residue/Sugawara supplier attributions remain with their source files.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetChargedJacobi

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeAllStateField
open LatticeSugawaraConformal LatticeSugawaraCurrents LatticeDiscriminantTheta
open LatticeCosetCompression LatticeCosetSeparation LatticeCosetCreationSeparation
open LatticeCosetProjectedAction LatticeCosetOperatorCorrection LatticeActualVertexAlgebra
open LatticeDualCosetConformal MvPolynomial Matrix
open scoped BigOperators VertexOperator

noncomputable section

open private projection_single from D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression
open private rat_unit pairRaw_symm from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open private polynomialMode_monomial from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetProjectedAction
open private map_finsum_linear from D5.S3.VertexAlgebra.Sectors.LatticeCosetFieldSeparation
open private reconstruction_finite mixed_injection from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetOperatorCorrection

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

local notation "E" => ambient D e B C hC hCe
local notation "π" => polynomialProjection D B C hC hCe
local notation "P" => projection D B C hC hCe
local notation "J" => injection D B C hC hCe
local notation "I" => compressed D B C hC hCe
local notation "S" => schur D B C
local notation "H" => Matrix.map (inverseRat D) (Rat.castHom ℂ)
local notation "T[" d "]" => moduleL D (Matrix.mulVec B d) H (-1)
local notation "χ[" a "," n "]" =>
  PowerSeries.coeff n (creationExponential (externalLattice C hC hCe) a)

private theorem projection_oscillator_derivation (p : Oscillator E) :
    π (oscillatorDerivation E p) = oscillatorDerivation D (π p) := by
  letI : Algebra (Oscillator E) (Oscillator D) := (π).toRingHom.toAlgebra
  letI : IsScalarTower ℂ (Oscillator E) (Oscillator D) := IsScalarTower.of_algHom π
  let L : Oscillator E →ₗ[Oscillator E] Oscillator D := Algebra.linearMap _ _
  have hx (i : Fin (D.rank+e)) (k : ℕ) :
      π (X (i,k)) = projectionVariable D B C hC hCe (i,k) := by
    simp [polynomialProjection]
  have h : L.compDer (oscillatorDerivation E) =
      (oscillatorDerivation D).compAlgebraMap (Oscillator E) := by
    apply MvPolynomial.derivation_ext
    rintro ⟨i,k⟩
    change π (oscillatorDerivation E (X (i,k))) =
      oscillatorDerivation D (π (X (i,k)))
    rw [show oscillatorDerivation E (X (i,k)) =
      (k+1 : ℂ) • X (i,k+1) by simp [oscillatorDerivation, MvPolynomial.mkDerivation_X],
      map_smul, hx, hx]
    induction i using Fin.addCases with
    | left i =>
      simp [projectionVariable, oscillatorDerivation, MvPolynomial.mkDerivation_X]
    | right i =>
      simp only [projectionVariable, Fin.addCases_right, map_sum, Derivation.map_smul,
        oscillatorDerivation, MvPolynomial.mkDerivation_X]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun j _ => smul_comm _ _ _)
  exact DFunLike.congr_fun h p

private theorem projection_translation (hD : (gramReal D).PosDef) (d : Fin e → ℤ) :
    Function.Semiconj (P d) (translation E) T[d] := by
  classical
  have hG : (gramRat D).map (Rat.castHom ℂ) = gramComplex D := by
    apply Matrix.ext
    intro i j
    simp [gramRat, gramComplex, Matrix.map_apply, Rat.cast_intCast]
  have hHG : H * gramComplex D = 1 := by
    have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℚ =>
      M.map (Rat.castHom ℂ)) (Matrix.nonsing_inv_mul (gramRat D) (rat_unit D hD))
    simpa only [inverseRat, Matrix.map_mul,
      Matrix.map_one _ (map_zero (Rat.castHom ℂ)) (map_one (Rat.castHom ℂ)), hG] using h
  have hGH : gramComplex D * H = 1 := by
    have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℚ =>
      M.map (Rat.castHom ℂ)) (Matrix.mul_nonsing_inv (gramRat D) (rat_unit D hD))
    simpa only [inverseRat, Matrix.map_mul,
      Matrix.map_one _ (map_zero (Rat.castHom ℂ)) (map_one (Rat.castHom ℂ)), hG] using h
  let U (i : Fin D.rank) : ℂ :=
    ∑ j, (longitudinal D B i j : ℂ) * (d j : ℂ)
  have huQ : Matrix.mulVec (longitudinal D B) (fun j => (d j : ℚ)) =
      Matrix.mulVec (inverseRat D) (fun k => ((Matrix.mulVec B d k : ℤ) : ℚ)) := by
    have hv : Matrix.mulVec (B.map (Int.castRingHom ℚ)) (fun j => (d j : ℚ)) =
        fun k => ((Matrix.mulVec B d k : ℤ) : ℚ) := by
      funext k
      simp [Matrix.mulVec_apply_eq_sum, Matrix.map_apply, Int.cast_sum, Int.cast_mul]
    rw [longitudinal, ← Matrix.mulVec_mulVec, hv]
  have hu (i : Fin D.rank) :
      U i = ∑ k, H i k * ((Matrix.mulVec B d k : ℤ) : ℂ) := by
    have hi := congrFun huQ i
    simp only [Matrix.mulVec, dotProduct] at hi
    change (∑ j, (longitudinal D B i j : ℂ) * (d j : ℂ)) =
      ∑ k, (↑(inverseRat D i k) : ℂ) * ((Matrix.mulVec B d k : ℤ) : ℂ)
    exact_mod_cast hi
  have hGu : ∀ i, ∑ j, (D.G i j : ℂ) * U j = ((Matrix.mulVec B d i : ℤ) : ℂ) := by
    intro i
    simp only [hu]
    exact inverse_dual_vector D (Matrix.mulVec B d) H hGH i
  have hcharge (γ : Charge E) (hd : externalCharge D B C hC hCe γ = d) :
      π (chargePolynomial E γ) =
        ∑ i, ((oldCharge D B C hC hCe γ i : ℂ) + U i) • X (i,0) := by
    have hd' (j : Fin e) : γ (j.natAdd D.rank) = d j := congrFun hd j
    have hx (i : Fin (D.rank+e)) :
        π (X (i,0)) = projectionVariable D B C hC hCe (i,0) := by
      simp [polynomialProjection]
    simp only [chargePolynomial, map_add, map_sum, map_smul, hx, Fin.sum_univ_add,
      projectionVariable, Fin.addCases_left, Fin.addCases_right, oldCharge, hd',
      add_smul, Finset.sum_add_distrib]
    congr 1
    simp only [U, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (d j : ℂ)]
  have hl : (P d).comp (translation E) = T[d].comp (P d) := by
    apply Finsupp.lhom_ext
    intro γ p
    simp only [LinearMap.comp_apply, translation_single, projection_single]
    split_ifs with hd
    · rw [moduleL_minus_one_single D (Matrix.mulVec B d) H hHG hGH U hGu,
        map_add, map_mul, projection_oscillator_derivation, hcharge γ hd]
    · rw [map_zero]
  intro v
  exact DFunLike.congr_fun hl v

include hC in
private theorem schur_swap (a c : Fin e → ℤ) : S c a = S a c := by
  classical
  have hp (j k : Fin e) :
      (∑ i, (B i j : ℚ) * longitudinal D B i k) =
        pairRaw D (fun i => B i k) (fun i => B i j) := by
    simp only [pairRaw, dualVector, dotProduct, Matrix.mulVec, longitudinal,
      Matrix.mul_apply, Matrix.map_apply, Int.coe_castRingHom]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  have hswap (j k : Fin e) :
      (C j k : ℚ) - ∑ i, (B i j : ℚ) * longitudinal D B i k =
        (C k j : ℚ) - ∑ i, (B i k : ℚ) * longitudinal D B i j := by
    rw [hC j k, hp j k, hp k j, pairRaw_symm]
  unfold schur
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hswap j k]
  ring

private theorem reverse_contraction (hD : (gramReal D).PosDef)
    (a d c : Fin e → ℤ) (g w : Carrier D) (n : ℕ) (t : ℤ) :
    P (d+c) (((Y E (J c w))[[t]]) (mixedState D B C hC hCe d χ[a,n] g)) =
      correction D B C c a n • P (d+c) (((Y E (J c w))[[t-n]]) (J d g)) := by
  rw [mixed_injection D B C hC hCe, projected_transverse_polynomial D B C hC hCe hD,
    transverse_creation_coefficient D B C hC hCe hD,
    map_smul, Polynomial.X_pow_eq_monomial, polynomialMode_monomial, one_smul]

private theorem source_mixed (hD : (gramReal D).PosDef)
    (a d c : Fin e → ℤ) (g w : Carrier D) (n : ℕ) (m : ℤ) :
    P (d+c) (((Y E (mixedState D B C hC hCe d χ[a,n] g))[[m]]) (J c w)) =
      ((Ring.choose (S a c) n : ℚ) : ℂ) • I d c g (m-n) w := by
  let A := mixedState D B C hC hCe d χ[a,n] g
  let U := J d g
  let W := J c w
  let phase (k : ℤ) (j : ℕ) : ℂ :=
    (-1 : ℂ) ^ (k+(j : ℤ)+1) / (j.factorial : ℂ)
  let q : ℂ := ((Ring.choose (S a c) n : ℚ) : ℂ)
  let rev (k : ℤ) (v : Carrier E) (j : ℕ) : Carrier E :=
    phase k j • (translation E ^ j) (((Y E W)[[k+j]]) v)
  have hA := (StateField.SkewSymmetry.skew_symmetry (actualVertexAlgebra E) A W).1 m
  have hU := (StateField.SkewSymmetry.skew_symmetry (actualVertexAlgebra E) U W).1 (m-n)
  have hpow (j : ℕ) (v : Carrier E) :
      P (d+c) ((translation E ^ j) v) = (T[d+c] ^ j) (P (d+c) v) := by
    simpa only [Module.End.coe_pow] using
      (projection_translation D B C hC hCe hD (d+c)).iterate_right j v
  have hphase (j : ℕ) :
      phase m j * correction D B C c a n = q * phase (m-n) j := by
    have hz : m+(j : ℤ)+1 = (m-(n : ℤ)+(j : ℤ)+1) + (n : ℤ) := by omega
    have hsq : (-1 : ℂ)^n * (-1 : ℂ)^n = 1 := by
      rw [← mul_pow]
      norm_num
    have hc : correction D B C c a n = (-1 : ℂ)^n * q := by
      simp only [correction, schur_swap D B C hC a c, q]
    unfold phase
    rw [hz, zpow_add₀ (show (-1 : ℂ) ≠ 0 by norm_num), zpow_natCast, hc]
    calc
      _ = ((-1 : ℂ) ^ (m-(n : ℤ)+(j : ℤ)+1) / (j.factorial : ℂ)) *
          ((-1 : ℂ)^n * (-1 : ℂ)^n) * q := by ring
      _ = _ := by rw [hsq, mul_one, mul_comm]
  change P (d+c) (((Y E A)[[m]]) W) = q • P (d+c) (((Y E U)[[m-n]]) W)
  have hAf : Function.HasFiniteSupport (rev m A) := hA.1
  have hUf : Function.HasFiniteSupport (rev (m-n) U) := hU.1
  have hAs : ((Y E A)[[m]]) W = ∑ᶠ j, rev m A j := hA.2
  have hUs : ((Y E U)[[m-n]]) W = ∑ᶠ j, rev (m-n) U j := hU.2
  have hUPf : Function.HasFiniteSupport (fun j => P (d+c) (rev (m-n) U j)) :=
    hUf.subset (by
      intro j hj hz
      exact hj (by
        change P (d+c) (rev (m-n) U j) = 0
        rw [hz, map_zero]))
  rw [hAs, hUs, map_finsum_linear (P (d+c)) _ hAf,
    map_finsum_linear (P (d+c)) _ hUf, smul_finsum' q hUPf]
  apply finsum_congr
  intro j
  simp only [rev, map_smul, hpow]
  rw [show P (d+c) (((Y E W)[[m+j]]) A) =
      correction D B C c a n • P (d+c) (((Y E W)[[m+j-n]]) U) from
    reverse_contraction D B C hC hCe hD a d c g w n (m+j)]
  rw [show m+(j : ℤ)-(n : ℤ) = m-(n : ℤ)+(j : ℤ) by omega]
  simp only [map_smul, smul_smul, hphase]

private theorem exact_source_probe (hD : (gramReal D).PosDef)
    (a b c : Fin e → ℤ) (u v w : Carrier D) (r m : ℤ) :
    Function.HasFiniteSupport (fun n : ℕ => ((Ring.choose (S a c) n : ℚ) : ℂ) •
      I (a+b) c (I a b u (r+n) v) (m-n) w) ∧
    P (a+b+c) (((Y E (((Y E (J a u))[[r]]) (J b v)))[[m]]) (J c w)) =
      ∑ᶠ n : ℕ, ((Ring.choose (S a c) n : ℚ) : ℂ) •
        I (a+b) c (I a b u (r+n) v) (m-n) w := by
  classical
  constructor
  · obtain ⟨N,hN⟩ := compressed_high_modes D B C hC hCe a b u v r
    apply (Finset.finite_toSet (Finset.range N)).subset
    intro n hn
    apply Finset.mem_range.mpr
    by_contra hnot
    apply hn
    dsimp only
    rw [hN n (by omega)]
    simp [compressed]
  · let M : Carrier E →ₗ[ℂ] Carrier D :=
      (P (a+b+c)).comp
        ((LinearMap.applyₗ (R := ℂ) (J c w)).comp
          ((LinearMap.proj m).comp
            ((VertexOperator.ncoeff : VertexOperator ℂ (Carrier E) →ₗ[ℂ]
              ℤ → Module.End ℂ (Carrier E)).comp (Y E))))
    change M (((Y E (J a u))[[r]]) (J b v)) = _
    rw [inner_creation_expansion D B C hC hCe hD,
      map_finsum_linear M _ (reconstruction_finite D B C hC hCe a b u v r)]
    apply finsum_congr
    intro n
    exact source_mixed D B C hC hCe hD a (a+b) c (I a b u (r+n) v) w n m

open LatticeAllStateReconstruction LatticeAllStateJacobi
open StateFieldResidueReconstruction (integerBinomial)

/- No new summation API: finsum_curry and finsum_sum_filter perform the
reindexing. The cutoff below is on the actual vector sequence, not on either
binomial coefficient (which need not have finite support). -/
private theorem binomial_convolution {V : Type} [AddCommGroup V] [Module ℂ V]
    (x y : ℚ) (z : ℂ) (f : ℕ → V)
    (cutoff : ∃ N : ℕ, ∀ k : ℕ, N ≤ k → f k = 0) :
    (∑ᶠ i : ℕ, (z^i * ((Ring.choose x i : ℚ) : ℂ)) •
      (∑ᶠ j : ℕ, (z^j * ((Ring.choose y j : ℚ) : ℂ)) • f (i+j))) =
    ∑ᶠ k : ℕ, (z^k * ((Ring.choose (x+y) k : ℚ) : ℂ)) • f k := by
  classical
  obtain ⟨N,hN⟩ := cutoff
  let F : ℕ × ℕ → V := fun ij =>
    ((z^ij.1 * ((Ring.choose x ij.1 : ℚ) : ℂ)) *
      (z^ij.2 * ((Ring.choose y ij.2 : ℚ) : ℂ))) • f (ij.1+ij.2)
  let T : Finset (ℕ × ℕ) :=
    ((Finset.range N).product (Finset.range N)).filter (fun ij => ij.1+ij.2 < N)
  have zero_triangle (ij : ℕ × ℕ) (h : N ≤ ij.1+ij.2) : F ij = 0 := by
    simp only [F, hN _ h, smul_zero]
  have support_triangle : Function.support F ⊆ (T : Set (ℕ × ℕ)) := by
    intro ij hij
    have hlt : ij.1+ij.2 < N := by
      by_contra h
      exact hij (zero_triangle ij (by omega))
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩, hlt⟩
  have joint : Function.HasFiniteSupport F := T.finite_toSet.subset support_triangle
  have row (i : ℕ) : Function.HasFiniteSupport
      (fun j : ℕ => (z^j * ((Ring.choose y j : ℚ) : ℂ)) • f (i+j)) := by
    apply (Finset.finite_toSet (Finset.range N)).subset
    intro j hj
    apply Finset.mem_range.mpr
    by_contra h
    exact hj (by dsimp only; rw [hN (i+j) (by omega), smul_zero])
  have diagonal (k : ℕ) :
      (∑ ij ∈ T with ij.1+ij.2 = k, F ij) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, F ij := by
    apply Finset.sum_subset
    · intro ij hij
      exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (Finset.mem_filter.mp hij).2
    · intro ij hij hnot
      have hk : ij.1+ij.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      apply zero_triangle
      by_contra h
      apply hnot
      apply Finset.mem_filter.mpr
      refine ⟨?_,hk⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩, by omega⟩
  calc
    _ = ∑ᶠ i : ℕ, ∑ᶠ j : ℕ, F (i,j) := by
      apply finsum_congr
      intro i
      rw [smul_finsum' _ (row i)]
      apply finsum_congr
      intro j
      simp only [F, smul_smul]
    _ = ∑ᶠ ij : ℕ × ℕ, F ij := (finsum_curry F joint).symm
    _ = ∑ ij ∈ T, F ij := finsum_eq_sum_of_support_subset _ support_triangle
    _ = ∑ᶠ k : ℕ, ∑ ij ∈ T with ij.1+ij.2 = k, F ij :=
      (finsum_sum_filter (fun ij : ℕ × ℕ => ij.1+ij.2) T F).symm
    _ = ∑ᶠ k : ℕ, ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, F ij :=
      finsum_congr diagonal
    _ = _ := by
      apply finsum_congr
      intro k
      have vandermonde : ((Ring.choose (x+y) k : ℚ) : ℂ) =
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
            ((Ring.choose x ij.1 : ℚ) : ℂ) * ((Ring.choose y ij.2 : ℚ) : ℂ) := by
        exact_mod_cast (Ring.add_choose_eq (r := x) (s := y) k
          (show Commute x y from mul_comm x y))
      calc
        _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
            (z^k * (((Ring.choose x ij.1 : ℚ) : ℂ) *
              ((Ring.choose y ij.2 : ℚ) : ℂ))) • f k := by
          apply Finset.sum_congr rfl
          intro ij hij
          have hk : ij.1+ij.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
          dsimp only [F]
          rw [hk]
          congr 1
          calc
            _ = z^(ij.1+ij.2) * (((Ring.choose x ij.1 : ℚ) : ℂ) *
                ((Ring.choose y ij.2 : ℚ) : ℂ)) := by rw [pow_add]; ring
            _ = _ := by rw [hk]
        _ = _ := by rw [← Finset.sum_smul, ← Finset.mul_sum, ← vandermonde]

private theorem integer_choose (t : ℤ) (i : ℕ) :
    integerBinomial t i = ((Ring.choose (t : ℚ) i : ℚ) : ℂ) := by
  have h := Ring.map_choose (Int.castRingHom ℚ) t i
  have hc := congrArg (fun q : ℚ => (q : ℂ)) h
  simpa only [integerBinomial, Int.coe_castRingHom, Rat.cast_intCast] using hc

/- These are statewise truncation statements BEFORE scalar multiplication. -/
private theorem iterate_cutoff (a b c : Fin e → ℤ) (u v w : Carrier D) (r t : ℤ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      I (a+b) c (I a b u (r+k) v) (t-k) w = 0 := by
  obtain ⟨N,hN⟩ := compressed_high_modes D B C hC hCe a b u v r
  refine ⟨N, fun k hk => ?_⟩
  rw [hN k hk]
  simp [compressed]

private theorem product_cutoff (a b c : Fin e → ℤ) (u v w : Carrier D) (t q : ℤ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      I a (b+c) u (t-k) (I b c v (q+k) w) = 0 := by
  obtain ⟨N,hN⟩ := compressed_high_modes D B C hC hCe b c v w q
  refine ⟨N, fun k hk => ?_⟩
  rw [hN k hk, map_zero]

/-- The actual composable-charge generalized Jacobi identity. All charges,
original states and integer modes are arbitrary. Ambient positivity,
nondegeneracy and an ambient inverse are absent from the telescope. -/
theorem charged_borcherds (hD : (gramReal D).PosDef)
    (a b c : Fin e → ℤ) (u v w : Carrier D) (p r s : ℤ) :
    (∑ᶠ i : ℕ, ((Ring.choose ((p : ℚ)+S a c) i : ℚ) : ℂ) •
      I (a+b) c (I a b u (r+i) v) (p+s-i) w) =
    (∑ᶠ i : ℕ, ((-1 : ℂ)^i * ((Ring.choose ((r : ℚ)+S a b) i : ℚ) : ℂ)) •
      I a (b+c) u (p+r-i) (I b c v (s+i) w)) -
    (-1 : ℂ)^r •
    (∑ᶠ i : ℕ, ((-1 : ℂ)^i * ((Ring.choose ((r : ℚ)+S a b) i : ℚ) : ℂ)) •
      I b (a+c) v (r+s-i) (I a c u (p+i) w)) := by
  classical
  let f : ℕ → Carrier D := fun k => I (a+b) c (I a b u (r+k) v) (p+s-k) w
  let g : ℕ → Carrier D := fun k => I a (b+c) u (p+r-k) (I b c v (s+k) w)
  let h : ℕ → Carrier D := fun k => I b (a+c) v (r+s-k) (I a c u (p+k) w)
  have fcut : ∃ N : ℕ, ∀ k : ℕ, N ≤ k → f k = 0 :=
    iterate_cutoff D B C hC hCe a b c u v w r (p+s)
  have gcut : ∃ N : ℕ, ∀ k : ℕ, N ≤ k → g k = 0 :=
    product_cutoff D B C hC hCe a b c u v w (p+r) s
  have hcut : ∃ N : ℕ, ∀ k : ℕ, N ≤ k → h k = 0 :=
    product_cutoff D B C hC hCe b a c v u w (r+s) p
  have left (i : ℕ) :
      P (a+b+c) (jacobiLeftTerm E p s r (J a u) (J b v) (J c w) i) =
      ((Ring.choose (p : ℚ) i : ℚ) : ℂ) •
        (∑ᶠ n : ℕ, ((Ring.choose (S a c) n : ℚ) : ℂ) • f (i+n)) := by
    simp only [jacobiLeftTerm, mu, map_smul, integer_choose]
    rw [(exact_source_probe D B C hC hCe hD a b c u v w (r+i) (p+s-i)).2]
    apply congrArg (fun x : Carrier D => ((Ring.choose (p : ℚ) i : ℚ) : ℂ) • x)
    apply finsum_congr
    intro n
    simp only [f, Nat.cast_add, add_assoc, sub_sub]
  have first (i : ℕ) :
      P (a+b+c) (jacobiRightFirstTerm E p s r (J a u) (J b v) (J c w) i) =
      ((-1 : ℂ)^i * ((Ring.choose (r : ℚ) i : ℚ) : ℂ)) •
        (∑ᶠ j : ℕ, ((-1 : ℂ)^j * ((Ring.choose (S a b) j : ℚ) : ℂ)) •
          g (i+j)) := by
    simp only [jacobiRightFirstTerm, mu, map_smul, integer_choose]
    rw [(intermediate_projection_correction D B C hC hCe hD
      a b c u v w (p+r-i) (s+i)).2]
    apply congrArg (fun x : Carrier D =>
      ((-1 : ℂ)^i * ((Ring.choose (r : ℚ) i : ℚ) : ℂ)) • x)
    apply finsum_congr
    intro j
    simp only [correction, g, Nat.cast_add, add_assoc, sub_sub]
  have second (i : ℕ) :
      P (a+b+c) (jacobiRightSecondTerm E p s r (J a u) (J b v) (J c w) i) =
      (-1 : ℂ)^r •
        (((-1 : ℂ)^i * ((Ring.choose (r : ℚ) i : ℚ) : ℂ)) •
          (∑ᶠ j : ℕ, ((-1 : ℂ)^j * ((Ring.choose (S a b) j : ℚ) : ℂ)) •
            h (i+j))) := by
    simp only [jacobiRightSecondTerm, mu, map_smul, integer_choose,
      StateFieldResidueReconstruction.epsilon]
    have hp := (intermediate_projection_correction D B C hC hCe hD
      b a c v u w (s+r-i) (p+i)).2
    rw [show b+a+c = a+b+c by abel] at hp
    rw [hp, smul_comm (((-1 : ℂ)^i) * ((Ring.choose (r : ℚ) i : ℚ) : ℂ))
      ((-1 : ℂ)^r)]
    apply congrArg (fun x : Carrier D => (-1 : ℂ)^r • x)
    apply congrArg (fun x : Carrier D =>
      ((-1 : ℂ)^i * ((Ring.choose (r : ℚ) i : ℚ) : ℂ)) • x)
    apply finsum_congr
    intro j
    simp only [correction, schur_swap D B C hC a b, h, Nat.cast_add,
      add_assoc, sub_sub]
    rw [show s+r = r+s by omega]
  have sumL :
      (∑ᶠ i : ℕ, P (a+b+c)
        (jacobiLeftTerm E p s r (J a u) (J b v) (J c w) i)) =
      ∑ᶠ i : ℕ, ((Ring.choose ((p : ℚ)+S a c) i : ℚ) : ℂ) • f i := by
    calc
      _ = ∑ᶠ i : ℕ, ((Ring.choose (p : ℚ) i : ℚ) : ℂ) •
          (∑ᶠ n : ℕ, ((Ring.choose (S a c) n : ℚ) : ℂ) • f (i+n)) :=
        finsum_congr left
      _ = _ := by
        simpa only [one_pow, one_mul] using
          binomial_convolution (p : ℚ) (S a c) (1 : ℂ) f fcut
  have sumA :
      (∑ᶠ i : ℕ, P (a+b+c)
        (jacobiRightFirstTerm E p s r (J a u) (J b v) (J c w) i)) =
      ∑ᶠ i : ℕ, ((-1 : ℂ)^i * ((Ring.choose ((r : ℚ)+S a b) i : ℚ) : ℂ)) •
        g i := by
    calc
      _ = ∑ᶠ i : ℕ, ((-1 : ℂ)^i * ((Ring.choose (r : ℚ) i : ℚ) : ℂ)) •
          (∑ᶠ j : ℕ, ((-1 : ℂ)^j * ((Ring.choose (S a b) j : ℚ) : ℂ)) •
            g (i+j)) := finsum_congr first
      _ = _ := binomial_convolution (r : ℚ) (S a b) (-1 : ℂ) g gcut
  have sumB :
      (∑ᶠ i : ℕ, P (a+b+c)
        (jacobiRightSecondTerm E p s r (J a u) (J b v) (J c w) i)) =
      (-1 : ℂ)^r •
        (∑ᶠ i : ℕ, ((-1 : ℂ)^i * ((Ring.choose ((r : ℚ)+S a b) i : ℚ) : ℂ)) •
          h i) := by
    have rowsFinite : Function.HasFiniteSupport (fun i : ℕ =>
        ((-1 : ℂ)^i * ((Ring.choose (r : ℚ) i : ℚ) : ℂ)) •
          (∑ᶠ j : ℕ, ((-1 : ℂ)^j * ((Ring.choose (S a b) j : ℚ) : ℂ)) •
            h (i+j))) := by
      obtain ⟨N,hN⟩ := hcut
      apply (Finset.finite_toSet (Finset.range N)).subset
      intro i hi
      apply Finset.mem_range.mpr
      by_contra hn
      apply hi
      have hz : (∑ᶠ j : ℕ,
          ((-1 : ℂ)^j * ((Ring.choose (S a b) j : ℚ) : ℂ)) • h (i+j)) = 0 := by
        apply finsum_eq_zero_of_forall_eq_zero
        intro j
        rw [hN (i+j) (by omega), smul_zero]
      dsimp only
      rw [hz, smul_zero]
    calc
      _ = ∑ᶠ i : ℕ, (-1 : ℂ)^r •
          (((-1 : ℂ)^i * ((Ring.choose (r : ℚ) i : ℚ) : ℂ)) •
            (∑ᶠ j : ℕ, ((-1 : ℂ)^j * ((Ring.choose (S a b) j : ℚ) : ℂ)) •
              h (i+j))) := finsum_congr second
      _ = (-1 : ℂ)^r •
          (∑ᶠ i : ℕ, ((-1 : ℂ)^i * ((Ring.choose (r : ℚ) i : ℚ) : ℂ)) •
            (∑ᶠ j : ℕ, ((-1 : ℂ)^j * ((Ring.choose (S a b) j : ℚ) : ℂ)) •
              h (i+j))) := (smul_finsum' _ rowsFinite).symm
      _ = _ := congrArg (fun v : Carrier D => (-1 : ℂ)^r • v)
        (binomial_convolution (r : ℚ) (S a b) (-1 : ℂ) h hcut)
  obtain ⟨hfL,hfA,hfB,he⟩ :=
    LatticeAllStateJacobi.borcherds E (J a u) (J b v) (J c w) p s r
  simp_rw [smul_sub] at he
  change (∑ᶠ i : ℕ, jacobiLeftTerm E p s r (J a u) (J b v) (J c w) i) =
    ∑ᶠ i : ℕ, (jacobiRightFirstTerm E p s r (J a u) (J b v) (J c w) i -
      jacobiRightSecondTerm E p s r (J a u) (J b v) (J c w) i) at he
  rw [finsum_sub_distrib hfA hfB] at he
  have projected := congrArg (P (a+b+c)) he
  rw [map_sub,
    map_finsum_linear (P (a+b+c)) _ hfL,
    map_finsum_linear (P (a+b+c)) _ hfA,
    map_finsum_linear (P (a+b+c)) _ hfB,
    sumL, sumA, sumB] at projected
  exact projected

/- Specialization and exponent bookkeeping (exposition, no retained bind-only
declaration). At a=0, schur 0 b = schur 0 c = 0 by the displayed definition.
For C=0, the already published canonical neutral supplier identifies
I 0 b u with the ORIGINAL action in module B*b; the first product acts in
module B*(b+c)=B*b+B*c, and the reverse inner action is in module B*c.
Thus this specializes literally to the existing original-acting mixed law.

For canonical rational modes, q_ab=-S(a,b) at C=0 and
K_ab(u)[m-q_ab]v=I_ab(u)[m]v. Bilinearity of the displayed Schur sum gives
q_(a+b),c=q_ac+q_bc and q_a,(b+c)=q_ab+q_ac without a new premise.
The integer theorem then reads exactly as the rational formula in the brief,
using raw rational q, not q modulo Z. No theorem using the not-yet-retained
canonical module is imported here. This coefficient conversion is exposition;
the charged_borcherds theorem supplies the all-state identity above.
-/

end
end D5.S3.VertexAlgebra.LatticeCosetChargedJacobi

