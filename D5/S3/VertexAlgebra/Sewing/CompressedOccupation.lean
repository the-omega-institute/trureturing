/- GID: D5/S3/VertexAlgebra/Sewing/CompressedOccupation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sewing/CompressedOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal compressed blocks have factorial occupation contractions absolutely summable on the open unit disk. -/
/- Delivery scope and attribution: the native import-to-EOF proof source is
preserved exactly; only this metadata prefix is authored for canonical delivery.
proof_shape: content for the transpose/chain-rule, mass inequalities and weighted
support argument (LongitudinalFockTranspose); content for the literal projected
row/column estimates and all-disk summability (CompressedOccupation).
admission_basis: escape-witness. The live non-binding step is the actual Fischer
transpose and its frequency-preserving uniform occupation majorant, used to
transport the ambient factorial column estimate through the literal projection.
Scalar/sum/radius normalization helpers are consumed in those proof paths;
they are organizational helpers, not separate new mathematical results.
utility: none: these are symbolic identities/estimates over all polynomials,
occupations and signed modes, not finite enumeration, a checker, a numerical
reduction or a certified finite instance. No completed state space is assumed.
Source attribution: supplied final native LongitudinalFockTranspose export
SHA256 518543a4ac559b5f5f651e37bb80dbdfe7b974425970e9b129fcb2d4712e745b;
supplied final native CompressedOccupation export SHA256
969e9b20dbc3c8434530097e8d2f90343215bf829fd3d4c6a55d70295037dc7d.
FactorialFockMetric, CanonicalOccupation/Row, LatticeCosetCompression and
Mathlib retain their source attribution. No literature-priority claim is made.
The actual finite ranks include zero, B is arbitrary integral, C is symmetric
even, and the original cocycle is unchanged. No additional positivity or
nondegeneracy premise is imposed. This pair proves no product identification,
braid/category coherence, full CFT, string or AdS/CFT completion.
The Blueprint mirror is produced by make emit. No separate experimental
artifact is specified by this formal content; the mirror-E field uses the
canonical route's evidence-not-specified-by-formal-manifest representation.
Typed escape registration remains separately subject to a current bounded
attempt. The incomplete source-bound audit and exact missing witnesses are
disclosed at https://github.com/the-omega-institute/trureturing/issues/29344;
no Contract registration or declared_validated status is claimed. -/

import D5.S3.VertexAlgebra.Sewing.CanonicalOccupation
import D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression
import D5.S3.VertexAlgebra.Sewing.LongitudinalFockTranspose
import Batteries.Tactic.OpenPrivate

/-! Absolute occupation summability for the literal compressed field.
   The ambient row/column estimates are reused, but ambient sewing is not:
   the inserted projection is controlled by its actual factorial transpose.
   No positivity of the ambient block, modified cocycle, radial loss, finite
   intermediate-state cutoff, or convergent-completion premise is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.CompressedOccupationSewing

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSectorIntertwiner
open CanonicalOccupationSewing MvPolynomial
open LongitudinalFockTranspose
open scoped BigOperators VertexOperator

open private wordMap wordCoeff word_row_bound rowWeight rowWeight_nonneg
  from D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow
open private word_column_bound columnWeight factorialEnvelope
  factorialEnvelope_nonneg factorialEnvelope_mul
  polynomial_factorialEnvelope_summable canonical_monomial_word
  polynomial_expansion inner_coefficient_expansion inner_basis_coordinate
  from D5.S3.VertexAlgebra.Sewing.CanonicalOccupation
open private injection_single projection_single
  from D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression

noncomputable section

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

abbrev E := LatticeCosetCompression.ambient D e B C hC hCe

/-- The exact longitudinal projection matrix, with old coordinates first. -/
def projectionMatrix : Matrix (Fin D.rank) (Fin (D.rank+e)) ℂ :=
  fun i j => Fin.addCases (fun k => if i = k then 1 else 0)
    (fun k => (LatticeCosetCompression.longitudinal D B i k : ℂ)) j

theorem projection_eq_linearSub :
    LatticeCosetCompression.polynomialProjection D B C hC hCe =
      linearSub (projectionMatrix D B) := by
  classical
  ext x
  rcases x with ⟨j,m⟩
  induction j using Fin.addCases with
  | left j =>
    simp [LatticeCosetCompression.polynomialProjection,
      LatticeCosetCompression.projectionVariable, linearSub, projectionMatrix]
  | right j =>
    simp [LatticeCosetCompression.polynomialProjection,
      LatticeCosetCompression.projectionVariable, linearSub, projectionMatrix]

def oldIndex (x : Index D) : Index (E D B C hC hCe) := (x.1.castAdd e,x.2)

def oldOccupation (d : Occ D) : Occ (E D B C hC hCe) :=
  d.mapDomain (oldIndex D B C hC hCe)

theorem oldOccupation_degree (d : Occ D) :
    (oldOccupation D B C hC hCe d).degree = d.degree := by
  exact Finsupp.degree_mapDomain _ _

theorem oldOccupation_level (d : Occ D) :
    level (E D B C hC hCe) (oldOccupation D B C hC hCe d) = level D d := by
  classical
  unfold level LatticePositiveEnergy.oscillatorEnergy oldOccupation
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp)
    (by intros; simp [add_mul])]
  rfl

theorem injection_basis (d : Occ D) :
    LatticeCosetCompression.polynomialInjection D B C hC hCe (b D d) =
      b (E D B C hC hCe) (oldOccupation D B C hC hCe d) := by
  exact MvPolynomial.rename_monomial _ _ _

/-- This is precisely the block requested in the task, extracted at α+β. -/
def T (a b' : Fin e → ℤ) (α β : Charge D)
    (u : Oscillator D) (m : ℤ) (v : Oscillator D) : Oscillator D :=
  (LatticeCosetCompression.compressed D B C hC hCe a b'
    (Finsupp.single α u) m (Finsupp.single β v)) (α+β)

theorem block_as_actual_projection (a b' : Fin e → ℤ) (α β : Charge D)
    (u v : Oscillator D) (m : ℤ) :
    T D B C hC hCe a b' α β u m v =
      LatticeCosetCompression.polynomialProjection D B C hC hCe
        (canonical (E D B C hC hCe)
          (LatticeCosetCompression.liftCharge D B C hC hCe a α)
          (LatticeCosetCompression.liftCharge D B C hC hCe b' β)
          (LatticeCosetCompression.polynomialInjection D B C hC hCe u) m
          (LatticeCosetCompression.polynomialInjection D B C hC hCe v)) := by
  classical
  have hadd : LatticeCosetCompression.liftCharge D B C hC hCe a α +
      LatticeCosetCompression.liftCharge D B C hC hCe b' β =
        LatticeCosetCompression.liftCharge D B C hC hCe (a+b') (α+β) := by
    ext i
    induction i using Fin.addCases <;> simp [LatticeCosetCompression.liftCharge]
  unfold T LatticeCosetCompression.compressed
  simp only [LinearMap.comp_apply, injection_single]
  have hinc := inclusion_canonical (E D B C hC hCe)
    (LatticeCosetCompression.liftCharge D B C hC hCe a α)
    (LatticeCosetCompression.liftCharge D B C hC hCe b' β)
    (LatticeCosetCompression.polynomialInjection D B C hC hCe u)
    (LatticeCosetCompression.polynomialInjection D B C hC hCe v) m
  simp only [LatticeSectorIntertwiner.inclusion, Finsupp.lsingle_apply] at hinc
  rw [← hinc]
  change (LatticeCosetCompression.projection D B C hC hCe (a+b')
    (Finsupp.single _ _)) (α+β) = _
  rw [hadd, projection_single]
  have hext : LatticeCosetCompression.externalCharge D B C hC hCe
      (LatticeCosetCompression.liftCharge D B C hC hCe (a+b') (α+β)) = a+b' := by
    funext j
    change Fin.addCases (α+β) (a+b') (j.natAdd D.rank) = (a+b') j
    exact Fin.addCases_right j
  have hold : LatticeCosetCompression.oldCharge D B C hC hCe
      (LatticeCosetCompression.liftCharge D B C hC hCe (a+b') (α+β)) = α+β := by
    funext i
    change Fin.addCases (α+β) (a+b') (i.castAdd e) = (α+β) i
    exact Fin.addCases_left i
  rw [if_pos hext, hold, Finsupp.single_eq_same]

/-- The same projected coefficients, with the actual ambient descendant word.
The integral ambient charges here are exactly (α,a) and (β,b'). -/
def W (a b' : Fin e → ℤ) (α β : Charge D)
    (ω : List (Index (E D B C hC hCe))) (m : ℤ) (d f : Occ D) : ℂ :=
  (LatticeCosetCompression.polynomialProjection D B C hC hCe
    (wordMap (E D B C hC hCe)
      (LatticeCosetCompression.liftCharge D B C hC hCe a α)
      (LatticeCosetCompression.liftCharge D B C hC hCe b' β)
      ω m (b (E D B C hC hCe) (oldOccupation D B C hC hCe f)))).coeff d

theorem block_coefficient_expansion (a b' : Fin e → ℤ) (α β : Charge D)
    (u v : Oscillator D) (m : ℤ) (d : Occ D) :
    (T D B C hC hCe a b' α β u m v).coeff d =
      ∑ U ∈ u.support, ∑ V ∈ v.support, (u.coeff U * v.coeff V) *
        W D B C hC hCe a b' α β
          (occurrences (E D B C hC hCe) (oldOccupation D B C hC hCe U)) m d V := by
  classical
  rw [block_as_actual_projection]
  conv_lhs =>
    rw [polynomial_expansion D u, polynomial_expansion D v]
  simp only [map_sum, map_smul, Finset.sum_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Pi.smul_apply, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, injection_basis, canonical_monomial_word,
    Finset.mul_sum, W, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  ring

private theorem W_transpose (a b' : Fin e → ℤ) (α β : Charge D)
    (ω : List (Index (E D B C hC hCe))) (m : ℤ) (d f : Occ D) :
    W D B C hC hCe a b' α β ω m d f =
      (∑ t ∈ (transposeSub (projectionMatrix D B) (b D d)).support,
        (FactorialFockMetric.weight t : ℂ) *
          star ((transposeSub (projectionMatrix D B) (b D d)).coeff t) *
          wordCoeff (E D B C hC hCe)
            (LatticeCosetCompression.liftCharge D B C hC hCe a α)
            (LatticeCosetCompression.liftCharge D B C hC hCe b' β)
            ω m t (oldOccupation D B C hC hCe f)) /
        (FactorialFockMetric.weight d : ℂ) := by
  unfold W
  rw [projection_eq_linearSub]
  exact coefficient_transpose _ d _

/-- The genuine uniform row estimate for the projected operator. The output
occupation is fixed, while the input occupation and signed mode are arbitrary.
The matrix transpose is finite only because this test state is fixed. -/
theorem projected_word_row_bound (a b' : Fin e → ℤ) (α β : Charge D) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ ω : List (Index (E D B C hC hCe)),
      ∃ K : ℕ, ∀ d : Occ D, ∃ S : ℝ, 0 ≤ S ∧ ∀ (f : Occ D) (m : ℤ),
        ‖W D B C hC hCe a b' α β ω m d f‖ ≤ S * rowWeight D L K f := by
  classical
  obtain ⟨L,hL,hr⟩ := word_row_bound (E D B C hC hCe)
    (LatticeCosetCompression.liftCharge D B C hC hCe a α)
    (LatticeCosetCompression.liftCharge D B C hC hCe b' β)
  refine ⟨L,hL,?_⟩
  intro ω
  obtain ⟨K,hr⟩ := hr ω
  choose S hS hb using hr
  refine ⟨K,?_⟩
  intro d
  let τ := transposeSub (projectionMatrix D B) (b D d)
  let Z : ℝ := (FactorialFockMetric.weight d : ℝ)
  have hZ : 0 < Z := by dsimp [Z]; exact_mod_cast FactorialFockMetric.weight_pos d
  refine ⟨(∑ t ∈ τ.support,
    (FactorialFockMetric.weight t : ℝ) * ‖τ.coeff t‖ * S t) / Z,
    div_nonneg (Finset.sum_nonneg (fun t ht =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (hS t))) hZ.le, ?_⟩
  intro f m
  rw [W_transpose, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hZ).mpr
  calc
    _ ≤ ∑ t ∈ τ.support,
        ‖(FactorialFockMetric.weight t : ℂ) * star (τ.coeff t) *
          wordCoeff (E D B C hC hCe)
            (LatticeCosetCompression.liftCharge D B C hC hCe a α)
            (LatticeCosetCompression.liftCharge D B C hC hCe b' β)
            ω m t (oldOccupation D B C hC hCe f)‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ τ.support,
        (FactorialFockMetric.weight t : ℝ) * ‖τ.coeff t‖ *
          (S t * rowWeight D L K f) := by
      apply Finset.sum_le_sum
      intro t ht
      simp only [norm_mul, norm_star, Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [rowWeight, oldOccupation_level, oldOccupation_degree] using
        hb t (oldOccupation D B C hC hCe f) m
    _ = (∑ t ∈ τ.support,
        (FactorialFockMetric.weight t : ℝ) * ‖τ.coeff t‖ * S t) * rowWeight D L K f := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = _ := by field_simp [ne_of_gt hZ]

private theorem factorialEnvelope_as_radius (F : LatticeData) (A : ℝ) (t : Occ F) :
    factorialEnvelope F A t =
      monomialRadius (frequencyRadius A) t / (FactorialFockMetric.weight t : ℝ) := rfl

/-- Column transport under a literal projection. This is where the arbitrary
intermediate occupation is controlled; the support of its transpose may grow.
The mass theorem estimates all of that support with a single factorial bound. -/
private theorem projection_column_transport (A S : ℝ) (hA : 0 ≤ A) (hS : 0 ≤ S)
    (J : ℕ) (f : Oscillator (E D B C hC hCe))
    (hf : ∀ t : Occ (E D B C hC hCe),
      ‖f.coeff t‖ ≤ S * (1 + (level (E D B C hC hCe) t : ℝ))^J *
        factorialEnvelope (E D B C hC hCe) A t) (d : Occ D) :
    ‖(LatticeCosetCompression.polynomialProjection D B C hC hCe f).coeff d‖ ≤
      S * (1 + (level D d : ℝ))^J *
        factorialEnvelope D (A * rowSumBound (projectionMatrix D B)) d := by
  classical
  let τ := transposeSub (projectionMatrix D B) (b D d)
  let Z : ℝ := (FactorialFockMetric.weight d : ℝ)
  have hZ : 0 < Z := by dsimp [Z]; exact_mod_cast FactorialFockMetric.weight_pos d
  have henergy (t : Occ (E D B C hC hCe)) (ht : t ∈ τ.support) :
      level (E D B C hC hCe) t = level D d := by
    exact transpose_monomial_energy (projectionMatrix D B) d (MvPolynomial.mem_support_iff.mp ht)
  have hcancel (t : Occ (E D B C hC hCe)) :
      (FactorialFockMetric.weight t : ℝ) * factorialEnvelope (E D B C hC hCe) A t =
        monomialRadius (frequencyRadius A) t := by
    rw [factorialEnvelope_as_radius]
    have hw : (FactorialFockMetric.weight t : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (FactorialFockMetric.weight_pos t))
    field_simp [hw]
  rw [projection_eq_linearSub, coefficient_transpose, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hZ).mpr
  calc
    _ ≤ ∑ t ∈ τ.support,
        ‖(FactorialFockMetric.weight t : ℂ) * star (τ.coeff t) * f.coeff t‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ τ.support,
        (FactorialFockMetric.weight t : ℝ) * ‖τ.coeff t‖ *
          (S * (1 + (level (E D B C hC hCe) t : ℝ))^J *
            factorialEnvelope (E D B C hC hCe) A t) := by
      apply Finset.sum_le_sum
      intro t ht
      simp only [norm_mul, norm_star, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hf t) (by positivity)
    _ = (S * (1 + (level D d : ℝ))^J) * mass (frequencyRadius A) τ := by
      rw [mass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [henergy t ht, ← hcancel t]
      ring
    _ ≤ (S * (1 + (level D d : ℝ))^J) *
        monomialRadius (frequencyRadius (A * rowSumBound (projectionMatrix D B))) d :=
      mul_le_mul_of_nonneg_left
        (transpose_monomial_mass (projectionMatrix D B) A hA d) (by positivity)
    _ = _ := by
      rw [factorialEnvelope_as_radius]
      have hw : (FactorialFockMetric.weight d : ℝ) ≠ 0 := ne_of_gt hZ
      dsimp [Z]
      field_simp [hw]

/-- The actual factorial complementary column estimate, uniform in every
output occupation and every signed mode, for every ambient descendant word. -/
theorem projected_word_column_bound (a b' : Fin e → ℤ) (α β : Charge D) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ ω : List (Index (E D B C hC hCe)),
      ∃ J : ℕ, ∀ f : Occ D, ∃ S : ℝ, 0 ≤ S ∧ ∀ (d : Occ D) (m : ℤ),
        ‖W D B C hC hCe a b' α β ω m d f‖ ≤
          S * columnWeight D A (J+f.degree) d := by
  classical
  obtain ⟨A,hA,hc⟩ := word_column_bound (E D B C hC hCe)
    (LatticeCosetCompression.liftCharge D B C hC hCe a α)
    (LatticeCosetCompression.liftCharge D B C hC hCe b' β)
  let R := rowSumBound (projectionMatrix D B)
  have hR : 1 ≤ R := rowSumBound_one_le _
  have hAR : 1 ≤ A*R := by
    simpa only [one_mul] using mul_le_mul hA hR (by norm_num : (0 : ℝ) ≤ 1)
      (show 0 ≤ A by linarith)
  refine ⟨A*R, hAR, ?_⟩
  intro ω
  obtain ⟨J,hc⟩ := hc ω
  refine ⟨J,?_⟩
  intro f
  obtain ⟨S,hS,hc⟩ := hc (oldOccupation D B C hC hCe f)
  refine ⟨S,hS,?_⟩
  intro d m
  unfold W columnWeight
  rw [← mul_assoc]
  apply projection_column_transport D B C hC hCe A S (by linarith) hS
    (J+f.degree) _ _ d
  intro t
  simpa only [wordCoeff, columnWeight, oldOccupation_degree, mul_assoc] using hc t m

/-- Uniform projection bounds imply all-disk absolute summability. The proof
consumes only the library factorial-envelope summability machinery; it never
calls canonical_sewing_summable or ambient occupation sewing. -/
private theorem projected_word_contraction_summable
    (a b' c : Fin e → ℤ) (α β γ : Charge D)
    (ω ν : List (Index (E D B C hC hCe))) (P F : Occ D)
    (m n : Occ D → ℤ) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun d : Occ D => ‖q ^ level D d *
      W D B C hC hCe a (b'+c) α (β+γ) ω (m d) P d *
      W D B C hC hCe b' c β γ ν (n d) d F‖) := by
  obtain ⟨L,hL,hr⟩ := projected_word_row_bound D B C hC hCe a (b'+c) α (β+γ)
  obtain ⟨K,hr⟩ := hr ω
  obtain ⟨S,hS,hr⟩ := hr P
  obtain ⟨A,hA,hc⟩ := projected_word_column_bound D B C hC hCe b' c β γ
  obtain ⟨J,hc⟩ := hc ν
  obtain ⟨V,hV,hc⟩ := hc F
  have hLA : 0 ≤ L*A := mul_nonneg (by linarith) (by linarith)
  have hs := (polynomial_factorialEnvelope_summable D (L*A) hLA
    (K+(J+F.degree)) q hq).mul_left (S*V)
  refine hs.of_nonneg_of_le (fun d => norm_nonneg _) ?_
  intro d
  rw [norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ ‖q‖ ^ level D d * (S * rowWeight D L K d) *
        (V * columnWeight D A (J+F.degree) d) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hr d (m d)) (pow_nonneg (norm_nonneg q) _))
        (hc d (n d)) (norm_nonneg _)
        (mul_nonneg (pow_nonneg (norm_nonneg q) _)
          (mul_nonneg hS (rowWeight_nonneg D L hL K d)))
    _ = _ := by
      dsimp [rowWeight, columnWeight]
      rw [pow_add, ← factorialEnvelope_mul]
      ring

def term (a b' c : Fin e → ℤ) (α β γ : Charge D)
    (u v w p : Oscillator D) (r s : ℤ) (q : ℂ) (d : Occ D) : ℂ :=
  q ^ level D d *
    H D p (T D B C hC hCe a (b'+c) α (β+γ) u (r+(level D d : ℤ)) (b D d)) *
    H D (b D d) (T D B C hC hCe b' c β γ v (s-(level D d : ℤ)) w) /
    (FactorialFockMetric.weight d : ℂ)

private theorem block_basis_expansion (a b' : Fin e → ℤ) (α β : Charge D)
    (u : Oscillator D) (m : ℤ) (P d : Occ D) :
    (T D B C hC hCe a b' α β u m (b D d)).coeff P =
      ∑ U ∈ u.support, u.coeff U * W D B C hC hCe a b' α β
        (occurrences (E D B C hC hCe) (oldOccupation D B C hC hCe U)) m P d := by
  classical
  rw [block_coefficient_expansion]
  simp [b]

private theorem term_expansion (a b' c : Fin e → ℤ) (α β γ : Charge D)
    (u v w p : Oscillator D) (r s : ℤ) (q : ℂ) (d : Occ D) :
    term D B C hC hCe a b' c α β γ u v w p r s q d =
      ∑ P ∈ p.support, ∑ U ∈ u.support, ∑ V ∈ v.support, ∑ F ∈ w.support,
        ((FactorialFockMetric.weight P : ℂ) * star (p.coeff P) *
          u.coeff U * v.coeff V * w.coeff F) *
        (q ^ level D d *
          W D B C hC hCe a (b'+c) α (β+γ)
            (occurrences (E D B C hC hCe) (oldOccupation D B C hC hCe U))
            (r+(level D d : ℤ)) P d *
          W D B C hC hCe b' c β γ
            (occurrences (E D B C hC hCe) (oldOccupation D B C hC hCe V))
            (s-(level D d : ℤ)) d F) := by
  classical
  unfold term
  rw [mul_div_assoc, inner_basis_coordinate, inner_coefficient_expansion,
    block_coefficient_expansion]
  simp only [block_basis_expansion, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := w.support) (t := p.support)]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := w.support) (t := u.support),
    Finset.sum_comm (s := v.support) (t := u.support)]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro F hF
  ring

/-- Arbitrary actual oscillator descendants, every original occupation,
arbitrary signed offsets, and the entire open unit disk. This statement is
stronger in its Gram assumptions than required: the algebraic substitution
proof needs no ambient or original positivity. Thus it applies, in particular,
to the task's positive definite original Gram and arbitrary symmetric even C.
The original native epsilon is preserved through block_as_actual_projection. -/
theorem compressed_sewing_summable (a b' c : Fin e → ℤ) (α β γ : Charge D)
    (u v w p : Oscillator D) (r s : ℤ) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun d : Occ D => ‖q ^ level D d *
      H D p (T D B C hC hCe a (b'+c) α (β+γ) u (r+(level D d : ℤ)) (b D d)) *
      H D (b D d) (T D B C hC hCe b' c β γ v (s-(level D d : ℤ)) w) /
      (FactorialFockMetric.weight d : ℂ)‖) := by
  classical
  change Summable (fun d : Occ D => ‖term D B C hC hCe a b' c α β γ u v w p r s q d‖)
  have hs : Summable (fun d : Occ D =>
      ∑ P ∈ p.support, ∑ U ∈ u.support, ∑ V ∈ v.support, ∑ F ∈ w.support,
        ‖((FactorialFockMetric.weight P : ℂ) * star (p.coeff P) *
            u.coeff U * v.coeff V * w.coeff F) *
          (q ^ level D d *
            W D B C hC hCe a (b'+c) α (β+γ)
              (occurrences (E D B C hC hCe) (oldOccupation D B C hC hCe U))
              (r+(level D d : ℤ)) P d *
            W D B C hC hCe b' c β γ
              (occurrences (E D B C hC hCe) (oldOccupation D B C hC hCe V))
              (s-(level D d : ℤ)) d F)‖) := by
    apply summable_sum
    intro P hP
    apply summable_sum
    intro U hU
    apply summable_sum
    intro V hV
    apply summable_sum
    intro F hF
    simpa only [norm_mul] using
      (projected_word_contraction_summable D B C hC hCe a b' c α β γ
        (occurrences (E D B C hC hCe) (oldOccupation D B C hC hCe U))
        (occurrences (E D B C hC hCe) (oldOccupation D B C hC hCe V)) P F
        (fun d => r+(level D d : ℤ)) (fun d => s-(level D d : ℤ)) q hq).mul_left _
  refine hs.of_nonneg_of_le (fun d => norm_nonneg _) ?_
  intro d
  rw [term_expansion]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun P hP =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun U hU =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun V hV => norm_sum_le _ _))))))

end
end D5.S3.VertexAlgebra.CompressedOccupationSewing
