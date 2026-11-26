/- GID: D5/S3/Zeros/GRH/New/Filling/CrudeBoundDefs
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/CrudeBoundDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.CrudeBoundDefs. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/CrudeBoundDefs.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.LevelBridge
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

Part of: Agreeing characters force shared vectors up the flag (see New.Filling.BoxPartition).

This file: Chinese remainder lift at level primes; fixers of frame vectors modulo them. Levels,
normal forms, cells, near and congruent terms, boxes and size parameters. -/

noncomputable section

open Fintype Function Matrix

variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰}

lemma Filling.reduction_apply_congr {k} l i w {a b} (h : k.1.1 a b = l.1.1 a b) :
    S.reduction k i w a b = S.reduction l i w a b := congr(⟦⟨$h _, _⟩⟧)

lemma Filling.exists_reduceAboveG_eq (t : ∀ _, _) : ∃ y, ∀ x, S.reduceAboveG x y = t x := ⟨∑ x,
  cond x.2 star id (surjInv (algebraMap_ResField_surjective _) (t x) • ⟨_, idem_mem_Ô {↑x.1.2}⟩), by
  simp [sum_prod_type_right, Algebra.smul_def, S.chosenPlaces_injective.eq_iff, surjInv_eq,
    reduceAboveG]
  grind [Finset.sum_eq_zero, star_idem, coe_star_Ô, reduceAt_idem, star_notMem_chosenPlaces]⟩

/-- At the chosen place w, the component s_w (its inverse adjoint if d.1 is true, that is,
modulo w̄) fixes the nonzero vector of the span of the frame with coordinates d.2. -/
def Filling.vectorFixer {i} (w : S.chosenPlaces i) (d : _ × {v : _ → ResField w.1 // v ≠ 0}) :=
  (MulAction.stabilizer _ (inclMatrix _ 𝔰.besselFrame *ᵥ d.2.1)).comap (.mk' (fun s : S.GRes ↦
  S.idOrInvAdjoint d.1 (s i w)) (by simp))

/-- For some finite set of primes w or w̄ above g with product of norms at least x, s fixes
modulo each a nonzero vector of the span of the frame. -/
def Filling.FixesNormAtLeast s x := ∃ A : Finset ((Σ i, S.chosenPlaces i) × _), x ≤ ∏ p ∈ A,
  S.levelPrime p.1.1 ∧ ∀ p ∈ A, ∃ v, s ∈ S.vectorFixer p.1.2 (p.2, v)

/-- The s fixing the given vector d_w at each w in Σ and, unless Σ holds all chosen places above
q₀, having all leading minors of Z(s_w) nonzero at some chosen w above q₀. -/
def Filling.fixingSet Sg (d : ∀ _, _) := {s | (∀ w ∈ Sg, s ∈ S.vectorFixer (i := 0) w (d w)) ∧
    (Sg = Finset.univ ∨ ∃ w, ∀ l, leadingMinor ((S.latMiddle _).frameGram (s 0 w).1) l ≠ 0)}

variable {R} [CommRing R] {𝔰 : Shape} (T : 𝔰.Form R)

/-- For a square matrix T on the middle coordinates, the two-row block diagonal matrix with two
copies of the row of T indexed by z. -/
abbrev Filling.zFormPair := T.toRows₂.fromBlocks 0 0 T.toRows₂

variable [StarRing R] {T : 𝔰.Form R} (γ γ' : T.G) (c c')

/-- The space T° of x for which some pair (x, x'), both components orthogonal to z, lies in the
links of both γ and γ'. -/
def commonLink :=
  (link γ ⊓ link γ' ⊓ (Filling.zFormPair T).mulVecLin.ker).map (.funLeft R R (.inl ∘ .inl))

/-- The frames f and γf satisfy fx = γfy for some coefficient vectors x, y that vanish at
indices above a and have x_a = c, y_a = c'. -/
def HasCommonFlagVector a := ∃ x y, frameImage 1 *ᵥ x = frameImage γ.1.1 *ᵥ y ∧ x a = c ∧ y a = c' ∧
  ∀ b > a, x b = 0 ∧ y b = 0

/-- For one c with c c̄ = 1 and every index a ≥ j (counted from 0), the flags of f and γf share
a vector with leading coefficients c and 1 at a. -/
def IsNormalForm (j : ℕ) (γ : T.G) := ∃ c, c * star c = 1 ∧ ∀ a, j ≤ a.1 →
  HasCommonFlagVector γ c 1 a

variable (S : Filling E 𝔰) (c : _)

/-- The Gram matrix over E of the form h on V: two dual isotropic blocks of rank ϱ around the
Gram matrix T of X₀⊕Ez. -/
abbrev Filling.ratGram := (S.ratMiddle E).splitGram

/-- The block diagonal matrix diag(T, −T) over E, Gram matrix of the form h⊕−h on two copies of
X₀⊕Ez. -/
abbrev Filling.linkForm := (S.ratMiddle E).fromBlocks 0 0 (-S.ratMiddle E)

/-- For a class c, the inverse of the matrix `Filling.classBasis` c; it takes rational coordinates
to coordinates in the basis of the lattice h_cΛ₀. -/
def Filling.classCoord := (S.classBasis c)⁻¹.1

/-- The matrix whose columns are the standard basis vectors of X₀, written in the basis of the
middle part of the lattice of the class c. -/
def Filling.classCoordX₀ (c : S.Classes) := middleBaseChange 𝔰 S.piBar * c.out⁻¹.1.1

/-- The real number |S̄|·#{c}·N^{−kf}·(2τ²)^i, with #{c} the number of classes, k = |κ| and f
the number of infinite places; S̄ is the reduction of the Bessel subgroup
(`Filling.reducedImage`), τ = `Filling.tailScale`. -/
abbrev Filling.countWeight i := Nat.card (S.reducedImage besselS) * card S.Classes / S.N ^
  (𝔰.k * numInfPlaces E) * (2 * S.tailScale ^ 2) ^ i

variable (j) (γ : S.G E)

/-- γ has level j ≤ ϱ+1: `IsNormalForm` j holds, the leading minor D_j of Z(γ) is nonzero, and 𝗀(γ)
≠ 0 exactly when j = ϱ+1. -/
def Filling.HasLevel := IsNormalForm j.1 γ ∧ leadingMinor (S.frameProducts γ) j ≠ 0 ∧
  (𝔰.ϱ < j ↔ S.termDisc γ ≠ 0)

/-- γ and γ' are congruent terms: both lie over (c, s, c') for one and the same s in the finite
group 𝖦. -/
def Filling.CongruentTerms (c' : S.Classes) (γ γ' : S.G E) := ∃ s, γ ∈ S.termsOver c s c' ∧
  γ' ∈ S.termsOver c s c'

/-- The product over the infinite places v of E of the absolute values |𝗀(γ)|_v, where 𝗀(γ) =
|D_{ϱ+1}|² − N²|D_ϱ|². -/
def Filling.termDiscNorm := ∏ v, ‖Φ v (S.termDisc γ)‖

/-- The set of archimedean points y such that at every infinite place y_v lies in `frameBox` of size
`Filling.boxSize` and `besselSize` y_v ≤ b^{6(ϱ+1)+2}. -/
def Filling.boxedPoints :=
  {y : NumberField.InfinitePlace E → 𝔰.G₁ | ∀ v, y v ∈ frameBox S.boxSize ∧ InCut (y v) S.b}

/-- The rational element γ is near: there is an archimedean point y such that both y and γ⁻¹y
lie in the set `Filling.boxedPoints` of boxed points. -/
def Filling.IsNear := ∃ y ∈ S.boxedPoints, (S.ratToInf γ)⁻¹ * y ∈ S.boxedPoints

/-- The finite character `Filling.unipotentChar` takes the same value at u and at γ⁻¹uγ for every
rational u in 𝖴 ∩ γ𝖴γ⁻¹. -/
def Filling.CharsAgree := ∀ u ∈ besselU, ∀ u' ∈ besselU, u * γ = γ * u' →
  S.unipotentChar (S.ratToFin u) = S.unipotentChar (S.ratToFin u')
