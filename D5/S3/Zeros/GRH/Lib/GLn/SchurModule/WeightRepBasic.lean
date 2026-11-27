/- GID: D5/S3/Zeros/GRH/Lib/GLn/SchurModule/WeightRepBasic
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GLn/SchurModule/WeightRepBasic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GLn.SchurModule.WeightRepBasic. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GLn/SchurModule/WeightRepBasic.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.DeltaForms
import D5.S3.Zeros.GRH.Lib.ClassField.Places.UnramifiedCharacters
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.RationalPoints
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Contravariant form on Weyl's lattice, Fischer product, irreducibility under U(n) (known
result; see Lib.Adelic.CuspForms.DeltaForms).

This file: Unitary groups acting on Weyl modules, invariant metric, extremal vector, Harish-Chandra
parameter. Algebraic modular forms on the standard definite unitary group; p-adic gauge. Weight
representation: base change, integrality, unitary invariance of the contravariant form. -/

noncomputable section

open Matrix Finset Fintype NumberField Space ComplexConjugate Units
variable {Φ n : Type} [Fintype Φ] [Fintype n] {R : Type} [CommRing R] (κ : Φ → ℕ → ℕ) (e : Φ → ℤ)
  (l : Φ → n → ℤ) {s : n → ℤˣ}

/-- The matrix representation of the product over places of the unitary groups of the diagonal
form of signs s: g acts by `weylRep` at the entrywise complex conjugate of g. -/
abbrev conjWeylMatrix := (weylRep κ e).comp (.pi ((GeneralLinearGroup.map (starRingEnd ℂ)).comp <|
  (USign s).subtype.comp <| Pi.evalMonoidHom _ ·))

/-- The complex linear representation of the product over places of the unitary groups of signs
s on coordinate vectors of weight κ, acting by the matrices `conjWeylMatrix`. -/
def conjWeylRep : Representation ℂ (Φ → USign s) (WeylIndex n κ → ℂ) :=
  toLinAlgEquiv'.toMonoidHom.comp (conjWeylMatrix κ e)

/-- For an integer vector l and an index i, the number of indices j with l_j > l_i. -/
def decrPosition (l : n → ℤ) i := #{j | l i < l j}

/-- The complex evaluation vector of weight κ at the array with entry 1 in row a of block w
exactly in column #{j : l_w(j) > l_w(a)}, and 0 elsewhere. -/
def highestVector : WeylIndex n κ → ℂ := weylEval _ κ (_root_.permArray (l · |> decrPosition <| ·))

/-- The integer 2λ_p + N − 1 − 2p, entry p (counted from 0) of twice λ + ρ in rank N, where λ_p
= e_w + Σ_{p<h<N} κ_w(h) at the place w. -/
def hcParameter N w p := 2 * (e w + diagramWeight (fun _ ↦ N) κ (w, p)) + N - 1 - 2 * p

/-- Each l_w is injective and is twice the Harish-Chandra parameter of (κ,e): l_w(i) =
2(e_w+λ(w,p)) + |n|−1−2p, p the number of j with l_w(j) > l_w(i). -/
def IsHCParam := ∀ w, (l w).Injective ∧ ∀ i, ∃ p < card n, l w i = hcParameter κ e (card n) w p

variable {κ} (hκ : ∀ τ, ∀ k ≠ card n, κ τ k = 0) (z : Φ → Matrix n n R)

/-- The sesquilinear form (ξ,η) ↦ ξ* G η on complex coordinate vectors of weight κ, conjugate
linear in ξ, with G the integer Gram matrix. -/
def gramForm : (WeylIndex n κ → ℂ) →ₗ⋆[ℂ] (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ := (dotProductBilin ..).compl₂
  weylGramOver.mulVecLin ∘ₛₗ (starLinearEquiv ℂ).1

lemma gramForm_apply (ξ η : WeylIndex n κ → ℂ) : gramForm ξ η = star ξ ⬝ᵥ weylGramOver *ᵥ η := rfl

include hκ

lemma nablaBasis_eq_one j :
  nablaBasis R n κ j = 1 := by simp [nablaBasis, tableauPoly, prod_fin_eq_prod_range, *, ne_of_lt]

lemma schur_eq_one : schur κ z = 1 := PolyRep.schur_eq_of_expansion (by simp [nablaBasis_eq_one hκ])

omit hκ
variable {E n : Type} [Field E] [CMType E] [Fintype n]
  (κ : InfinitePlace E → _) (e : NumberField.InfinitePlace E → ℤ) {s : n → _} {p : ℕ} [Fact p.Prime]
  [ι : PadicPlace p]

/-- The representation of the rational unitary group U(J)(E) on coordinate vectors of weight (κ,
e), through its components at the infinite places and `conjWeylRep`. -/
@[simps! -isSimp apply] def Space.weightRep (V : Space E n s) : Representation ℂ (U V.J) (WeylIndex
  n κ → ℂ) := (conjWeylRep κ e).comp ((MonoidHom.fst ..).comp V.ratEmbed)

variable (n) in
/-- Algebraic forms of weight (κ, e) on I_n: functions φ on the finite adelic unitary group with
open right stabiliser and φ(γg) = ρ(γ)φ(g) for rational γ, ρ = `Space.weightRep`. -/
abbrev AlgForm := SmoothForm (stdSpace E n).embFin (weightRep κ e _)

/-- The representation of the finite adelic unitary group on the space of algebraic forms of
weight (κ,e), by right translation. -/
abbrev algFormRep := smoothFormRep (stdSpace E n).embFin (weightRep κ e _)

/-- The gauge of ξ at g: the largest p-adic absolute value of a coordinate of g⁻¹·ι(ξ), where
g⁻¹ acts in weight (κ, e), at τ through its component at the prime induced by x ↦
ι(Φ_τ(x̄)). -/
def weylGauge (g : Gf E n) ξ := ‖weylRep κ e (fun τ ↦
  .map (adeleExtension (weightEmbedding ιₚ τ)) g⁻¹.1) *ᵥ ιₚ ∘ ξ‖

variable (n p)

/-- The subgroup of finite adelic unitary points whose components at all primes above p are
integral invertible matrices. -/
abbrev integralAbove {E : Type} (n : Type) [Field E] [NumberField E] [IsCMField E] [Fintype n]
    (p : ℕ) := localLevel n {w : FinPlace E | ↑p ∈ w.1}

variable {E n : Type} [Field E] [CMType E] [Fintype n] {T R S : Type} [CommRing R] [CommRing S]
  [Fintype T] {κ e : _} (σ : ℂ →+* ℂ) (γ : ↥(U (stdSpace E n).J)) (u : WeylIndex n κ → ℂ)
  (v : WeylIndex n κ → ℂ)

lemma weylRep_map (f : R →+* S) (g : T → GL n R) : weylRep κ e (.map f <| g ·) =
  (weylRep κ e g).map f :=
  Matrix.ext (by simp [weylRep, schur_map, ← map_zpow, Units.smul_def, f.map_det, -coe_units_zpow])

lemma weylRep_entry_mem A {g : T → GL n R} (h : ∀ τ, g τ ∈ intGL n A) i j :
    weylRep κ e g i j ∈ A := funext (h · |>.choose_spec) ▸ by simp [weylRep_map]

lemma stdSpace_ratEmbed_apply w : (((stdSpace E n).ratEmbed γ).1 w).1.1 =
  (PlaceEmbedding.Φ w).mapMatrix γ := by erw [Subtype.coe_mk]; aesop

lemma stdSpace_weightRep_apply : (stdSpace E n).weightRep κ e γ v =
  weylRep κ e (fun τ ↦ .map ((PlaceEmbedding.Φ τ).comp conj) γ) *ᵥ v :=
  congr(weylRep κ e $(by ext; simp [stdSpace_ratEmbed_apply, @starRingEnd_apply E]) *ᵥ v)

/-- The Gram pairing on coordinate vectors of weight κ is invariant under the product of the
compact groups U(n), acting in weight (κ, e). -/
lemma gramForm_conjWeylRep (x : T → USign 1) ξ η :
  gramForm (n := n) (conjWeylRep κ e x ξ) (conjWeylRep κ e x η) = gramForm
  ξ η := have d τ := congr((fun M ↦ (M, star M.det)) $((U.map conj (by simp) rfl (x τ)).2))
  by simp_all [gramForm, conjWeylRep, weylRep, Units.smul_def, star_mulVec_dotProduct, ← mul_zpow,
    PolyRep.schur_conjTranspose_weylGram_schur .refl, ← mul_assoc, ← Finset.prod_mul_distrib, U.map]

lemma map_weightRep (σ : ℂ →+* R) γ v : σ ∘ (stdSpace E n).weightRep κ e γ v =
  weylRep κ e (fun τ ↦ .map ((σ.comp (PlaceEmbedding.Φ τ)).comp conj) γ) *ᵥ σ ∘
  v := by ext; simp [stdSpace_weightRep_apply, σ.map_mulVec, weylRep_map]

lemma gramForm_map_weightRep : gramForm (σ ∘ (stdSpace E n).weightRep κ e γ u)
  (σ ∘ (stdSpace ..).weightRep κ e γ v) = gramForm (σ ∘ u)
  (σ ∘ v) := by convert gramForm_conjWeylRep (e := e) (fun τ ↦ U.map (σ.comp (Φ τ)) _ _ γ) ..
  <;> simp [map_weightRep, conjWeylRep] <;> congr with <;> apply map_star_complex (σ.comp _)
