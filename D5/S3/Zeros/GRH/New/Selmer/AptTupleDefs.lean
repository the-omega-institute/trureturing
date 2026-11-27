/- GID: D5/S3/Zeros/GRH/New/Selmer/AptTupleDefs
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/AptTupleDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.AptTupleDefs. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/AptTupleDefs.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.DeterminantBound
import D5.S3.Zeros.GRH.New.Selmer.LevelPlacesChosen
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Part of: Galois representations of theta lifts: irreducible block plus string (see
New.Selmer.RowsExist).

This file: here (unlike New.Rows, New.Columns, where they are forms) a column is a conjugate
self-dual ℓ-adic representation with prescribed jumps, unramified off S and ℓg, and a row is one
with S empty whose lattices span all matrices. Also the Selmer length bound and the unit cr_ℓ.
Apt labels, idempotents, normalising character, labelled columns, row-plus-string predicate. -/

noncomputable section

variable {ℓ} [ThePrime ℓ] {P} (D : Data P) [PadicIso ℓ] {n} [Fintype n] (t)
  (J : (D.E →+* ℂ) → Multiset ℤ) (ψ : AbsGal D →* PadicAlgCl ℓ) (S) (R : GalRep ℓ D.E n)

/-- R is continuous, has non-degenerate trace form, and is conjugate self-dual on traces: tr
R(g^c) = cyc(g)^{1−t} tr R(g⁻¹) for all g, with t = 0 read as t = 1. -/
structure IsConjSelfDual {D : Data P} {n} [Fintype n] t (R : GalRep ℓ D.E n) where
  continuous : Continuous R
  nondeg : IsTraceNondeg R
  trace_conj g : (R (conjGal g)).1.trace = cycInv ℓ _ _ g ^ (t - 1) * (R g⁻¹).1.trace

/-- The real number cr_ℓ = v_ℓ(Mk) + 2^{−ℓ}, where Mk is the integer `Data.chosenGroupOrder`. -/
def crudeUnit (ℓ : ℕ) {P} (D : Data P) : NNReal := padicValNat ℓ D.chosenGroupOrder + (1 / 2) ^ ℓ

variable {D} in
/-- For all large O: z ∈ O, z − 1 is a unit, and on some lattice in ψR the element γ ∈ ker cyc
acts by z, and the continuous cocycles mod ℓ^m unramified off ℓg₀g₁, Q, Q̄, obeying
`crysRels`, zero at γ, have normalised length ≤ (10fn + 1)·`crudeUnit`, n the
rank. -/
def SelmerLengthLe Q m γ (z : intQpBar ℓ) := ∀ᶠ O : CoeffRing ℓ in .atTop, ∃ u ψ' y, y.1 = ↑z ∧
  IsLatticeIn R u ∧ (∀ g, ψ' g = ψ g) ∧ let ρ := twistRep (.id O) ψ' u; ρ γ = (y : ↑O) • 1 ∧
    IsUnit (y - 1) ∧ cycChar Ω ℓ γ = 1 ∧ O.normLength (Module.length O ↥(selmerModule ρ
    (placesDividing _ ℓ ∪ placesAboveG D ∪ .conjClosure Q) (crysRels ρ) (QuotSpan (ℓ ^ m : ↑O)) ⊓
    (LinearMap.proj γ).ker)) ≤ 10 * D.f * Fintype.card n * crudeUnit ℓ D + crudeUnit ℓ D

/-- A column of level S: R satisfies `IsConjSelfDual`; at places off S or above ℓg it is
potentially crystalline (finite on inertia off ℓ) with jumps J, and crystalline (unramified
off ℓ) if the place is prime to g. -/
structure IsColumn extends IsConjSelfDual t R where
  local_conditions : ∀ v ∉ S \ (placesDividing _ ℓ ∪ placesAboveG D), ∀ ⦃A : ClosurePlace⦄,
    IsPlaceOver A v → IsFiniteTypeAt R A ∧ HasJumpsAt R A J ∧ (v ∉ placesAboveG D → IsGoodAt R A)

/-- A row: `IsColumn` with S empty, jumps as in `IsRowType`, bounded v(det(R(γ) −
1)) at places above g, lattices spanning all matrices, and two elements acting by scalars,
one inertial and residually of large order. -/
structure IsRow extends IsColumn D t J ∅ R, IsRowType D (Fintype.card n) t J where
  inertia_above_g : ∀ v ∈ placesAboveG D \ placesDividing _ ℓ,
    ∀ ⦃A : ClosurePlace⦄ (h : IsPlaceOver A v), ∃ γ N, (D.IsChosen v → γ = h.tameGenerator) ∧
    A.valuation N.cast = 1 ∧ (∀ i ∈ inertiaGroup _ A, R (i ^ N) = 1) ∧
    ∀ b, ellVal ((R (idOrConjInv b γ)).1 - 1).det ≤ Fintype.card n * crudeUnit ℓ D
  span_and_scalar : ∀ᶠ O in .atTop, ∀ u, IsLatticeIn (O := O) R u → Submodule.span O
    (.range u) = ⊤ ∧ ∃ g i α, (cycChar Ω ℓ g).1 = D.g i ^ Fintype.card n ∧ u g = (α : ↑O) • 1
  exists_scalar_inertia : ∃ᵉ (γ ∈ inertiaAbove (placesAboveG D \ placesDividing _ ℓ)) (y :
    PadicAlgCl ℓ), (R γ).1 = y • 1 ∧
    ∀ᵉ (a) (j ∈ Set.Icc 1 (4 * Fintype.card n + 2)), ‖(y ^ ℓ ^ a) ^ j - 1‖ = 1

open Polynomial Fintype Set AlgHeckeChar AutChar
variable {ℓ : _} [ThePrime ℓ] {P : _} {D : Data P} [PadicIso ℓ] {r} {n : _} {m} [Fintype r] [Fintype
  n] [Fintype m] (O : AuxPair D.E r n) (k) (J : _) (c : ∀ i, (ResField (O.chosenPlace i))[X]) (S :
  _) (z) (R : _)

/-- The ℓ-adic avatar of the algebraic character bc(υ^{−r₋})·υ^r·|·|^{r/2}, r the rank of W and
r₋ its number of signs −1; it normalises representations of forms on V. -/
abbrev chiOneInv := (HasWeight.inv (μ := O.a).toAlgebraic (-card r) 0).avatar

/-- Let A lie over w ∤ ℓ and let s⁻¹ act on the residue field of A as the (Nw)^k-th power. Then
`chiOneInv` sends s to ι(ν_w)^{−k}, ν_w the scalar `AutChar.frobValue` for υ^{r₋} and the
rank of W. -/
lemma chiOneInv_spec {O : AuxPair D.E r n} {w : FinPlace _} {A : ClosurePlace} (a :
  IsPlaceOver A w) (l : ↑ℓ ∉ w.1) k {s} (h :
  IsFrob A (w.q ^ k) s⁻¹) : chiOneInv O s = ιℓ (O.a.frobValue r w)⁻¹ ^ k := by
  choose z _ e using a.exists_localArtin_eq h k
  simp [avatar_localArtin _ a _ e, ↓CharUnramifiedAt.apply_locIdele_eq_zpow _ z, *, frobValue,
    AutChar.spaceChar, HasWeight.toAlgebraic,
    HeckeChar.atUnif, ↓HasWeight.charUnramifiedAt_toAlgebraic]; ring

/-- The normalised representation: R twisted by the character `chiOneInv`. -/
abbrev normalisedRep := twistByChar (m := n) (chiOneInv O) R

/-- The label c_i with its roots multiplied by the element of the residue field that labels the
character ψ_w⁻¹, w the i-th chosen place of O and ψ the tame part of its character. -/
def twistedLabel i :=
  (c i).scaleRoots (charName (faithfulChar (ResField (O.chosenPlace i))) (O.ψ _)⁻¹).1

/-- O has the places of ϑ, tame part ω^jϑ (1 ≤ j ≤ m), odd ranks r' ≤ r, n − r' ≤ t; the c_i are
labels of degree r', twisted labels lack the root 1, and over each g_k one label is
primitive with r' = r, or X − 1 with r' = 1. -/
structure IsApt (ϑ : D.Twist) where
  toLevelPlaces_eq : O.toLevelPlaces = D.levelPlaces ϑ
  tame_part_eq : ∃ j ∈ Icc 1 D.m, O.ψ = D.ω ^ (j : ℤ) * ϑ.ψ
  odd : Odd (card r) ∧ Odd O.rankDiff
  rank_le : card r ≤ D.r ∧ O.rankDiff ≤ D.t
  isLabel i : IsLabel (card r) (c i)
  exists_primitive k : ∃ i, ↑(D.g k) ∈ (O.chosenPlace i).1 ∧
    (card r = D.r ∧ IsPrimitiveLabel (card r) (c i) ∨ card r = 1 ∧ c i = X - 1)
  isLabel_twistedLabel i : ¬(twistedLabel O c i).IsRoot 1

/-- The endomorphism of the space of forms given by the action of the group-algebra idempotent
attached to the tuple of labels c. -/
abbrev tupleProj := O.groupAlgAction (tupleIdem r c)

/-- R is a row, and for every tame character ϑ, each eigenform lifting z on a pair V with
character μϑ has normalised trace ψ·tr R + Σ_{e<t} cyc^{−e}, ψ the avatar of ϑ⁻¹. -/
def HasRow := (∃ τ, IsRow (n := r) D O.rankDiff τ R) ∧ ∀ {ϑ : D.TameChar} {V : AuxPair _ r n} {y H
  S}, V.μ = O.μ * ϑ.toAutChar → V.Lifts y z → IsEigenform y H → Attached H S → ∀ g, (normalisedRep V
  S g).1.trace = ϑ.invAvatar g * (R g).1.trace + ∑ e ∈ .range V.rankDiff, cycInv ℓ _ _ g ^ e

/-- R is a column (`IsColumn`) for k of type J and level S, and inertia at each chosen place
of O is killed through the tame characters given by the roots of its label c. -/
structure IsLabelledColumn extends IsColumn (n := m) D k J S R where
  labelled ⦃i A⦄ : IsLabelledAt A (faithfulChar (ResField (O.chosenPlace i))) (card r).factorial
    (PolyKillsAt R A) (c i)
