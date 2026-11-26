import GRH.Lib.Adelic.Adeles.LocalComponents
import GRH.Lib.General.NumberTheory.StableLattice
import GRH.Lib.ClassField.HeckeCharacter.CharacterLevels
import GRH.Lib.ClassField.Local.ArtinMapAtPlace
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Bound for the odd part of a twisted Tate–Shafarevich group of an abelian CM field
(known result; see Lib.Cyclotomic.OddSha.OddShaBound).

Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes (known
result; see Lib.ClassField.Places.LocalFrobenius).

This file: Complex conjugation, anticyclotomic characters, Selmer cocycles, Tate twists, odd Sha:
definitions. -/

noncomputable section


variable {ℓ : ℕ} [Fact ℓ.Prime] (E : Type) [Field E] [EmbeddedNumberField E]
  [NumberField.IsCMField E] {C} [CommMonoid C]

/-- E is a CM number field, stably unramified (`StablyUnram`), with an embedding in the algebraic
closure Ω of ℚ. -/
class UnramCMField E [Field E] extends EmbeddedNumberField E, NumberField.IsCMField E, StablyUnram E

/-- The valuation −log_ℓ|x| in [0, ∞], normalised by v(ℓ) = 1; it is ∞ at 0, and 0 for |x| ≥ 1. -/
def ellVal (x : PadicAlgCl ℓ) := ite (‖x‖ = 0) ⊤ (ENNReal.ofReal (-.logb ℓ ‖x‖))

/-- A complex conjugation in Gal(Ω/ℚ), chosen once and for all. -/
def cmConj := (exists_isComplexConj Gal(Ω/ℚ) Rat.isReal_infinitePlace).choose

/-- The chosen element c = `cmConj` of Gal(Ω/ℚ) is a complex conjugation: for some embedding j :
Ω → ℂ, j(cx) is the complex conjugate of j(x) for all x. -/
lemma isComplexConj_cmConj : IsComplexConj cmConj := .choose_spec _

/-- For a natural number N, the set of finite places of E whose prime ideal contains N. -/
def placesDividing (N : ℕ) := {v : FinPlace E | ↑N ∈ v.1}

instance : Fintype (placesDividing E ℓ) := (finite_natCast_mem ℓ).fintype

variable {E G O O' n} [CommRing O] [CommRing O'] [Fintype n] [Monoid G]

@[simp] lemma cmConj_cmConj x : cmConj (cmConj x) = x := congr($isComplexConj_cmConj.mul_self x)

/-- For a CM field E embedded in Ω, the chosen complex conjugation of Ω restricts to the complex
conjugation of E. -/
@[simp] lemma cmConj_algebraMap x : cmConj (algebraMap E Ω x) = algebraMap E Ω (star x) :=
  isComplexConj_cmConj.elim (·.injective <| map_star_complex (.comp ..) x ▸ · _)

/-- The endomorphism g ↦ g^c = cgc of the Galois group of Ω over E, c the chosen complex
conjugation. -/
def conjGal : Gal(Ω/E) →* Gal(Ω/E) :=
  .mk' ({cmConj * ·.restrictScalars ℚ * cmConj with commutes' := by simp}) (by aesop)

/-- χ is locally constant and χ(Art x) = η(x/x̄), η a character of finite ideles trivial on E^× and
on ideles that off S ∪ S̄ are units and ≡ 1 at the places of I outside S ∪ S̄. -/
structure IsFromU1 S I (χ : Gal(Ω/E) →* C) where
  isLocallyConstant : IsLocallyConstant χ
  exists_ideleChar : ∃ η : _ →* C, (∀ x, η (principalIdele x) = 1) ∧ (∀ a ∈ idelesUnitOff
    (.conjClosure S), (∀ w ∈ I \ S.conjClosure, Valued.v ((ideleAt w a).1 - 1) < 1) → η a = 1) ∧
    ∀ x (g : Gal(Ω/E)), artinMap Gal(Ω/E) x = g → χ g = η (x / star x)

/-- Given a ring map e:O→O', a character ψ:G→O' and a matrix representation ρ over O, the
representation g ↦ ψ(g)·e(ρ(g)) over O'. -/
def twistRep (e : O →+* O') (ψ : G →* O') (ρ : G →* Matrix n n O) :=
  smulMonoidHom.comp (ψ.prod (e.mapMatrix.1.comp ρ))

variable (ρ : Gal(Ω/E) → Matrix n n O) (S L B) [AddCommGroup B] [Module O B]

/-- The O-submodule of functions from a topological space G to an O-module B consisting of the
locally constant functions. -/
def locConst [TopologicalSpace G] : Submodule O (G → B) :=
  ⟨⟨⟨Set.ofPred IsLocallyConstant, (·.add)⟩, .const _⟩, fun _ ↦ (·.comp _)⟩

/-- The Selmer module: locally constant cocycles for ρ with values in B^n, unramified outside S
and obeying the relations L. -/
def selmerModule := obeying (cocycleRels ρ ∪ (.single · 1) '' inertiaAbove Sᶜ ∪ L) B ⊓ locConst _


variable (ℓ E) (Λ : Type) [CommRing Λ] [Algebra ℤ_[ℓ] Λ] (e ν : ℕ)

/-- The inverse of the ℓ-adic cyclotomic character of Gal(Ω/E), with values in the ℤ_ℓ-algebra
Λ. -/
def cycInv := (Units.coeHom _).comp (cycCharIn (Γ := Gal(Ω/E)) Λ Ω ℓ)⁻¹

/-- The rank-one representation Λ(−e): the character cyc^{−e} with values in Λ, as 1 × 1
matrices. -/
def tateTwist := (Matrix.scalar Unit).1.comp (cycInv ℓ E Λ ^ e)

/-- The union over places above ℓ of the inertia groups if e = 0, and of the kernels of cyc in
the decomposition groups if e ≠ 0. -/
def shaLocalSet := {g : Gal(Ω/E) | ∃ A : ClosurePlace, A.valuation ℓ < 1 ∧
  if e = 0 then g ∈ inertiaGroup _ A else g ∈ decompGroup _ A ∧ cycChar Ω ℓ g = 1}

/-- The locally constant cocycles z in (Λ/ℓ^νΛ)(−e), unramified outside ℓ, vanishing on
`shaLocalSet` for e, and, if e ≠ 0, odd: z(g^c) = −z(g). -/
def shaOdd := .pi (shaLocalSet ℓ E e) ⊥ ⊓ (⨅ _ : e ≠ 0, LinearMap.ker (1 + .funLeft _ _ conjGal)) ⊓
  selmerModule (tateTwist ℓ E Λ e) (placesDividing E ℓ) ∅ (QuotSpan (ℓ ^ ν : Λ))
