/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/WachGamma/KisinModuleDefs
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/WachGamma/KisinModuleDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.WachGamma.KisinModuleDefs. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/WachGamma/KisinModuleDefs.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin.DeRhamValues
import D5.S3.Zeros.GRH.Lib.PadicHodge.Herr.GaloisLattices
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: the Artin–Schreier–Witt resolution over the tilt. This file treats only the φ−1
step of Herr's complex, on Witt vectors of the tilt of C_p modulo p^m, and not the Γ-step. Source:
L. Herr, Sur la cohomologie galoisienne des corps p-adiques, Bull. SMF 126 (1998) 563–600.

Part of: Kisin modules: Galois action trivial modulo the variable, Hodge–Tate weights read off
(known result; see Lib.PadicHodge.WachGamma.Letters).

Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

Artin–Schreier–Witt: φ-1 onto on W(C♭)⊗Z/p^m(1);
φd − d ∈ W(m♭) forces d ∈ Z/p^m(1) + W(m♭); continuity. Kisin module of a
lattice inside A_inf, invariant forms, decomposition by unramified embeddings. -/

noncomputable section

section

open TensorProduct
variable {p} [ThePrime p] [Γ : GroupOverGp p] {ρ ρ' ρ'' : Rep ℤ_[p] Γ} (f : ρ →ₗ[ℤ_[p]] ρ')
  (b : ρ →ₗ[ℤ_[p]] ρ' →ₗ[ℤ_[p]] ρ'') {R R'} [Semiring R] [Module R WittCFlat] [SMulCommClass ℤ_[p] R
  WittCFlat] [Semiring R'] [Module R' WittCFlat] [SMulCommClass ℤ_[p] R' WittCFlat] [SMul R R']
  [IsScalarTower R R' WittCFlat]

/-- For a ℤ_p-representation ρ of Γ on T, the module W(C^♭) ⊗ T; ℤ × Γ acts by (n, g)(w ⊗ t) =
φ^n j(g)w ⊗ ρ(g)t. -/
def Lift.DiagTensor (T : Rep ℤ_[p] Γ) := WittCFlat ⊗[ℤ_[p]] T deriving AddCommGroup

namespace Lift.DiagTensor

instance : Module R (DiagTensor ρ) := leftModule

deriving instance IsScalarTower R R' for DiagTensor ρ

instance : DistribMulAction (FrobGroup Γ) (DiagTensor ρ) :=
  .compHom (_ ⊗ ρ) ((actionRep _ WittCFlat (.id _)).tprod (ρ.ρ.comp FrobGroup.snd))

instance : SMulCommClass (FrobGroup Γ) ℤ_[p] (DiagTensor ρ) := ⟨fun _ ↦ (TensorProduct.map ..).2⟩

/-- For a Z_p-linear map f: T → T', the W(C^♭)-linear map 1 ⊗ f from W(C^♭) ⊗ T to W(C^♭) ⊗ T'. -/
def map : DiagTensor ρ →ₗ[WittCFlat] DiagTensor ρ' := f.baseChange _

/-- For a Z_p-bilinear map b: T × T' → T'', its W(C^♭)-bilinear extension (W(C^♭) ⊗ T) × (W(C^♭)
⊗ T') → W(C^♭) ⊗ T''. -/
def pair : DiagTensor ρ →ₗ[WittCFlat] DiagTensor ρ' →ₗ[WittCFlat] DiagTensor ρ'' :=
  baseChangePairing b

/-- The canonical map (a, t) ↦ a ⊗ t into W(C^♭) ⊗ T, linear over W(C^♭) in a and over Z_p in t. -/
def mk : WittCFlat →ₗ[WittCFlat] ρ →ₗ[ℤ_[p]] DiagTensor ρ := AlgebraTensorModule.mk ..

lemma _root_.Lift.diagTensor_induction {P : DiagTensor ρ → Prop} (h : ∀ a t, P (mk a t)) (k : ∀ x y,
  P x → P y →
  P (x + y) := by simp +contextual <;> grind) x : P x := x.induction_on (by simpa using! h 0) h k

@[simp] lemma smul_mk m a t : m • no_index (mk a t) = mk (m • a) (ρ.ρ (FrobGroup.snd m) t) := rfl

instance [SMul (FrobGroup Γ) R] [SMulDistribClass (FrobGroup Γ) R WittCFlat] :
  SMulDistribClass (FrobGroup Γ) R
  (DiagTensor ρ) := ⟨fun _ _ ↦ diagTensor_induction fun _ _ ↦ congr($(smul_distrib_smul ..) ⊗ₜ _)⟩

@[simp] lemma map_mk a t : map f (no_index (mk a t)) = mk a (f t) := rfl

@[simp] lemma pair_mk a a' t t' : pair b (no_index (mk a t)) (no_index (mk a' t')) =
  mk (a * a') (b t t') := rfl

end Lift.DiagTensor

end

namespace Lift

section

open Algebra TensorProduct Ideal Ideal.Quotient FrobGroup algebraMap WittVector Witt
variable {p} [ThePrime p] [Γ : GroupOverGp p]

/-- The A_inf-submodule W(𝔪^♭)·(1 ⊗ 1) of W(C^♭) ⊗ ℤ/p^m(1), the image of the ideal
`Lift.wittMaxIdeal`; here Γ acts on ℤ/p^m by the cyclotomic character. -/
def smallPart m := Submodule.map (.toSpanSingleton _
  (DiagTensor (.of (charRep (QuotSpan (p ^ m : ℤ_[p])) χ))) (.mk 1 1)) wittMaxIdeal

@[simp] lemma FrobGroup.snd_inr g : snd (.inr g) = g := rfl

@[simp] lemma FrobGroup.snd_φ : snd φ = 1 := rfl

lemma FrobGroup.phi_mul_comm n : Commute φ n := .prod (.all ..) (.one_left _)

lemma smul_mem_smallPart {m} (g : Γ) {x} : x ∈ smallPart m → inr g • x ∈ smallPart m | ⟨a, h, e⟩ => e ▸ ⟨_,
                           wittMaxIdeal.smul_of_tower_mem (χ g) (mem_wittMaxIdeal.2 (mem_wittMaxIdeal.1 h · ∘ .of_map
                           (MulDistribMulAction.toMulEquiv ..) _)), by simpa [smul_distrib_smul] using! smul_tmul ..⟩

/-- Let S be the image of W(𝔪^♭) in M=W(C^♭)⊗ℤ/p^m(1). Then p^m kills M, φ−1 is onto, φd−d∈S
implies d∈ℤ/p^m(1)+S, S∩ℤ/p^m(1)=0; and for ρ trivial modulo p^m near 1, L: W(C^♭)⊗ρ→M
linear and any v, L(hv−v)∈S for h near 1.

Known result: Artin–Schreier–Witt resolution over the tilt. -/
lemma TateTwist.smallPart_spec {m} {ρ : Rep ℤ_[p] Γ} (h : ∀ y, ∀ᶠ h in nearOne Γ, ∃ w, ρ.ρ h y - y =
  p ^ m • w) (L : DiagTensor ρ →ₗ[WittCFlat] _) : let S := smallPart m
  (∀ d, p ^ m • d = 0 ∧ (∃ e, d = φ • e - e) ∧ (φ • d - d ∈ S → ∃ k, d - .mk 1 k ∈ S))
                  ∧ (∀ k, .mk 1 k ∈ S → k = 0) ∧ ∀ v, ∀ᶠ h in nearOne Γ, L (inr h • v - v) ∈ S := by
  let : ∀ d, p ^ m • d = L 0 := diagTensor_induction (by simp [← map_nsmul, ↓nsmul_quot_eq_zero])
  have s : (.mk · 1 : _ → type_of% (L 0)).Surjective := flip_mk_surjective _ mk_surjective
  have M x : .mk x 1 ∈ smallPart m ↔ _ := exists_congr fun _ ↦ and_congr_right'
    ((tensorQuotEquivQuotSMul ..).apply_eq_iff_eq.symm.trans (comm.trans SModEq.sub_mem))
  simp_all [s.forall, s.exists, mk_surjective.forall, mk_surjective.exists, -map_sub, show ∀ c,
    (.mk 1 (mk _ c) : type_of% (L 0)) = .mk _ 1 from includeRight.commutes, eq_zero_iff_dvd,
    phi_smul_wittCFlat,
    ← DiagTensor.mk.map_sub₂, mem_span_singleton, ← algebraMap_eq_smul_one, sub_eq_iff_eq_add]
  use fun x ↦ ⟨(artin_schreier_witt 1 x).imp (by aesop), fun a _ ⟨w, _⟩ ↦ ?_⟩, fun _ _ ha h ↦ by
    erw [mem_wittMaxIdeal, ← wittVector_map_algebraMap (R := OFlat), ← map_dvd_iff (equiv p).symm,
      map_pow, map_natCast, ← sub_zero ((equiv p).symm _), pow_dvd_sub_iff_coeff_eq] at *
    peel h
    simpa using ha _ ∘ ((coe_inj ..).1 this).subst ∘ .map _, diagTensor_induction (fun x y ↦
    (s (L (.mk 1 y))).rec fun d _ ↦
    ((WittCFlat.eventually_smul_sub_mem x d m).comap _).mp ((h y).mono fun _ ⟨_, _⟩ ↦ by
    erw [← M, DiagTensor.mk.map_smul₂]
    simpa [*, ← map_smul, ← DiagTensor.mk.map_smul₂] using! (·)))
    fun _ _ ↦ (·.mp <| ·.mono (by simp_all [add_sub_add_comm, add_mem]))
  obtain ⟨⟨e, rfl⟩, w, rfl⟩ := a.exists_frobEnd_sub_xi_pow_mul_eq 0, artin_schreier_witt 1 w
  obtain ⟨c⟩ := exists_algebraMap_eq_of_frobenius_eq (toWittResidue e) (by simp_all [wittMaxIdeal,
    toWittResidue, frobEnd_eq_frobenius, WittVector.ext_iff])
  peel exists_algebraMap_eq_of_frobenius_eq (x - (p ^ m * w + ↑(e - c)) : WittCFlat) (by
    simp_all [← phi_smul_wittCFlat, frobGroup_phi_smul, smul_sub, sub_eq_iff_eq_add]; ring)
  exact ⟨e - c, by simp_all [WittCFlat, wittMaxIdeal]⟩

end

open WittVector Submodule Set FrobGroup Module Fintype Algebra
variable {p} [ThePrime p] [Γ : GroupOverGp p] [k :
  KummerChart Γ] {R X} [CommRing R] [AddCommGroup X] [Module R X] {Q : Submodule R X}

instance : SMulCommClass ℤ_[p] Ainf WittCFlat := inferInstance

/-- The saturation of a submodule P of X by a submonoid M: the x in X with mx in P for some m in
M. -/
def saturateBy (M : Submonoid R) (P : Submodule R X) := ((torsion' _ _ M).comap P.mkQ).copy
  {x | ∃ r ∈ M, r • x ∈ P} (by simp [← Quotient.mk_smul])

lemma le_saturateBy {M x} (h : x ∈ Q) : x ∈ saturateBy M Q := ⟨1, by simpa⟩

lemma mem_saturateBy_of_smul {M r s x} (d : r ∣ s) (h : s ∈ M) : r • x ∈ saturateBy M Q → x ∈
  saturateBy M Q := fun ⟨a, _⟩ ↦ ⟨a * s, by grind [dvd_def, mul_smul, smul_comm, smul_mem, mul_mem]⟩

@[elab_as_elim] lemma saturateBy_induction {ι x} {f : ι → R} {C : X → Prop} (hx : x ∈ saturateBy
  (.closure (range f)) Q) (h₀ : ∀ x ∈ Q, C x) (h₁ : ∀ a x, C (f a • x) → C x) : C x := by
  obtain ⟨_, hr, _⟩ := hx
  induction hr using Submonoid.closure_induction_right generalizing x <;> grind [mul_smul, one_smul]

namespace KummerChart

/-- The letters of a Kummer chart: the multiplicative group of the field with p^f elements in
O^♭. -/
def Letter := (flatFq k.f)ˣ deriving CommGroup, Finite, IsCyclic

instance : Fintype Letter := .ofFinite _

instance : Invertible (card Letter : ℤ_[p]) := IsUnit.invertible (.of_map PadicInt.toZMod _ (by
  simp [↓card_eq_nat_card, Letter, Nat.card_units, NeZero.pos]))

/-- The permutation i ↦ i^p of the letters, the units of the field with p^f elements. -/
def letterFrob : Equiv.Perm Letter := (Units.mapEquiv (frobeniusEquiv _ p).toMulEquiv).1

/-- The multiplicative map sending a letter to its Teichmüller lift in the Witt vectors of the
field with p^f elements, viewed in the ring S of the chart. -/
def letterTeich : Letter →* k.S := (algebraMap ..).1.comp ((teichmuller p).comp (Units.coeHom _))

/-- The elements ζ of O with ζ^q = 1, where q = p^f − 1 is the number of letters of the chart. -/
abbrev LetterRoot O [Monoid O] := {ζ : O // ζ ^ .card Letter = 1}

/-- A coefficient ring for the Kummer chart k: the integer ring O of a finite extension of ℚ_p
(`PadicIntegerRing`) with an element ζ satisfying ζ^(p^f − 1) = 1. -/
structure Coeffs where (O) [commRing : CommRing O] [algebraZp : PadicIntegerRing O p]
                       (ζ : LetterRoot O)

attribute [instance] Coeffs.commRing Coeffs.algebraZp

instance : CoeSort Coeffs Type := ⟨Coeffs.O⟩

/-- A lattice Y, crystalline over Γ', with finite sets U_i of integers containing its jumps at
every embedding γ of O with γ(ζ) = θ(ω(i)), for each letter i. -/
structure JumpLattice (O : Coeffs) extends toGalLattice : GalLattice O Γ where
  (U : _ → _) /-- one set of integers for each embedding of `O` -/ (embJumps)
  /-- the lattice is crystalline on `Γ'` and has its jumps at the embedding `g` in `embJumps g` -/
  inClass : InClass (.map Γ'.subtype ⊤) ⊥ embJumps toGalLattice
  /-- `U i` contains `embJumps g` for the embeddings `g` above the letter `i` -/
  embJumps_subset {g i} : g O.ζ = (theta (letterTeich i)).1 → embJumps g ⊆ U i

variable {k O} {L : JumpLattice O} (L' : JumpLattice O) (i : Letter) (l a : ℕ) (u : ℤ)

/-- The letter a steps before i: the image of i under the a-th power of the inverse of the
permutation x ↦ x^p. -/
@[simp] abbrev Letter.stepBack := (k.letterFrob ^ a)⁻¹ i

/-- The exponent at φ^a E on the line of the jump u that is 0 for a < l and −u for a ≥ l. -/
@[grind] def stdExponent := if a < l then 0 else -u

namespace JumpLattice

/-- The module W(C^♭)⊗L for the lattice underlying L. -/
abbrev Ambient := DiagTensor (.of (overZp L.ρ))

/-- For an O-linear map F between the lattices underlying L and L', the W(C^♭)-linear map 1 ⊗ F
from W(C^♭) ⊗ L to W(C^♭) ⊗ L'. -/
abbrev wittMap (F : L.Carrier →ₗ[O] L'.Carrier) : L.Ambient →ₗ[WittCFlat] L'.Ambient :=
  DiagTensor.map F

/-- The A_inf-submodule of W(C^♭) ⊗ L spanned by the elements 1 ⊗ y, y in L. -/
def ainfLattice := span Ainf (M := L.Ambient) (range (DiagTensor.mk 1))

/-- The type of A_inf-linear maps from W(C^♭) ⊗ L to B_dR. -/
abbrev Functional := L.Ambient →ₗ[Ainf] BdR

/-- The set of A_inf-linear maps μ: W(C^♭) ⊗ L → B_dR that are Γ'-equivariant on 1 ⊗ L, that is,
μ(1 ⊗ gt) = g·μ(1 ⊗ t). -/
def forms := {μ : L.Functional | ∀ t (g : k.Γ'), μ (.mk 1 (L.ρ g t)) = toGp g.1 • μ (.mk 1 t)}

lemma frobGroup_smul_smul (m : FrobGroup Γ) (r : Ainf) (x : L.Ambient) : m • r • x =
  (m • r) • m • x := smul_distrib_smul ..

/-- The action of an element m of ℤ × Γ on W(C^♭) ⊗ L, as a map semilinear for the action of m
on A_inf. -/
@[simps] def semilinearAct (m : FrobGroup Γ) : L.Ambient →ₛₗ[MulSemiringAction.toRingHom _ Ainf m]
  L.Ambient := ⟨⟨_, smul_add m⟩, frobGroup_smul_smul m⟩

/-- The A_inf-module of the x in A_inf[1/τ] ⊗ L with μ(φ^n x) in B_dR^+ for all n ≥ 1 and all μ
in `Lift.KummerChart.JumpLattice.forms`. -/
def kisinAinf := saturateBy (.powers tau) L.ainfLattice ⊓ ⟨⟨⟨{x | ∀ n, ∀ μ ∈ L.forms, μ (φ ^ (n + 1)
  • x) ∈ hodgeFil 0}, by aesop⟩, by simp⟩, by simp_all [frobGroup_smul_smul, smul_of_tower_mem]⟩

/-- The invariant functionals μ (`Lift.KummerChart.JumpLattice.forms`) whose restriction to 1 ⊗ L
comes from a Z_p-linear map of L into the crystalline period ring B. -/
def crysForms := {μ ∈ L.forms | ∃ l : _ →ₗ[ℤ_[p]] Bcris, ∀ t, μ (.mk 1 t) = algebraMap _ _ (l t)}

/-- For an A_inf-submodule Q of W(C^♭) ⊗ L, the S-submodule of x in Q with μ(x) in the field 𝒦₀
(`Lift.KummerChart.valueField` 0) for every Γ'-equivariant form μ. -/
def valueFieldPoints (Q : Submodule Ainf L.Ambient) : Submodule k.S L.Ambient := ⟨⟨⟨{x ∈ Q | ∀ μ ∈
  forms, μ x ∈ valueField 0}, by aesop⟩, by simp⟩, fun s _ ↦ .imp (smul_mem _ _) (by
  simpa [phiInvToBdR, smul_def'] using! mul_mem (phiInvToBdR_mem_valueField s) <| · · ·)⟩

/-- The Kisin module of L: the S-module of the x in `Lift.KummerChart.JumpLattice.kisinAinf` on
which all Γ'-equivariant forms take values in the field 𝒦₀ (`Lift.KummerChart.valueField`). -/
abbrev kisinModule := valueFieldPoints L.kisinAinf

/-- The A_inf-submodule φ^l(M) of W(C^♭) ⊗ L: the x with φ^{−l}x in M =
`Lift.KummerChart.JumpLattice.kisinAinf`. -/
def frobKisinAinf := L.kisinAinf.comap (semilinearAct (φ ^ l)⁻¹)

/-- The module M = `Lift.KummerChart.JumpLattice.kisinAinf` with all φ^a E inverted: the x in W(C^♭)
⊗ L that some finite product of the φ^a E multiplies into M. -/
def kisinLocAinf := saturateBy (.closure (range (k.frobE · |>.1))) L.kisinAinf

/-- The Kisin module N with all φ^a E inverted: the x in W(C^♭) ⊗ L that some product of the φ^a
E multiplies into N. -/
def kisinLoc := L.valueFieldPoints kisinLocAinf

/-- A Γ-equivariant O-linear map L → L' between lattices with the same element ζ. -/
abbrev Hom := L.ρ.IntertwiningMap L'.ρ

/-- For an equivariant map F : L → L', the W(C^♭)-linear map W(C^♭)⊗L → W(C^♭)⊗L' obtained by
extension of scalars. -/
abbrev Hom.wittMap {L'} (F : Hom L') := L.wittMap _ F.1

/-- Scalar multiplication on L by the root of unity ζ of the coefficient ring O, as an
equivariant map from L to itself. -/
def mulZeta : L.Hom L := ⟨.lsmul _ _ O.ζ, by aesop⟩

/-- The endomorphism ω(i)⁻¹ζ of W(C^♭) ⊗ L, with ζ acting through L and ω(i), the Teichmüller
lift of the letter i, as a scalar. -/
def letterOp := k.letterTeich i⁻¹ • L.mulZeta.wittMap

/-- The part of W(C^♭) ⊗ L at the letter i: the A_inf-submodule on which ζ acts as the
Teichmüller lift ω(i). -/
def letterPart := (L.letterOp i - 1).ker.restrictScalars Ainf

/-- The endomorphism q⁻¹ Σ_{n<q} (ω(i)⁻¹ζ)^n of W(C^♭) ⊗ L, q = p^f − 1; it projects to the
letter i when ζ^q = 1. -/
def letterProj := ⅟(card Letter : ℤ_[p]) • ∑ n ∈ .range (card Letter), L.letterOp i ^ n

/-- The A_inf-linear μ: W(C^♭) ⊗ L → B_dR that are Γ'-equivariant on 1 ⊗ L and send the
projection of 1 ⊗ L to the letter i into t^{−u}B_dR^+. -/
def formsOfType := {μ ∈ L.forms | ∀ t, μ (L.letterProj i (.mk 1 t)) ∈ hodgeFil (-u)}

/-- The total multiplicity of the Hodge–Tate jump u of L over all embeddings γ of O in ℂ_p above
the letter i, that is, with γ(ζ) = θ(ω(i)). -/
abbrev jumpMultiplicity := ∑ γ with γ O.ζ = ↑(theta (k.letterTeich i)), jump L.ρ γ u

/-- The x in W(C^♭) ⊗ L that some non-zero element of A_inf multiplies into the A_inf-span of 1
⊗ L. -/
abbrev fracSpan := saturateBy (nonZeroDivisors _) L.ainfLattice

/-- The least natural number a such that all Hodge–Tate jumps of L, as a Z_p-representation of
Γ', lie in [−a, a]; it is 0 if there is none. -/
def jumpBound :=
  sInf {a : ℕ | ∀ u, jump ((overZp L.ρ).comp k.Γ'.subtype) (ofId ..) u ≠ 0 → -a ≤ u ∧ u ≤ a}

/-- For an A_inf-linear μ: W(C^♭) ⊗ L → B_dR, the map μ ∘ φ^{−a}, semilinear along
`Lift.phiInvToBdR` a: A_inf → B_dR, which is φ^{−a} followed by the structure map. -/
def valueAt (μ : L.Functional) : L.Ambient →ₛₗ[phiInvToBdR a] BdR :=
  ⟨μ.1.comp (semilinearAct (φ ^ a)⁻¹).1, by simp [phiInvToBdR, smul_def']⟩
