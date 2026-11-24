import Reg.D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
import D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.Module.ULift

/-! # Source registration for simultaneous Steiner switch counts -/

namespace Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport

open Function LeanInformationAudit Module Submodule
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Matroids
open _root_.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
open SteinerSchreierExtension (extensionMul extensionSteinerAndCentre)
open SteinerReturnDependencies (returnRow)
open SteinerSwitchCentre (steinerMul product_comm)
open SteinerMatchingTranslations (translate translate_involutive)
open SteinerAlternatingSwitches (SuccessfulStart point_deleted_successful_starts)
open PointDeletedSteinerSwitch (pointDeletedFamily)
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered Uncovered)
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
  (affinePlane_valid affinePlane_complete)
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
  (sig actual rejected affine_not_central)
open _root_.Reg.Support.UniverseSingleReadout (sensitivity signature)

universe j u v

noncomputable section

def commonCountLaw (R : Realization sig.{v}) : Prop :=
  ∀ {J : Type j} {L : Type u} {A : Type v} [Finite L] [Finite A] [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A]
    (e : L) (p q : J → L)
    (_unit : ∀ x : L, e * x = x) (_comm : ∀ x y : L, x * y = y * x)
    (_invol : ∀ x y : L, x * (x * y) = y) (_centreless : Set.center L = {e})
    (_different : ∀ i, p i ≠ q i) (counts : J → ℕ),
    (∃ labels : Set L → A,
      letI := extensionMul e labels
      Set.center (L × A) = {x | x.1 = e} ∧
      ∀ i, ({y : L × A | (q i, 0) * ((p i, 0) * y) ≠
        (p i, 0) * ((q i, 0) * y)} : Set (L × A)).ncard = counts i) ↔
      ∃ H : Submodule (ZMod 2) (Set L →₀ ZMod 2),
        finrank (ZMod 2) ((Set L →₀ ZMod 2) ⧸ H) ≤ finrank (ZMod 2) A ∧
        ∀ i, R.readout () () A * ({x : L |
          let g := fun y : L => p i * (q i * y)
          g (g x) ≠ x ∨ returnRow e (p i) (q i) x ∉ H} : Set L).ncard = counts i

abbrev commonCountArena : Arena := ⟨sig, commonCountLaw.{j,u,v}⟩

private abbrev AffineLoop := ULift.{u} (Option (Fin 9))

private instance : Mul AffineLoop.{u} :=
  letI := steinerMul affinePlane_valid affinePlane_complete
  inferInstanceAs (Mul (ULift (Option (Fin 9))))

private abbrev affineIdentity : AffineLoop.{u} := ULift.up none

private theorem affine_unit (x : AffineLoop.{u}) : affineIdentity * x = x := rfl

private theorem affine_comm (x y : AffineLoop.{u}) : x * y = y * x :=
  ULift.ext (product_comm affinePlane_valid affinePlane_complete x.down y.down)

private theorem affine_invol (x y : AffineLoop.{u}) : x * (x * y) = y := by
  letI := steinerMul affinePlane_valid affinePlane_complete
  apply ULift.ext
  change x.down * (x.down * y.down) = y.down
  cases h : x.down with
  | none => rfl
  | some i => exact translate_involutive affinePlane_valid affinePlane_complete i y.down

private theorem affine_centreless : Set.center AffineLoop.{u} = {affineIdentity} := by
  letI := steinerMul affinePlane_valid affinePlane_complete
  ext x
  constructor
  · intro central
    let proj : AffineLoop →ₙ* Option (Fin 9) := ⟨ULift.down, fun _ _ => rfl⟩
    have onto : Function.Surjective proj := fun y => ⟨ULift.up y, rfl⟩
    have down := Set.mem_center_iff.mp central |>.map (f := proj) onto
    have h : x.down = none := by
      change IsMulCentral x.down at down
      cases hx : x.down with
      | none => rfl
      | some i => exact (affine_not_central i (hx ▸ down)).elim
    exact ULift.ext h
  · intro equal
    change x = affineIdentity at equal
    subst x
    have rightUnit (y : AffineLoop) : y * affineIdentity = y :=
      (affine_comm y affineIdentity).trans (affine_unit y)
    exact ⟨affine_comm affineIdentity, fun _ _ => by rw [affine_unit, affine_unit],
      fun _ _ => by rw [rightUnit, rightUnit]⟩

private theorem affine_noncommuting :
    ∃ p q x : AffineLoop.{u}, q * (p * x) ≠ p * (q * x) := by
  let p : AffineLoop := ULift.up (some 0)
  suffices ∃ q x : AffineLoop, q * (p * x) ≠ p * (q * x) by
    obtain ⟨q, x, h⟩ := this
    exact ⟨p, q, x, h⟩
  by_contra! commutes
  have central : p ∈ Set.center AffineLoop := by
    refine ⟨affine_comm p, ?_, ?_⟩
    · intro x y
      calc
        p * (x * y) = p * (y * x) := congrArg (p * ·) (affine_comm x y)
        _ = y * (p * x) := (commutes y x).symm
        _ = (p * x) * y := affine_comm _ _
    · intro x y
      calc
        (x * y) * p = p * (x * y) := affine_comm _ _
        _ = x * (p * y) := (commutes x y).symm
        _ = x * (y * p) := congrArg (x * ·) (affine_comm p y)
  rw [affine_centreless] at central
  exact Option.some_ne_none _ (congrArg ULift.down (Set.mem_singleton_iff.mp central))

private theorem commonCount_rejected : ¬ commonCountLaw.{j,u,v} rejected := by
  intro bound
  let J := PUnit.{j+1}
  let A := PUnit.{v+1}
  letI : Module.Finite (ZMod 2) A :=
    Module.Finite.of_surjective (0 : ZMod 2 →ₗ[ZMod 2] A) (fun a => ⟨0, Subsingleton.elim _ a⟩)
  obtain ⟨p, q, x, noncommuting⟩ := affine_noncommuting.{u}
  have different : p ≠ q := by
    intro equal
    subst q
    exact noncommuting rfl
  let labels : Set AffineLoop → A := fun _ => 0
  letI := extensionMul affineIdentity labels
  have centre := (extensionSteinerAndCentre affineIdentity labels affine_unit affine_comm
    affine_invol (fun _ => Subsingleton.elim _ _) affine_centreless).2.2.2
  let successful : Set (AffineLoop × A) :=
    {y | (q, 0) * ((p, 0) * y) ≠ (p, 0) * ((q, 0) * y)}
  have good : (x, (0 : A)) ∈ successful :=
    fun equal => noncommuting (congrArg Prod.fst equal)
  have positive : 0 < successful.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, good⟩
  obtain ⟨H, _, noStarts⟩ := (bound (J := J) (A := A) affineIdentity (fun _ => p)
    (fun _ => q) affine_unit affine_comm affine_invol affine_centreless (fun _ => different)
    (fun _ => successful.ncard)).mp ⟨labels, centre, fun _ => rfl⟩
  have impossible := noStarts PUnit.unit
  simp only [rejected, realize, zero_mul] at impossible
  exact (Nat.ne_of_gt positive) impossible.symm

private theorem cardinality_dependence : ObservationalDependence sig.{v} actual := by
  intro role
  refine ⟨(), PUnit.{v+1}, ULift.{v} Bool, ?_⟩
  change Nat.card (PUnit.{v+1}) ≠ Nat.card (ULift.{v} Bool)
  simp [Nat.card_eq_fintype_card]

def commonCountSource :
    Registration commonCountArena.{j,u,v} (type_of% (@commonSwitchCounts.{j,u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@commonSwitchCounts, rejected, commonCount_rejected⟩
  sensitivity := sensitivity commonCountLaw actual rejected commonCount_rejected
  dependence := cardinality_dependence

def commonCountRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@commonSwitchCounts.{j,u,v}) (Realization sig.{v}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Matroids.SteinerSwitchSupport.commonSwitchCounts.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport.commonCountSource
  realizationSource := none
  generated := false
  arena := .source ⟨commonCountArena⟩
  objectArena := .source ⟨commonCountArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source commonCountArena ⟨commonCountSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "arg", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def labelledCountLaw (R : Realization sig.{v}) : Prop :=
  ∀ {J : Type j} {L : Type u} {A : Type v}
    [Finite L] [Nontrivial L] [Finite A] [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A]
    (e : L) (p q : J → L)
    (_unit : ∀ x : L, e * x = x) (_comm : ∀ x y : L, x * y = y * x)
    (_invol : ∀ x y : L, x * (x * y) = y) (_centreless : Set.center L = {e})
    (_hp : ∀ j, p j ≠ e) (_hq : ∀ j, q j ≠ e) (_different : ∀ j, p j ≠ q j)
    (H : Submodule (ZMod 2) (Set L →₀ ZMod 2))
    (_dimension : finrank (ZMod 2) ((Set L →₀ ZMod 2) ⧸ H) ≤ finrank (ZMod 2) A),
    ∃ (labels : Set L → A) (r : ℕ) (label : Option (Fin (r + 1)) ≃ L × A)
      (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
      (cover : ∀ a b : Fin (r + 1), a ≠ b → Covered S a b),
      letI := extensionMul e labels
      label none = (e, 0) ∧
      Set.center (L × A) = {x | x.1 = e} ∧
      (∀ i a, label (translate valid cover i a) = label (some i) * label a) ∧
      ∀ j, ∃ (i : Fin (r + 1)) (v : Fin r) (m : Fin r → Fin r),
        label (some i) = (p j, 0) ∧ label (some (i.succAbove v)) = (q j, 0) ∧
        (∀ a b, Uncovered (pointDeletedFamily S i) a b ↔ m a = b) ∧
        ({a | SuccessfulStart (pointDeletedFamily S i) m v a} : Set (Fin r)).ncard =
          R.readout () () A * ({x : L |
            let g := fun y : L => p j * (q j * y)
            g (g x) ≠ x ∨ returnRow e (p j) (q j) x ∉ H} : Set L).ncard

abbrev labelledCountArena : Arena := ⟨sig, labelledCountLaw.{j,u,v}⟩

private theorem labelledCount_rejected : ¬ labelledCountLaw.{j,u,v} rejected := by
  intro bound
  let J := PUnit.{j+1}
  let A := PUnit.{v+1}
  letI : Module.Finite (ZMod 2) A :=
    Module.Finite.of_surjective (0 : ZMod 2 →ₗ[ZMod 2] A) (fun a => ⟨0, Subsingleton.elim _ a⟩)
  obtain ⟨p, q, x, noncommuting⟩ := affine_noncommuting.{u}
  have hp : p ≠ affineIdentity := by
    intro h
    exact noncommuting (by rw [h, affine_unit, affine_unit])
  have hq : q ≠ affineIdentity := by
    intro h
    exact noncommuting (by rw [h, affine_unit, affine_unit])
  have hpq : p ≠ q := by
    intro h
    subst q
    exact noncommuting rfl
  let H : Submodule (ZMod 2) (Set AffineLoop →₀ ZMod 2) := ⊤
  have dimension : finrank (ZMod 2) ((Set AffineLoop →₀ ZMod 2) ⧸ H) ≤ finrank (ZMod 2) A := by
    have h : finrank (ZMod 2) ((Set AffineLoop →₀ ZMod 2) ⧸ H) = 0 := by
      change finrank (ZMod 2) ((Set AffineLoop →₀ ZMod 2) ⧸
        (⊤ : Submodule (ZMod 2) (Set AffineLoop →₀ ZMod 2))) = 0
      exact Module.finrank_zero_of_subsingleton
    rw [h]
    exact Nat.zero_le _
  obtain ⟨_, r, label, S, valid, cover, _, _, _, profiles⟩ :=
    bound (J := J) (A := A) affineIdentity (fun _ => p) (fun _ => q)
      affine_unit affine_comm affine_invol affine_centreless (fun _ => hp) (fun _ => hq)
      (fun _ => hpq) H dimension
  obtain ⟨i, v, m, _, _, leave, noStarts⟩ := profiles PUnit.unit
  have size := Nat.card_congr label
  have rEq : r = 8 := by
    change Nat.card (Option (Fin (r + 1))) = Nat.card (ULift.{u} (Option (Fin 9)) × A) at size
    dsimp only [A] at size
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin,
      Fintype.card_prod, Fintype.card_ulift, Fintype.card_punit, mul_one] at size
    omega
  have hr : 4 ∣ r := rEq.symm ▸ (by decide : 4 ∣ 8)
  obtain ⟨_, canonical, canonicalLeave, starts⟩ := point_deleted_successful_starts S valid cover i
  have same : canonical = m := funext fun a =>
    ((leave a (canonical a)).mp ((canonicalLeave a (canonical a)).mpr rfl)).symm
  subst canonical
  have six := (starts v).2.2 hr
  simp only [rejected, realize, zero_mul] at noStarts
  omega

def labelledCountSource :
    Registration labelledCountArena.{j,u,v} (type_of% (@labelledCommonSwitchCounts.{j,u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@labelledCommonSwitchCounts, rejected, labelledCount_rejected⟩
  sensitivity := sensitivity labelledCountLaw actual rejected labelledCount_rejected
  dependence := cardinality_dependence

def labelledCountRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@labelledCommonSwitchCounts.{j,u,v}) (Realization sig.{v}) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Matroids.SteinerSwitchSupport.labelledCommonSwitchCounts.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport.labelledCountSource
  realizationSource := none
  generated := false
  arena := .source ⟨labelledCountArena⟩
  objectArena := .source ⟨labelledCountArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source labelledCountArena ⟨labelledCountSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg",
        "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg",
        "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev supportSig := signature (Sigma fun _ : Type j => Type v)
    (fun P => P.1 → P.2) (fun P => P.1 → P.2)

def supportActual : Realization supportSig.{j,v} :=
  realize supportSig (fun _ _ target => target) (fun anchor => nomatch anchor)

def supportRejected : Realization supportSig.{j,v} := by
  classical
  exact realize supportSig (fun _ _ target i =>
    if h : ∃ a, a ≠ target i then Classical.choose h else target i) (fun anchor => nomatch anchor)

def supportLaw (R : Realization supportSig.{j,v}) : Prop :=
  ∀ {I : Type j} {L : Type u} {A : Type v} [Finite L] [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A] [Module.Finite (ZMod 2) A]
    (e : L) (p q rep : I → L) (G : I → SimpleGraph L)
    (_unit : ∀ x : L, e * x = x) (_comm : ∀ x y : L, x * y = y * x)
    (_invol : ∀ x y : L, x * (x * y) = y) (_centreless : Set.center L = {e})
    (_edges : ∀ i u v, (G i).Adj u v ↔ p i * u = v ∨ q i * u = v)
    (vanishes : I → Prop),
    (∃ labels : Set L → A, ∃ target : I → A,
      (∀ i, R.readout () ⟨I, A⟩ target i = 0 ↔ vanishes i) ∧
      letI := extensionMul e labels
      ∀ i x, (G i).Reachable (rep i) x → ∀ a : A,
        (fun y : L × A => (p i, 0) * ((q i, 0) * y))^[
          minimalPeriod (fun y => p i * (q i * y)) x] (x, a) = (x, a + target i)) ↔
      HasAvoidingSubspace (K := ZMod 2) (fun i => returnRow e (p i) (q i) (rep i))
        vanishes (finrank (ZMod 2) A)

abbrev supportArena : Arena := ⟨supportSig, supportLaw.{j,u,v}⟩

private theorem support_rejected : ¬ supportLaw.{j,u,v} supportRejected := by
  classical
  intro rule
  let I := PUnit.{j+1}
  let L := AffineLoop.{u}
  let A := ULift.{v} (ZMod 2)
  let e : L := affineIdentity
  let p : L := ULift.up (some 0)
  let G : SimpleGraph L := SimpleGraph.fromRel (fun x y => p * x = y)
  have hp : p ≠ e := fun h => Option.some_ne_none _ (congrArg ULift.down h)
  have edges (i : I) (x y : L) : G.Adj x y ↔ p * x = y ∨ p * x = y := by
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, h | h⟩
      · exact Or.inl h
      · exact Or.inl ((congrArg (p * ·) h).symm.trans (affine_invol p y))
    · intro h
      have hxy := h.elim id id
      refine ⟨?_, Or.inl hxy⟩
      intro equal
      have px : p * x = e * x := (hxy.trans equal.symm).trans (affine_unit x).symm
      have xp : x * p = x * e := by simpa only [affine_comm x p, affine_comm x e] using px
      exact hp ((show Involutive (x * ·) from affine_invol x).injective xp)
  have avoiding : HasAvoidingSubspace (K := ZMod 2)
      (fun _ : I => returnRow e p p e) (fun _ => True) (finrank (ZMod 2) A) := by
    unfold HasAvoidingSubspace
    dsimp only
    refine ⟨⊤, ?_, fun _ no => (no trivial).elim⟩
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  obtain ⟨labels, target, support, returns⟩ :=
    (rule (A := A) e (fun _ => p) (fun _ => p) (fun _ => e) (fun _ => G) affine_unit
      affine_comm affine_invol affine_centreless edges (fun _ => True)).mpr avoiding
  letI := extensionMul e labels
  have twice (a : A) : a + a = 0 := by
    apply ULift.ext
    exact (show ∀ b : ZMod 2, b + b = 0 by decide) a.down
  obtain ⟨_, _, invol, _⟩ :=
    extensionSteinerAndCentre e labels affine_unit affine_comm affine_invol twice affine_centreless
  have period : minimalPeriod (fun y : L => p * (p * y)) e = 1 :=
    minimalPeriod_eq_one_iff_isFixedPt.mpr (affine_invol p e)
  have zero := returns PUnit.unit e SimpleGraph.Reachable.rfl 0
  rw [period, Function.iterate_one, invol] at zero
  have targetZero : target PUnit.unit = 0 := by
    simpa only [zero_add] using (congrArg Prod.snd zero).symm
  have others : ∃ a : A, a ≠ target PUnit.unit := by
    rw [targetZero]
    exact ⟨ULift.up 1, by decide⟩
  have observed := (support PUnit.unit).mpr trivial
  simp only [supportRejected, realize, dif_pos others] at observed
  exact Classical.choose_spec others (observed.trans targetZero.symm)

private theorem support_dependence : ObservationalDependence supportSig.{j,v} supportActual := by
  intro role
  refine ⟨⟨PUnit.{j+1}, ULift.{v} Bool⟩, (fun _ => ULift.up false),
    (fun _ => ULift.up true), ?_⟩
  intro equal
  exact Bool.noConfusion (congrArg ULift.down (congrFun equal PUnit.unit))

def supportSource :
    Registration supportArena.{j,u,v} (type_of% (@realizesReturnSupport.{j,u,v})) where
  actual := supportActual
  bridge := Iff.rfl
  variation := ⟨@realizesReturnSupport, supportRejected, support_rejected⟩
  sensitivity := sensitivity supportLaw supportActual supportRejected support_rejected
  dependence := support_dependence

def supportRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@realizesReturnSupport.{j,u,v}) (Realization supportSig.{j,v})
      (Sigma fun _ : Type j => Type v) Unit where
  unitName :=
    `D5.S3.Combinatorics.Matroids.SteinerSwitchSupport.realizesReturnSupport.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport.supportSource
  realizationSource := none
  generated := false
  arena := .source ⟨supportArena⟩
  objectArena := .source ⟨supportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source supportArena ⟨supportSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize supportSig supportActual.readout supportActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "arg", "body", "fn", "arg", "body", "fn", "arg",
        "fn", "arg", "fn"]
      stateBinder := 20
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
