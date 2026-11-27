import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation
import Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhan

/-! The prefix-chain and quantitative rank-loss observations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.Combinatorics.Lattices.HarderNarasimhan
open _root_.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

namespace Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Threshold

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Type u) List List

def actual : Realization signature :=
  realize signature.{u} (fun _ _ l => l) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature.{u} (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law V := ∀ {Λ : Type u} [Lattice Λ] (D : SlopeData Λ) {a b : Λ} {l : List Λ}
    (_hf : D.Filtration a b l) (t : ℝ),
    ∃ c p q, a ≤ c ∧ c ≤ b ∧ D.Filtration a c (V.readout () Λ p) ∧
      D.Filtration c b q ∧ l = p ++ q ∧ (a < c → t ≤ D.muMin a c) ∧
      (c < b → D.muMax c b < t) ∧
      (((slopeList D a l).filter (fun x => decide (x < t))).length : ℝ) =
        (D.rank b : ℝ) - D.rank c

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  let D := HarderNarasimhan.Extremal.integerRankData.{u}
  have hs : D.Semistable (ULift.up 0) (ULift.up 1) := by
    constructor
    · change (0 : ℤ) < 1
      omega
    · intro x hx hxb
      simp [SlopeData.slope, D, HarderNarasimhan.Extremal.integerRankData]
  have hf : D.Filtration (ULift.up 0) (ULift.up 1) [ULift.up 1] :=
    .cons hs le_rfl (.nil _) trivial
  obtain ⟨c, p, q, hac, hcb, hp, hq, hl, hmin, hmax, hcount⟩ := law D hf 0
  change D.Filtration (ULift.up 0) c [] at hp
  cases hp
  have he := filtration_extremes D (ULift.up 0) (ULift.up 1) (ULift.up 1) [] hf
  have hm := hmax hs.1
  rw [he.2.2.2.2.1] at hm
  norm_num [SlopeData.slope, D, HarderNarasimhan.Extremal.integerRankData] at hm

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨ULift.{u} ℤ, [], [⟨0⟩], ?_⟩
  simp [actual, realize]

def family : Registration arena.{u} (type_of% @threshold_truncation.{u}) where
  actual := actual.{u}
  bridge := Iff.rfl
  variation := ⟨@threshold_truncation.{u}, rejected.{u}, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual.{u} rejected.{u} rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@threshold_truncation.{u}) (Realization signature.{u}) Unit Unit where
  unitName := .str
    `D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.threshold_truncation
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Threshold.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ l => l) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg",
        "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Threshold

namespace Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Quantitative

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {Λ : Type u} [Lattice Λ] (D : SlopeData Λ) {a b : Λ} {l : List Λ}
    (_hf : D.Filtration a b l) (s u τ : ℝ)
    (_hmax : a < b → D.muMax a b ≤ s + u),
    ∃ c p q, a ≤ c ∧ c ≤ b ∧ D.Filtration a c p ∧ D.Filtration c b q ∧
      l = p ++ q ∧ (a < c → s - τ ≤ D.muMin a c) ∧
      (c < b → D.muMax c b < s - τ) ∧
      (u + τ) * ((D.rank b : ℝ) - D.rank c) ≤
        (s + V.readout () () u) * ((D.rank b : ℝ) - D.rank a) -
          (D.degree b - D.degree a) ∧
      (0 < u + τ →
        s * ((D.rank b : ℝ) - D.rank a) ≤ D.degree b - D.degree a →
        (D.rank b : ℝ) - D.rank c ≤
          u / (u + τ) * ((D.rank b : ℝ) - D.rank a)) ∧
      (c < b → (u + τ) * ((D.rank b : ℝ) - D.rank c) <
        (s + u) * ((D.rank b : ℝ) - D.rank a) - (D.degree b - D.degree a)) ∧
      (c < b → 0 < u + τ →
        s * ((D.rank b : ℝ) - D.rank a) ≤ D.degree b - D.degree a →
        (D.rank b : ℝ) - D.rank c <
          u / (u + τ) * ((D.rank b : ℝ) - D.rank a)) ∧
      (((slopeList D a l).filter (fun x => decide (x < s - τ))).length : ℝ) =
        (D.rank b : ℝ) - D.rank c

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  let D := HarderNarasimhan.Extremal.integerRankData.{u}
  have hs : D.Semistable (ULift.up 0) (ULift.up 1) := by
    constructor
    · change (0 : ℤ) < 1
      omega
    · intro x hx hxb
      simp [SlopeData.slope, D, HarderNarasimhan.Extremal.integerRankData]
  have hf : D.Filtration (ULift.up 0) (ULift.up 1) [ULift.up 1] :=
    .cons hs le_rfl (.nil _) trivial
  have hm : (ULift.up (0 : ℤ) : ULift.{u} ℤ) < ULift.up 1 →
      D.muMax (ULift.up 0) (ULift.up 1) ≤ 0 + 1 := by
    intro _
    have he := filtration_extremes D (ULift.up 0) (ULift.up 1) (ULift.up 1) [] hf
    rw [he.2.2.2.2.1]
    norm_num [SlopeData.slope, D, HarderNarasimhan.Extremal.integerRankData]
  obtain ⟨c, p, q, hac, hcb, hp, hq, hl, hmin, hmax, hr, hdiv, hstrict, hstrictdiv, hcount⟩ :=
    law D hf 0 1 1 hm
  simp only [rejected, realize, D, HarderNarasimhan.Extremal.integerRankData] at hr
  norm_num at hr
  have hc : c.down ≤ (1 : ℤ) := hcb
  have hc' : (c.down : ℝ) ≤ 1 := by exact_mod_cast hc
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena.{u} (type_of% @quantitative_truncation.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quantitative_truncation.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quantitative_truncation.{u}) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.quantitative_truncation
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Quantitative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "body", "arg",
        "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Quantitative

namespace Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Spectrum

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => List ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ l => l.sum) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {Λ : Type u} [Lattice Λ] (D : SlopeData Λ) {a b : Λ} {l : List Λ}
    (_hf : D.Filtration a b l),
    ((slopeList D a l).length : ℝ) = (D.rank b : ℝ) - D.rank a ∧
      V.readout () () (slopeList D a l) = D.degree b - D.degree a ∧
      (∀ x ∈ slopeList D a l, D.muMin a b ≤ x ∧ x ≤ D.muMax a b) ∧
      ∀ t, ∃ c p q, a ≤ c ∧ c ≤ b ∧ D.Filtration a c p ∧ D.Filtration c b q ∧
        l = p ++ q ∧ (a < c → t ≤ D.muMin a c) ∧
        (c < b → D.muMax c b < t) ∧
        (((slopeList D a l).filter (fun x => decide (x < t))).length : ℝ) =
          (D.rank b : ℝ) - D.rank c

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  have h := (law HarderNarasimhan.Extremal.integerRankData.{u}
    (SlopeData.Filtration.nil (ULift.up 0))).2.1
  norm_num [rejected, realize, HarderNarasimhan.Extremal.integerRankData] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), [], [1], ?_⟩
  norm_num [actual, realize]

def family : Registration arena.{u} (type_of% @hn_spectrum.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hn_spectrum.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hn_spectrum.{u}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.hn_spectrum
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Spectrum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ l => l.sum) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg",
        "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Spectrum

namespace Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Scalar

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (D R w e η ρ t X z : ℝ)
    (_hD : 0 < D) (_hR : 0 < R) (_hwD : w ≤ D) (_hρ : 0 ≤ ρ)
    (_ht : R * (1 - Real.sqrt e) ≤ t) (_hX0 : 0 ≤ X)
    (_hX : X ≤ η * t ^ 2 / D)
    (_hlow : t / D * w - Real.sqrt w * Real.sqrt X ≤ z)
    (_hup : z ≤ R * (ρ + Real.sqrt (ρ * e))) (_he4 : e ≤ 1 / 4),
    V.readout () () w ((η + 4 * ρ + 4 * Real.sqrt e) * D)
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro law
  exact law 1 1 0 0 0 0 1 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hh

def family : Registration arena (type_of% @scalar_rank_estimate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@scalar_rank_estimate, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@scalar_rank_estimate) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.scalar_rank_estimate
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Scalar.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Scalar

namespace Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Variance

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (Q : H →ₗ[ℝ] H) (_hQ : Q.IsSymmetric),
    V.readout () ()
      (hs2 (Q - (LinearMap.trace ℝ H Q / (Module.finrank ℝ H : ℝ)) • LinearMap.id))
      (LinearMap.trace ℝ H (Q ∘ₗ Q) -
        (LinearMap.trace ℝ H Q) ^ 2 / Module.finrank ℝ H)
private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  exact law (H := EuclideanSpace ℝ (ULift.{u} Unit)) LinearMap.id
    LinearMap.IsSymmetric.id
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hh

def family : Registration arena.{u} (type_of% @variance_eq.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@variance_eq.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@variance_eq.{u}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.variance_eq
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Variance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Variance

namespace Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Deficit

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

open Module Finset
abbrev arena : Arena where
  signature := signature
  Law V := ∀ {K : Type u} [Fintype K] (y : K → ℝ) (s u H e η D : ℝ)
    (_hu : 0 ≤ u) (_hH : 0 ≤ H) (_hK : 0 < Fintype.card K)
    (_hlow : ∀ j, s - H ≤ y j)
    (_hcount : ∀ t ∈ Set.Icc (0 : ℝ) H,
      ((univ.filter fun j => y j < s - t).card : ℝ) ≤
        (η + 4 * (u / (u + t)) + 4 * Real.sqrt e) * D),
    V.readout () () (∑ j, max (s - y j) 0)
      (D * (4 * u * Real.log (1 + H / u) + (η + 4 * Real.sqrt e) * H)) ∧
    s - (∑ j, y j) / Fintype.card K ≤ D / Fintype.card K *
      (4 * u * Real.log (1 + H / u) + (η + 4 * Real.sqrt e) * H)
private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  have h := law (K := ULift.{u} Unit) (fun _ => 0) 0 0 0 0 0 1
    (by norm_num) (by norm_num) (by simp) (by simp)
    (by
      intro t ht
      have hzero : t = 0 := le_antisymm ht.2 ht.1
      subst t
      simp)
  exact h.1

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hh

def family : Registration arena.{u} (type_of% @finite_spectral_deficit.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_spectral_deficit.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_spectral_deficit.{u}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.finite_spectral_deficit
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Deficit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation.Deficit
