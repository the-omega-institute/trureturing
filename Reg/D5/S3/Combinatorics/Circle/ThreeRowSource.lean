import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.ThreeRowSource
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.ThreeRowSource

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.ThreeRowSource

abbrev signature : Signature where
  Params := Σ J : ℕ, Σ m : ℕ, Σ d : ℕ, ℕ
  State p := Fin (p.2.2.1 * baseLength p.1 p.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p i =>
    let J := p.1
    let m := p.2.1
    let d := p.2.2.1
    let s := p.2.2.2
    let k0 := baseLength J m
    let k := d * k0
    let lam := (2 ^ k - 1) / (2 ^ k0 - 1)
    let t := (lam * (M (r J) (q J m)).toNat) % (2 ^ k - 1)
    let ts := (2 ^ s * t) % (2 ^ k - 1)
    actualSource k ts i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (J m d s : ℕ) (hJ : 2 ≤ J) (hm : 1 ≤ m) (hd : 1 ≤ d),
    let k0 := baseLength J m
    let k := d * k0
    let lam := (2 ^ k - 1) / (2 ^ k0 - 1)
    let t := (lam * (M (r J) (q J m)).toNat) % (2 ^ k - 1)
    let ts := (2 ^ s * t) % (2 ^ k - 1)
    ∃ word : List (Fin k), word.Perm (List.finRange k) ∧
      (word.map (R.readout () ⟨J, ⟨m, ⟨d, s⟩⟩⟩)).sum = 0 ∧
      ∀ n : ℕ, ((word.take n).map
        (R.readout () ⟨J, ⟨m, ⟨d, s⟩⟩⟩)).sum ∈
        Set.Icc (0 : ℤ) (((2 : ℤ) ^ k - 2) / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨word, hp, hsum, _⟩ := h 2 1 1 0 (by decide) (by decide) (by decide)
  have hlength : word.length = 21 := by
    simpa [baseLength, rowLength] using hp.length_eq
  norm_num [rejected, realize, List.map_const', hlength] at hsum

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, ⟨1, ⟨1, 0⟩⟩⟩, ⟨0, by simp [baseLength, rowLength]⟩,
    ⟨1, by simp [baseLength, rowLength]⟩, ?_⟩
  norm_num [actual, realize, actualSource, centered, modulus, baseLength, rowLength,
    r, q, M, H, C, N, a, b, delta, e2, z1, z2, D, V1, V2, W1, W2]

def source_registration : Registration arena (type_of% (@exists_order)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_order, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@exists_order)
    (Realization signature) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.ThreeRowSource.exists_order.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.ThreeRowSource.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.ThreeRowSource
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration

end Reg.D5.S3.Combinatorics.Circle.ThreeRowSource
