import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.SparseThickFrameFamily
import Reg.Support.DependentFamily

open _root_.D5.S3.Combinatorics.Partitions.SparseThickFrameFamily
open _root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore
open _root_.D5.S3.Combinatorics.Partitions.PaddedWordPartition
open _root_.D5.S3.Combinatorics.Partitions.WordPartitionInverse
open _root_.D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.Partitions.SparseThickFrameFamily

abbrev wordSignature : Signature where
  Params := Σ _u : ℕ, Σ _v : ℕ, ℕ
  State p := FrameIndex p.2.2 (min p.1 p.2.2) (min p.2.1 p.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def wordActual : Realization wordSignature :=
  realize.{0,0,0,0,0} wordSignature
    (fun _ p x => sourceWord p.1 p.2.1 p.2.2 (min p.1 p.2.2) (min p.2.1 p.2.2) x)
    (fun e => nomatch e)

def wordRejected : Realization wordSignature :=
  realize.{0,0,0,0,0} wordSignature (fun _ _ _ => []) (fun e => nomatch e)

def wordArena : Arena where
  signature := wordSignature
  Law r := ∀ (u v k : ℕ) (_hk : 4096 ≤ k)
    (_hu : 4096 * k ≤ u ^ 2) (_hv : 4096 * k ≤ v ^ 2),
    let U := min u k
    let V := min v k
    (∀ x : FrameIndex k U V,
      r.readout () ⟨u,⟨v,k⟩⟩ x ∈ wordFiber u v k ∧
      (r.readout () ⟨u,⟨v,k⟩⟩ x).count true = u ∧
      (r.readout () ⟨u,⟨v,k⟩⟩ x).count false = v ∧
      scatteredTrueFalseCount (r.readout () ⟨u,⟨v,k⟩⟩ x) = k ∧
      rows (r.readout () ⟨u,⟨v,k⟩⟩ x) =
        sourceRows k U V x ++ List.replicate (v - (sourceRows k U V x).length) 0 ∧
      (sourceRows k U V x).length = grid V (side k) x.2.1 ∧
      (sourceRows k U V x).SortedGE ∧
      (∀ a ∈ sourceRows k U V x, a ≤ grid U (side k) x.1) ∧
      (sourceRows k U V x).sum = k ∧
      (thickness k U : ℝ) * (grid U (side k) x.1) ^ 2 ≤ squareRows (sourceRows k U V x) ∧
      squareRows (sourceRows k U V x) ≤
        (thickness k U : ℝ) * (grid U (side k) x.1) ^ 2 + 7 * k * side k ∧
      (thickness k V : ℝ) * (grid V (side k) x.2.1) ^ 2 ≤ oddRows (sourceRows k U V x) ∧
      oddRows (sourceRows k U V x) ≤
        (thickness k V : ℝ) * (grid V (side k) x.2.1) ^ 2 + 7 * k * side k) ∧
    Function.Injective (fun x : FrameIndex k U V =>
      (squareRows (sourceRows k U V x), oddRows (sourceRows k U V x))) ∧
    Function.Injective (fun x : FrameIndex k U V =>
      ((G (r.readout () ⟨u,⟨v,k⟩⟩ x)).e, (G (r.readout () ⟨u,⟨v,k⟩⟩ x)).f)) ∧
    Function.Injective (r.readout () ⟨u,⟨v,k⟩⟩) ∧
    (Set.range (r.readout () ⟨u,⟨v,k⟩⟩)).ncard =
      gridCount U (side k) * gridCount V (side k) * (q (level k)) ^ 6 ∧
    (Set.range (fun x : FrameIndex k U V =>
      ((G (r.readout () ⟨u,⟨v,k⟩⟩ x)).e, (G (r.readout () ⟨u,⟨v,k⟩⟩ x)).f))).ncard =
      gridCount U (side k) * gridCount V (side k) * (q (level k)) ^ 6 ∧
    gridCount U (side k) * gridCount V (side k) * (q (level k)) ^ 6 ≤ capacity u v k ∧
    U ≤ 6144 * side k * gridCount U (side k) ∧
    V ≤ 6144 * side k * gridCount V (side k) ∧
    side k < 1120 * q (level k) ∧ k ≤ (side k) ^ 2 ∧
    c0 * U * V * (k : ℝ) ^ 2 ≤ capacity u v k

private theorem wordBad : ¬ wordArena.Law wordRejected := by
  intro h
  let x : FrameIndex 4096 4096 4096 :=
    ⟨⟨0, by simp [gridCount]⟩, ⟨0, by simp [gridCount]⟩,
      ⟨⟨0, by
          norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q,
            level, side, Nat.sqrt]⟩,
        ⟨0, by
          norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q,
            level, side, Nat.sqrt]⟩⟩⟩
  have hm := ((h 4096 4096 4096 (by norm_num) (by norm_num) (by norm_num)).1 x).1
  exact hm.1 rfl

def wordRegistration : Registration wordArena (type_of% @separated_frame_family) where
  actual := wordActual
  bridge := Iff.rfl
  variation := ⟨separated_frame_family, wordRejected, wordBad⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨wordRejected, ?_, rfl, wordBad⟩
      intro j hj
      change Unit at j
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := by
    change ObservationalDependence wordSignature wordActual
    intro i
    let x : FrameIndex 1000000 1000000 1000000 :=
      ⟨⟨0, by simp [gridCount]⟩, ⟨0, by simp [gridCount]⟩,
        ⟨⟨0, by
            norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q,
              level, side, Nat.sqrt]⟩,
          ⟨0, by
            norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q,
              level, side, Nat.sqrt]⟩⟩⟩
    let y : FrameIndex 1000000 1000000 1000000 :=
      ⟨⟨0, by simp [gridCount]⟩, ⟨0, by simp [gridCount]⟩,
        ⟨⟨1, by
            norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q,
              level, side, Nat.sqrt]⟩,
          ⟨0, by
            norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q,
              level, side, Nat.sqrt]⟩⟩⟩
    refine ⟨⟨1000000,⟨1000000,1000000⟩⟩, x, y, ?_⟩
    intro he
    have hinj := (separated_frame_family 1000000 1000000 1000000
      (by norm_num) (by norm_num) (by norm_num)).2.2.2.1
    have hxy : x = y := hinj he
    have hb := congrArg (fun z : FrameIndex 1000000 1000000 1000000 => z.2.2.1.val) hxy
    norm_num [x,y] at hb

noncomputable def registration_1 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Partitions.SparseThickFrameFamily.separated_frame_family)
      (type_of% (realize.{0,0,0,0,0} wordSignature
        (fun _ p x => sourceWord p.1 p.2.1 p.2.2 (min p.1 p.2.2) (min p.2.1 p.2.2) x)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Partitions.SparseThickFrameFamily.separated_frame_family.__information_unit,
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.SparseThickFrameFamily.wordRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨wordArena⟩,
  objectArena := .source ⟨wordArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source wordArena ⟨wordRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} wordSignature
    (fun _ p x => sourceWord p.1 p.2.1 p.2.2 (min p.1 p.2.2) (min p.2.1 p.2.2) x)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.SparseThickFrameFamily
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

abbrev originalSignature : Signature where
  Params := Σ _u : ℤ, Σ _v : ℤ, ℤ
  State p := OriginalIndex p.1 p.2.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def originalActual : Realization originalSignature :=
  realize.{0,0,0,0,0} originalSignature
    (fun _ p x => originalWord p.1 p.2.1 p.2.2 x) (fun e => nomatch e)

def originalRejected : Realization originalSignature :=
  realize.{0,0,0,0,0} originalSignature (fun _ _ _ => []) (fun e => nomatch e)

def originalArena : Arena where
  signature := originalSignature
  Law r := ∀ (u v K : ℤ) (_hu : 1 ≤ u) (_hv : 1 ≤ v)
    (_hK0 : 0 ≤ K) (_hK1 : K ≤ u * v) (_hk : 1 ≤ min K (u * v - K))
    (_hs : 4096 * min K (u * v - K) ≤ (min u v) ^ 2),
    let k := min K (u * v - K)
    let U := min u k
    let V := min v k
    c0 * (U : ℝ) * (V : ℝ) * (k : ℝ) ^ 2 ≤ capacity u v K ∧
    (capacity u v K : ℤ) ≤ U * V * k ^ 2 ∧
    (4096 ≤ k →
      (∀ x : OriginalIndex u v K, r.readout () ⟨u,⟨v,K⟩⟩ x ∈ wordFiber u v K) ∧
      Function.Injective (fun x : OriginalIndex u v K =>
        ((G (r.readout () ⟨u,⟨v,K⟩⟩ x)).e, (G (r.readout () ⟨u,⟨v,K⟩⟩ x)).f)) ∧
      Function.Injective (r.readout () ⟨u,⟨v,K⟩⟩) ∧
      (Set.range (r.readout () ⟨u,⟨v,K⟩⟩)).ncard = originalFamilySize u v K ∧
      (Set.range (fun x : OriginalIndex u v K =>
        ((G (r.readout () ⟨u,⟨v,K⟩⟩ x)).e, (G (r.readout () ⟨u,⟨v,K⟩⟩ x)).f))).ncard =
        originalFamilySize u v K)

private theorem originalBad : ¬ originalArena.Law originalRejected := by
  intro h
  let x : OriginalIndex 4096 4096 4096 :=
    ⟨⟨0, by simp [gridCount]⟩, ⟨0, by simp [gridCount]⟩,
      ⟨⟨0, by norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q,
        level, side, Nat.sqrt, normalizedArea]⟩,
       ⟨0, by norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q,
        level, side, Nat.sqrt, normalizedArea]⟩⟩⟩
  have hf := (h 4096 4096 4096 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).2.2 (by norm_num)
  exact (hf.1 x).1 rfl

def originalRegistration : Registration originalArena (type_of% @sparse_joint_moment_capacity) where
  actual := originalActual
  bridge := Iff.rfl
  variation := ⟨sparse_joint_moment_capacity, originalRejected, originalBad⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨originalRejected, ?_, rfl, originalBad⟩
      intro j hj
      change Unit at j
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := by
    change ObservationalDependence originalSignature originalActual
    intro i
    let x : OriginalIndex 1000000 1000000 1000000 :=
      ⟨⟨0, by simp [gridCount]⟩, ⟨0, by simp [gridCount]⟩,
        ⟨⟨0, by norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q,
          level, side, Nat.sqrt, normalizedArea]⟩,
         ⟨0, by norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q,
          level, side, Nat.sqrt, normalizedArea]⟩⟩⟩
    let y : OriginalIndex 1000000 1000000 1000000 :=
      ⟨⟨0, by simp [gridCount]⟩, ⟨0, by simp [gridCount]⟩,
        ⟨⟨1, by
          change 1 < (2 ^ level 1000000) ^ 3
          norm_num [level, side, Nat.sqrt]⟩,
         ⟨0, by norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q,
          level, side, Nat.sqrt, normalizedArea]⟩⟩⟩
    refine ⟨⟨1000000,⟨1000000,1000000⟩⟩, x, y, ?_⟩
    intro he
    have hf := (sparse_joint_moment_capacity 1000000 1000000 1000000
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2.2
      (by norm_num)
    have hxy : x = y := hf.2.2.1 he
    have hb := congrArg (fun z : OriginalIndex 1000000 1000000 1000000 => z.2.2.1.val) hxy
    norm_num [x,y] at hb

noncomputable def registration_2 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Partitions.SparseThickFrameFamily.sparse_joint_moment_capacity)
      (type_of% (realize.{0,0,0,0,0} originalSignature
        (fun _ p x => originalWord p.1 p.2.1 p.2.2 x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Partitions.SparseThickFrameFamily.sparse_joint_moment_capacity.__information_unit,
  realizationName :=
    `Reg.D5.S3.Combinatorics.Partitions.SparseThickFrameFamily.originalRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨originalArena⟩,
  objectArena := .source ⟨originalArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source originalArena ⟨originalRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} originalSignature
    (fun _ p x => originalWord p.1 p.2.1 p.2.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.SparseThickFrameFamily
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "arg", "body", "fn", "arg", "body", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms wordRegistration
#print axioms registration_1
#print axioms originalRegistration
#print axioms registration_2

end Reg.D5.S3.Combinatorics.Partitions.SparseThickFrameFamily
