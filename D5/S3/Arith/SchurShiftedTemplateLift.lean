/- GID: D5/S3/Arith/SchurShiftedTemplateLift
   generality: G
   mirror-B: D5/B/S3/Arith/SchurShiftedTemplateLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/SchurShiftedTemplateLift.schur_shifted_widthTen_lift; instance=D5/S3/Arith/SchurShiftedTemplateLift.tableII_finite_compatibility
   digest: A checked shifted width-ten template extends every finite Schur coloring by two colors and two terminal positions. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.SchurShiftedTemplateLift

/-- A coloring of the positive interval through `n` with no monochromatic
solution of `x + y = z`. -/
def SchurColoring (k n : Nat) (c : Nat -> Fin k) : Prop :=
  forall x y z, 0 < x -> 0 < y -> z <= n -> x + y = z ->
    Not (c x = c y /\ c y = c z)

/-- Existence of a sum-free `k`-coloring of the positive interval through `n`. -/
def HasSchurColoring (k n : Nat) : Prop :=
  Exists fun c : Nat -> Fin k => SchurColoring k n c

/-- The defining convention has the expected first three small cases. -/
theorem schur_coloring_small_values :
    HasSchurColoring 1 1 /\ HasSchurColoring 2 4 /\
      Not (HasSchurColoring 1 2) := by
  constructor
  · refine ⟨fun _ => 0, ?_⟩
    intro x y z hx hy hz hxy
    omega
  constructor
  · let c : Nat -> Fin 2 := fun x => if x = 1 \/ x = 4 then 0 else 1
    refine ⟨c, ?_⟩
    intro x y z hx hy hz hxy same
    dsimp [c] at same
    split_ifs at same <;> simp_all <;> omega
  · rintro ⟨c, hc⟩
    have bad := hc 1 1 2 (by omega) (by omega) (by omega) (by omega)
    exact bad ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The classical construction with two copies of the old coloring separated
by a monochromatic middle interval. -/
theorem schur_triple_lift (k n : Nat) :
    HasSchurColoring k n -> HasSchurColoring (k + 1) (3 * n + 1) := by
  rintro ⟨c, hc⟩
  let liftOld : Fin k -> Fin (k + 1) := Fin.castLE (by omega)
  let color : Nat -> Fin (k + 1) := fun x =>
    if x <= n then liftOld (c x)
    else if x <= 2 * n + 1 then ⟨k, by omega⟩
    else liftOld (c (x - (2 * n + 1)))
  refine ⟨color, ?_⟩
  intro x y z hx hy hz hxy same
  rcases same with ⟨hxyc, hyzc⟩
  dsimp [color] at hxyc hyzc
  by_cases xLeft : x <= n
  · simp only [if_pos xLeft] at hxyc
    by_cases yLeft : y <= n
    · simp only [if_pos yLeft] at hxyc hyzc
      by_cases zLeft : z <= n
      · simp only [if_pos zLeft] at hyzc
        apply hc x y z hx hy zLeft hxy
        constructor
        · apply Fin.ext
          simpa [liftOld] using congrArg Fin.val hxyc
        · apply Fin.ext
          simpa [liftOld] using congrArg Fin.val hyzc
      · have zMiddle : z <= 2 * n + 1 := by omega
        simp only [if_neg zLeft, if_pos zMiddle] at hyzc
        have values := congrArg Fin.val hyzc
        simp [liftOld] at values
        omega
    · simp only [if_neg yLeft] at hxyc
      by_cases yMiddle : y <= 2 * n + 1
      · simp only [if_pos yMiddle] at hxyc
        have values := congrArg Fin.val hxyc
        simp [liftOld] at values
        omega
      · simp only [if_neg yMiddle] at hxyc
        simp only [if_neg yLeft, if_neg yMiddle] at hyzc
        have zRight : Not (z <= 2 * n + 1) := by omega
        have zNotLeft : Not (z <= n) := by omega
        simp only [if_neg zNotLeft, if_neg zRight] at hyzc
        apply hc x (y - (2 * n + 1)) (z - (2 * n + 1))
        · exact hx
        · omega
        · omega
        · omega
        constructor
        · apply Fin.ext
          simpa [liftOld] using congrArg Fin.val hxyc
        · apply Fin.ext
          simpa [liftOld] using congrArg Fin.val hyzc
  · simp only [if_neg xLeft] at hxyc
    by_cases xMiddle : x <= 2 * n + 1
    · simp only [if_pos xMiddle] at hxyc
      by_cases yLeft : y <= n
      · simp only [if_pos yLeft] at hxyc
        have values := congrArg Fin.val hxyc
        simp [liftOld] at values
        omega
      · by_cases yMiddle : y <= 2 * n + 1
        · have zRight : Not (z <= 2 * n + 1) := by omega
          have zNotLeft : Not (z <= n) := by omega
          simp only [if_neg yLeft, if_pos yMiddle] at hxyc
          simp only [if_neg yLeft, if_pos yMiddle, if_neg zNotLeft,
            if_neg zRight] at hyzc
          have values := congrArg Fin.val hyzc
          simp [liftOld] at values
          omega
        · omega
    · by_cases yLeft : y <= n
      · simp only [if_pos yLeft] at hxyc
        simp only [if_pos yLeft] at hyzc
        have zRight : Not (z <= 2 * n + 1) := by omega
        have zNotLeft : Not (z <= n) := by omega
        simp only [if_neg xMiddle] at hxyc
        simp only [if_neg zNotLeft, if_neg zRight] at hyzc
        apply hc (x - (2 * n + 1)) y (z - (2 * n + 1))
        · omega
        · exact hy
        · omega
        · omega
        constructor
        · apply Fin.ext
          simpa [liftOld] using congrArg Fin.val hxyc
        · apply Fin.ext
          simpa [liftOld] using congrArg Fin.val hyzc
      · omega

/-- Cell labels used by shifted width-ten templates. -/
inductive ShiftedTemplateLabel where
  | A
  | B
  | PminusOne
  | Pzero
  deriving DecidableEq, Repr

/-- A width-ten template has one row for the first block and one row for all
subsequent blocks. -/
abbrev WidthTenTemplate := Bool -> Fin 10 -> ShiftedTemplateLabel

private def labelShift : ShiftedTemplateLabel -> Option Int
  | .A | .B => none
  | .PminusOne => some (-1)
  | .Pzero => some 0

private def labelsCompatible (carry : Nat)
    (left right result : ShiftedTemplateLabel) : Bool :=
  !(left == .A && right == .A && result == .A) &&
  !(left == .B && right == .B && result == .B) &&
  match labelShift left, labelShift right, labelShift result with
  | some a, some b, some c => c == a + b + 1 - carry
  | _, _, _ => true

private def columnCarry (u v : Fin 10) : Nat :=
  (u.val + v.val + 1) / 10

private def sumColumn (u v : Fin 10) : Fin 10 :=
  ⟨(u.val + v.val + 1) % 10, Nat.mod_lt _ (by omega)⟩

private def resultIsFirst (leftFirst rightFirst : Bool) (carry : Nat) : Bool :=
  leftFirst && rightFirst && carry == 0

private def tailLabelAtNat (tail : Fin 2 -> ShiftedTemplateLabel) (column : Nat) :
    ShiftedTemplateLabel :=
  if h : column < 2 then tail ⟨column, h⟩ else .A

private abbrev WidthTenCase := Bool × Bool × Fin 10 × Fin 10

private def FirstRowLicit (template : WidthTenTemplate) : Prop :=
  forall u, Not (template true u = .PminusOne)

private def MainCaseCompatible (template : WidthTenTemplate)
    (input : WidthTenCase) : Prop :=
  labelsCompatible (columnCarry input.2.2.1 input.2.2.2)
    (template input.1 input.2.2.1) (template input.2.1 input.2.2.2)
    (template (resultIsFirst input.1 input.2.1
      (columnCarry input.2.2.1 input.2.2.2))
      (sumColumn input.2.2.1 input.2.2.2)) = true

private def MainTableCompatible (template : WidthTenTemplate) : Prop :=
  forall input : WidthTenCase, MainCaseCompatible template input

private def TailCaseCompatible (template : WidthTenTemplate)
    (tail : Fin 2 -> ShiftedTemplateLabel) (input : WidthTenCase) : Prop :=
  (sumColumn input.2.2.1 input.2.2.2).val < 2 ->
  resultIsFirst input.1 input.2.1
    (columnCarry input.2.2.1 input.2.2.2) = false ->
  labelsCompatible (columnCarry input.2.2.1 input.2.2.2)
    (template input.1 input.2.2.1) (template input.2.1 input.2.2.2)
    (tailLabelAtNat tail (sumColumn input.2.2.1 input.2.2.2).val) = true

private def TailTableCompatible (template : WidthTenTemplate)
    (tail : Fin 2 -> ShiftedTemplateLabel) : Prop :=
  forall input : WidthTenCase, TailCaseCompatible template tail input

/-- The complete finite obligations for a width-ten shifted template and a
two-cell ordinary-color tail. -/
def WidthTenTemplateCompatible (template : WidthTenTemplate)
    (tail : Fin 2 -> ShiftedTemplateLabel) : Prop :=
  FirstRowLicit template /\ MainTableCompatible template /\
    TailTableCompatible template tail

/-- Executable checker for all first/subsequent row choices and column pairs. -/
def checkWidthTenTemplate (template : WidthTenTemplate)
    (tail : Fin 2 -> ShiftedTemplateLabel) : Bool :=
  letI : DecidablePred (MainCaseCompatible template) := fun input => by
    unfold MainCaseCompatible
    infer_instance
  letI : DecidablePred (TailCaseCompatible template tail) := fun input => by
    unfold TailCaseCompatible
    infer_instance
  @decide (FirstRowLicit template) Fintype.decidableForallFintype &&
    @decide (MainTableCompatible template) Fintype.decidableForallFintype &&
    @decide (TailTableCompatible template tail) Fintype.decidableForallFintype

/-- Acceptance of the finite checker implies every compatibility obligation. -/
theorem checkWidthTenTemplate_sound (template : WidthTenTemplate)
    (tail : Fin 2 -> ShiftedTemplateLabel)
    (accepted : checkWidthTenTemplate template tail = true) :
    WidthTenTemplateCompatible template tail := by
  let _ : DecidablePred (MainCaseCompatible template) := fun input => by
    unfold MainCaseCompatible
    infer_instance
  let _ : DecidablePred (TailCaseCompatible template tail) := fun input => by
    unfold TailCaseCompatible
    infer_instance
  let _ : Decidable (FirstRowLicit template) := Fintype.decidableForallFintype
  let _ : Decidable (MainTableCompatible template) := Fintype.decidableForallFintype
  let _ : Decidable (TailTableCompatible template tail) :=
    Fintype.decidableForallFintype
  simp only [checkWidthTenTemplate, Bool.and_eq_true] at accepted
  exact ⟨of_decide_eq_true accepted.1.1, of_decide_eq_true accepted.1.2,
    of_decide_eq_true accepted.2⟩

/-- The width-ten shifted template recorded in Table II of arXiv:2607.15034. -/
def tableIITemplate : WidthTenTemplate := fun first column =>
  match first, column.val with
  | true, 0 => .B
  | false, 0 => .PminusOne
  | true, 1 => .A
  | false, 1 => .B
  | _, 2 => .Pzero
  | _, 3 => .Pzero
  | _, 4 => .B
  | _, 5 => .A
  | _, 6 => .A
  | _, 7 => .B
  | _, 8 => .Pzero
  | _, _ => .Pzero

/-- The two-cell tail recorded with the Table II template. -/
def tableIITail : Fin 2 -> ShiftedTemplateLabel := fun column =>
  if column.val = 0 then .A else .B

private def blockRow (x : Nat) : Nat := (x - 1) / 10
private def blockColumnNat (x : Nat) : Nat := (x - 1) % 10

private theorem blockColumnNat_lt (x : Nat) : blockColumnNat x < 10 := by
  exact Nat.mod_lt _ (by omega)

private def blockColumn (x : Nat) : Fin 10 :=
  ⟨blockColumnNat x, blockColumnNat_lt x⟩

/-- Table II passes the finite checker, and positive width-ten block
coordinates split addition into the stated row carry and column residue. -/
theorem tableII_finite_compatibility :
    checkWidthTenTemplate tableIITemplate tableIITail = true /\
    forall x y z : Nat, 0 < x -> 0 < y -> x + y = z ->
      blockRow z = blockRow x + blockRow y +
          (blockColumnNat x + blockColumnNat y + 1) / 10 /\
        blockColumnNat z =
          (blockColumnNat x + blockColumnNat y + 1) % 10 := by
  constructor
  · decide +kernel
  · intro x y z hx hy hxy
    subst z
    simp only [blockRow, blockColumnNat]
    omega

private def encodeColor {k : Nat} : Fin k ⊕ Fin 2 -> Fin (k + 2)
  | .inl old => ⟨old.val, by omega⟩
  | .inr fresh => ⟨k + fresh.val, by omega⟩

private theorem encodeColor_injective {k : Nat} :
    Function.Injective (@encodeColor k) := by
  intro left right equal
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          congr 1
          apply Fin.ext
          simpa [encodeColor] using congrArg Fin.val equal
      | inr right =>
          have values := congrArg Fin.val equal
          simp [encodeColor] at values
          omega
  | inr left =>
      cases right with
      | inl right =>
          have values := congrArg Fin.val equal
          simp [encodeColor] at values
          omega
      | inr right =>
          congr 1
          apply Fin.ext
          simpa [encodeColor] using congrArg Fin.val equal

private def labelColorSum {k : Nat} (c : Nat -> Fin k) (row : Nat) :
    ShiftedTemplateLabel -> Fin k ⊕ Fin 2
  | .A => .inr 0
  | .B => .inr 1
  | .PminusOne => .inl (c row)
  | .Pzero => .inl (c (row + 1))

private def labelColor {k : Nat} (c : Nat -> Fin k) (row : Nat)
    (label : ShiftedTemplateLabel) : Fin (k + 2) :=
  encodeColor (labelColorSum c row label)

private def oldIndex (row : Nat) : ShiftedTemplateLabel -> Nat
  | .PminusOne => row
  | _ => row + 1

private theorem compatible_label_colors_sum_free {k n : Nat}
    (c : Nat -> Fin k) (hc : SchurColoring k n c)
    {leftRow rightRow resultRow carry : Nat}
    {leftLabel rightLabel resultLabel : ShiftedTemplateLabel}
    (rowEquation : resultRow = leftRow + rightRow + carry)
    (carryBound : carry <= 1)
    (resultBound : resultRow < n)
    (leftLicit : leftLabel = .PminusOne -> 0 < leftRow)
    (rightLicit : rightLabel = .PminusOne -> 0 < rightRow)
    (resultLicit : resultLabel = .PminusOne -> 0 < resultRow)
    (compatible : labelsCompatible carry leftLabel rightLabel resultLabel = true) :
    Not (labelColor c leftRow leftLabel = labelColor c rightRow rightLabel /\
      labelColor c rightRow rightLabel = labelColor c resultRow resultLabel) := by
  rintro ⟨leftRight, rightResult⟩
  have leftRight' := encodeColor_injective leftRight
  have rightResult' := encodeColor_injective rightResult
  let leftIndex := oldIndex leftRow leftLabel
  let rightIndex := oldIndex rightRow rightLabel
  let resultIndex := oldIndex resultRow resultLabel
  cases leftLabel <;> cases rightLabel <;> cases resultLabel <;>
    simp [labelsCompatible, labelShift, labelColorSum] at compatible leftRight' rightResult' leftLicit rightLicit resultLicit
  all_goals try omega
  all_goals
    refine hc leftIndex rightIndex resultIndex
      (by simp [leftIndex, oldIndex] <;> omega)
      (by simp [rightIndex, oldIndex] <;> omega)
      (by simp [resultIndex, oldIndex]; omega)
      (by simp [leftIndex, rightIndex, resultIndex, oldIndex]; omega)
      ⟨leftRight', rightResult'⟩

private theorem compatible_label_colors_fresh_result {k : Nat}
    (c : Nat -> Fin k) {leftRow rightRow carry : Nat}
    {leftLabel rightLabel resultLabel : ShiftedTemplateLabel}
    (resultFresh : resultLabel = .A \/ resultLabel = .B)
    (compatible : labelsCompatible carry leftLabel rightLabel resultLabel = true) :
    Not (labelColor c leftRow leftLabel = labelColor c rightRow rightLabel /\
      labelColor c rightRow rightLabel = labelColor c 0 resultLabel) := by
  rintro ⟨leftRight, rightResult⟩
  have leftRight' := encodeColor_injective leftRight
  have rightResult' := encodeColor_injective rightResult
  rcases resultFresh with rfl | rfl <;>
    cases leftLabel <;> cases rightLabel <;>
      simp [labelsCompatible, labelShift, labelColorSum] at compatible leftRight' rightResult'

private def shiftedWidthTenColor {k : Nat} (c : Nat -> Fin k) (n x : Nat) :
    Fin (k + 2) :=
  if _main : x <= 10 * n then
    labelColor c (blockRow x)
      (tableIITemplate (blockRow x == 0) (blockColumn x))
  else if _firstTail : x = 10 * n + 1 then
    labelColor c 0 (tableIITail 0)
  else
    labelColor c 0 (tableIITail 1)

/-- The checked shifted template sends every `k`-coloring through `n` to a
`k+2`-coloring through `10*n+2`. -/
theorem schur_shifted_widthTen_lift (k n : Nat) :
    HasSchurColoring k n -> HasSchurColoring (k + 2) (10 * n + 2) := by
  rintro ⟨c, hc⟩
  obtain ⟨checked, decomposition⟩ := tableII_finite_compatibility
  have compatible := checkWidthTenTemplate_sound _ _ checked
  refine ⟨shiftedWidthTenColor c n, ?_⟩
  intro x y z hx hy hz hxy same
  have parts := decomposition x y z hx hy hxy
  have rowEquation : blockRow z = blockRow x + blockRow y +
      columnCarry (blockColumn x) (blockColumn y) := by
    simpa [columnCarry, blockColumn] using parts.1
  have columnEquation : blockColumn z =
      sumColumn (blockColumn x) (blockColumn y) := by
    apply Fin.ext
    simpa [sumColumn, blockColumn] using parts.2
  have carryBound : columnCarry (blockColumn x) (blockColumn y) <= 1 := by
    have leftColumn := blockColumnNat_lt x
    have rightColumn := blockColumnNat_lt y
    simp only [columnCarry, blockColumn]
    omega
  have firstEquation : (blockRow z == 0) =
      resultIsFirst (blockRow x == 0) (blockRow y == 0)
        (columnCarry (blockColumn x) (blockColumn y)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [resultIsFirst, Bool.and_eq_true, beq_iff_eq]
    omega
  by_cases zMain : z <= 10 * n
  · have xMain : x <= 10 * n := by omega
    have yMain : y <= 10 * n := by omega
    have resultBound : blockRow z < n := by
      simp only [blockRow]
      omega
    have localCompatible := compatible.2.1
      (((blockRow x == 0), (blockRow y == 0), blockColumn x, blockColumn y) :
        WidthTenCase)
    unfold MainCaseCompatible at localCompatible
    rw [<- firstEquation, <- columnEquation] at localCompatible
    have leftLicit :
        tableIITemplate (blockRow x == 0) (blockColumn x) = .PminusOne ->
          0 < blockRow x := by
      intro label
      by_contra notPositive
      have rowZero : blockRow x = 0 := by omega
      exact compatible.1 (blockColumn x) (by simpa [rowZero] using label)
    have rightLicit :
        tableIITemplate (blockRow y == 0) (blockColumn y) = .PminusOne ->
          0 < blockRow y := by
      intro label
      by_contra notPositive
      have rowZero : blockRow y = 0 := by omega
      exact compatible.1 (blockColumn y) (by simpa [rowZero] using label)
    have resultLicit :
        tableIITemplate (blockRow z == 0) (blockColumn z) = .PminusOne ->
          0 < blockRow z := by
      intro label
      by_contra notPositive
      have rowZero : blockRow z = 0 := by omega
      exact compatible.1 (blockColumn z) (by simpa [rowZero] using label)
    apply compatible_label_colors_sum_free c hc rowEquation carryBound
      resultBound leftLicit rightLicit resultLicit localCompatible
    simpa [shiftedWidthTenColor, xMain, yMain, zMain] using same
  · by_cases xMain : x <= 10 * n
    · by_cases yMain : y <= 10 * n
      · have nPositive : 0 < n := by omega
        have resultNotFirst :
            resultIsFirst (blockRow x == 0) (blockRow y == 0)
              (columnCarry (blockColumn x) (blockColumn y)) = false := by
          rw [<- firstEquation]
          have zRow : blockRow z = n := by
            simp only [blockRow]
            omega
          simp [zRow, Nat.ne_of_gt nPositive]
        have tailColumnBound :
            (sumColumn (blockColumn x) (blockColumn y)).val < 2 := by
          rw [<- columnEquation]
          simp only [blockColumn, blockColumnNat]
          omega
        have localCompatible := compatible.2.2
          (((blockRow x == 0), (blockRow y == 0), blockColumn x, blockColumn y) :
            WidthTenCase) tailColumnBound resultNotFirst
        by_cases firstTail : z = 10 * n + 1
        · have sumColumnZero :
              (sumColumn (blockColumn x) (blockColumn y)).val = 0 := by
            rw [<- columnEquation]
            simp only [blockColumn, blockColumnNat]
            omega
          apply compatible_label_colors_fresh_result c
            (Or.inl (by simp [tailLabelAtNat, tableIITail, sumColumnZero]))
            localCompatible
          simpa [shiftedWidthTenColor, xMain, yMain, zMain, firstTail,
            tailLabelAtNat, tableIITail, sumColumnZero] using same
        · have lastTail : z = 10 * n + 2 := by omega
          have sumColumnOne :
              (sumColumn (blockColumn x) (blockColumn y)).val = 1 := by
            rw [<- columnEquation]
            simp only [blockColumn, blockColumnNat]
            omega
          apply compatible_label_colors_fresh_result c
            (Or.inr (by simp [tailLabelAtNat, tableIITail, sumColumnOne]))
            localCompatible
          simpa [shiftedWidthTenColor, xMain, yMain, zMain, firstTail,
            lastTail, tailLabelAtNat, tableIITail, sumColumnOne] using same
      · have yFirstTail : y = 10 * n + 1 := by omega
        have zLastTail : z = 10 * n + 2 := by omega
        have zNotFirstTail : Not (z = 10 * n + 1) := by omega
        have colorEq : labelColor c 0 (tableIITail 0) =
            labelColor c 0 (tableIITail 1) := by
          simpa [shiftedWidthTenColor, yMain, zMain, yFirstTail,
            zNotFirstTail] using same.2
        have colors := encodeColor_injective colorEq
        simp [tableIITail, labelColorSum] at colors
    · have xFirstTail : x = 10 * n + 1 := by omega
      have zLastTail : z = 10 * n + 2 := by omega
      have zNotFirstTail : Not (z = 10 * n + 1) := by omega
      have colorEq : labelColor c 0 (tableIITail 0) =
          labelColor c 0 (tableIITail 1) := by
        simpa [shiftedWidthTenColor, xMain, zMain, xFirstTail,
          zNotFirstTail] using same.1.trans same.2
      have colors := encodeColor_injective colorEq
      simp [tableIITail, labelColorSum] at colors

/-- The two lifts reproduce the standard values 13 and 42 from the small
colorings above. -/
theorem schur_numerical_fidelity :
    HasSchurColoring 3 13 /\ HasSchurColoring 4 42 := by
  constructor
  · exact schur_triple_lift 2 4 schur_coloring_small_values.2.1
  · exact schur_shifted_widthTen_lift 2 4 schur_coloring_small_values.2.1

#print axioms schur_coloring_small_values
#print axioms schur_triple_lift
#print axioms tableII_finite_compatibility
#print axioms schur_shifted_widthTen_lift
#print axioms schur_numerical_fidelity

end D5.S3.Arith.SchurShiftedTemplateLift
