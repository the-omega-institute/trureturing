/- GID: D5/S3/Arith/SchurShiftedTemplateLift
   generality: G
   mirror-B: D5/B/S3/Arith/SchurShiftedTemplateLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Literal Schur templates give the 3n+1 and width-10 shifted 10n+2 lifts. -/

import Mathlib

namespace D5.S3.Arith.SchurShiftedTemplateLift

/-- A coloring of `1, ..., n` with no monochromatic solution of `x + y = z`. -/
def SchurColoring (k n : Nat) (c : Nat -> Fin k) : Prop :=
  forall x y z,
    1 <= x -> x <= n ->
    1 <= y -> y <= n ->
    1 <= z -> z <= n ->
    x + y = z ->
    Not (And (c x = c y) (c y = c z))

/-- Existence of a Schur coloring of `1, ..., n` with `k` colors. -/
def HasSchurColoring (k n : Nat) : Prop :=
  Exists fun c : Nat -> Fin k => SchurColoring k n c

private def oldColor {k : Nat} (a : Fin k) : Fin (k + 2) :=
  Fin.castLE (by omega) a

private def newColor (k : Nat) (a : Fin 2) : Fin (k + 2) :=
  Fin.natAdd k a

private theorem oldColor_injective {k : Nat} : Function.Injective (@oldColor k) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin (k + 2) => x.val) h

private theorem newColor_injective {k : Nat} : Function.Injective (newColor k) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [newColor] using this

private theorem oldColor_ne_newColor {k : Nat} (a : Fin k) (b : Fin 2) :
    Not (oldColor a = newColor k b) := by
  intro h
  have hval := congrArg (fun x : Fin (k + 2) => x.val) h
  simp [oldColor, newColor] at hval
  omega

inductive ShiftedLabel where
  | A
  | B
  | Pm1
  | P0
  deriving DecidableEq, Repr

/-- Table II of Bengone et al., with columns numbered from zero. -/
def shiftedTemplateLabel (firstRow : Bool) (u : Fin 10) : ShiftedLabel :=
  if u = 0 then
    if firstRow then .B else .Pm1
  else if u = 1 then
    if firstRow then .A else .B
  else if u = 2 then .P0
  else if u = 3 then .P0
  else if u = 4 then .B
  else if u = 5 then .A
  else if u = 6 then .A
  else if u = 7 then .B
  else if u = 8 then .P0
  else .P0

def shiftedTemplateNewLabel : ShiftedLabel -> Option (Fin 2)
  | .A => some 0
  | .B => some 1
  | .Pm1 => none
  | .P0 => none

/-- The one-based source-row offset: `P-1` uses `r`, while `P0` uses `r+1`. -/
def shiftedTemplateOldOffset : ShiftedLabel -> Option Nat
  | .A => none
  | .B => none
  | .Pm1 => some 0
  | .P0 => some 1

def shiftedTemplateCarry (u v : Fin 10) : Nat :=
  if u.val + v.val + 1 < 10 then 0 else 1

def shiftedTemplateOutCol (u v : Fin 10) : Fin 10 :=
  if h : u.val + v.val + 1 < 10 then
    (show Fin 10 from ⟨u.val + v.val + 1, h⟩)
  else
    (show Fin 10 from ⟨u.val + v.val + 1 - 10, by
      have hu := u.isLt
      have hv := v.isLt
      omega⟩)

def shiftedTemplateResultFirst (fx fy : Bool) (u v : Fin 10) : Bool :=
  fx && fy && decide (shiftedTemplateCarry u v = 0)

private theorem shiftedTemplate_tailA_compatible :
    forall (fx fy : Bool) (u v : Fin 10),
      u.val + v.val = 9 ->
      Not (And
        (shiftedTemplateNewLabel (shiftedTemplateLabel fx u) = some 0)
        (shiftedTemplateNewLabel (shiftedTemplateLabel fy v) = some 0)) := by
  decide

private theorem shiftedTemplate_tailB_compatible :
    forall (fx fy : Bool) (u v : Fin 10),
      (u.val + v.val = 0 -> Not (And (fx = true) (fy = true))) ->
      (u.val + v.val = 0 \/ u.val + v.val = 10) ->
      Not (And
        (shiftedTemplateNewLabel (shiftedTemplateLabel fx u) = some 1)
        (shiftedTemplateNewLabel (shiftedTemplateLabel fy v) = some 1)) := by
  decide

private theorem shiftedTemplate_new_compatible :
    forall (fx fy : Bool) (u v : Fin 10) (a : Fin 2),
      Not (And
        (shiftedTemplateNewLabel (shiftedTemplateLabel fx u) = some a)
        (And
          (shiftedTemplateNewLabel (shiftedTemplateLabel fy v) = some a)
          (shiftedTemplateNewLabel
            (shiftedTemplateLabel (shiftedTemplateResultFirst fx fy u v)
              (shiftedTemplateOutCol u v)) = some a))) := by
  decide

def shiftedTemplateOldCompatible (fx fy : Bool) (u v : Fin 10) : Bool :=
  match shiftedTemplateOldOffset (shiftedTemplateLabel fx u),
      shiftedTemplateOldOffset (shiftedTemplateLabel fy v),
      shiftedTemplateOldOffset
        (shiftedTemplateLabel (shiftedTemplateResultFirst fx fy u v)
          (shiftedTemplateOutCol u v)) with
  | some dx, some dy, some dz => decide (dz + shiftedTemplateCarry u v = dx + dy)
  | _, _, _ => true

private theorem shiftedTemplate_old_compatible :
    forall (fx fy : Bool) (u v : Fin 10),
      shiftedTemplateOldCompatible fx fy u v = true := by
  decide

def blockRow (x : Nat) : Nat := (x - 1) / 10

def blockCol (x : Nat) : Fin 10 :=
  ⟨(x - 1) % 10, Nat.mod_lt _ (by omega)⟩

private theorem block_decompose {x : Nat} (hx : 1 <= x) :
    x = 10 * blockRow x + (blockCol x).val + 1 := by
  have h := Nat.div_add_mod (x - 1) 10
  simp only [blockRow, blockCol]
  omega

private theorem block_add_coordinates {x y z : Nat}
    (hx : 1 <= x) (hy : 1 <= y) (hxyz : x + y = z) :
    And
      (blockRow z = blockRow x + blockRow y +
        shiftedTemplateCarry (blockCol x) (blockCol y))
      (blockCol z = shiftedTemplateOutCol (blockCol x) (blockCol y)) := by
  have hdx := block_decompose hx
  have hdy := block_decompose hy
  have hzpos : 1 <= z := by omega
  have hdz := block_decompose hzpos
  have hcx := (blockCol x).isLt
  have hcy := (blockCol y).isLt
  have hcz := (blockCol z).isLt
  have hsum :
      10 * blockRow z + (blockCol z).val =
        10 * (blockRow x + blockRow y) +
          (blockCol x).val + (blockCol y).val + 1 := by
    omega
  constructor
  · simp only [shiftedTemplateCarry]
    split_ifs <;> omega
  · apply Fin.ext
    unfold shiftedTemplateOutCol
    split
    next h =>
      change (blockCol z).val = (blockCol x).val + (blockCol y).val + 1
      omega
    next h =>
      change (blockCol z).val = (blockCol x).val + (blockCol y).val + 1 - 10
      omega

/-- The four finite Table-II checks and the width-10 coordinate carry law. -/
theorem shiftedTemplateCompatibilityCertificates :
    (forall (fx fy : Bool) (u v : Fin 10) (a : Fin 2),
      Not (And
        (shiftedTemplateNewLabel (shiftedTemplateLabel fx u) = some a)
        (And
          (shiftedTemplateNewLabel (shiftedTemplateLabel fy v) = some a)
          (shiftedTemplateNewLabel
            (shiftedTemplateLabel (shiftedTemplateResultFirst fx fy u v)
              (shiftedTemplateOutCol u v)) = some a)))) ∧
    (forall (fx fy : Bool) (u v : Fin 10),
      shiftedTemplateOldCompatible fx fy u v = true) ∧
    (forall (fx fy : Bool) (u v : Fin 10),
      u.val + v.val = 9 ->
      Not (And
        (shiftedTemplateNewLabel (shiftedTemplateLabel fx u) = some 0)
        (shiftedTemplateNewLabel (shiftedTemplateLabel fy v) = some 0))) ∧
    (forall (fx fy : Bool) (u v : Fin 10),
      (u.val + v.val = 0 -> Not (And (fx = true) (fy = true))) ->
      (u.val + v.val = 0 \/ u.val + v.val = 10) ->
      Not (And
        (shiftedTemplateNewLabel (shiftedTemplateLabel fx u) = some 1)
        (shiftedTemplateNewLabel (shiftedTemplateLabel fy v) = some 1))) ∧
    (forall {x y z : Nat},
      1 <= x -> 1 <= y -> x + y = z ->
      And
        (blockRow z = blockRow x + blockRow y +
          shiftedTemplateCarry (blockCol x) (blockCol y))
        (blockCol z = shiftedTemplateOutCol (blockCol x) (blockCol y))) := by
  exact ⟨shiftedTemplate_new_compatible, shiftedTemplate_old_compatible,
    shiftedTemplate_tailA_compatible, shiftedTemplate_tailB_compatible,
    block_add_coordinates⟩

private theorem resultFirst_eq (rx ry : Nat) (u v : Fin 10) :
    decide (rx + ry + shiftedTemplateCarry u v = 0) =
      shiftedTemplateResultFirst (decide (rx = 0)) (decide (ry = 0)) u v := by
  simp only [shiftedTemplateResultFirst]
  by_cases hx : rx = 0
  · subst rx
    by_cases hy : ry = 0
    · subst ry
      simp [shiftedTemplateCarry]
    · simp [hy]
  · by_cases hy : ry = 0
    · subst ry
      simp [hx]
    · simp [hx, hy]

private def labelColor {k : Nat} (c : Nat -> Fin k) (row : Nat) :
    ShiftedLabel -> Fin (k + 2)
  | .A => newColor k 0
  | .B => newColor k 1
  | .Pm1 => oldColor (c row)
  | .P0 => oldColor (c (row + 1))

private theorem label_partition (l : ShiftedLabel) :
    (Exists fun a => shiftedTemplateNewLabel l = some a) \/
      (Exists fun d => shiftedTemplateOldOffset l = some d) := by
  cases l <;> simp [shiftedTemplateNewLabel, shiftedTemplateOldOffset]

private theorem labelColor_of_new {k : Nat} (c : Nat -> Fin k)
    (row : Nat) (l : ShiftedLabel) (a : Fin 2)
    (h : shiftedTemplateNewLabel l = some a) :
    labelColor c row l = newColor k a := by
  cases l <;> simp [shiftedTemplateNewLabel] at h <;>
    simp_all [labelColor]

private theorem labelColor_of_old {k : Nat} (c : Nat -> Fin k)
    (row : Nat) (l : ShiftedLabel) (d : Nat)
    (h : shiftedTemplateOldOffset l = some d) :
    labelColor c row l = oldColor (c (row + d)) := by
  cases l <;> simp [shiftedTemplateOldOffset] at h
  · subst d
    simp [labelColor]
  · subst d
    simp [labelColor]

private theorem newLabel_of_labelColor_eq_new {k : Nat} (c : Nat -> Fin k)
    (row : Nat) (l : ShiftedLabel) (a : Fin 2)
    (h : labelColor c row l = newColor k a) :
    shiftedTemplateNewLabel l = some a := by
  cases l with
  | A =>
      change newColor k 0 = newColor k a at h
      have ha : (0 : Fin 2) = a := newColor_injective h
      subst a
      rfl
  | B =>
      change newColor k 1 = newColor k a at h
      have ha : (1 : Fin 2) = a := newColor_injective h
      subst a
      rfl
  | Pm1 =>
      change oldColor (c row) = newColor k a at h
      exact (oldColor_ne_newColor (c row) a h).elim
  | P0 =>
      change oldColor (c (row + 1)) = newColor k a at h
      exact (oldColor_ne_newColor (c (row + 1)) a h).elim

private theorem oldOffset_le_one (l : ShiftedLabel) (d : Nat)
    (h : shiftedTemplateOldOffset l = some d) : d <= 1 := by
  cases l <;> simp [shiftedTemplateOldOffset] at h <;> omega

private theorem oldIndex_pos (r : Nat) (u : Fin 10) (d : Nat)
    (h : shiftedTemplateOldOffset
      (shiftedTemplateLabel (decide (r = 0)) u) = some d) :
    1 <= r + d := by
  by_cases hr : r = 0
  · subst r
    fin_cases u <;>
      simp [shiftedTemplateLabel, shiftedTemplateOldOffset] at h <;>
      omega
  · have : 1 <= r := Nat.one_le_iff_ne_zero.mpr hr
    omega

private def shiftedTemplateMainColor {k : Nat} (c : Nat -> Fin k) (x : Nat) :
    Fin (k + 2) :=
  labelColor c (blockRow x)
    (shiftedTemplateLabel (decide (blockRow x = 0)) (blockCol x))

/-- The coloring obtained from the literal width-10 template and tail `(A,B)`. -/
def shiftedTemplateColor {k n : Nat} (c : Nat -> Fin k) (x : Nat) : Fin (k + 2) :=
  if x <= 10 * n then shiftedTemplateMainColor c x
  else if x = 10 * n + 1 then newColor k 0
  else newColor k 1

private theorem shiftedTemplateColor_main {k n : Nat} (c : Nat -> Fin k)
    {x : Nat} (hx : x <= 10 * n) :
    shiftedTemplateColor (n := n) c x = shiftedTemplateMainColor c x := by
  simp [shiftedTemplateColor, hx]

private theorem shiftedTemplateColor_tailA {k n : Nat} (c : Nat -> Fin k) :
    shiftedTemplateColor (n := n) c (10 * n + 1) = newColor k 0 := by
  simp [shiftedTemplateColor]

private theorem shiftedTemplateColor_tailB {k n : Nat} (c : Nat -> Fin k) :
    shiftedTemplateColor (n := n) c (10 * n + 2) = newColor k 1 := by
  simp [shiftedTemplateColor]

private theorem shiftedTemplateMain_noMono {k n : Nat} (c : Nat -> Fin k)
    (hc : SchurColoring k n c) {x y z : Nat}
    (hx : 1 <= x) (hxn : x <= 10 * n)
    (hy : 1 <= y) (_hyn : y <= 10 * n)
    (hz : 1 <= z) (hzn : z <= 10 * n)
    (hxyz : x + y = z) :
    Not (And
      (shiftedTemplateMainColor c x = shiftedTemplateMainColor c y)
      (shiftedTemplateMainColor c y = shiftedTemplateMainColor c z)) := by
  intro hmono
  let lx := shiftedTemplateLabel (decide (blockRow x = 0)) (blockCol x)
  let ly := shiftedTemplateLabel (decide (blockRow y = 0)) (blockCol y)
  let lz := shiftedTemplateLabel (decide (blockRow z = 0)) (blockCol z)
  have hcoords := shiftedTemplateCompatibilityCertificates.2.2.2.2 hx hy hxyz
  have hzlabel :
      shiftedTemplateLabel (decide (blockRow z = 0)) (blockCol z) =
        shiftedTemplateLabel
          (shiftedTemplateResultFirst
            (decide (blockRow x = 0)) (decide (blockRow y = 0))
            (blockCol x) (blockCol y))
          (shiftedTemplateOutCol (blockCol x) (blockCol y)) := by
    rw [hcoords.1, resultFirst_eq, hcoords.2]
  have hrx : blockRow x < n := by
    have hd := block_decompose hx
    have hc := (blockCol x).isLt
    omega
  have hry : blockRow y < n := by
    have hd := block_decompose hy
    have hc := (blockCol y).isLt
    omega
  have hrz : blockRow z < n := by
    have hd := block_decompose hz
    have hc := (blockCol z).isLt
    omega
  change And (labelColor c (blockRow x) lx = labelColor c (blockRow y) ly)
    (labelColor c (blockRow y) ly = labelColor c (blockRow z) lz) at hmono
  rcases label_partition lx with ⟨ax, hax⟩ | ⟨dx, hdx⟩ <;>
    rcases label_partition ly with ⟨ay, hay⟩ | ⟨dy, hdy⟩ <;>
    rcases label_partition lz with ⟨az, haz⟩ | ⟨dz, hdz⟩
  · have hxy : newColor k ax = newColor k ay := by
      rw [← labelColor_of_new c (blockRow x) lx ax hax,
        ← labelColor_of_new c (blockRow y) ly ay hay]
      exact hmono.1
    have hyz : newColor k ay = newColor k az := by
      rw [← labelColor_of_new c (blockRow y) ly ay hay,
        ← labelColor_of_new c (blockRow z) lz az haz]
      exact hmono.2
    have haxy : ax = ay := newColor_injective hxy
    have hayz : ay = az := newColor_injective hyz
    subst ay
    subst az
    have haz' :
        shiftedTemplateNewLabel
          (shiftedTemplateLabel
            (shiftedTemplateResultFirst
              (decide (blockRow x = 0)) (decide (blockRow y = 0))
              (blockCol x) (blockCol y))
            (shiftedTemplateOutCol (blockCol x) (blockCol y))) = some ax := by
      rw [← hzlabel]
      exact haz
    exact shiftedTemplateCompatibilityCertificates.1
      (decide (blockRow x = 0)) (decide (blockRow y = 0))
      (blockCol x) (blockCol y) ax ⟨hax, hay, haz'⟩
  · have hyz : newColor k ay = oldColor (c (blockRow z + dz)) := by
      rw [← labelColor_of_new c (blockRow y) ly ay hay,
        ← labelColor_of_old c (blockRow z) lz dz hdz]
      exact hmono.2
    exact (oldColor_ne_newColor (c (blockRow z + dz)) ay) hyz.symm
  · have hxy : newColor k ax = oldColor (c (blockRow y + dy)) := by
      rw [← labelColor_of_new c (blockRow x) lx ax hax,
        ← labelColor_of_old c (blockRow y) ly dy hdy]
      exact hmono.1
    exact (oldColor_ne_newColor (c (blockRow y + dy)) ax) hxy.symm
  · have hxy : newColor k ax = oldColor (c (blockRow y + dy)) := by
      rw [← labelColor_of_new c (blockRow x) lx ax hax,
        ← labelColor_of_old c (blockRow y) ly dy hdy]
      exact hmono.1
    exact (oldColor_ne_newColor (c (blockRow y + dy)) ax) hxy.symm
  · have hxy : oldColor (c (blockRow x + dx)) = newColor k ay := by
      rw [← labelColor_of_old c (blockRow x) lx dx hdx,
        ← labelColor_of_new c (blockRow y) ly ay hay]
      exact hmono.1
    exact (oldColor_ne_newColor (c (blockRow x + dx)) ay) hxy
  · have hxy : oldColor (c (blockRow x + dx)) = newColor k ay := by
      rw [← labelColor_of_old c (blockRow x) lx dx hdx,
        ← labelColor_of_new c (blockRow y) ly ay hay]
      exact hmono.1
    exact (oldColor_ne_newColor (c (blockRow x + dx)) ay) hxy
  · have hyz : newColor k az = oldColor (c (blockRow y + dy)) := by
      rw [← labelColor_of_new c (blockRow z) lz az haz,
        ← labelColor_of_old c (blockRow y) ly dy hdy]
      exact hmono.2.symm
    exact (oldColor_ne_newColor (c (blockRow y + dy)) az) hyz.symm
  · have hxy : c (blockRow x + dx) = c (blockRow y + dy) :=
      oldColor_injective (by
        rw [← labelColor_of_old c (blockRow x) lx dx hdx,
          ← labelColor_of_old c (blockRow y) ly dy hdy]
        exact hmono.1)
    have hyz : c (blockRow y + dy) = c (blockRow z + dz) :=
      oldColor_injective (by
        rw [← labelColor_of_old c (blockRow y) ly dy hdy,
          ← labelColor_of_old c (blockRow z) lz dz hdz]
        exact hmono.2)
    have hdz' :
        shiftedTemplateOldOffset
          (shiftedTemplateLabel
            (shiftedTemplateResultFirst
              (decide (blockRow x = 0)) (decide (blockRow y = 0))
              (blockCol x) (blockCol y))
            (shiftedTemplateOutCol (blockCol x) (blockCol y))) = some dz := by
      rw [← hzlabel]
      exact hdz
    change shiftedTemplateOldOffset
      (shiftedTemplateLabel (decide (blockRow x = 0)) (blockCol x)) = some dx at hdx
    change shiftedTemplateOldOffset
      (shiftedTemplateLabel (decide (blockRow y = 0)) (blockCol y)) = some dy at hdy
    have hoff : dz + shiftedTemplateCarry (blockCol x) (blockCol y) = dx + dy := by
      have htable := shiftedTemplateCompatibilityCertificates.2.1
        (decide (blockRow x = 0)) (decide (blockRow y = 0))
        (blockCol x) (blockCol y)
      simpa [shiftedTemplateOldCompatible, hdx, hdy, hdz'] using htable
    have hsum :
        (blockRow x + dx) + (blockRow y + dy) = blockRow z + dz := by
      omega
    have hdx1 := oldOffset_le_one lx dx hdx
    have hdy1 := oldOffset_le_one ly dy hdy
    have hdz1 := oldOffset_le_one lz dz hdz
    have hxpos := oldIndex_pos (blockRow x) (blockCol x) dx hdx
    have hypos := oldIndex_pos (blockRow y) (blockCol y) dy hdy
    have hzpos := oldIndex_pos (blockRow z) (blockCol z) dz hdz
    have hxle : blockRow x + dx <= n := by omega
    have hyle : blockRow y + dy <= n := by omega
    have hzle : blockRow z + dz <= n := by omega
    exact (hc (blockRow x + dx) (blockRow y + dy) (blockRow z + dz)
      hxpos hxle hypos hyle hzpos hzle hsum) ⟨hxy, hyz⟩

/-- Table II's width-10 shifted-template lift, including its two-cell tail. -/
theorem shiftedTemplateLift {k n : Nat} :
    HasSchurColoring k n -> HasSchurColoring (k + 2) (10 * n + 2) := by
  rintro ⟨c, hc⟩
  refine ⟨shiftedTemplateColor (n := n) c, ?_⟩
  intro x y z hx hxn hy hyn hz hzn hxyz
  by_cases hzmain : z <= 10 * n
  · have hxmain : x <= 10 * n := by omega
    have hymain : y <= 10 * n := by omega
    rw [shiftedTemplateColor_main c hxmain,
      shiftedTemplateColor_main c hymain,
      shiftedTemplateColor_main c hzmain]
    exact shiftedTemplateMain_noMono c hc hx hxmain hy hymain hz hzmain hxyz
  · by_cases hza : z = 10 * n + 1
    · have hxmain : x <= 10 * n := by omega
      have hymain : y <= 10 * n := by omega
      intro hmono
      rw [shiftedTemplateColor_main c hxmain,
        shiftedTemplateColor_main c hymain, hza, shiftedTemplateColor_tailA c] at hmono
      have hxA := newLabel_of_labelColor_eq_new c (blockRow x)
        (shiftedTemplateLabel (decide (blockRow x = 0)) (blockCol x)) 0
        (hmono.1.trans hmono.2)
      have hyA := newLabel_of_labelColor_eq_new c (blockRow y)
        (shiftedTemplateLabel (decide (blockRow y = 0)) (blockCol y)) 0 hmono.2
      have hdx := block_decompose hx
      have hdy := block_decompose hy
      have hcx := (blockCol x).isLt
      have hcy := (blockCol y).isLt
      have hcol : (blockCol x).val + (blockCol y).val = 9 := by omega
      exact shiftedTemplateCompatibilityCertificates.2.2.1
        (decide (blockRow x = 0)) (decide (blockRow y = 0))
        (blockCol x) (blockCol y) hcol ⟨hxA, hyA⟩
    · have hzb : z = 10 * n + 2 := by omega
      by_cases hxmain : x <= 10 * n
      · by_cases hymain : y <= 10 * n
        · intro hmono
          rw [shiftedTemplateColor_main c hxmain,
            shiftedTemplateColor_main c hymain, hzb,
            shiftedTemplateColor_tailB c] at hmono
          have hxB := newLabel_of_labelColor_eq_new c (blockRow x)
            (shiftedTemplateLabel (decide (blockRow x = 0)) (blockCol x)) 1
            (hmono.1.trans hmono.2)
          have hyB := newLabel_of_labelColor_eq_new c (blockRow y)
            (shiftedTemplateLabel (decide (blockRow y = 0)) (blockCol y)) 1 hmono.2
          have hdx := block_decompose hx
          have hdy := block_decompose hy
          have hcx := (blockCol x).isLt
          have hcy := (blockCol y).isLt
          have hcols : (blockCol x).val + (blockCol y).val = 0 \/
              (blockCol x).val + (blockCol y).val = 10 := by
            omega
          have hfirst : (blockCol x).val + (blockCol y).val = 0 ->
              Not (And (decide (blockRow x = 0) = true)
                (decide (blockRow y = 0) = true)) := by
            intro hcol hrows
            simp only [decide_eq_true_eq] at hrows
            omega
          exact shiftedTemplateCompatibilityCertificates.2.2.2.1
            (decide (blockRow x = 0)) (decide (blockRow y = 0))
            (blockCol x) (blockCol y) hfirst hcols ⟨hxB, hyB⟩
        · have hyA : y = 10 * n + 1 := by omega
          intro hmono
          have hneq : Not (newColor k 0 = newColor k 1) := by
            intro h
            have : (0 : Fin 2) = 1 := newColor_injective h
            omega
          apply hneq
          rw [← shiftedTemplateColor_tailA c, ← shiftedTemplateColor_tailB c]
          simpa [hyA, hzb] using hmono.2
      · have hxA : x = 10 * n + 1 := by omega
        intro hmono
        have hneq : Not (newColor k 0 = newColor k 1) := by
          intro h
          have : (0 : Fin 2) = 1 := newColor_injective h
          omega
        apply hneq
        rw [← shiftedTemplateColor_tailA c, ← shiftedTemplateColor_tailB c]
        simpa [hxA, hzb] using hmono.1.trans hmono.2

private def classicalOldColor {k : Nat} (a : Fin k) : Fin (k + 1) :=
  Fin.castSucc a

private def classicalNewColor (k : Nat) : Fin (k + 1) :=
  Fin.last k

private theorem classicalOldColor_injective {k : Nat} :
    Function.Injective (@classicalOldColor k) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin (k + 1) => x.val) h

private theorem classicalOldColor_ne_newColor {k : Nat} (a : Fin k) :
    Not (classicalOldColor a = classicalNewColor k) := by
  intro h
  have hval := congrArg (fun x : Fin (k + 1) => x.val) h
  apply Nat.ne_of_lt a.isLt
  simpa [classicalOldColor, classicalNewColor] using hval

private def classicalLiftColor {k n : Nat} (c : Nat -> Fin k) (x : Nat) :
    Fin (k + 1) :=
  if x <= n then classicalOldColor (c x)
  else if x <= 2 * n + 1 then classicalNewColor k
  else classicalOldColor (c (x - (2 * n + 1)))

private theorem classicalLiftColor_left {k n : Nat} (c : Nat -> Fin k)
    {x : Nat} (hx : x <= n) :
    classicalLiftColor (n := n) c x = classicalOldColor (c x) := by
  simp [classicalLiftColor, hx]

private theorem classicalLiftColor_middle {k n : Nat} (c : Nat -> Fin k)
    {x : Nat} (hx : Not (x <= n)) (hx' : x <= 2 * n + 1) :
    classicalLiftColor (n := n) c x = classicalNewColor k := by
  simp [classicalLiftColor, hx, hx']

private theorem classicalLiftColor_right {k n : Nat} (c : Nat -> Fin k)
    {x : Nat} (hx : Not (x <= 2 * n + 1)) :
    classicalLiftColor (n := n) c x = classicalOldColor (c (x - (2 * n + 1))) := by
  have hx' : Not (x <= n) := by omega
  simp [classicalLiftColor, hx, hx']

/-- The classical Schur lift obtained from two old-color copies around one new-color interval. -/
theorem classicalLift {k n : Nat} :
    HasSchurColoring k n -> HasSchurColoring (k + 1) (3 * n + 1) := by
  rintro ⟨c, hc⟩
  refine ⟨classicalLiftColor (n := n) c, ?_⟩
  intro x y z hx hxn hy hyn hz hzn hxyz
  by_cases hzleft : z <= n
  · have hxleft : x <= n := by omega
    have hyleft : y <= n := by omega
    intro hmono
    have hxy : c x = c y := classicalOldColor_injective (by
      rw [← classicalLiftColor_left c hxleft, ← classicalLiftColor_left c hyleft]
      exact hmono.1)
    have hyz : c y = c z := classicalOldColor_injective (by
      rw [← classicalLiftColor_left c hyleft, ← classicalLiftColor_left c hzleft]
      exact hmono.2)
    exact (hc x y z hx hxleft hy hyleft hz hzleft hxyz) ⟨hxy, hyz⟩
  · by_cases hzmiddle : z <= 2 * n + 1
    · have hxupper : x <= 2 * n + 1 := by omega
      have hyupper : y <= 2 * n + 1 := by omega
      intro hmono
      have hxnotleft : Not (x <= n) := by
        intro hxleft
        have hbad : classicalOldColor (c x) = classicalNewColor k := by
          rw [← classicalLiftColor_left c hxleft,
            ← classicalLiftColor_middle c hzleft hzmiddle]
          exact hmono.1.trans hmono.2
        exact classicalOldColor_ne_newColor (c x) hbad
      have hynotleft : Not (y <= n) := by
        intro hyleft
        have hbad : classicalOldColor (c y) = classicalNewColor k := by
          rw [← classicalLiftColor_left c hyleft,
            ← classicalLiftColor_middle c hzleft hzmiddle]
          exact hmono.2
        exact classicalOldColor_ne_newColor (c y) hbad
      omega
    · intro hmono
      have hxNotMiddle : Not (And (Not (x <= n)) (x <= 2 * n + 1)) := by
        rintro ⟨hxleft, hxupper⟩
        have hbad : classicalNewColor k =
            classicalOldColor (c (z - (2 * n + 1))) := by
          rw [← classicalLiftColor_middle c hxleft hxupper,
            ← classicalLiftColor_right c hzmiddle]
          exact hmono.1.trans hmono.2
        exact classicalOldColor_ne_newColor
          (c (z - (2 * n + 1))) hbad.symm
      have hyNotMiddle : Not (And (Not (y <= n)) (y <= 2 * n + 1)) := by
        rintro ⟨hyleft, hyupper⟩
        have hbad : classicalNewColor k =
            classicalOldColor (c (z - (2 * n + 1))) := by
          rw [← classicalLiftColor_middle c hyleft hyupper,
            ← classicalLiftColor_right c hzmiddle]
          exact hmono.2
        exact classicalOldColor_ne_newColor
          (c (z - (2 * n + 1))) hbad.symm
      by_cases hxleft : x <= n
      · by_cases hyleft : y <= n
        · omega
        · have hyright : Not (y <= 2 * n + 1) := by
            intro hyupper
            exact hyNotMiddle ⟨hyleft, hyupper⟩
          have hxy : c x = c (y - (2 * n + 1)) :=
            classicalOldColor_injective (by
              rw [← classicalLiftColor_left c hxleft,
                ← classicalLiftColor_right c hyright]
              exact hmono.1)
          have hyz : c (y - (2 * n + 1)) = c (z - (2 * n + 1)) :=
            classicalOldColor_injective (by
              rw [← classicalLiftColor_right c hyright,
                ← classicalLiftColor_right c hzmiddle]
              exact hmono.2)
          have hypos : 1 <= y - (2 * n + 1) := by omega
          have hzpos : 1 <= z - (2 * n + 1) := by omega
          have hyle : y - (2 * n + 1) <= n := by omega
          have hzle : z - (2 * n + 1) <= n := by omega
          have hsum : x + (y - (2 * n + 1)) = z - (2 * n + 1) := by omega
          exact (hc x (y - (2 * n + 1)) (z - (2 * n + 1))
            hx hxleft hypos hyle hzpos hzle hsum) ⟨hxy, hyz⟩
      · by_cases hyleft : y <= n
        · have hxright : Not (x <= 2 * n + 1) := by
            intro hxupper
            exact hxNotMiddle ⟨hxleft, hxupper⟩
          have hxy : c (x - (2 * n + 1)) = c y :=
            classicalOldColor_injective (by
              rw [← classicalLiftColor_right c hxright,
                ← classicalLiftColor_left c hyleft]
              exact hmono.1)
          have hyz : c y = c (z - (2 * n + 1)) :=
            classicalOldColor_injective (by
              rw [← classicalLiftColor_left c hyleft,
                ← classicalLiftColor_right c hzmiddle]
              exact hmono.2)
          have hxpos : 1 <= x - (2 * n + 1) := by omega
          have hzpos : 1 <= z - (2 * n + 1) := by omega
          have hxle : x - (2 * n + 1) <= n := by omega
          have hzle : z - (2 * n + 1) <= n := by omega
          have hsum : (x - (2 * n + 1)) + y = z - (2 * n + 1) := by omega
          exact (hc (x - (2 * n + 1)) y (z - (2 * n + 1))
            hxpos hxle hy hyleft hzpos hzle hsum) ⟨hxy, hyz⟩
        · have hxright : Not (x <= 2 * n + 1) := by
            intro hxupper
            exact hxNotMiddle ⟨hxleft, hxupper⟩
          have hyright : Not (y <= 2 * n + 1) := by
            intro hyupper
            exact hyNotMiddle ⟨hyleft, hyupper⟩
          omega

private theorem hasSchurColoring_one_one : HasSchurColoring 1 1 := by
  refine ⟨fun _ => 0, ?_⟩
  intro x y z hx hxn hy hyn hz hzn hxyz _
  omega

/-- The explicit two-color assignment used by the small-value certificates. -/
def twoFourColoring (x : Nat) : Fin 2 :=
  if x = 1 \/ x = 4 then 0 else 1

private theorem twoFourColoring_finite_check :
    forall x y z : Fin 5,
      1 <= x.val -> 1 <= y.val -> 1 <= z.val -> x.val + y.val = z.val ->
      Not (And (twoFourColoring x.val = twoFourColoring y.val)
        (twoFourColoring y.val = twoFourColoring z.val)) := by
  decide

private theorem hasSchurColoring_two_four : HasSchurColoring 2 4 := by
  refine ⟨twoFourColoring, ?_⟩
  intro x y z hx hxn hy hyn hz hzn hxyz
  exact twoFourColoring_finite_check
    ⟨x, by omega⟩ ⟨y, by omega⟩ ⟨z, by omega⟩ hx hy hz hxyz

private theorem not_hasSchurColoring_one_two : Not (HasSchurColoring 1 2) := by
  rintro ⟨c, hc⟩
  exact (hc 1 1 2 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega))
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The one- and two-color base cases, including the one-color obstruction at length two. -/
theorem schurColoringSmallValues :
    HasSchurColoring 1 1 ∧ HasSchurColoring 2 4 ∧
      Not (HasSchurColoring 1 2) := by
  exact ⟨hasSchurColoring_one_one, hasSchurColoring_two_four,
    not_hasSchurColoring_one_two⟩

/-- The numerical consequences obtained from the base coloring by the two lifts. -/
theorem schurLiftNumericalConsequences :
    HasSchurColoring 3 13 ∧ HasSchurColoring 4 42 := by
  constructor
  · simpa using classicalLift schurColoringSmallValues.2.1
  · simpa using shiftedTemplateLift schurColoringSmallValues.2.1

#print axioms schurColoringSmallValues
#print axioms classicalLift
#print axioms shiftedTemplateCompatibilityCertificates
#print axioms shiftedTemplateLift
#print axioms schurLiftNumericalConsequences

-- Fidelity witnesses: the premise is inhabited and the color domains are nonempty.
example : HasSchurColoring 2 4 := schurColoringSmallValues.2.1

example : Fin 2 := 0

end D5.S3.Arith.SchurShiftedTemplateLift
