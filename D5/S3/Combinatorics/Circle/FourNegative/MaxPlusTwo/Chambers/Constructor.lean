/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Constructor
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Constructor
   mirror-E: none(waiver:internal-constructor)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Physical binary-mask constructor covering every max-plus-two chamber. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable
import Mathlib.Data.Nat.Bitwise
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic

/-! All sectors of the explicit physical-mask algorithm, before its correctness proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers

open private ceilpos from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic

/-- A mask is decoded into the original physical labels in increasing order. -/
def labels (len off mask : ℕ) : List ℕ :=
  ((List.range len).filter (fun i => mask.testBit i)).map (off + ·)

/-- Four positive blocks; each is followed by its own physical negative label. -/
structure Blocks where
  first : List ℕ
  second : List ℕ
  third : List ℕ
  fourth : List ℕ

def Blocks.word (P : Blocks) (a b c d : ℕ) : List ℕ :=
  P.first ++ [d-1] ++ P.second ++ [d+c-1] ++ P.third ++ [d+c+b-1] ++
    P.fourth ++ [d+c+b+a-1]

/-- The common template permits both releasing U-bits and advancing V-bits. -/
def maskedBlocks (a b c d u1 u2 u3 v0 v2 v3 w : ℕ) : Blocks :=
  let U := labels (d-1) 0
  let V := labels (c-1) d
  let W := labels (b-1) (d+c)
  let X := labels (a-1) (d+c+b)
  let uf := 2^(d-1)-1
  let vf := 2^(c-1)-1
  let wf := 2^(b-1)-1
  let xf := 2^(a-1)-1
  ⟨U (uf ^^^ u1) ++ V v0,
   U (u1 ^^^ u2) ++ V (vf ^^^ (v0 ||| v2)),
   U (u2 ^^^ u3) ++ V (v2 ^^^ v3) ++ W (wf ^^^ w),
   U u3 ++ V v3 ++ W w ++ X xf⟩

/-- Monotone chambers, including the descending boundary's advanced X-positive. -/
def monotoneBlocks (a b c : ℕ) : Blocks :=
  let R : ℕ := 2^a
  let T : ℕ := 2^b
  let Z : ℕ := 2^c
  let d := max (max a b) c + 2
  let D : ℤ := 2^d
  let A : ℤ := (R:ℤ)*T*Z + R*T + R + 1
  let e1 := D*(R*T+R+1)/2
  let e2 := D*(R+1)*Z/2
  let e3 := D*T*Z/2
  if c ≤ b ∧ b ≤ a then
    let U := labels (d-1) 0
    let V := labels (c-1) d
    let W := labels (b-1) (d+c)
    let X := labels (a-1) (d+c+b)
    let uf := 2^(d-1)-1
    let vf := 2^(c-1)-1
    let wf := 2^(b-1)-1
    let xf := 2^(a-1)-1
    if Z = 4 ∧ R = 2*T then
      let l1 := T ||| 4 ||| 1
      let l2 := 5
      ⟨U (uf ^^^ l1), U (l1 ^^^ l2) ++ V vf,
       W wf ++ X 1, U l2 ++ X (xf ^^^ 1)⟩
    else
      let l1 := (2*R/Z) ||| (2*R/T) ||| 2
      let l2 := (2*R/T) ||| 2
      maskedBlocks a b c d l1 l2 2 0 0 0 0
  else
    let u := if R = T ∧ T = Z then 2 else 3
    let v := if R = T ∧ T = Z then 0 else ceilpos (e2-3*A) (2*e1)
    let s2 := 3*A+2*e1*v
    let wl :=
      if R = T ∧ T = Z then (0,0)
      else if 4*R ≤ T then (ceilpos (e3-s2) (2*e2),0)
      else if T = 2*R then
        if e3 ≤ s2 then (0,0)
        else (1,ceilpos (s2+2*e2-2*e3+A) A)
      else (0,ceilpos (s2-2*e3+A) A)
    maskedBlocks a b c d u u (u ^^^ wl.2) 0 v v wl.1

/-- Strict valley and peak chambers use the same physical mask template. -/
def extremaBlocks (a b c : ℕ) : Blocks :=
  let R : ℕ := 2^a
  let T : ℕ := 2^b
  let Z : ℕ := 2^c
  let d := max (max a b) c + 2
  let D : ℤ := 2^d
  let A : ℤ := (R:ℤ)*T*Z+R*T+R+1
  let e1 := D*(R*T+R+1)/2
  let e2 := D*(R+1)*Z/2
  let e3 := D*T*Z/2
  if b < min a c then
    if Z ≤ R then
      let u := 2*(2*R/Z)-1
      let uv := if Z = 2*T then (2,1) else (u,ceilpos (e2-A*u) (2*e1))
      maskedBlocks a b c d u uv.1 2 0 uv.2 0 0
    else
      let p := Z/(2*R)
      let q := Z/(2*T)
      maskedBlocks a b c d 3 0 0 0 (p+q) p 0
  else
    let s := if Z ≤ R then 2 else 3
    let uv :=
      if 4*Z ≤ T then (2*T/Z+s,0)
      else
        let n := ceilpos (e1-3*A) (8*A-2*e1)
        (8*n+3,n)
    let uw := if 4*R ≤ T then (s,ceilpos (e3-s*A) (2*e2)) else (0,1)
    maskedBlocks a b c d uv.1 s uw.1 uv.2 0 0 uw.2

/-- Exact supplied chamber constructor at the minimal fourth gap. -/
def baseBlocks (a b c : ℕ) : Blocks :=
  if min a c ≤ b ∧ b ≤ max a c then monotoneBlocks a b c
  else extremaBlocks a b c

def baseWord (a b c : ℕ) : List ℕ :=
  (baseBlocks a b c).word a b c (max (max a b) c + 2)

/-- Natural lift adds new low U-labels and shifts every inherited physical label. -/
def physicalWord (a b c d : ℕ) : List ℕ :=
  let t := d-(max (max a b) c+2)
  List.range t ++ (baseWord a b c).map (t+·)

theorem labels_mem (len off mask i : ℕ) :
    i ∈ labels len off mask ↔ ∃ e < len, mask.testBit e = true ∧ off+e=i := by
  simp only [labels, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨e, ⟨he,hb⟩,hi⟩
    exact ⟨e,he,hb,hi⟩
  · rintro ⟨e,he,hb,hi⟩
    exact ⟨e,⟨he,hb⟩,hi⟩

theorem labels_nodup (len off mask : ℕ) : (labels len off mask).Nodup := by
  apply List.Nodup.map (fun x y h => Nat.add_left_cancel h)
  exact (List.nodup_range (n := len)).filter _

/- Public names consumed by the complete endpoint.  The definitions remain the
   single source of the physical mask algorithm above. -/
def chamberLabels (len off mask : ℕ) : List ℕ := labels len off mask
def chamberMaskedWord (a b c d u1 u2 u3 v0 v2 v3 w : ℕ) : List ℕ :=
  let U := chamberLabels (d-1) 0
  let V := chamberLabels (c-1) d
  let W := chamberLabels (b-1) (d+c)
  let X := chamberLabels (a-1) (d+c+b)
  let uf := 2^(d-1)-1
  let vf := 2^(c-1)-1
  let wf := 2^(b-1)-1
  let xf := 2^(a-1)-1
  (U (uf ^^^ u1) ++ V v0) ++ [d-1] ++
    (U (u1 ^^^ u2) ++ V (vf ^^^ (v0 ||| v2))) ++ [d+c-1] ++
    (U (u2 ^^^ u3) ++ V (v2 ^^^ v3) ++ W (wf ^^^ w)) ++ [d+c+b-1] ++
    (U u3 ++ V v3 ++ W w ++ X xf) ++ [d+c+b+a-1]
def chamberBaseWord (a b c : ℕ) : List ℕ := baseWord a b c
def chamberPhysicalWord (a b c d : ℕ) : List ℕ := physicalWord a b c d

theorem chamberLabels_mem (len off mask i : ℕ) :
    i ∈ chamberLabels len off mask ↔
      ∃ e < len, mask.testBit e = true ∧ off+e=i := by
  exact labels_mem len off mask i

theorem chamberLabels_nodup (len off mask : ℕ) :
    (chamberLabels len off mask).Nodup := by
  exact labels_nodup len off mask

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
