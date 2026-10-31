/- GID: D5/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Arithmetic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Arithmetic
   mirror-E: none(waiver:consumed-balanced-endpoint-arithmetic)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Unbounded endpoint inequalities for sixteen balanced physical plans. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps

private def offsets : Fin 16 → Fin 4 → ℕ :=
  ![![0,0,0,0], ![0,0,0,1], ![0,0,1,0], ![0,0,1,1],
    ![0,1,0,0], ![0,1,0,1], ![0,1,1,0], ![0,1,1,1],
    ![1,0,0,0], ![1,0,0,1], ![1,0,1,0], ![1,0,1,1],
    ![1,1,0,0], ![1,1,0,1], ![1,1,1,0], ![1,1,1,1]]

private def order : Fin 16 → List (Fin 4) :=
  ![[0,1,2,3], [0,1,2,3], [1,0,2,3], [1,3,0,2],
    [2,1,0,3], [0,3,2,1], [0,1,2,3], [0,1,2,3],
    [3,0,1,2], [0,2,3,1], [3,0,1,2], [3,2,1,0],
    [3,1,2,0], [1,2,3,0], [1,2,3,0], [0,1,2,3]]

private def ear : Fin 16 → Fin 4 := ![0,3,2,1,2,1,2,3,2,2,1,0,1,2,3,0]

private def transfer : Fin 16 → Option (Fin 4 × Fin 4) :=
  ![none,none,none,none,none,none,some (2,0),none,
    none,none,none,some (0,2),none,some (0,1),none,none]

private def correction (n : Fin 16) (v : Fin 4 → ℤ) (r : Fin 4) : ℤ :=
  match transfer n with
  | none => 0
  | some (src,dst) => (if r=dst then 2*v src else 0) - (if r=src then 2*v src else 0)

private def powers (n : Fin 16) (q : ℤ) (r : Fin 4) : ℤ := 2^(offsets n r)*q
private def modulus (n : Fin 16) (q : ℤ) : ℤ :=
  powers n q 0 * powers n q 1 * powers n q 2 * powers n q 3 - 1
private def bases (n : Fin 16) (q : ℤ) : Fin 4 → ℤ :=
  let x := powers n q 0
  let y := powers n q 1
  let z := powers n q 2
  let t := powers n q 3
  ![x*y*z+(1+x+x*y), t*(1+x+x*y)+1, t*(z*(1+x))+1+z, t*(y*z)+1+y+y*z]
private def newBases (n : Fin 16) (q : ℤ) (r : Fin 4) : ℤ :=
  2*bases n q r - (![0,1,1+powers n q 2,1+powers n q 1+powers n q 1*powers n q 2] : Fin 4 → ℤ) r
private def lengths (n : Fin 16) (q : ℤ) : Fin 4 → ℤ :=
  ![powers n q 3,powers n q 2,powers n q 1,powers n q 0]
private def masses (n : Fin 16) (q : ℤ) (v : Fin 4 → ℤ) (r : Fin 4) : ℤ :=
  (lengths n q r-2)*v r + correction n v r
private def drops (n : Fin 16) (q : ℤ) : Fin 4 → ℤ :=
  ![bases n q 1,bases n q 2,bases n q 3,bases n q 0] - fun _ => modulus n q
private def newDrops (n : Fin 16) (q : ℤ) : Fin 4 → ℤ :=
  ![newBases n q 1,newBases n q 2,newBases n q 3,bases n q 0] - fun _ => 2*modulus n q+1

private def checks (C h : ℤ) : List (ℤ × ℤ) → Prop
  | [] => True
  | (m,v)::bs => 0 ≤ h+m+v ∧ h+m ≤ C ∧ checks C (h+m+v) bs
private def earChecks (C E h : ℤ) : ℕ → List (ℤ × ℤ) → Prop
  | _, [] => True
  | 0, (m,v)::bs => 0 ≤ h+(m+E)+v ∧ h+(m+E) ≤ C ∧ checks C (h+(m+E)+v) bs
  | e+1, (m,v)::bs => 0 ≤ h+m+v ∧ h+m ≤ C ∧ earChecks C E (h+m+v) e bs

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
private theorem polynomial_endpoints (n : Fin 16) (q : ℤ) (hq : 4 ≤ q) :
    checks (modulus n q-1) 0 ((order n).map (fun r => (masses n q (bases n q) r,drops n q r))) ∧
    earChecks (2*modulus n q) (2*bases n q 0) 0 (ear n).val
      ((order n).map (fun r => (masses n q (newBases n q) r,newDrops n q r))) := by
  let u := q-4
  have hu : 0 ≤ u := by dsimp [u]; omega
  have he : q=u+4 := by dsimp [u]; ring
  rw [he]
  fin_cases n <;>
    norm_num [order,ear,checks,earChecks,masses,correction,transfer,lengths,bases,newBases,
      drops,newDrops,modulus,powers,offsets,Pi.sub_apply] <;>
    repeat' apply And.intro
  all_goals
    first | apply sub_nonneg.mp | apply sub_pos.mp
    ring_nf
    positivity

end D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps
