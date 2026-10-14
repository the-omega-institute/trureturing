/- Static UNCOMPILED private-consumer candidate. Paste after the existing
J2 c helpers in NativeJ2SurvivingEdges and remove the import/namespace wrapper.
It intentionally uses that file's private j2Contact/seeds and coordinate macro.

Write R=finRotate(m+1), C=contactAnchor(j*), D_i=gapAnchor C i,
L=lowerPort(j*), and tau=swap(0,m), with j*=m-3.

Actual short a/b row table:
  word 0: [a,b] at R^m in owner 1;
          U_(m-2) at C*R^(m-2)*a in owner C;
          U_(m-1) at D_(m-1)*b in owner D_(m-1).
  word 1: (ab)^(m-1) at R^(m-1)*a in owner 1;
          final [a] at L in owner L.
  word 2: initial [a] at C*R^m in owner C;
          final [a,b,a] at D_(m-2) in owner D_(m-2).
  word 3: initial [a] at D_(m-1)*a in owner D_(m-1);
          U_(m-2) at D_(m-2)*b in owner D_(m-2).
  word 4: [a,b] at tau*R^m in owner tau;
          U_(m-1) at L*b in owner L.

For z*R^r*a and k<=r, U_k traverses reflected and positive coordinates
r,r-1,...,r-k, ending at positive r-k. Thus the three reverse b-start
rows above have r=m and end at positive 1,2,1 respectively. The C row
has r=k=m-2 and ends at C; the initial word-1 row ends at a before its
next a step would cross the deleted core a cut. This is a coordinate
description for the sole writer's actual partial-path construction, not
a standalone claim that those rows have already passed Lean.
-/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges

private theorem j2_word1_initial_reflected {m : Nat} (hm : 5 ≤ m) :
    wordStart m 1 = finRotate (m + 1) ^ (m - 1) * a m := by
  solve_j2_seam_coordinate m

private theorem j2_word0_contact_reflected {m : Nat} (hm : 5 ≤ m) :
    c m = contactAnchor (j2Contact hm) * finRotate (m + 1) ^ (m - 2) * a m := by
  solve_j2_seam_coordinate m

private theorem j2_word0_final_b_start {m : Nat} (hm : 5 ≤ m) :
    contactAnchor (j2Contact hm) * c m =
      gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 1, by omega⟩ * b m := by
  solve_j2_seam_coordinate m

private theorem j2_word2_initial_positive {m : Nat} (hm : 5 ≤ m) :
    wordStart m 2 = contactAnchor (j2Contact hm) * finRotate (m + 1) ^ m := by
  solve_j2_seam_coordinate m

private theorem j2_word3_initial_reflected {m : Nat} (hm : 5 ≤ m) :
    wordStart m 3 =
      gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 1, by omega⟩ * a m := by
  solve_j2_seam_coordinate m

private theorem j2_word3_final_b_start {m : Nat} (hm : 5 ≤ m) :
    wordStart m 3 * a m * c m =
      gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 2, by omega⟩ * b m := by
  solve_j2_seam_coordinate m

private theorem j2_word4_final_b_start {m : Nat} (hm : 5 ≤ m) :
    wordStart m 4 * a m * b m * c m = lowerPort (j2Contact hm) * b m := by
  solve_j2_seam_coordinate m

private theorem j2_cb_c_pow (m t : Nat) :
    (c m * b m) ^ t * c m = c m * (b m * c m) ^ t := by
  induction t with
  | zero => simp only [pow_zero, one_mul, mul_one]
  | succ t ih =>
    calc
      _ = (c m * b m) * ((c m * b m) ^ t * c m) := by
        rw [pow_succ', mul_assoc]
      _ = (c m * b m) * (c m * (b m * c m) ^ t) := by rw [ih]
      _ = c m * ((b m * c m) * (b m * c m) ^ t) := by simp only [mul_assoc]
      _ = c m * (b m * c m) ^ (t + 1) := by rw [pow_succ']

private theorem j2_word1_final_a_start {m : Nat} (hm : 5 ≤ m) :
    wordStart m 1 * (a m * b m) ^ (m - 1) *
        (c m * b m) ^ (m - 3) * c m = lowerPort (j2Contact hm) := by
  rw [j2_word1_seed hm, mul_assoc (a m), j2_cb_c_pow]
  simp only [lowerPort, j2Contact, Fin.val_mk, mul_assoc]

private theorem j2_word2_final_aba_start {m : Nat} (hm : 5 ≤ m) :
    wordStart m 2 * a m * (c m * b m) ^ (m - 3) * c m =
      gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 2, by omega⟩ := by
  rw [j2_word2_seed hm, mul_assoc (contactAnchor (j2Contact hm)), j2_b_cb_pow]
  simp only [← mul_assoc, gapAnchor, Fin.val_mk]
  rw [show m - 2 = (m - 3) + 1 by omega, pow_succ]
  simp only [mul_assoc]

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
