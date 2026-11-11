/- GID: D5/S3/Combinatorics/Circle/Orbit/MersennePhaseRotationStabilizer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/Orbit/MersennePhaseRotationStabilizer
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Exact rotation stabilizer of the full physical three-phase integer-zero family. -/
module

public import D5.S3.Combinatorics.Circle.Orbit.MersennePhaseNoncyclicFamily
import all D5.S3.Combinatorics.Circle.Orbit.MersennePhaseNoncyclicFamily
public import Mathlib.Logic.Equiv.Fin.Rotate

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.MersennePhaseRotationStabilizer

open scoped BigOperators
open MersennePhaseNoncyclicFamily

open private mem_phaseLift phaseRead phaseRead_phaseLift
  from D5.S3.Combinatorics.Circle.Orbit.MersennePhaseNoncyclicFamily

/- The exponent is unrestricted. In particular, this does not use the
bounded-exponent rotate_val from TwoBitZeroSubsets. -/
private theorem rotate_pow_val {n : ℕ} (hn : 1 < n) (h : ℕ) (i : Fin n) :
    (((finRotate n : Equiv.Perm (Fin n)) ^ h) i).val = (i.val + h) % n := by
  haveI : NeZero n := ⟨by omega⟩
  induction h with
  | zero =>
      change i.val = (i.val + 0) % n
      simp only [Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
  | succ h ih =>
      calc
        _ = ((((finRotate n : Equiv.Perm (Fin n)) ^ h) i).val + 1) % n := by
          rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add,
            Fin.val_one', Nat.mod_eq_of_lt hn]
        _ = (i.val + (h + 1)) % n := by
          rw [ih, Nat.mod_add_mod, Nat.add_assoc]

/- Forward physical rotation induces forward phase rotation for every h. -/
private theorem rotation_phase (d : ℕ) (hd : 3 ≤ d) (h : ℕ)
    (i : Fin (3 * d)) :
    (⟨(((finRotate (3 * d) : Equiv.Perm (Fin (3 * d))) ^ h) i).val % d,
      Nat.mod_lt _ (by omega)⟩ : Fin d) =
      ((finRotate d : Equiv.Perm (Fin d)) ^ h)
        ⟨i.val % d, Nat.mod_lt _ (by omega)⟩ := by
  apply Fin.ext
  change (((finRotate (3 * d) : Equiv.Perm (Fin (3 * d))) ^ h) i).val % d =
    (((finRotate d : Equiv.Perm (Fin d)) ^ h)
      ⟨i.val % d, Nat.mod_lt _ (by omega)⟩).val
  rw [rotate_pow_val (by omega), rotate_pow_val (by omega)]
  rw [Nat.mod_mod_of_dvd (i.val + h) (show d ∣ 3 * d from ⟨3, by omega⟩)]
  exact (Nat.mod_add_mod i.val d h).symm

/- Transport all physical labels by image; no quotient of the subset domain
or identification of equal source values is made. -/
private theorem phaseLift_image (d : ℕ) (hd : 3 ≤ d) (h : ℕ)
    (B : Finset (Fin d)) :
    (phaseLift d B).image ((finRotate (3 * d) : Equiv.Perm (Fin (3 * d))) ^ h) =
      phaseLift d (B.image ((finRotate d : Equiv.Perm (Fin d)) ^ h)) := by
  classical
  have hdpos : 0 < d := by omega
  let R : Equiv.Perm (Fin (3 * d)) := (finRotate (3 * d)) ^ h
  let S : Equiv.Perm (Fin d) := (finRotate d) ^ h
  let rho : Fin (3 * d) → Fin d := fun i => ⟨i.val % d, Nat.mod_lt _ hdpos⟩
  have hcomm (i : Fin (3 * d)) : rho (R i) = S (rho i) :=
    rotation_phase d hd h i
  change (phaseLift d B).image R = phaseLift d (B.image S)
  apply Finset.ext
  intro y
  constructor
  · rintro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    apply (mem_phaseLift hdpos (B.image S) (R x)).mpr
    change rho (R x) ∈ B.image S
    rw [hcomm]
    exact Finset.mem_image.mpr ⟨rho x, (mem_phaseLift hdpos B x).mp hx, rfl⟩
  · intro hy
    have hy' : rho y ∈ B.image S := (mem_phaseLift hdpos (B.image S) y).mp hy
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hy'
    have hxphase : rho (R.symm y) = j := by
      apply S.injective
      calc
        S (rho (R.symm y)) = rho (R (R.symm y)) := (hcomm _).symm
        _ = rho y := by rw [R.apply_symm_apply]
        _ = S j := he.symm
    apply Finset.mem_image.mpr
    refine ⟨R.symm y, ?_, R.apply_symm_apply y⟩
    apply (mem_phaseLift hdpos B (R.symm y)).mpr
    change rho (R.symm y) ∈ B
    rwa [hxphase]

/- Consume the supplied read/lift inverse, rather than reconstructing fibres. -/
private theorem phaseLift_injective (d : ℕ) (hd : 0 < d) :
    Function.Injective (phaseLift d) := by
  intro B C he
  have hr := congrArg (phaseRead d hd) he
  simpa only [phaseRead_phaseLift d hd] using hr

/- This uses the kernel-checked full classification interface, including its unique
witness, without reopening the trace, gcd, binary-mask, or counting proofs. -/
private theorem zero_phaseLift_iff (d : ℕ) (hd : 3 ≤ d)
    (h19 : ¬19 ∣ (2 ^ (d + 1) - 3)) (B : Finset (Fin d)) :
    (∑ i ∈ phaseLift d B,
      SourceWidth.actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0 ↔
      ((⟨d - 3, by omega⟩ : Fin d) ∈ B ↔ (⟨d - 1, by omega⟩ : Fin d) ∈ B) := by
  classical
  have hinj := phaseLift_injective d (by omega)
  constructor
  · intro hz
    obtain ⟨C, ⟨he, hp⟩, _⟩ :=
      (actual_zero_iff_phase_pair d hd h19 (phaseLift d B)).mp hz
    have hBC : B = C := hinj he
    simpa only [hBC] using hp
  · intro hp
    apply (actual_zero_iff_phase_pair d hd h19 (phaseLift d B)).mpr
    refine ⟨B, ⟨rfl, hp⟩, ?_⟩
    intro C hC
    exact (hinj hC.1).symm

/-- Exact forward-rotation preservation of the full physical integer-zero
family. The exceptional d=4 symmetry is included, and h is any natural number. -/
theorem actual_zero_family_rotation_iff (d h : ℕ) (hd : 3 ≤ d)
    (h19 : ¬19 ∣ (2 ^ (d + 1) - 3)) :
    (∀ A : Finset (Fin (3 * d)),
      (∑ i ∈ A.image ((finRotate (3 * d) : Equiv.Perm (Fin (3 * d))) ^ h),
        SourceWidth.actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0 ↔
      (∑ i ∈ A,
        SourceWidth.actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0) ↔
      (if d = 4 then 2 else d) ∣ h := by
  classical
  have hdpos : 0 < d := by omega
  let R : Equiv.Perm (Fin (3 * d)) := (finRotate (3 * d)) ^ h
  let S : Equiv.Perm (Fin d) := (finRotate d) ^ h
  let a : Fin d := ⟨d - 3, by omega⟩
  let b : Fin d := ⟨d - 1, by omega⟩
  let e : ℕ := h % d
  have he_lt : e < d := Nat.mod_lt h hdpos
  have hab : a ≠ b := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [a, b] at hv
    omega
  have hval (j : Fin d) : (S j).val = (j.val + e) % d := by
    dsimp [S]
    rw [rotate_pow_val (by omega)]
    dsimp [e]
    simp only [Nat.add_mod, Nat.mod_mod]
  have hcriterion :
      (∀ A : Finset (Fin (3 * d)),
        (∑ i ∈ A.image R,
          SourceWidth.actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0 ↔
        (∑ i ∈ A,
          SourceWidth.actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0) ↔
        e = 0 ∨ (d = 4 ∧ e = 2) := by
    constructor
    · intro hpres
      have hsingle (j : Fin d) :
          (∑ i ∈ phaseLift d {j},
            SourceWidth.actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0 ↔
            (j ≠ a ∧ j ≠ b) := by
        rw [zero_phaseLift_iff d hd h19]
        change (a ∈ ({j} : Finset (Fin d)) ↔ b ∈ ({j} : Finset (Fin d))) ↔ _
        simp only [Finset.mem_singleton]
        constructor
        · intro hp
          constructor
          · intro hja
            have hbj : b = j := hp.mp hja.symm
            exact hab (hja.symm.trans hbj.symm)
          · intro hjb
            have haj : a = j := hp.mpr hjb.symm
            exact hab (haj.trans hjb)
        · rintro ⟨hja, hjb⟩
          constructor
          · intro haj
            exact False.elim (hja haj.symm)
          · intro hbj
            exact False.elim (hjb hbj.symm)
      have hsingle_transport (j : Fin d) :
          (S j ≠ a ∧ S j ≠ b) ↔ (j ≠ a ∧ j ≠ b) := by
        have ht := hpres (phaseLift d {j})
        have himg : (phaseLift d {j}).image R = phaseLift d {S j} := by
          simpa only [Finset.image_singleton] using phaseLift_image d hd h {j}
        rw [himg, hsingle, hsingle] at ht
        exact ht
      have hsupport (j : Fin d) : (S j = a ∨ S j = b) ↔ (j = a ∨ j = b) := by
        have ht := not_congr (hsingle_transport j)
        simpa only [not_and_or, not_not] using ht
      have hSa : S a = a ∨ S a = b := (hsupport a).mpr (Or.inl rfl)
      have hSb : S b = a ∨ S b = b := (hsupport b).mpr (Or.inr rfl)
      /- Only two wraps are possible for j+e. This explicit quotient argument
      avoids asking omega to reason about division by a variable modulus. -/
      have hmod (x : ℕ) (hx : x < 2 * d) : x % d = x ∨ (d ≤ x ∧ x % d = x - d) := by
        have hq : x / d < 2 := Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hx)
        have hm := Nat.mod_add_div x d
        have hqc : x / d = 0 ∨ x / d = 1 := by
          have exhaustive : ∀ q : Fin 2, q.val = 0 ∨ q.val = 1 := by decide
          exact exhaustive ⟨x / d, hq⟩
        rcases hqc with hq0 | hq1
        · simp only [hq0, Nat.mul_zero, Nat.add_zero] at hm
          exact Or.inl hm
        · simp only [hq1, Nat.mul_one] at hm
          exact Or.inr ⟨by omega, by omega⟩
      rcases hSa with haa | hab'
      · left
        have hv := congrArg Fin.val haa
        rw [hval] at hv
        change (d - 3 + e) % d = d - 3 at hv
        have hm := hmod (d - 3 + e) (by omega)
        rcases hm with hm | ⟨hwrap, hm⟩ <;> omega
      · have he2 : e = 2 := by
          have hv := congrArg Fin.val hab'
          rw [hval] at hv
          change (d - 3 + e) % d = d - 1 at hv
          have hm := hmod (d - 3 + e) (by omega)
          rcases hm with hm | ⟨hwrap, hm⟩ <;> omega
        have hba : S b = a := by
          rcases hSb with hba | hbb
          · exact hba
          · exact False.elim (hab (S.injective (hab'.trans hbb.symm)))
        have hd4 : d = 4 := by
          have hv := congrArg Fin.val hba
          rw [hval] at hv
          change (d - 1 + e) % d = d - 3 at hv
          have hm := hmod (d - 1 + e) (by omega)
          rcases hm with hm | ⟨hwrap, hm⟩ <;> omega
        exact Or.inr ⟨hd4, he2⟩
    · intro he
      have hsend : (S a = a ∧ S b = b) ∨ (S a = b ∧ S b = a) := by
        rcases he with he0 | ⟨hd4, he2⟩
        · left
          constructor
          · apply Fin.ext
            rw [hval, he0, Nat.add_zero, Nat.mod_eq_of_lt a.isLt]
          · apply Fin.ext
            rw [hval, he0, Nat.add_zero, Nat.mod_eq_of_lt b.isLt]
        · subst d
          right
          constructor <;> apply Fin.ext <;> rw [hval, he2] <;> norm_num [a, b]
      have hmem (B : Finset (Fin d)) (j : Fin d) :
          S j ∈ B.image S ↔ j ∈ B := by
        constructor
        · intro hj
          obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hj
          have hxj : x = j := S.injective heq
          simpa only [hxj] using hx
        · intro hj
          exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      have hpair (B : Finset (Fin d)) :
          (a ∈ B.image S ↔ b ∈ B.image S) ↔ (a ∈ B ↔ b ∈ B) := by
        rcases hsend with ⟨haa, hbb⟩ | ⟨hab', hba⟩
        · have hma : a ∈ B.image S ↔ a ∈ B := by
            simpa only [haa] using hmem B a
          have hmb : b ∈ B.image S ↔ b ∈ B := by
            simpa only [hbb] using hmem B b
          exact iff_congr hma hmb
        · have hma : b ∈ B.image S ↔ a ∈ B := by
            simpa only [hab'] using hmem B a
          have hmb : a ∈ B.image S ↔ b ∈ B := by
            simpa only [hba] using hmem B b
          exact (iff_congr hmb hma).trans iff_comm
      intro A
      constructor
      · intro hz
        obtain ⟨C, ⟨hAC, hCpair⟩, _⟩ :=
          (actual_zero_iff_phase_pair d hd h19 (A.image R)).mp hz
        let B : Finset (Fin d) := C.image S.symm
        have hBC : B.image S = C := by
          simp only [B, Finset.image_image, Function.comp_def, S.apply_symm_apply,
            Finset.image_id']
        have hAB : A = phaseLift d B := by
          apply Finset.image_injective R.injective
          calc
            A.image R = phaseLift d C := hAC
            _ = (phaseLift d B).image R := by
              rw [phaseLift_image d hd h B]
              exact congrArg (phaseLift d) hBC.symm
        have hBpair : a ∈ B ↔ b ∈ B := (hpair B).mp (by
          rw [hBC]
          exact hCpair)
        rw [hAB]
        exact (zero_phaseLift_iff d hd h19 B).mpr hBpair
      · intro hz
        obtain ⟨B, ⟨hAB, hBpair⟩, _⟩ :=
          (actual_zero_iff_phase_pair d hd h19 A).mp hz
        rw [hAB, phaseLift_image d hd h B]
        exact (zero_phaseLift_iff d hd h19 (B.image S)).mpr ((hpair B).mpr hBpair)
  change (∀ A : Finset (Fin (3 * d)),
    (∑ i ∈ A.image R,
      SourceWidth.actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0 ↔
    (∑ i ∈ A,
      SourceWidth.actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0) ↔ _
  rw [hcriterion]
  change (h % d = 0 ∨ (d = 4 ∧ h % d = 2)) ↔ (if d = 4 then 2 else d) ∣ h
  by_cases hd4 : d = 4
  · subst d
    simp only [ite_true, true_and]
    omega
  · simp only [hd4, false_and, or_false, ite_false]
    exact Nat.dvd_iff_mod_eq_zero.symm

end D5.S3.Combinatorics.Circle.MersennePhaseRotationStabilizer
