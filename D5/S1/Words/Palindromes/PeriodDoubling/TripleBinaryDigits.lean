/- GID: D5/S1/Words/Palindromes/PeriodDoubling/TripleBinaryDigits
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/TripleBinaryDigits
   mirror-E: none(waiver:signed-binary-carry-construction)
   anchors: []
   utility: none
   digest: Shifted binary digit differences give a minimum nonadjacent signed expansion. -/

/-
proof_shape: content (triple_digits_value_and_minimality)
escape_witness: Binary carry reconstruction and the nonadjacency of differences for three times X.
admission_basis: escape-witness
Direct frozen dependencies: none; NonadjacentSignedDigits is delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.NonadjacentSignedDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

/-- Shifted binary digits of `3X` and `X` give a minimum signed expansion. -/
theorem triple_digits_value_and_minimality (X h : ℕ) (hbound : 3 * X < 2 ^ (h + 1)) :
    (List.ofFn (fun i : Fin h =>
      ((3 * X / 2 ^ (i.val + 1) % 2 : ℕ) : ℤ) -
        ((X / 2 ^ (i.val + 1) % 2 : ℕ) : ℤ))).foldr
          (fun z acc => z + 2 * acc) 0 = (X : ℤ) ∧
    (List.ofFn (fun i : Fin h =>
      ((3 * X / 2 ^ (i.val + 1) % 2 : ℕ) : ℤ) -
        ((X / 2 ^ (i.val + 1) % 2 : ℕ) : ℤ))).IsChain
          (fun a b => a = 0 ∨ b = 0) ∧
    signedWeight (X : ℤ) =
      ((List.ofFn (fun i : Fin h =>
        ((3 * X / 2 ^ (i.val + 1) % 2 : ℕ) : ℤ) -
          ((X / 2 ^ (i.val + 1) % 2 : ℕ) : ℤ))).filter (fun z => z != 0)).length := by
  have evaluate (h a b : ℕ) :
      (List.ofFn (fun i : Fin h => ((a / 2 ^ i.val % 2 : ℕ) : ℤ) -
        ((b / 2 ^ i.val % 2 : ℕ) : ℤ))).foldr (fun z acc => z+2*acc) 0 =
        ((a % 2 ^ h : ℕ) : ℤ) - ((b % 2 ^ h : ℕ) : ℤ) := by
    induction h generalizing a b with
    | zero => simp
    | succ h ih =>
      rw [List.ofFn_succ, List.foldr_cons]
      have ht :
          List.ofFn (fun i : Fin h => ((a / 2 ^ (i.val+1) % 2 : ℕ) : ℤ) -
            ((b / 2 ^ (i.val+1) % 2 : ℕ) : ℤ)) =
          List.ofFn (fun i : Fin h => (((a/2) / 2 ^ i.val % 2 : ℕ) : ℤ) -
            (((b/2) / 2 ^ i.val % 2 : ℕ) : ℤ)) := by
        congr 1
        funext i
        rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      simp only [Fin.val_zero, Fin.val_succ, pow_zero, Nat.div_one]
      rw [ht, ih]
      rw [pow_succ', Nat.mod_mul, Nat.mod_mul]
      push_cast
      ring
  let ds := List.ofFn (fun i : Fin h =>
      ((3 * X / 2 ^ (i.val + 1) % 2 : ℕ) : ℤ) -
        ((X / 2 ^ (i.val + 1) % 2 : ℕ) : ℤ))
  have hv : ds.foldr (fun z acc => z+2*acc) 0 = (X : ℤ) := by
    have he := evaluate h (3*X/2) (X/2)
    have he' : ds = List.ofFn (fun i : Fin h =>
      (((3*X/2) / 2 ^ i.val % 2 : ℕ) : ℤ) -
        (((X/2) / 2 ^ i.val % 2 : ℕ) : ℤ)) := by
      dsimp [ds]
      apply congrArg List.ofFn
      funext i
      have ha : (3*X)/2^(i.val+1)%2 = (3*X)/2/2^i.val%2 := by
        rw [pow_succ', Nat.div_div_eq_div_mul]
      have hb : X/2^(i.val+1)%2 = X/2/2^i.val%2 := by
        rw [pow_succ', Nat.div_div_eq_div_mul]
      exact congrArg₂ (fun a b : ℕ => (a : ℤ) - (b : ℤ)) ha hb
    rw [he', he]
    have ha : 3*X/2 < 2^h := by rw [pow_succ] at hbound; omega
    have hb : X/2 < 2^h := by omega
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    have hn : 3*X/2-X/2 = X := by omega
    have hle : X/2 ≤ 3*X/2 := by omega
    rw [← Nat.cast_sub hle, hn]
  have hcoeff : ∀ z ∈ ds, z = -1 ∨ z = 0 ∨ z = 1 := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    have ha := Nat.mod_lt (3*X/2^(i.val+1)) (by decide : 0<2)
    have hb := Nat.mod_lt (X/2^(i.val+1)) (by decide : 0<2)
    omega
  have hgap : ds.IsChain (fun a b => a=0 ∨ b=0) := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [ds, List.getElem_ofFn]
    let T := 2 ^ (i+1)
    have hT : 0 < T := by dsimp [T]; exact Nat.pow_pos (by decide)
    let a := X / T
    let r := X % T
    let c := (3*r)/T
    have hr : r < T := Nat.mod_lt X hT
    have hX : X = T*a+r := by
      exact (Nat.mod_add_div X T).symm.trans (Nat.add_comm _ _)
    have hq : 3*X/T = 3*a+c := by
      rw [hX]
      have he : 3*(T*a+r) = 3*r+T*(3*a) := by ring
      rw [he, Nat.add_mul_div_left _ _ hT]
      exact Nat.add_comm _ _
    have hc : c ≤ 2 := by
      dsimp [c]
      have ht : 3*r/T < 3 := (Nat.div_lt_iff_lt_mul hT).mpr (by omega)
      omega
    have hnext : 3*X/(2*T) = (3*a+c)/2 := by
      rw [mul_comm 2 T, ← Nat.div_div_eq_div_mul, hq]
    have hanext : X/(2*T) = a/2 := by
      rw [mul_comm 2 T, ← Nat.div_div_eq_div_mul]
    have hp : 2 ^ (i+1+1) = 2*T := by dsimp [T]; ring
    rw [hp, hnext, hanext]
    change ((3*X/T % 2 : ℕ) : ℤ) - ((a%2 : ℕ) : ℤ) = 0 ∨
      (((3*a+c)/2 % 2 : ℕ) : ℤ) - ((a/2%2 : ℕ) : ℤ) = 0
    rw [hq]
    have rule (a c : ℕ) (hc : c ≤ 2) :
        (3*a+c)%2 = a%2 ∨ ((3*a+c)/2)%2 = (a/2)%2 := by
      omega
    rcases rule a c hc with hh | hh
    · left
      exact sub_eq_zero.mpr (congrArg (fun x : ℕ => (x : ℤ)) hh)
    · right
      exact sub_eq_zero.mpr (congrArg (fun x : ℕ => (x : ℤ)) hh)
  have hw := signed_weight_nonadjacent ds hcoeff hgap
  rw [hv] at hw
  exact ⟨hv, hgap, hw⟩

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.triple_digits_value_and_minimality
