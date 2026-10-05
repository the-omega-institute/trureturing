/- GID: D5/S1/Words/RankOneMorphismIterationBoundArithmetic
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundArithmetic
   mirror-E: none(waiver:consumed-source-arithmetic)
   anchors: []
   utility: none
   digest: Positive primitive rank-one binary incidence parameters and exact iterated counts. -/
import D5.S1.Words.RankOneMorphismIterationBoundDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound

theorem incidence_positive {f : Morphism} (hne : Nonerasing f)
    (hp : Prolongable f) (hprim : Primitive f) (hr : RankOne f) :
    ∀ c b, 0 < parikh (f c) b := by
  obtain ⟨v, hv, hf⟩ := hp
  have haa : 0 < parikh (f 0) 0 := by
    simp [hf, parikh, AbelianBorders.AbelianBorderQuestionDefs.letterCount]
  have hba : 0 < parikh (f 0) 1 := by
    by_contra h
    have ha : parikh (f 0) 1 = 0 := by omega
    have hb : parikh (f 1) 1 = 0 := by
      dsimp [RankOne] at hr
      rw [ha, mul_zero] at hr
      exact (Nat.mul_eq_zero.mp hr).resolve_left (by omega)
    have hz : ∀ k, parikh (image f k 0) 1 = 0 := by
      intro k
      induction k with
      | zero => simp [parikh, AbelianBorders.AbelianBorderQuestionDefs.letterCount]
      | succ k ih => rw [image_succ, parikh_subst, ha, hb]; simp
    obtain ⟨k, hk, hmem⟩ := hprim
    have hc : 0 < parikh (image f k 0) 1 := by
      exact List.count_pos_iff.mpr (hmem 0 1)
    rw [hz k] at hc
    omega
  have hab : 0 < parikh (f 1) 0 := by
    by_contra h
    have ha : parikh (f 1) 0 = 0 := by omega
    have hb : parikh (f 1) 1 = 0 := by
      dsimp [RankOne] at hr
      rw [ha, zero_mul] at hr
      exact (Nat.mul_eq_zero.mp hr).resolve_left (by omega)
    have hl := parikh_binary_length (f 1)
    have hn := hne 1
    omega
  have hbb : 0 < parikh (f 1) 1 := by
    have h := Nat.mul_pos hab hba
    dsimp [RankOne] at hr
    rw [← hr] at h
    exact Nat.pos_of_mul_pos_left h
  intro c b
  fin_cases c <;> fin_cases b
  · exact haa
  · exact hba
  · exact hab
  · exact hbb

/-- Parameters are extracted from the actual incidence matrix, without an extra
    arithmetic hypothesis on the final source domain. -/
theorem exists_parameters {f : Morphism} (hne : Nonerasing f)
    (hp : Prolongable f) (hprim : Primitive f) (hr : RankOne f) :
    Nonempty (Parameters f) := by
  have hpos := incidence_positive hne hp hprim hr
  let aa := parikh (f 0) 0
  let ab := parikh (f 1) 0
  let ba := parikh (f 0) 1
  let bb := parikh (f 1) 1
  let A := Nat.gcd aa ab
  let n := aa / A
  let m := ab / A
  have hA : 0 < A := Nat.gcd_pos_of_pos_left ab (hpos 0 0)
  have hnA : n * A = aa := Nat.div_mul_cancel (Nat.gcd_dvd_left aa ab)
  have hmA : m * A = ab := Nat.div_mul_cancel (Nat.gcd_dvd_right aa ab)
  have hn : 0 < n := by
    apply Nat.pos_of_mul_pos_right (b := A)
    rw [hnA]; exact hpos 0 0
  have hm : 0 < m := by
    apply Nat.pos_of_mul_pos_right (b := A)
    rw [hmA]; exact hpos 1 0
  have hcop : Nat.Coprime n m := Nat.coprime_div_gcd_div_gcd hA
  have hcross : n * bb = m * ba := by
    apply Nat.eq_of_mul_eq_mul_right hA
    calc n * bb * A = (n * A) * bb := by ring
         _ = aa * bb := by rw [hnA]
         _ = ab * ba := hr
         _ = m * ba * A := by rw [← hmA]; ring
  have hdvd : n ∣ ba := hcop.dvd_of_dvd_mul_left (by rw [← hcross]; exact dvd_mul_right n bb)
  let B := ba / n
  have hnB : n * B = ba := Nat.mul_div_cancel' hdvd
  have hmB : m * B = bb := by
    apply Nat.eq_of_mul_eq_mul_left hn
    calc n * (m * B) = m * (n * B) := by ring
         _ = m * ba := by rw [hnB]
         _ = n * bb := hcross.symm
  have hB : 0 < B := by
    apply Nat.pos_of_mul_pos_left (a := n)
    rw [hnB]; exact hpos 0 1
  refine ⟨⟨A, B, n, m, hA, hB, hn, hm, hcop, ?_, ?_⟩⟩
  · intro c; fin_cases c
    · simpa [aa] using hnA.symm
    · simpa [ab] using hmA.symm
  · intro c; fin_cases c
    · simpa [ba] using hnB.symm
    · simpa [bb] using hmB.symm

namespace Parameters
variable {f : Morphism} (p : Parameters f)

theorem iterated_count (t : ℕ) (c b : Letter) :
    parikh (image f (t+1) c) b =
      p.mult c * p.lam ^ t * (if b = 0 then p.A else p.B) := by
  induction t generalizing b with
  | zero =>
    simp only [image_one, pow_zero, mul_one]
    fin_cases b
    · simpa [mult] using p.count_a c
    · simpa [mult] using p.count_b c
  | succ t ih =>
    rw [image_succ, parikh_subst, ih 0, ih 1]
    fin_cases b <;> simp [p.count_a, p.count_b, mult, lam, pow_succ] <;> split_ifs <;> ring

theorem iterated_length (t : ℕ) (c : Letter) :
    (image f (t+1) c).length = p.mult c * (p.d * p.lam ^ t) := by
  rw [← parikh_binary_length, p.iterated_count t c 0, p.iterated_count t c 1]
  simp [d]
  ring

theorem iterated_gcd (t : ℕ) :
    Nat.gcd (image f (t+1) 0).length (image f (t+1) 1).length = p.d * p.lam ^ t := by
  rw [p.iterated_length, p.iterated_length]
  norm_num [mult]
  rw [Nat.gcd_mul_right, p.coprime.gcd_eq_one, one_mul]

theorem charge_zero_iff {w : Word} {t : ℕ}
    (hl : w.length = p.d * p.lam ^ t) :
    p.charge w = 0 ↔ parikh w = fun b => p.lam ^ t * (if b = 0 then p.A else p.B) := by
  have hlen := parikh_binary_length w
  have ha : (0 : ℤ) < p.A := by exact_mod_cast p.A_pos
  have hb : (0 : ℤ) < p.B := by exact_mod_cast p.B_pos
  have hz : (parikh w 0 : ℤ) + parikh w 1 = (p.A + p.B : ℤ) * p.lam ^ t := by
    exact_mod_cast (show parikh w 0 + parikh w 1 = (p.A + p.B) * p.lam ^ t by simpa [d] using hlen.trans hl)
  constructor
  · intro h
    dsimp [charge] at h
    have h0 : (parikh w 0 : ℤ) = p.lam ^ t * p.A := by nlinarith
    have h1 : (parikh w 1 : ℤ) = p.lam ^ t * p.B := by nlinarith
    ext b; fin_cases b
    · simpa using (show parikh w 0 = p.lam ^ t * p.A by exact_mod_cast h0)
    · simpa using (show parikh w 1 = p.lam ^ t * p.B by exact_mod_cast h1)
  · intro h
    dsimp [charge]; rw [congrFun h 0, congrFun h 1]
    norm_num only [Fin.reduceFinMk, Fin.isValue, Fin.zero_eta, Fin.mk_one, ite_true, show (1 : Letter) ≠ 0 by decide, ite_false, Nat.cast_mul, Nat.cast_pow]
    ring

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
