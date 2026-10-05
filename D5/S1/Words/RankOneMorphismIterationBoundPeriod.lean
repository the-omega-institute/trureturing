/- GID: D5/S1/Words/RankOneMorphismIterationBoundPeriod
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundPeriod
   mirror-E: none(waiver:consumed-source-period-arithmetic)
   anchors: []
   digest: Effective lambda-factor stripping with exact divisibility and one-sided phases. -/
import D5.S1.Words.RankOneMorphismIterationBoundFixedWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
namespace Parameters
variable {f : Morphism} (p : Parameters f)

/-- Strip only gcd factors actually dividing lambda, by decreasing positive
    integers. An arbitrary original period divides the retained coprime ray step. -/
theorem strip_period (P : ℕ) (hP : 0 < P) :
    ∃ q t : ℕ, 0 < q ∧ Nat.Coprime q p.lam ∧ P ∣ q*p.lam^t := by
  induction P using Nat.strong_induction_on with
  | h P ih =>
    by_cases hc : Nat.Coprime P p.lam
    · exact ⟨P,0,hP,hc,by simp⟩
    · have hg : 0 < Nat.gcd P p.lam := Nat.gcd_pos_of_pos_left _ hP
      have hg2 : 1 < Nat.gcd P p.lam := by
        have hne : Nat.gcd P p.lam ≠ 1 := hc
        omega
      have hsmall : P / Nat.gcd P p.lam < P := Nat.div_lt_self hP hg2
      have hquot : 0 < P / Nat.gcd P p.lam :=
        Nat.div_pos (Nat.gcd_le_left _ hP) hg
      obtain ⟨q,t,hq,hcop,hdiv⟩ := ih _ hsmall hquot
      refine ⟨q,t+1,hq,hcop,?_⟩
      have hprod := Nat.mul_dvd_mul (Nat.gcd_dvd_right P p.lam) hdiv
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left P p.lam)] at hprod
      convert hprod using 1 <;> rw [pow_succ] <;> ring

/-- Taking a divisible subray retains the actual one-sided phase exactly. -/
theorem height_subray {x : ℕ → Letter} {r P Q : ℕ} (hdiv : P ∣ Q)
    (h : ∀ j, p.height x (r+j*P) = p.height x r) :
    ∀ j, p.height x (r+j*Q) = p.height x r := by
  obtain ⟨k,rfl⟩ := hdiv
  intro j
  convert h (j*k) using 1 <;> congr 2 <;> ring

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
