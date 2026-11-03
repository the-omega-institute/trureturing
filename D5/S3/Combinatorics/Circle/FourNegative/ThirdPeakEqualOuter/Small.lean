import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.SmallArithmetic

/-! UNELABORATED. Exact dyadic exhaustion of the three adjacent families,
including the single 15-label exception. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
open SourceWidth PeriodicShortening RunFirstEarTransport
open private A B L K SU SV SW Window AfterWWindows pow_split pow_lower
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Arithmetic
open private Joint realize_split
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Source
open private afterW_realize
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.AfterW
open private smallY smallM threshold small_selector
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.SmallArithmetic
open private oldValue newValue sourceMod
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

private def smallB : Fin 3 → ℕ := ![2,2,3]
private def smallC : Fin 3 → ℕ := ![1,2,2]

private theorem small_unbounded (i : Fin 3) (a : ℕ) (ha : smallB i < a)
    (hs : threshold i ≤ (2:ℤ)^(a-smallB i)) :
    Joint a (smallB i) (a+smallC i) := by
  let b := smallB i
  let c := a+smallC i
  let s : ℤ := 2^(a-b)
  have hb : 2 ≤ b := by fin_cases i <;> norm_num [b,smallB]
  have hc : 2 ≤ c := by dsimp [c]; omega
  have hy : (2:ℤ)^b=smallY i := by fin_cases i <;> norm_num [b,smallB,smallY]
  have hm : (2:ℤ)^(smallC i)=smallM i := by fin_cases i <;> norm_num [smallC,smallM]
  have hx : (2:ℤ)^a=s*smallY i := by rw [pow_split a b (by omega),hy]; rfl
  have hz : (2:ℤ)^c=smallM i*(s*smallY i) := by
    dsimp [c]; rw [pow_add,hm,hx]; ring
  obtain ⟨r,v,hr,hrcap,hv,hvcap,hw⟩ := small_selector i s hs
  let rn := r.toNat
  let vn := v.toNat
  have er : (rn:ℤ)=r := Int.toNat_of_nonneg (by omega)
  have ev : (vn:ℤ)=v := Int.toNat_of_nonneg (by omega)
  have half (n : ℕ) (hn : 1 ≤ n) : (2:ℤ)^n=2*2^(n-1) := by
    conv_lhs => rw [show n=(n-1)+1 by omega,pow_succ]
    ring
  have hrn : rn ≤ 2^(a-1) := by
    have hh := half a (by omega)
    have hh' : 2*r ≤ (2:ℤ)^a := by rw [hx]; nlinarith only [hrcap]
    have : (rn:ℤ) ≤ (2:ℤ)^(a-1) := by rw [er]; omega
    exact_mod_cast this
  have hvn : vn ≤ 2^(c-1) := by
    have hh := half c (by omega)
    have hh' : 2*v < (2:ℤ)^c := by rw [hz]; nlinarith only [hvcap]
    have : (vn:ℤ) ≤ (2:ℤ)^(c-1) := by rw [ev]; omega
    exact_mod_cast this
  apply afterW_realize a b c rn vn (by omega) hb hc
    (by exact_mod_cast (show (1:ℤ) ≤ rn by omega)) hrn
    (by exact_mod_cast (show (1:ℤ) ≤ vn by omega)) hvn
  simpa only [hx,hy,hz,er,ev] using hw

private theorem small_A (a : ℕ) (ha : 3 ≤ a) : Joint a 2 (a+1) := by
  by_cases h3 : a=3
  · subst a
    apply afterW_realize 3 2 4 2 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    norm_num [AfterWWindows,Window,A,B,L,K,SU,SV,SW]
  · by_cases h4 : a=4
    · subst a
      let pre : List ℕ := [13,11,6,10]
      let post : List ℕ := [12,7,14,9,5,4,8,2,1,0,3]
      apply realize_split 4 2 5 (by decide) (by decide) (by decide) pre post
      · decide
      · decide
      · decide
    · have hs : (8:ℤ) ≤ 2^(a-2) := by simpa using pow_lower (a-2) 3 (by omega)
      simpa only [smallB,smallC] using small_unbounded 0 a (by simp [smallB]; omega)
        (by simpa [smallB,threshold] using hs)

private theorem small_B (a : ℕ) (ha : 3 ≤ a) : Joint a 2 (a+2) := by
  by_cases h3 : a=3
  · subst a
    apply afterW_realize 3 2 5 2 6 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    norm_num [AfterWWindows,Window,A,B,L,K,SU,SV,SW]
  · have hs : (4:ℤ) ≤ 2^(a-2) := by simpa using pow_lower (a-2) 2 (by omega)
    simpa only [smallB,smallC] using small_unbounded 1 a (by simp [smallB]; omega)
      (by simpa [smallB,threshold] using hs)

private theorem small_C (a : ℕ) (ha : 4 ≤ a) : Joint a 3 (a+2) := by
  by_cases h4 : a=4
  · subst a
    apply afterW_realize 4 3 6 2 7 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    norm_num [AfterWWindows,Window,A,B,L,K,SU,SV,SW]
  · have hs : (4:ℤ) ≤ 2^(a-3) := by simpa using pow_lower (a-3) 2 (by omega)
    simpa only [smallB,smallC] using small_unbounded 2 a (by simp [smallB]; omega)
      (by simpa [smallB,threshold] using hs)

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
