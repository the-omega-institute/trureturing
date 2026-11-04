/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Arithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Arithmetic
   mirror-E: none(waiver:consumed-arithmetic)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Nonnegative ceiling, capacity and reserve interval arithmetic. -/
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-! Integer rounding and uniform margins for physical chamber reserves. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers

private def ceilpos (n d : ℤ) : ℕ := ((n+d-1)/d).toNat

private theorem ceilpos_bounds (n d : ℤ) (hd : 0 < d) :
    n ≤ d*(ceilpos n d:ℤ) ∧
      (0 < ceilpos n d → d*((ceilpos n d:ℤ)-1)<n) := by
  let q := (n+d-1)/d
  have hrem := Int.emod_nonneg (n+d-1) (show d≠0 by omega)
  have hrem' := Int.emod_lt_of_pos (n+d-1) hd
  have heq := Int.emod_add_mul_ediv (n+d-1) d
  change n ≤ d*(q.toNat:ℤ) ∧ (0<q.toNat → d*((q.toNat:ℤ)-1)<n)
  by_cases hq : 0 ≤ q
  · rw [Int.toNat_of_nonneg hq]
    constructor
    · dsimp [q] at *; nlinarith
    · intro _; dsimp [q] at *; nlinarith
  · have hz : q.toNat=0 := Int.toNat_eq_zero.mpr (by omega)
    rw [hz]
    simp only [Nat.cast_zero, mul_zero, Nat.lt_irrefl, false_implies, and_true]
    have hq' : q≤-1 := by omega
    have hm := mul_le_mul_of_nonneg_left hq' hd.le
    dsimp [q] at hm
    nlinarith

private theorem ceilpos_capacity (n d : ℤ) (cap : ℕ) (hd : 0 < d)
    (hcap : n ≤ d*(cap:ℤ)) : ceilpos n d ≤ cap := by
  have h := ceilpos_bounds n d hd
  by_contra hh
  have hn : 0 < ceilpos n d := by omega
  have hn' : (cap:ℤ)+1 ≤ (ceilpos n d:ℤ) := by exact_mod_cast (show cap+1≤ceilpos n d by omega)
  have hle : (cap:ℤ) ≤ (ceilpos n d:ℤ)-1 := by omega
  have hm := mul_le_mul_of_nonneg_left hle hd.le
  nlinarith [h.2 hn]

/-- Rounding by the previous even reserve base fits the next reserve interval. -/
private theorem rounded_reserve (A e E S : ℤ) (hA : 0 < A)
    (he : 0 < e) (hS : A ≤ S ∧ S ≤ 2*e-A) (hE : 2*e ≤ E) :
    let n := ceilpos (E-S) (2*e)
    E ≤ S+2*e*n ∧ S+2*e*n ≤ 2*E-A := by
  dsimp only
  have h := ceilpos_bounds (E-S) (2*e) (by omega)
  have hn : 0 < ceilpos (E-S) (2*e) := by
    by_contra hh
    have hz : ceilpos (E-S) (2*e)=0 := by omega
    rw [hz] at h
    norm_num at h
    omega
  constructor
  · nlinarith [h.1]
  · by_cases hn1 : ceilpos (E-S) (2*e)=1
    · rw [hn1]; norm_num; omega
    · have hn2 : (2:ℤ) ≤ ceilpos (E-S) (2*e) := by exact_mod_cast (show 2≤ceilpos (E-S) (2*e) by omega)
      have hm : 0≤2*e*((ceilpos (E-S) (2*e):ℤ)-2) := mul_nonneg (by omega) (by omega)
      nlinarith [h.2 hn]

/-- The uniform mass margin used by every chamber is strict, including R=T=Z=4. -/
private theorem mass_margin (R T Z : ℤ) (hR : 4 ≤ R) (hT : 4 ≤ T) (hZ : 4 ≤ Z) :
    3*(R*T+R+1)<R*T*Z := by
  have hT0 : 0≤T := by omega
  have hm := mul_nonneg hT0 (show 0≤Z-4 by omega)
  have hR0 : 0≤R := by omega
  have hm' := mul_nonneg hR0 (show 0≤T*(Z-3)-3 by nlinarith)
  have hinner : 1≤T*(Z-3)-3 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hinner hR0
  nlinarith

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
