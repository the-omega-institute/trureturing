/- GID: D5/S3/ArithUnits/PellClassSuccessor
   generality: I
   mirror-B: D5/B/S3/ArithUnits/PellClassSuccessor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The least square partner detects multiple integral Pell solution classes. -/

import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

namespace D5.S3.ArithUnits.PellClassSuccessor

def Discriminant (k : ℕ) : ℤ := (k : ℤ)^2 + 1

def Sol (k : ℕ) (x y : ℤ) : Prop :=
  x^2 - Discriminant k * y^2 = Discriminant k

def SameClass (k : ℕ) (x y r s : ℤ) : Prop :=
  ∃ u v : ℤ,
    u^2 - Discriminant k * v^2 = 1 ∧
    x = r*u + Discriminant k*s*v ∧
    y = r*v + s*u

def MultipleClasses (k : ℕ) : Prop :=
  ∃ x y r s : ℤ,
    Sol k x y ∧ Sol k r s ∧ ¬ SameClass k x y r s

def NextSquarePartner (k m : ℕ) : Prop :=
  k < m ∧ IsSquare ((k^2 + 1)*(m^2 + 1)) ∧
    ∀ n : ℕ, k < n → IsSquare ((k^2 + 1)*(n^2 + 1)) → m ≤ n

/-- The exact A399755 conjecture, with unconditional least-partner existence.
Source: OEIS A399755 revision 12 and A399491 revision 25; integral class
semantics follow Robertson (2004), pp. 12–14. -/
theorem result :
    ∀ k : ℕ, 0 < k →
      ∃ m : ℕ, NextSquarePartner k m ∧
        (m < 4*k^3 + 3*k ↔ MultipleClasses k) := by
  intro k hk
  classical
  let K : ℤ := k
  let D : ℤ := K^2 + 1
  let A : ℤ := 2*K^2 + 1
  let B : ℤ := 4*K^3 + 3*K
  have hK : 0 < K := by dsimp [K]; exact_mod_cast hk
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hunit : A^2 - D*(2*K)^2 = 1 := by dsimp [A, D]; ring
  have hbase : Sol k D K := by dsimp [Sol, Discriminant, D, K]; ring
  have hclasses : MultipleClasses k ↔ ∃ x y : ℤ, Sol k x y ∧ ¬ D ∣ x := by
    have hdiv_class : ∀ x y r s : ℤ, Sol k x y → Sol k r s →
        D ∣ x → D ∣ r → SameClass k x y r s := by
      intro x y r s hxy hrs hx hr
      obtain ⟨z, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := hr
      change (D*z)^2 - D*y^2 = D at hxy
      change (D*t)^2 - D*s^2 = D at hrs
      have hz : D*z^2 - y^2 = 1 := by
        apply (mul_left_cancel₀ (ne_of_gt hD))
        nlinarith only [hxy]
      have ht : D*t^2 - s^2 = 1 := by
        apply (mul_left_cancel₀ (ne_of_gt hD))
        nlinarith only [hrs]
      refine ⟨D*z*t-y*s, y*t-z*s, ?_, ?_, ?_⟩
      · change (D*z*t-y*s)^2-D*(y*t-z*s)^2=1
        calc
          _ = (D*z^2-y^2)*(D*t^2-s^2) := by ring
          _ = 1 := by rw [hz, ht]; norm_num
      · change D*z = (D*t)*(D*z*t-y*s)+D*s*(y*t-z*s)
        nlinarith only [congrArg (fun q : ℤ => D*z*q) ht]
      · nlinarith only [congrArg (fun q : ℤ => y*q) ht]
    constructor
    · rintro ⟨x,y,r,s,hxy,hrs,hne⟩
      by_cases hx : D ∣ x
      · exact ⟨r,s,hrs,fun hr => hne (hdiv_class x y r s hxy hrs hx hr)⟩
      · exact ⟨x,y,hxy,hx⟩
    · rintro ⟨x,y,hxy,hx⟩
      refine ⟨x,y,D,K,hxy,hbase,?_⟩
      rintro ⟨u,v,hu,hxv,hyv⟩
      apply hx
      refine ⟨u+K*v, ?_⟩
      change x = D*u+D*K*v at hxv
      nlinarith only [hxv]
  have hnorm : ∀ x y : ℤ, Sol k x y →
      Sol k (A*x-2*K*D*y) (A*y-2*K*x) := by
    intro x y hxy
    change x^2-D*y^2=D at hxy
    change (A*x-2*K*D*y)^2-D*(A*y-2*K*x)^2=D
    calc
      _ = (A^2-D*(2*K)^2)*(x^2-D*y^2) := by ring
      _ = D := by rw [hunit, hxy]; ring
  have hnorm_abs : ∀ x y : ℤ, Sol k x y → Sol k |x| |y| := by
    intro x y hxy
    simpa only [Sol, sq_abs] using hxy
  have hnd_step : ∀ x y : ℤ, ¬ D ∣ x → ¬ D ∣ |A*x-2*K*D*y| := by
    intro x y hx hd
    rw [dvd_abs] at hd
    obtain ⟨z,hz⟩ := hd
    apply hx
    refine ⟨2*x-2*K*y-z, ?_⟩
    dsimp [A,D] at hz ⊢
    linear_combination -hz
  have hsmall_div : ∀ x y : ℤ, Sol k x y → D ∣ x → K ≤ |y| := by
    intro x y hxy hd
    obtain ⟨z,rfl⟩ := hd
    change (D*z)^2-D*y^2=D at hxy
    have hz : D*z^2-y^2=1 := by
      apply mul_left_cancel₀ (ne_of_gt hD)
      nlinarith only [hxy]
    have hz0 : z ≠ 0 := by intro heq; rw [heq] at hz; nlinarith [sq_nonneg y]
    have hz1 : 1 ≤ z^2 := by have := sq_pos_of_ne_zero hz0; omega
    have hb : D ≤ D*z^2 := by nlinarith only [mul_nonneg hD.le (sub_nonneg.mpr hz1)]
    have hy2 : K^2 ≤ |y|^2 := by rw [sq_abs]; dsimp [D] at hb; nlinarith only [hb,hz]
    exact (sq_le_sq₀ hK.le (abs_nonneg y)).mp hy2
  have hdesc : ∀ x y : ℤ, 0 ≤ x → 0 ≤ y → Sol k x y → K < y →
      |A*y-2*K*x| < y := by
    intro x y hx hy hxy hky
    change x^2-D*y^2=D at hxy
    have hxky : K*y < x := by
      apply (sq_lt_sq₀ (mul_nonneg hK.le hy) hx).mp
      have heq : x^2-(K*y)^2=y^2+D := by
        dsimp [D] at hxy ⊢
        linear_combination hxy
      nlinarith only [heq,sq_nonneg y,hD]
    have hkx : K*x < D*y := by
      apply (sq_lt_sq₀ (mul_nonneg hK.le hx) (mul_nonneg hD.le hy)).mp
      have hyy : 0 < y^2-K^2 := by nlinarith only [hky,hK]
      have heq : (D*y)^2-(K*x)^2=D*(y^2-K^2) := by
        dsimp [D] at hxy ⊢
        linear_combination -K^2*hxy
      have := mul_pos hD hyy
      nlinarith only [heq,this]
    rw [abs_lt]
    constructor
    · dsimp [A,D] at hkx ⊢
      nlinarith only [hkx]
    · have := mul_pos hK (sub_pos.mpr hxky)
      dsimp [A]
      nlinarith only [this]
  have hinterval : ∀ x y : ℤ, 0 ≤ x → 0 ≤ y → Sol k x y →
      K < y → y < B → |A*y-2*K*x| < K := by
    intro x y hx hy hxy hky hyB
    change x^2-D*y^2=D at hxy
    have hlo : (2*K*x)^2 < (A*y+K)^2 := by
      have hp : 0 < (y-K)*(y+B) := mul_pos (sub_pos.mpr hky) (by omega)
      have heq : (A*y+K)^2-(2*K*x)^2=(y-K)*(y+B) := by
        dsimp [A,B,D] at hxy ⊢
        linear_combination -4*K^2*hxy
      nlinarith only [hp,heq]
    have hhi : (A*y-K)^2 < (2*K*x)^2 := by
      have hp : 0 < (B-y)*(y+K) := mul_pos (sub_pos.mpr hyB) (by omega)
      have heq : (2*K*x)^2-(A*y-K)^2=(B-y)*(y+K) := by
        dsimp [A,B,D] at hxy ⊢
        linear_combination 4*K^2*hxy
      nlinarith only [hp,heq]
    have hlo' : 2*K*x < A*y+K :=
      (sq_lt_sq₀ (by positivity) (by positivity)).mp hlo
    have hhi' : A*y-K < 2*K*x := by
      have hh := (sq_lt_sq).mp hhi
      rw [abs_of_nonneg (show 0 ≤ 2*K*x by positivity)] at hh
      exact lt_of_le_of_lt (le_abs_self _) hh
    rw [abs_lt]
    constructor <;> linarith only [hlo',hhi']
  have hex : ∃ n : ℕ, k < n ∧ IsSquare ((k^2+1)*(n^2+1)) := by
    refine ⟨4*k^3+3*k, ?_, (k^2+1)*(4*k^2+1), ?_⟩
    · nlinarith
    · ring
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  refine ⟨m, ⟨hm.1, hm.2, fun n hn hs => Nat.find_min' hex ⟨hn,hs⟩⟩, ?_⟩
  constructor
  · intro hmb
    obtain ⟨w,hw⟩ := hm.2
    have hsol : Sol k (w : ℤ) (m : ℤ) := by
      have hwz : ((k:ℤ)^2+1)*((m:ℤ)^2+1)=(w:ℤ)*(w:ℤ) := by
        exact_mod_cast hw
      dsimp [Sol, Discriminant]
      nlinarith only [hwz]
    have hky : K < (m:ℤ) := by dsimp [K]; exact_mod_cast hm.1
    have hmB : (m:ℤ) < B := by dsimp [B,K]; exact_mod_cast hmb
    refine hclasses.mpr ⟨w,m,hsol,?_⟩
    intro hd
    have hd' : D ∣ A*(w:ℤ)-2*K*D*(m:ℤ) := by
      obtain ⟨z,hz⟩ := hd
      refine ⟨A*z-2*K*(m:ℤ), ?_⟩
      rw [hz]
      ring
    have hlow := hsmall_div _ _ (hnorm _ _ hsol) hd'
    have hupp := hinterval _ _ (by positivity) (by positivity) hsol hky hmB
    omega
  · intro hc
    obtain ⟨x,y,hxy,hnd⟩ := hclasses.mp hc
    have hne : ∃ n : ℕ, ∃ t : ℤ, 0 ≤ t ∧ Sol k t n ∧ ¬ D ∣ t := by
      refine ⟨y.natAbs, |x|, abs_nonneg _, ?_, ?_⟩
      · simpa only [Int.natCast_natAbs] using hnorm_abs x y hxy
      · simpa only [dvd_abs] using hnd
    let s : ℕ := Nat.find hne
    obtain ⟨r,hr,hrs,hrnd⟩ := Nat.find_spec hne
    have hsK : (s:ℤ) ≤ K := by
      by_contra hh
      have hlt := hdesc r s hr (by positivity) hrs (by omega)
      have hnext := hnorm_abs _ _ (hnorm r s hrs)
      have hmin : s ≤ (A*(s:ℤ)-2*K*r).natAbs := by
        apply Nat.find_min' hne
        refine ⟨|A*r-2*K*D*(s:ℤ)|, abs_nonneg _, ?_, hnd_step r s hrnd⟩
        simpa only [Int.natCast_natAbs] using hnext
      have hminz : (s:ℤ) ≤ |A*(s:ℤ)-2*K*r| := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hmin
      omega
    change r^2-D*(s:ℤ)^2=D at hrs
    have hrK : K < r := by
      apply (sq_lt_sq₀ hK.le hr).mp
      have hp := mul_nonneg hD.le (sq_nonneg (s:ℤ))
      have hDK : D = K^2+1 := rfl
      nlinarith only [hrs,hp,hDK]
    have hrD : r < D := by
      have hss : (s:ℤ)^2 ≤ K^2 :=
        (sq_le_sq₀ (by positivity) hK.le).mpr hsK
      have hp := mul_nonneg hD.le (sub_nonneg.mpr hss)
      have hle : r ≤ D := by
        apply (sq_le_sq₀ hr hD.le).mp
        dsimp [D] at hrs hp ⊢
        nlinarith only [hrs,hp]
      have hne : r ≠ D := by
        intro heq
        apply hrnd
        rw [heq]
      omega
    let t : ℤ := 2*K*r+A*(s:ℤ)
    let q : ℤ := A*r+2*K*D*(s:ℤ)
    have htK : K < t := by
      have hr1 : 1 ≤ r := by omega
      have hp := mul_nonneg hK.le (sub_nonneg.mpr hr1)
      have hAs := mul_nonneg hA.le (show 0 ≤ (s:ℤ) by positivity)
      dsimp [t]
      nlinarith only [hp,hAs,hK]
    have htB : t < B := by
      have hxmul := mul_lt_mul_of_pos_left hrD (show 0 < 2*K by omega)
      have hymul := mul_le_mul_of_nonneg_left hsK hA.le
      have heq : 2*K*D+A*K=B := by dsimp [A,B,D]; ring
      dsimp [t]
      nlinarith only [hxmul,hymul,heq]
    have hqt : q^2-D*t^2=D := by
      calc
        _ = (A^2-D*(2*K)^2)*(r^2-D*(s:ℤ)^2) := by dsimp [q,t]; ring
        _ = D := by rw [hunit,hrs]; ring
    have htn : (t.toNat : ℤ) = t := Int.toNat_of_nonneg (by omega)
    have hkn : k < t.toNat := by
      have hh : (k:ℤ) < (t.toNat:ℤ) := by
        change K < _
        rw [htn]
        exact htK
      exact_mod_cast hh
    have hnB : t.toNat < 4*k^3+3*k := by
      have hh : (t.toNat:ℤ) < 4*(k:ℤ)^3+3*(k:ℤ) := by
        rw [htn]
        exact htB
      exact_mod_cast hh
    have hsq : IsSquare ((k^2+1)*(t.toNat^2+1)) := by
      refine ⟨q.natAbs, ?_⟩
      have hh : (((k^2+1)*(t.toNat^2+1):ℕ):ℤ) = ((q.natAbs*q.natAbs:ℕ):ℤ) := by
        push_cast
        rw [htn]
        change D*(t^2+1) = |q| * |q|
        nlinarith only [hqt,sq_abs q]
      exact_mod_cast hh
    exact lt_of_le_of_lt (Nat.find_min' hex ⟨hkn,hsq⟩) hnB


end D5.S3.ArithUnits.PellClassSuccessor
