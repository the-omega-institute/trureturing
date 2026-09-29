/- GID: D5/S3/Arith/Congruence/PrimePowerAffineBehavior
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/PrimePowerAffineBehavior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Tagged coordinates classify positive affine depth responses modulo a prime power. -/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.PrimePowerAffineBehavior

/-- Saturated prime depth, with the zero residue assigned the full depth. -/
def depth (p h : ℕ) (x : ℤ) : ℕ := Nat.log p (Int.gcd x ((p : ℤ) ^ h))

/-- Disjoint low `S(r,u)` and high `D(z)` coordinates. Unit membership of the
low residue is established by the classification theorem, including modulus one. -/
def eta (p h e : ℕ) (x : ℤ) : (ℕ × ZMod (p ^ (h - e))) ⊕ ZMod (p ^ (h - e)) :=
  if depth p h x < e then
    Sum.inl (depth p h x, ((x / (p : ℤ) ^ depth p h x : ℤ) : ZMod (p ^ (h - e))))
  else Sum.inr ((x / (p : ℤ) ^ e : ℤ) : ZMod (p ^ (h - e)))

/-- A finite continuation consists of positive scalar multiplications and forward
translations by one copy of the allowed prime power. -/
def run (p e : ℕ) : List (ℕ+ ⊕ Unit) → ℤ → ℤ
  | [], x => x
  | Sum.inl a :: w, x => run p e w ((a : ℕ) * x)
  | Sum.inr _ :: w, x => run p e w (x + (p : ℤ) ^ e)

/-- The complete local classifier, including representative independence, the
valuation convention, unit coordinates, positive lifts, and finite continuations. -/
theorem local_classification (p h e : ℕ) (hp : p.Prime) (he : e ≤ h) :
    (∀ x : ℤ, depth p h x ≤ h ∧
      Int.gcd x ((p : ℤ) ^ h) = p ^ depth p h x ∧
      (depth p h x = h ↔ (p : ℤ) ^ h ∣ x) ∧
      (x ≠ 0 → depth p h x = min (padicValInt p x) h) ∧
      (depth p h x < e → IsUnit ((x / (p : ℤ) ^ depth p h x : ℤ) :
        ZMod (p ^ (h - e))))) ∧
    (∀ x y : ℤ, Int.ModEq ((p : ℤ) ^ h) x y →
      depth p h x = depth p h y ∧ eta p h e x = eta p h e y) ∧
    (∀ x : ℤ, ∃ X : ℤ, 0 < X ∧ Int.ModEq ((p : ℤ) ^ h) x X) ∧
    (∀ a b : ℤ, ∃ A B : ℤ, 0 < A ∧ 0 ≤ B ∧
      ∀ x : ℤ, Int.ModEq ((p : ℤ) ^ h)
        (a * x + (p : ℤ) ^ e * b) (A * x + (p : ℤ) ^ e * B)) ∧
    (∀ w : List (ℕ+ ⊕ Unit), ∃ A B : ℕ, 0 < A ∧
      ∀ x : ℤ, run p e w x = A * x + (p : ℤ) ^ e * B) ∧
    (∀ A B : ℕ, 0 < A → ∃ w : List (ℕ+ ⊕ Unit),
      ∀ x : ℤ, run p e w x = A * x + (p : ℤ) ^ e * B) ∧
    (∀ x y : ℤ, (eta p h e x = eta p h e y ↔
      ∀ a b : ℤ, 0 < a → 0 ≤ b →
        depth p h (a * x + (p : ℤ) ^ e * b) =
        depth p h (a * y + (p : ℤ) ^ e * b)) ∧
      (eta p h e x = eta p h e y ↔
        ∀ w : List (ℕ+ ⊕ Unit), depth p h (run p e w x) = depth p h (run p e w y))) ∧
    (e = h → ∀ u v : (ZMod (p ^ (h - e)))ˣ, u = v) := by
  classical
  have hp0 : 0 < p := hp.pos
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp0
  have hpow (j : ℕ) : (0 : ℤ) < (p : ℤ) ^ j := pow_pos hpz j
  have hdepth (x : ℤ) : depth p h x ≤ h ∧
      Int.gcd x ((p : ℤ) ^ h) = p ^ depth p h x := by
    have hd : Int.gcd x ((p : ℤ) ^ h) ∣ p ^ h := by
      have := Int.gcd_dvd_right x ((p : ℤ) ^ h)
      exact_mod_cast this
    obtain ⟨j, hj, hg⟩ := (Nat.dvd_prime_pow hp).mp hd
    have hr : depth p h x = j := by simp [depth, hg, Nat.log_pow hp.one_lt]
    exact ⟨hr ▸ hj, hr ▸ hg⟩
  have hdiv (x : ℤ) (j : ℕ) :
      (p : ℤ) ^ j ∣ x ∧ j ≤ h ↔ j ≤ depth p h x := by
    constructor
    · rintro ⟨hx, hj⟩
      have hD : (p : ℤ) ^ j ∣ (Int.gcd x ((p : ℤ) ^ h) : ℤ) :=
        Int.dvd_coe_gcd hx (pow_dvd_pow _ hj)
      rw [(hdepth x).2] at hD
      have : p ^ j ∣ p ^ depth p h x := by exact_mod_cast hD
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp this
    · intro hj
      constructor
      · apply dvd_trans (pow_dvd_pow (p : ℤ) hj)
        have := Int.gcd_dvd_left x ((p : ℤ) ^ h)
        simpa [(hdepth x).2] using this
      · exact hj.trans (hdepth x).1
  have hval (x : ℤ) (hx : x ≠ 0) :
      depth p h x = min (padicValInt p x) h := by
    apply Nat.le_antisymm
    · refine le_min ?_ (hdepth x).1
      exact ((padicValInt_dvd_iff_of_ne_one hp.ne_one _ x).mp
        ((hdiv x _).mpr le_rfl).1).resolve_left hx
    · apply (hdiv x _).mp
      exact ⟨(padicValInt_dvd_iff_of_ne_one hp.ne_one _ x).mpr
        (Or.inr (min_le_left _ _)), min_le_right _ _⟩
  have hsat (x : ℤ) : depth p h x = h ↔ (p : ℤ) ^ h ∣ x := by
    constructor
    · intro hx
      exact ((hdiv x h).mpr (by omega)).1
    · intro hx
      exact Nat.le_antisymm (hdepth x).1 ((hdiv x h).mp ⟨hx, le_rfl⟩)
  have hgcong {x y : ℤ} (hc : Int.ModEq ((p : ℤ) ^ h) x y) :
      Int.gcd x ((p : ℤ) ^ h) = Int.gcd y ((p : ℤ) ^ h) := by
    rw [← Int.gcd_emod x, ← Int.gcd_emod y, hc]
  have hdcong {x y : ℤ} (hc : Int.ModEq ((p : ℤ) ^ h) x y) :
      depth p h x = depth p h y := congrArg (Nat.log p) (hgcong hc)
  have low_sufficiency : ∀ (r : ℕ), r < e → ∀ (x y : ℤ),
      Int.gcd x ((p : ℤ) ^ h) = p ^ r →
      Int.gcd y ((p : ℤ) ^ h) = p ^ r →
      Int.ModEq ((p : ℤ) ^ (h - e + r)) x y →
      ∀ a b : ℤ,
        Int.gcd (a * x + (p : ℤ) ^ e * b) ((p : ℤ) ^ h) =
        Int.gcd (a * y + (p : ℤ) ^ e * b) ((p : ℤ) ^ h) := by
    intro r hr x y hx hy hxy
    have hph : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpr : (p : ℤ) ^ r ≠ 0 := pow_ne_zero _ hph
    have hN : (p : ℤ) ^ h = (p : ℤ) ^ (h - r) * (p : ℤ) ^ r := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : r ≤ h)]
    have hD : (p : ℤ) ^ h = (p : ℤ) ^ e * (p : ℤ) ^ (h - e) := by
      rw [← pow_add, Nat.add_sub_of_le he]
    obtain ⟨u, q, huq, hxu, hNq⟩ :=
      Int.exists_gcd_one (show 0 < Int.gcd x ((p : ℤ) ^ h) by
        rw [hx]
        exact pow_pos hp.pos _)
    have hq : q = (p : ℤ) ^ (h - r) := by
      apply mul_right_cancel₀ hpr
      calc
        q * (p : ℤ) ^ r = (p : ℤ) ^ h := by
          simpa only [hx, Nat.cast_pow] using hNq.symm
        _ = (p : ℤ) ^ (h - r) * (p : ℤ) ^ r := hN
    have hu : Int.gcd u ((p : ℤ) ^ (h - r)) = 1 := by
      simpa only [hq] using huq
    have hxform : x = u * (p : ℤ) ^ r := by
      simpa only [hx, Nat.cast_pow] using hxu
    obtain ⟨v, q', hvq, hyv, hNq'⟩ :=
      Int.exists_gcd_one (show 0 < Int.gcd y ((p : ℤ) ^ h) by
        rw [hy]
        exact pow_pos hp.pos _)
    have hq' : q' = (p : ℤ) ^ (h - r) := by
      apply mul_right_cancel₀ hpr
      calc
        q' * (p : ℤ) ^ r = (p : ℤ) ^ h := by
          simpa only [hy, Nat.cast_pow] using hNq'.symm
        _ = (p : ℤ) ^ (h - r) * (p : ℤ) ^ r := hN
    have hv : Int.gcd v ((p : ℤ) ^ (h - r)) = 1 := by
      simpa only [hq'] using hvq
    have hyform : y = v * (p : ℤ) ^ r := by
      simpa only [hy, Nat.cast_pow] using hyv
    have huv : Int.ModEq ((p : ℤ) ^ (h - e)) u v := by
      apply Int.ModEq.mul_right_cancel' hpr
      simpa only [pow_add, hxform, hyform] using hxy
    let s : ℤ := Int.gcdA u ((p : ℤ) ^ (h - r))
    let t : ℤ := v * s
    have hu_inv : Int.ModEq ((p : ℤ) ^ (h - r)) (u * s) 1 := by
      apply Int.modEq_iff_dvd.mpr
      refine ⟨Int.gcdB u ((p : ℤ) ^ (h - r)), ?_⟩
      have hb := Int.gcd_eq_gcd_ab u ((p : ℤ) ^ (h - r))
      rw [hu, Nat.cast_one] at hb
      dsimp [s]
      linarith [hb]
    have htW : IsCoprime t ((p : ℤ) ^ (h - r)) :=
      (Int.isCoprime_iff_gcd_eq_one.mpr hv).mul_left
        (Int.isCoprime_gcdA (Int.isCoprime_iff_gcd_eq_one.mpr hu))
    have htP : IsCoprime t (p : ℤ) :=
      (IsCoprime.pow_right_iff (by omega : 0 < h - r)).mp htW
    have htN : IsCoprime t ((p : ℤ) ^ h) := htP.pow_right
    have htx : Int.ModEq ((p : ℤ) ^ h) (t * x) y := by
      have hu_t : Int.ModEq ((p : ℤ) ^ (h - r)) (t * u) v := by
        simpa only [t, mul_one, mul_assoc, mul_comm, mul_left_comm] using
          hu_inv.mul_left v
      have hscaled := hu_t.mul_right' (c := (p : ℤ) ^ r)
      rw [← hN] at hscaled
      simpa only [hxform, hyform, mul_assoc] using hscaled
    have ht1 : Int.ModEq ((p : ℤ) ^ (h - e)) t 1 := by
      have hi : Int.ModEq ((p : ℤ) ^ (h - e)) (u * s) 1 :=
        hu_inv.of_dvd (pow_dvd_pow (p : ℤ) (by omega : h - e ≤ h - r))
      exact (huv.mul_right s).symm.trans hi
    have htn : Nat.Coprime t.natAbs (((p : ℤ) ^ h).natAbs) := by
      change Int.gcd t ((p : ℤ) ^ h) = 1
      exact Int.isCoprime_iff_gcd_eq_one.mp htN
    have hgcd : ∀ z : ℤ,
        Int.gcd (t * z) ((p : ℤ) ^ h) = Int.gcd z ((p : ℤ) ^ h) := by
      intro z
      simpa only [Int.gcd_def, Int.natAbs_mul] using
        htn.gcd_mul_left_cancel z.natAbs
    intro a b
    have htranslation : Int.ModEq ((p : ℤ) ^ h)
        (t * ((p : ℤ) ^ e * b)) ((p : ℤ) ^ e * b) := by
      have hm := ht1.mul_left' (c := (p : ℤ) ^ e)
      rw [← hD] at hm
      simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using hm.mul_right b
    have hresponse : Int.ModEq ((p : ℤ) ^ h)
        (t * (a * x + (p : ℤ) ^ e * b)) (a * y + (p : ℤ) ^ e * b) := by
      simpa only [mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using
        (htx.mul_left a).add htranslation
    calc
      Int.gcd (a * x + (p : ℤ) ^ e * b) ((p : ℤ) ^ h) =
          Int.gcd (t * (a * x + (p : ℤ) ^ e * b)) ((p : ℤ) ^ h) :=
        (hgcd _).symm
      _ = Int.gcd (a * y + (p : ℤ) ^ e * b) ((p : ℤ) ^ h) := by
        calc
          _ = Int.gcd ((t * (a * x + (p : ℤ) ^ e * b)) % ((p : ℤ) ^ h))
              ((p : ℤ) ^ h) := (Int.gcd_emod _ _).symm
          _ = Int.gcd ((a * y + (p : ℤ) ^ e * b) % ((p : ℤ) ^ h))
              ((p : ℤ) ^ h) := congrArg (fun z => Int.gcd z ((p : ℤ) ^ h)) hresponse.eq
          _ = _ := Int.gcd_emod _ _
  have hform (x : ℤ) (j : ℕ) (hj : j ≤ depth p h x) :
      x = (x / (p : ℤ) ^ j) * (p : ℤ) ^ j :=
    (Int.ediv_mul_cancel ((hdiv x j).mpr hj).1).symm
  have hunit (x : ℤ) (hx : depth p h x < e) :
      IsUnit ((x / (p : ℤ) ^ depth p h x : ℤ) : ZMod (p ^ (h - e))) := by
    have hnorm := Int.gcd_ediv_gcd_ediv_gcd (show 0 < Int.gcd x ((p : ℤ) ^ h) by
      rw [(hdepth x).2]; exact pow_pos hp.pos _)
    have hN : (p : ℤ) ^ h = (p : ℤ) ^ (h - depth p h x) *
        (p : ℤ) ^ depth p h x := by
      rw [← pow_add, Nat.sub_add_cancel (hdepth x).1]
    rw [(hdepth x).2, Nat.cast_pow, hN, Int.mul_ediv_cancel _ (ne_of_gt (hpow _))] at hnorm
    have hc : IsCoprime (x / (p : ℤ) ^ depth p h x) ((p : ℤ) ^ (h - e)) :=
      (Int.isCoprime_iff_gcd_eq_one.mpr hnorm).of_isCoprime_of_dvd_right
        (pow_dvd_pow _ (by omega : h - e ≤ h - depth p h x))
    have hz := hc.intCast (R := ZMod (p ^ (h - e)))
    have hzero : (((p : ℤ) ^ (h - e) : ℤ) : ZMod (p ^ (h - e))) = 0 := by
      rw [← Nat.cast_pow, Int.cast_natCast, ZMod.natCast_self]
    rw [hzero, isCoprime_zero_right] at hz
    exact hz
  have hsigned (x y : ℤ) : eta p h e x = eta p h e y ↔
      ∀ a b : ℤ, Int.gcd (a * x + (p : ℤ) ^ e * b) ((p : ℤ) ^ h) =
        Int.gcd (a * y + (p : ℤ) ^ e * b) ((p : ℤ) ^ h) := by
    constructor
    · intro hη
      by_cases hx : depth p h x < e <;> by_cases hy : depth p h y < e
      · simp only [eta, if_pos hx, if_pos hy, Sum.inl.injEq, Prod.mk.injEq] at hη
        have hc : Int.ModEq ((p : ℤ) ^ (h - e))
            (x / (p : ℤ) ^ depth p h x) (y / (p : ℤ) ^ depth p h x) := by
          simpa only [hη.1, Nat.cast_pow] using
            (ZMod.intCast_eq_intCast_iff _ _ _).mp hη.2
        have hc' := hc.mul_right' (c := (p : ℤ) ^ depth p h x)
        have hxform := hform x (depth p h x) le_rfl
        have hyform := hform y (depth p h x) (by omega)
        rw [← pow_add, ← hxform, ← hyform] at hc'
        exact low_sufficiency _ hx x y (hdepth x).2 (hη.1 ▸ (hdepth y).2) hc'
      · simp [eta, hx, hy] at hη
      · simp [eta, hx, hy] at hη
      · simp only [eta, if_neg hx, if_neg hy, Sum.inr.injEq] at hη
        have hc : Int.ModEq ((p : ℤ) ^ (h - e))
            (x / (p : ℤ) ^ e) (y / (p : ℤ) ^ e) := by
          simpa only [Nat.cast_pow] using (ZMod.intCast_eq_intCast_iff _ _ _).mp hη
        have hc' := hc.mul_right' (c := (p : ℤ) ^ e)
        rw [← pow_add, Nat.sub_add_cancel he,
          ← hform x e (by omega), ← hform y e (by omega)] at hc'
        intro a b
        exact hgcong ((hc'.mul_left a).add_right _)
    · intro hb
      have hg : Int.gcd x ((p : ℤ) ^ h) = Int.gcd y ((p : ℤ) ^ h) := by
        simpa using hb 1 0
      have hr : depth p h x = depth p h y := congrArg (Nat.log p) hg
      let q := min (depth p h x) e
      have hqx : q ≤ depth p h x := min_le_left _ _
      have hqy : q ≤ depth p h y := by omega
      have hqe : q ≤ e := min_le_right _ _
      have hD : (p : ℤ) ^ e = (p : ℤ) ^ (e - q) * (p : ℤ) ^ q := by
        rw [← pow_add, Nat.sub_add_cancel hqe]
      have hxzero : (p : ℤ) ^ (e - q) * x +
          (p : ℤ) ^ e * -(x / (p : ℤ) ^ q) = 0 := by
        calc
          _ = (p : ℤ) ^ (e - q) * ((x / (p : ℤ) ^ q) * (p : ℤ) ^ q) +
            ((p : ℤ) ^ (e - q) * (p : ℤ) ^ q) * -(x / (p : ℤ) ^ q) := by
              rw [← hform x q hqx, ← hD]
          _ = 0 := by ring
      have hyresp : (p : ℤ) ^ (e - q) * y +
          (p : ℤ) ^ e * -(x / (p : ℤ) ^ q) =
          (p : ℤ) ^ e * (y / (p : ℤ) ^ q - x / (p : ℤ) ^ q) := by
        calc
          _ = (p : ℤ) ^ (e - q) * ((y / (p : ℤ) ^ q) * (p : ℤ) ^ q) +
            ((p : ℤ) ^ (e - q) * (p : ℤ) ^ q) * -(x / (p : ℤ) ^ q) := by
              rw [← hform y q hqy, ← hD]
          _ = _ := by rw [hD]; ring
      have htest := hb ((p : ℤ) ^ (e - q)) (-(x / (p : ℤ) ^ q))
      rw [hxzero, hyresp, Int.zero_gcd] at htest
      have hdvd : (p : ℤ) ^ h ∣
          (p : ℤ) ^ e * (y / (p : ℤ) ^ q - x / (p : ℤ) ^ q) :=
        Int.gcd_eq_natAbs_right_iff_dvd.mp htest.symm
      have hN : (p : ℤ) ^ h = (p : ℤ) ^ e * (p : ℤ) ^ (h - e) := by
        rw [← pow_add, Nat.add_sub_of_le he]
      rw [hN] at hdvd
      have hdvd' := (mul_dvd_mul_iff_left (ne_of_gt (hpow e))).mp hdvd
      have hc : ((x / (p : ℤ) ^ q : ℤ) : ZMod (p ^ (h - e))) =
          ((y / (p : ℤ) ^ q : ℤ) : ZMod (p ^ (h - e))) := by
        apply (ZMod.intCast_eq_intCast_iff _ _ _).mpr
        apply Int.modEq_iff_dvd.mpr
        simpa only [Nat.cast_pow] using hdvd'
      by_cases hx : depth p h x < e
      · have hy : depth p h y < e := by omega
        have hq : q = depth p h x := min_eq_left (by omega)
        simp only [eta, if_pos hx, if_pos hy, Sum.inl.injEq, Prod.mk.injEq]
        exact ⟨hr, by simpa only [hq, hr] using hc⟩
      · have hy : ¬depth p h y < e := by omega
        have hq : q = e := min_eq_right (by omega)
        simpa only [eta, if_neg hx, if_neg hy, Sum.inr.injEq, hq] using hc
  have hlift (x : ℤ) : ∃ X : ℤ, 0 < X ∧ Int.ModEq ((p : ℤ) ^ h) x X := by
    refine ⟨x % (p : ℤ) ^ h + (p : ℤ) ^ h, ?_, ?_⟩
    · exact add_pos_of_nonneg_of_pos (Int.emod_nonneg _ (ne_of_gt (hpow h))) (hpow h)
    · change x % (p : ℤ) ^ h = (x % (p : ℤ) ^ h + (p : ℤ) ^ h) % (p : ℤ) ^ h
      simp
  have hablift (a b : ℤ) : ∃ A B : ℤ, 0 < A ∧ 0 ≤ B ∧
      ∀ x : ℤ, Int.ModEq ((p : ℤ) ^ h)
        (a * x + (p : ℤ) ^ e * b) (A * x + (p : ℤ) ^ e * B) := by
    obtain ⟨A, hA, ha⟩ := hlift a
    refine ⟨A, b % (p : ℤ) ^ (h - e), hA,
      Int.emod_nonneg _ (ne_of_gt (hpow _)), ?_⟩
    have hb : Int.ModEq ((p : ℤ) ^ (h - e)) b (b % (p : ℤ) ^ (h - e)) := by
      change _ = _; simp
    have hb' := hb.mul_left' (c := (p : ℤ) ^ e)
    rw [← pow_add, Nat.add_sub_of_le he] at hb'
    intro x
    exact (ha.mul_right x).add hb'
  have hwords (w : List (ℕ+ ⊕ Unit)) : ∃ A B : ℕ, 0 < A ∧
      ∀ x : ℤ, run p e w x = A * x + (p : ℤ) ^ e * B := by
    induction w with
    | nil => exact ⟨1, 0, by omega, by intro x; simp [run]⟩
    | cons op w ih =>
      obtain ⟨A, B, hA, hw⟩ := ih
      cases op with
      | inl a =>
        refine ⟨A * (a : ℕ), B, Nat.mul_pos hA a.pos, ?_⟩
        intro x
        simp only [run, hw, Nat.cast_mul]
        ring
      | inr u =>
        refine ⟨A, A + B, hA, ?_⟩
        intro x
        simp only [run, hw, Nat.cast_add]
        ring
  have hrealize (A B : ℕ) (hA : 0 < A) : ∃ w : List (ℕ+ ⊕ Unit),
      ∀ x : ℤ, run p e w x = A * x + (p : ℤ) ^ e * B := by
    have htrans (b : ℕ) (x : ℤ) :
        run p e (List.replicate b (Sum.inr ())) x = x + (p : ℤ) ^ e * b := by
      induction b generalizing x with
      | zero => simp [run]
      | succ b ih => simp [List.replicate_succ, run, ih, Nat.cast_add]; ring
    refine ⟨Sum.inl ⟨A, hA⟩ :: List.replicate B (Sum.inr ()), ?_⟩
    intro x
    exact htrans B ((A : ℤ) * x)
  have hpositive (x y : ℤ) : eta p h e x = eta p h e y ↔
      ∀ a b : ℤ, 0 < a → 0 ≤ b →
        depth p h (a * x + (p : ℤ) ^ e * b) =
          depth p h (a * y + (p : ℤ) ^ e * b) := by
    constructor
    · intro hη a b _ _
      exact congrArg (Nat.log p) ((hsigned x y).mp hη a b)
    · intro hr
      apply (hsigned x y).mpr
      intro a b
      obtain ⟨A, B, hA, hB, hc⟩ := hablift a b
      have hh := (hdcong (hc x)).trans ((hr A B hA hB).trans (hdcong (hc y)).symm)
      rw [(hdepth _).2, (hdepth _).2, hh]
  refine ⟨fun x => ⟨(hdepth x).1, (hdepth x).2, hsat x, hval x, hunit x⟩,
    ?_, hlift, hablift, hwords, hrealize, ?_, ?_⟩
  · intro x y hc
    refine ⟨hdcong hc, (hsigned x y).mpr ?_⟩
    intro a b
    exact hgcong ((hc.mul_left a).add_right _)
  · intro x y
    refine ⟨hpositive x y, ?_⟩
    constructor
    · intro hη w
      obtain ⟨A, B, hA, hw⟩ := hwords w
      rw [hw, hw]
      exact (hpositive x y).mp hη A B (by exact_mod_cast hA) (by positivity)
    · intro hw
      apply (hpositive x y).mpr
      intro a b ha hb
      obtain ⟨w, hwr⟩ := hrealize a.toNat b.toNat (by omega)
      simpa only [hwr, Int.toNat_of_nonneg (le_of_lt ha), Int.toNat_of_nonneg hb] using hw w
  · intro heh u v
    subst e
    have hmod : p ^ (h - h) = 1 := by simp
    revert u v
    rw [hmod]
    exact fun u v => Subsingleton.elim u v

end D5.S3.Arith.Congruence.PrimePowerAffineBehavior
