/- GID: D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Each phase of the cubic Lucas tail fills an entire higher-power residue fibre, and the fibres are disjoint. -/

import D5.S3.Arith.Primes.GoldenCubicBlockTailPeriodClosed
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace WSSFinitePhase

/-- A phase whose first `n` samples are distinct at precision `M*n`
fills exactly the upper-precision residues above its value modulo `M`. -/
private theorem completePhase (M : Int) (hM : 0 < M) (n : Nat) (hn : 0 < n)
    (f : Nat → Int) (c : Int)
    (hphase : ∀ x, f x % M = c % M)
    (hinj : ∀ x y, x < n → y < n →
      f x % (M * (n:Int)) = f y % (M * (n:Int)) → x = y) (z : Int) :
    (∃ x < n, f x % (M * (n:Int)) = z % (M * (n:Int))) ↔ z % M = c % M := by
  have hn' : 0 < (n : Int) := by omega
  have hM' : M ≠ 0 := by omega
  have he {x : Int} (hx : x % M = c % M) : x = c + M * ((x-c)/M) := by
    have hd : M ∣ x-c := Int.dvd_iff_emod_eq_zero.mpr
      (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hx)
    have h := Int.mul_ediv_cancel_of_dvd hd
    omega
  have hequiv {x y : Int} (hx : x % M = c % M) (hy : y % M = c % M) :
      x % (M * (n:Int)) = y % (M * (n:Int)) ↔
      ((x-c)/M) % (n:Int) = ((y-c)/M) % (n:Int) := by
    have hleft := congrArg (· % (M * (n:Int))) (he hx)
    have hright := congrArg (· % (M * (n:Int))) (he hy)
    calc
      _ ↔ (c + M * ((x-c)/M)) % (M * (n:Int)) =
          (c + M * ((y-c)/M)) % (M * (n:Int)) :=
        ⟨fun h => hleft.symm.trans (h.trans hright), fun h => hleft.trans (h.trans hright.symm)⟩
      _ ↔ _ := by
        rw [Int.emod_add_cancel_left]
        simp only [Int.mul_emod_mul_of_pos _ _ hM]
        exact ⟨Int.eq_of_mul_eq_mul_left hM', congrArg (M * ·)⟩
  constructor
  · intro ⟨x, _, H⟩
    have hd : M ∣ z - f x :=
      Int.dvd_trans (show M ∣ M * (n:Int) from ⟨n,rfl⟩) (Int.dvd_iff_emod_eq_zero.mpr
        (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp H.symm))
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      (Int.dvd_iff_emod_eq_zero.mp hd)).trans (hphase x)
  · intro hz
    let mk (u : Int) : Fin n :=
      ⟨(u % (n:Int)).toNat, by
        have h0 := Int.emod_nonneg u (by omega : (n:Int) ≠ 0)
        have hlt := Int.emod_lt_of_pos u hn'
        omega⟩
    have hmk {u v : Int} (h : mk u = mk v) : u % (n:Int) = v % (n:Int) := by
      have h0 := Int.emod_nonneg u (by omega : (n:Int) ≠ 0)
      have h1 := Int.emod_nonneg v (by omega : (n:Int) ≠ 0)
      have hh := congrArg Fin.val h
      change (u % (n:Int)).toNat = (v % (n:Int)).toNat at hh
      omega
    let g (x : Fin n) := mk ((f x-c)/M)
    have hg {x y} (h : g x = g y) : x = y :=
      Fin.ext (hinj x y x.isLt y.isLt ((hequiv (hphase x) (hphase y)).mpr (hmk h)))
    obtain ⟨x, hx⟩ := Finite.surjective_of_injective (f := g) (fun _ _ h => hg h) (mk ((z-c)/M))
    exact ⟨x, x.isLt, (hequiv (hphase x) hz).mpr (hmk hx)⟩


/-- When the coarse and fine clocks have periods `t` and `t*d`,
each phase of the coarse clock hits its entire residue class at the finer precision. -/
theorem completeClockPhase (M : Int) (hM : 0 < M) (t d : Nat) (ht : 0 < t) (hd : 0 < d)
    (f : Nat → Int)
    (hcoarse : ∀ n m, m < n → (f n % M = f m % M ↔ t ∣ n-m))
    (hfine : ∀ n m, m < n →
      (f n % (M * (d:Int)) = f m % (M * (d:Int)) ↔ t*d ∣ n-m))
    (r : Nat) (z : Int) :
    (∃ x < d, f (r+t*x) % (M * (d:Int)) = z % (M * (d:Int))) ↔ z % M = f r % M := by
  apply completePhase M hM d hd (fun x => f (r+t*x)) (f r) _ _ z
  · intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hx' := Nat.mul_pos ht (Nat.pos_of_ne_zero hx)
      apply (hcoarse _ _ (by omega)).mpr
      have he : r + t*x - r = t*x := by omega
      rw [he]
      exact ⟨x, rfl⟩
  · intro x y hx hy he
    have stronger (a b : Nat) (ha : a < d) (hab : b < a)
        (he' : f (r+t*a) % (M * (d:Int)) = f (r+t*b) % (M * (d:Int))) : False := by
      have hmul := Nat.mul_lt_mul_of_pos_left hab ht
      have hh := (hfine (r+t*a) (r+t*b) (by omega)).mp he'
      rw [Nat.add_sub_add_left, ← Nat.mul_sub_left_distrib] at hh
      have h := Nat.dvd_of_mul_dvd_mul_left ht hh
      have hb := Nat.le_of_dvd (by omega : 0 < a-b) h
      omega
    by_cases hab : x < y
    · exact (stronger y x hy hab he.symm).elim
    · by_cases hba : y < x
      · exact (stronger x y hx hba he).elim
      · omega

/-- The complete fine orbit is the disjoint union of the `t` full fibres
above the first `t` coarse samples. -/
theorem completeClockImage (M : Int) (hM : 0 < M) (t d : Nat) (ht : 0 < t) (hd : 0 < d)
    (f : Nat → Int)
    (hcoarse : ∀ n m, m < n → (f n % M = f m % M ↔ t ∣ n-m))
    (hfine : ∀ n m, m < n →
      (f n % (M * (d:Int)) = f m % (M * (d:Int)) ↔ t*d ∣ n-m)) (z : Int) :
    (∃ x, f x % (M * (d:Int)) = z % (M * (d:Int))) ↔
      ∃ r < t, z % M = f r % M := by
  constructor
  · intro ⟨x, hx⟩
    have hdiv := Nat.div_add_mod x t
    have hmod := Nat.mod_lt x ht
    have hred : f x % M = f (x%t) % M := by
      by_cases heq : x = x%t
      · rw [← heq]
      · have hlt : x%t < x := by omega
        apply (hcoarse _ _ hlt).mpr
        refine ⟨x/t, ?_⟩
        omega
    have hdvd : M ∣ z - f x :=
      Int.dvd_trans (show M ∣ M * (d:Int) from ⟨d,rfl⟩)
        (Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hx.symm))
    exact ⟨x%t,hmod,(Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      (Int.dvd_iff_emod_eq_zero.mp hdvd)).trans hred⟩
  · intro ⟨r, _, hr⟩
    obtain ⟨x, _, hx⟩ := (completeClockPhase M hM t d ht hd f hcoarse hfine r z).mpr hr
    exact ⟨r+t*x, hx⟩

/-- Different phases below one coarse period are disjoint. -/
theorem completeClockPhasesDisjoint (M : Int) (t : Nat) (f : Nat → Int)
    (hcoarse : ∀ n m, m < n → (f n % M = f m % M ↔ t ∣ n-m))
    (r s : Nat) (hr : r < t) (hs : s < t) (h : f r % M = f s % M) : r = s := by
  by_cases hrs : r < s
  · have hd := (hcoarse _ _ hrs).mp h.symm
    have h := Nat.le_of_dvd (by omega : 0 < s-r) hd
    omega
  · by_cases hsr : s < r
    · have hd := (hcoarse _ _ hsr).mp h
      have h := Nat.le_of_dvd (by omega : 0 < r-s) hd
      omega
    · omega

end WSSFinitePhase

namespace D5.S3.Arith.Primes.GoldenCubicBlockTailOrbitImage

open D5.S1.Scale GoldenCubicBlockLagValuation GoldenCubicBlockTailPeriodClosed

/-- A tail sample with the first block after the earlier divisor as its origin. -/
def tailBlock (i n : ℕ) : ℤ := goldenLucas (3^(i+1+n))^2+3

/-- The upper end of the first nonconstant period plateau. -/
def tailPhaseDepth (p i : ℕ) : ℕ :=
  2 * padicValInt p (goldenLucas (3^i)^2+3) + padicValNat p (3^(p-1)-1)

private theorem phase_prime_coprime (p i : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
    (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) : IsCoprime (p:ℤ) 9 := by
  let b := goldenLucas (3^i)^2+3
  have hb9 : (b : ZMod 9) = ((1:ℤ):ZMod 9) :=
    (golden_cubic_lucas_block i hi).2.2.1
  have hr := (ZMod.intCast_eq_intCast_iff' b 1 9).mp hb9
  have hp3 : ¬ p ∣ 3 := by
    intro hd
    have he : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd
    rw [he] at hB
    have hw : b % 3 = 0 := Int.emod_eq_zero_of_dvd hB
    omega
  have hc : IsCoprime (p:ℤ) (3:ℤ) := (hp.coprime_iff_not_dvd.mpr hp3).isCoprime
  simpa using (hc.pow_right (n := 2))

/-- A single pair collision is equivalent to divisibility by the full
return period. This is stronger than mere periodicity. -/
theorem tailBlock_pair_collision_iff (p i a n m : ℕ) (hp : p.Prime)
    (hi : 1 ≤ i) (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) (hmn : m < n) :
    tailBlock i n ≡ tailBlock i m [ZMOD (p:ℤ)^a] ↔
      cubicTailPeriod p i a ∣ n-m := by
  have hclock := golden_cubic_tail_period_closed p i a (n-m) hp hi hB
  constructor
  · intro he
    apply hclock.mp
    intro j
    let w := 2*padicValInt p (goldenLucas (3^i)^2+3)
    by_cases hw : a ≤ w
    · exact golden_cubic_tail_constant p i a _ _ hp hi hB hw
    let r := a-w
    have ha : w+r=a := Nat.add_sub_of_le (by omega)
    have hm1 := golden_cubic_tail_collision p i r n m hp hi hB hmn
    have hj1 := golden_cubic_tail_collision p i r (j+(n-m)) j hp hi hB (by omega)
    change (tailBlock i n ≡ tailBlock i m [ZMOD (p:ℤ)^(w+r)]) ↔ _ at hm1
    change (tailBlock i (j+(n-m)) ≡ tailBlock i j [ZMOD (p:ℤ)^(w+r)]) ↔ _ at hj1
    rw [ha] at hm1 hj1
    have hpow := hm1.mp he
    have hbase : (9:ℤ)^(n-m) ≡ 1 [ZMOD (p:ℤ)^r] := by
      rw [Int.modEq_iff_dvd] at hpow ⊢
      have hn : (9:ℤ)^n = (9:ℤ)^(n-m)*(9:ℤ)^m := by
        rw [←pow_add, Nat.sub_add_cancel (by omega)]
      rw [hn, show (9:ℤ)^m-(9:ℤ)^(n-m)*(9:ℤ)^m =
        (1-(9:ℤ)^(n-m))*(9:ℤ)^m by ring] at hpow
      have hc : IsCoprime ((p:ℤ)^r) ((9:ℤ)^m) :=
        (phase_prime_coprime p i hp hi hB).pow_left.pow_right
      exact hc.dvd_of_dvd_mul_right hpow
    apply hj1.mpr
    simpa [pow_add, mul_comm] using hbase.mul_left ((9:ℤ)^j)
  · intro hd
    have h := hclock.mpr hd m
    have hn : m+(n-m)=n := by omega
    simpa only [hn, tailBlock] using h

private theorem tail_phase_coarse_fine (p i k : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
    (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) :
    cubicTailPeriod p i (tailPhaseDepth p i) = orderOf (9 : ZMod p) ∧
    cubicTailPeriod p i (tailPhaseDepth p i+k) = orderOf (9 : ZMod p)*p^k := by
  have hc := (cubicTailPeriod_profile_cutoffs p i hp hi hB).2.1
  change cubicTailPeriod p i (tailPhaseDepth p i) = orderOf (9 : ZMod p) at hc
  refine ⟨hc, ?_⟩
  have hh := (cubicTailPeriod_eq_initial_order_iff p i (tailPhaseDepth p i) hp hi hB).mp hc
  let w := 2*padicValInt p (goldenLucas (3^i)^2+3)
  let e := padicValNat p (3^(p-1)-1)
  change w < w+e ∧ _ at hh
  unfold cubicTailPeriod
  change (if w+e+k ≤ w then 1 else orderOf (9 : ZMod p)*p^(w+e+k-w-e)) = _
  rw [ite_eq_right (by omega : ¬ w+e+k ≤ w), show w+e+k-w-e = k by omega]

/-- At every added precision, each coarse clock phase visits exactly the full
fibre above its coarse residue, within the displayed number of samples. -/
theorem tailBlock_phase_image (p i k r : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
    (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) (z : ℤ) :
    (∃ x < p^k, tailBlock i (r+orderOf (9 : ZMod p)*x) ≡ z
      [ZMOD (p:ℤ)^(tailPhaseDepth p i+k)]) ↔
      z ≡ tailBlock i r [ZMOD (p:ℤ)^tailPhaseDepth p i] := by
  obtain ⟨hc,hf⟩ := tail_phase_coarse_fine p i k hp hi hB
  have ht := (golden_cubic_nine_order_gt_one p i hp hi hB).pos
  have hm : 0 < (p:ℤ)^tailPhaseDepth p i := pow_pos (by exact_mod_cast hp.pos : (0:ℤ) < (p:ℤ)) _
  have hd : 0 < p^k := pow_pos hp.pos _
  have H (n m a : ℕ) (h : m < n) :=
    tailBlock_pair_collision_iff p i a n m hp hi hB h
  have Hf : (p:ℤ)^tailPhaseDepth p i * ((p^k:ℕ):ℤ) =
      (p:ℤ)^(tailPhaseDepth p i+k) := by rw [Nat.cast_pow, pow_add]
  have h :=
    WSSFinitePhase.completeClockPhase ((p:ℤ)^tailPhaseDepth p i) hm
      (orderOf (9 : ZMod p)) (p^k) ht hd (tailBlock i)
      (fun n m h => by simpa only [hc, Int.ModEq] using H n m (tailPhaseDepth p i) h)
      (fun n m h => by
        rw [Hf]
        simpa only [hf, Int.ModEq] using H n m (tailPhaseDepth p i+k) h) r z
  simpa only [Hf, Int.ModEq] using h

/-- The entire tail image modulo a higher prime power is the union of the
full fibres above the coarse residues, indexed over exactly one phase cycle. -/
theorem tailBlock_total_image (p i k : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
    (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) (z : ℤ) :
    (∃ n, tailBlock i n ≡ z [ZMOD (p:ℤ)^(tailPhaseDepth p i+k)]) ↔
    ∃ r < orderOf (9 : ZMod p), z ≡ tailBlock i r [ZMOD (p:ℤ)^tailPhaseDepth p i] := by
  obtain ⟨hc,hf⟩ := tail_phase_coarse_fine p i k hp hi hB
  have ht := (golden_cubic_nine_order_gt_one p i hp hi hB).pos
  have hm : 0 < (p:ℤ)^tailPhaseDepth p i := pow_pos (by exact_mod_cast hp.pos : (0:ℤ) < (p:ℤ)) _
  have hd : 0 < p^k := pow_pos hp.pos _
  have H (n m a : ℕ) (h : m < n) :=
    tailBlock_pair_collision_iff p i a n m hp hi hB h
  have Hf : (p:ℤ)^tailPhaseDepth p i * ((p^k:ℕ):ℤ) =
      (p:ℤ)^(tailPhaseDepth p i+k) := by rw [Nat.cast_pow, pow_add]
  have h :=
    WSSFinitePhase.completeClockImage ((p:ℤ)^tailPhaseDepth p i) hm
      (orderOf (9 : ZMod p)) (p^k) ht hd (tailBlock i)
      (fun n m h => by simpa only [hc, Int.ModEq] using H n m (tailPhaseDepth p i) h)
      (fun n m h => by
        rw [Hf]
        simpa only [hf, Int.ModEq] using H n m (tailPhaseDepth p i+k) h) z
  simpa only [Hf, Int.ModEq] using h

/-- Two different phases below one coarse period cannot share a coarse residue,
so the fibres in the total image are pairwise disjoint. -/
theorem tailBlock_phases_disjoint (p i r s : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
    (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3)
    (hr : r < orderOf (9 : ZMod p)) (hs : s < orderOf (9 : ZMod p))
    (h : tailBlock i r ≡ tailBlock i s [ZMOD (p:ℤ)^tailPhaseDepth p i]) : r=s := by
  have hc := (tail_phase_coarse_fine p i 0 hp hi hB).1
  exact WSSFinitePhase.completeClockPhasesDisjoint _ _ (tailBlock i)
    (fun n m h => by simpa only [hc, Int.ModEq] using
      tailBlock_pair_collision_iff p i (tailPhaseDepth p i) n m hp hi hB h) r s hr hs h

/-- Every residue on the orbit has a unique representative in one full
cycle. Alongside the image theorem this gives exactly t*p^k residues. -/
theorem tailBlock_one_cycle (p i k n : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
    (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) :
    ∃! j : Fin (orderOf (9 : ZMod p) * p^k),
      tailBlock i j ≡ tailBlock i n [ZMOD (p:ℤ)^(tailPhaseDepth p i+k)] := by
  let P := orderOf (9 : ZMod p) * p^k
  have hpos : 0 < P :=
    Nat.mul_pos (golden_cubic_nine_order_gt_one p i hp hi hB).pos (pow_pos hp.pos _)
  let r : Fin P := ⟨n % P, Nat.mod_lt n hpos⟩
  have hP := (tail_phase_coarse_fine p i k hp hi hB).2
  have h (x y : ℕ) (hyx : y < x) :
      tailBlock i x ≡ tailBlock i y [ZMOD (p:ℤ)^(tailPhaseDepth p i+k)] ↔ P ∣ x-y := by
    simpa only [hP, P] using
      tailBlock_pair_collision_iff p i (tailPhaseDepth p i+k) x y hp hi hB hyx
  have hr : tailBlock i r ≡ tailBlock i n [ZMOD (p:ℤ)^(tailPhaseDepth p i+k)] := by
    have hle := Nat.mod_le n P
    have hdecomp := Nat.div_add_mod n P
    by_cases heq : n % P = n
    · change tailBlock i (n%P) ≡ tailBlock i n [ZMOD (p:ℤ)^(tailPhaseDepth p i+k)]
      rw [heq]
    · have hlt : n%P < n := by omega
      apply ((h n (n%P) hlt).mpr _).symm
      exact ⟨n/P, by omega⟩
  refine ⟨r, hr, ?_⟩
  intro j hj
  have hEq := hj.trans hr.symm
  apply Fin.ext
  have hjlt := j.isLt
  have hrlt := r.isLt
  by_cases hjr : j.val < r.val
  · have hD := (h r.val j.val hjr).mp hEq.symm
    have hL := Nat.le_of_dvd (by omega : 0 < r.val-j.val) hD
    omega
  · by_cases hrj : r.val < j.val
    · have hD := (h j.val r.val hrj).mp hEq
      have hL := Nat.le_of_dvd (by omega : 0 < j.val-r.val) hD
      omega
    · omega

/-- For the divisor 19 of the first cubic block, all higher-precision
residues are determined by these nine ordinary residues modulo 6859. -/
theorem tailBlock_nineteen_image (k : ℕ) (z : ℤ) :
    (∃ n, tailBlock 1 n ≡ z [ZMOD (19:ℤ)^(3+k)]) ↔
    z % 6859 ∈ ([5779, 3974, 1447, 6140, 364, 3252, 1808, 2530, 2169] : List ℤ) := by
  have hp : Nat.Prime 19 := by decide
  have hLucas : goldenLucas (3^1) = 4 := by
    open D5.S0.Carrier in norm_num [goldenLucas, trace, phi, pow_succ]
  have hB : (19:ℤ) ∣ goldenLucas (3^1)^2+3 := by rw [hLucas]; decide
  have hdepth : padicValInt 19 (goldenLucas (3^1)^2+3) = 1 := by
    rw [hLucas, show (4:ℤ)^2+3 = (↑(19:ℕ):ℤ) by decide]
    exact padicValInt.self hp.one_lt
  have ht : orderOf (9 : ZMod 19) = 9 := by
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact orderOf_eq_prime_pow (p := 3) (n := 1) (by decide) (by decide)
  have he : padicValNat 19 (3^(19-1)-1) = 1 := by
    have : Fact (Nat.Prime 19) := ⟨hp⟩
    have h0 : (3^(19-1)-1 : ℕ) ≠ 0 := by decide
    have hlo := (padicValNat_dvd_iff_le (p := 19) (n := 1) h0).mp (by decide)
    have hhi := (padicValNat_dvd_iff_le (p := 19) (n := 2) h0).not.mp (by decide)
    omega
  have hd : tailPhaseDepth 19 1 = 3 := by
    dsimp only [tailPhaseDepth]
    rw [hdepth, he]
  have h := tailBlock_total_image 19 1 k hp (by decide) hB z
  rw [hd, ht] at h
  refine h.trans ?_
  let F (x : ZMod 6859) := x*x*x + 3*x
  have hl (r : ℕ) : (goldenLucas (3^(1+1+r)) : ZMod 6859) = F^[r] 76 := by
    induction r with
    | zero =>
      have hs : goldenLucas (3^(1+1)) = 76 := by
        rw [(golden_cubic_lucas_block 1 (by decide)).2.2.2.2.2, hLucas]
        decide
      simpa using (show (goldenLucas (3^(1+1)) : ZMod 6859) = 76 by
        rw [hs]; decide)
    | succ r ihr =>
      rw [Function.iterate_succ_apply']
      have hs := (golden_cubic_lucas_block (1+1+r) (by omega)).2.2.2.2.2
      change goldenLucas (3^(1+1+r.succ)) = _ at hs
      rw [hs]
      push_cast
      rw [← ihr]
      dsimp [F]
      ring
  have hb (r : ℕ) : tailBlock 1 r % 6859 =
      ((F^[r] 76 : ZMod 6859)^2+3).val := by
    have hh : (tailBlock 1 r : ZMod 6859) = ((F^[r] 76 : ZMod 6859)^2+3) := by
      unfold tailBlock
      push_cast
      rw [hl]
    have hVal := congrArg ZMod.val hh
    exact_mod_cast (ZMod.val_intCast (tailBlock 1 r)).symm.trans (by exact_mod_cast hVal)
  have hres (r : ℕ) (hr : r < 9) :
      tailBlock 1 r % 6859 ∈ ([5779, 3974, 1447, 6140, 364, 3252, 1808, 2530, 2169] : List ℤ) := by
    rw [hb]
    interval_cases r <;> decide
  constructor
  · intro ⟨r, hr, heq⟩
    change z % 6859 = tailBlock 1 r % 6859 at heq
    rw [heq]
    exact hres r hr
  · intro hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · refine ⟨0, by decide, ?_⟩
      change z % 6859 = tailBlock 1 0 % 6859
      rw [h0, hb]; decide
    · refine ⟨1, by decide, ?_⟩
      change z % 6859 = tailBlock 1 1 % 6859
      rw [h1, hb]; decide
    · refine ⟨2, by decide, ?_⟩
      change z % 6859 = tailBlock 1 2 % 6859
      rw [h2, hb]; decide
    · refine ⟨3, by decide, ?_⟩
      change z % 6859 = tailBlock 1 3 % 6859
      rw [h3, hb]; decide
    · refine ⟨4, by decide, ?_⟩
      change z % 6859 = tailBlock 1 4 % 6859
      rw [h4, hb]; decide
    · refine ⟨5, by decide, ?_⟩
      change z % 6859 = tailBlock 1 5 % 6859
      rw [h5, hb]; decide
    · refine ⟨6, by decide, ?_⟩
      change z % 6859 = tailBlock 1 6 % 6859
      rw [h6, hb]; decide
    · refine ⟨7, by decide, ?_⟩
      change z % 6859 = tailBlock 1 7 % 6859
      rw [h7, hb]; decide
    · refine ⟨8, by decide, ?_⟩
      change z % 6859 = tailBlock 1 8 % 6859
      rw [h8, hb]; decide

end D5.S3.Arith.Primes.GoldenCubicBlockTailOrbitImage
