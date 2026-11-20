/- GID: D5/S3/Arith/Primes/GoldenCubicBlockJointClock
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockJointClock
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Two aligned native Lucas prime clocks have a gcd compatibility condition and an lcm collision rule. -/

import D5.S3.Arith.Primes.GoldenCubicBlockTailOrbitImage

set_option autoImplicit false

namespace D5.S3.Arith.Primes.GoldenCubicBlockJointClock

open D5.S1.Scale GoldenCubicBlockTailPeriodClosed GoldenCubicBlockTailOrbitImage

/-- A collision is exactly equality in the index clock and does not
depend on which later observation is the initial reading. -/
theorem individual_collision (p i a n m : ℕ) (hp : p.Prime)
    (hi : 1 ≤ i) (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) :
    tailBlock i n ≡ tailBlock i m [ZMOD (p:ℤ)^a] ↔
      n ≡ m [MOD cubicTailPeriod p i a] := by
  have fwd (x y : ℕ) (hyx : y < x) :
      tailBlock i x ≡ tailBlock i y [ZMOD (p:ℤ)^a] ↔
        y ≡ x [MOD cubicTailPeriod p i a] :=
    (tailBlock_pair_collision_iff p i a x y hp hi hB hyx).trans
      (Nat.modEq_iff_dvd' hyx.le).symm
  rcases lt_trichotomy m n with hm | he | hn
  · exact (fwd n m hm).trans Nat.ModEq.comm
  · subst m; exact ⟨fun _ => Nat.ModEq.refl _, fun _ => Int.ModEq.refl _⟩
  · exact ⟨fun h => (fwd m n hn).mp h.symm, fun h => ((fwd m n hn).mpr h).symm⟩

/-- The raw native block, with a node index shared by all primes. -/
def clockBlock (j : ℕ) : ℤ := goldenLucas (3^j)^2+3

/-- Offset choice does not change phase differences at any precision. -/
theorem aligned_collision (p i a K x y : ℕ) (hp : p.Prime)
    (hi : 1 ≤ i) (hB : (p:ℤ) ∣ clockBlock i) (hK : i+1 ≤ K) :
    clockBlock (K+x) ≡ clockBlock (K+y) [ZMOD (p:ℤ)^a] ↔
      x ≡ y [MOD cubicTailPeriod p i a] := by
  let d := K-(i+1)
  have e (z : ℕ) : K+z = i+1+(d+z) := by dsimp [d]; omega
  rw [e x, e y]
  change tailBlock i (d+x) ≡ tailBlock i (d+y) [ZMOD (p:ℤ)^a] ↔ _
  rw [individual_collision p i a _ _ hp hi hB]
  exact ⟨fun h => Nat.ModEq.add_left_cancel (Nat.ModEq.refl d) h,
    fun h => h.add_left d⟩

/-- A pair of individually observed residues at two primes comes from
one synchronous block exactly when the original time labels agree modulo
the gcd of the two least periods. No cross-prime independence is assumed. -/
theorem synchronous_pair_exists (p q i j a b K x y : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hpB : (p:ℤ) ∣ clockBlock i) (hqB : (q:ℤ) ∣ clockBlock j)
    (hKi : i+1 ≤ K) (hKj : j+1 ≤ K) :
    (∃ n : ℕ, clockBlock (K+n) ≡ clockBlock (K+x) [ZMOD (p:ℤ)^a] ∧
      clockBlock (K+n) ≡ clockBlock (K+y) [ZMOD (q:ℤ)^b]) ↔
      x ≡ y [MOD (cubicTailPeriod p i a).gcd (cubicTailPeriod q j b)] := by
  simp only [aligned_collision p i a K _ x hp hi hpB hKi,
    aligned_collision q j b K _ y hq hj hqB hKj]
  constructor
  · rintro ⟨n, hx, hy⟩
    exact (hx.of_dvd (Nat.gcd_dvd_left _ _)).symm.trans (hy.of_dvd (Nat.gcd_dvd_right _ _))
  · intro h
    exact ⟨Nat.chineseRemainder' h, (Nat.chineseRemainder' h).prop⟩

/-- The joint kernel is exactly congruence modulo the lcm, so the entire
joint orbit has that least positive period, rather than the product in
general. -/
theorem synchronous_pair_collision (p q i j a b K x y : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hpB : (p:ℤ) ∣ clockBlock i) (hqB : (q:ℤ) ∣ clockBlock j)
    (hKi : i+1 ≤ K) (hKj : j+1 ≤ K) :
    (clockBlock (K+x) ≡ clockBlock (K+y) [ZMOD (p:ℤ)^a] ∧
      clockBlock (K+x) ≡ clockBlock (K+y) [ZMOD (q:ℤ)^b]) ↔
      x ≡ y [MOD (cubicTailPeriod p i a).lcm (cubicTailPeriod q j b)] := by
  rw [aligned_collision p i a K x y hp hi hpB hKi,
    aligned_collision q j b K x y hq hj hqB hKj]
  exact ⟨fun ⟨hx, hy⟩ => Nat.mod_lcm hx hy, fun h =>
    ⟨h.of_dvd (Nat.dvd_lcm_left _ _), h.of_dvd (Nat.dvd_lcm_right _ _)⟩⟩

/-- Normalized time labels enumerate all and only compatible residue
pairs. In particular the shared phase cuts the apparent product of
individual periods by their gcd, without discarding any compatible pair. -/
noncomputable def compatibleResiduePairs (P Q : ℕ) (hP : 0 < P) (hQ : 0 < Q) :
    Fin (P.lcm Q) ≃ {z : Fin P × Fin Q // z.1.val ≡ z.2.val [MOD P.gcd Q]} := by
  apply Equiv.ofBijective (fun n =>
    ⟨(⟨n.val % P, Nat.mod_lt _ hP⟩, ⟨n.val % Q, Nat.mod_lt _ hQ⟩),
      ((Nat.mod_modEq _ _).of_dvd (Nat.gcd_dvd_left P Q)).trans
        (((Nat.mod_modEq _ _).of_dvd (Nat.gcd_dvd_right P Q)).symm)⟩)
  constructor
  · intro n m heq
    have hl : n.val % P = m.val % P :=
      congrArg (fun z : {z : Fin P × Fin Q // z.1.val ≡ z.2.val [MOD P.gcd Q]} =>
        z.val.1.val) heq
    have hr : n.val % Q = m.val % Q :=
      congrArg (fun z : {z : Fin P × Fin Q // z.1.val ≡ z.2.val [MOD P.gcd Q]} =>
        z.val.2.val) heq
    have hc : n.val ≡ m.val [MOD P.lcm Q] := Nat.mod_lcm hl hr
    exact Fin.ext (by simpa [Nat.ModEq, Nat.mod_eq_of_lt n.isLt, Nat.mod_eq_of_lt m.isLt] using hc)
  · intro z
    let k := Nat.chineseRemainder' z.prop
    refine ⟨⟨k.val, Nat.chineseRemainder'_lt_lcm z.prop hP.ne' hQ.ne'⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact Eq.trans k.prop.1 (Nat.mod_eq_of_lt z.val.1.isLt)
    · apply Fin.ext
      exact Eq.trans k.prop.2 (Nat.mod_eq_of_lt z.val.2.isLt)


end D5.S3.Arith.Primes.GoldenCubicBlockJointClock
