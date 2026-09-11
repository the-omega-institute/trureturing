/- GID: D5/S1/Words/Compositions/ConstantEqualSumDivisorIdentity
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/ConstantEqualSumDivisorIdentity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Equal-sum constant-block systems normalize uniquely by their support lcm. -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.GCDMonoid.Multiset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.SetTheory.Cardinal.Finite

open scoped BigOperators
namespace D5.S1.Words.Compositions.ConstantEqualSumDivisorIdentity

/-- A block value x denotes the constant block of D/x copies of x. -/
def ValidBlockValues (D : ℕ) (b : Multiset ℕ) : Prop :=
  ∀ x ∈ b, 0 < x ∧ x ∣ D

/-- Flatten the constant blocks; repetition in b records repeated identical blocks. -/
def expand (D : ℕ) (b : Multiset ℕ) : Multiset ℕ :=
  b.bind fun x => Multiset.replicate (D/x) x

/-- Existence of a decomposition into constant blocks with a common positive sum. -/
def Capable (m : Multiset ℕ) : Prop :=
  ∃ D b, 0 < D ∧ ValidBlockValues D b ∧ expand D b = m

/-- Count flattened, unlabeled integer partitions for which a decomposition exists. -/
noncomputable def capablePartitionCount (n : ℕ) : ℕ :=
  Nat.card {p : Nat.Partition n // Capable p.parts}

/-- For positive weight, a system consists of its common sum and the multiset of block values.
Each x denotes one block of D/x copies of x, so all block sums are D. -/
def ConstantEqualSumSystem (n : ℕ) :=
  {s : ℕ × Multiset ℕ // 0 < s.1 ∧ ValidBlockValues s.1 s.2 ∧ s.1 * s.2.card = n}

/-- Count every block multiset once. At weight zero the unique system is empty. -/
noncomputable def constantEqualSumSystemCount (n : ℕ) : ℕ :=
  if n = 0 then 1 else Nat.card (ConstantEqualSumSystem n)

private def Admits (m : Multiset ℕ) (D : ℕ) : Prop :=
  ∀ x ∈ m, x ∣ D ∧ D ∣ x * m.count x

private def System (n : ℕ) :=
  {p : Nat.Partition n × ℕ // 0 < p.2 ∧ Admits p.1.parts p.2}

private theorem count_expand (D x : ℕ) (b : Multiset ℕ) :
    (expand D b).count x = (D/x) * b.count x := by
  induction b using Multiset.induction_on with
  | empty => simp [expand]
  | cons a b ih =>
    simp only [expand, Multiset.cons_bind, Multiset.count_add] at ih ⊢
    by_cases h : a = x
    · subst a; simp [ih, mul_add, add_comm]
    · simp [Multiset.count_replicate, h, Ne.symm h, ih]

private theorem mem_expand {D x : ℕ} {b : Multiset ℕ} (hD : 0 < D) (h : ValidBlockValues D b) :
    x ∈ expand D b ↔ x ∈ b := by
  rw [← Multiset.count_pos, count_expand]
  constructor
  · intro hx
    exact Multiset.count_pos.mp (Nat.pos_of_mul_pos_left hx)
  · intro hx
    exact Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd hD (h x hx).2) (h x hx).1)
      (Multiset.count_pos.mpr hx)
private theorem sum_expand {D : ℕ} {b : Multiset ℕ} (h : ValidBlockValues D b) :
    (expand D b).sum = D * b.card := by
  induction b using Multiset.induction_on with
  | empty => simp [expand]
  | cons a b ih =>
    have ha := h a (by simp)
    have hb : ValidBlockValues D b := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    simp only [expand, Multiset.cons_bind, Multiset.sum_add, Multiset.sum_replicate,
      smul_eq_mul, Multiset.card_cons] at ih ⊢
    rw [Nat.div_mul_cancel ha.2, ih hb]
    ring

private theorem admits_expand {D : ℕ} {b : Multiset ℕ} (hD : 0 < D) (h : ValidBlockValues D b) :
    Admits (expand D b) D := by
  intro x hx
  have hxb := (mem_expand hD h).mp hx
  refine ⟨(h x hxb).2, ?_⟩
  rw [count_expand, ← mul_assoc, Nat.mul_div_cancel' (h x hxb).2]
  exact dvd_mul_right D _

private def blocksOf (m : Multiset ℕ) (D : ℕ) : Multiset ℕ :=
  ∑ x ∈ m.toFinset, (m.count x / (D/x)) • {x}

private theorem count_blocksOf (m : Multiset ℕ) (D x : ℕ) :
    (blocksOf m D).count x = m.count x / (D/x) := by
  unfold blocksOf
  rw [← Multiset.coe_countAddMonoidHom, map_sum]
  simp only [Multiset.coe_countAddMonoidHom, Multiset.count_nsmul, Multiset.count_singleton]
  by_cases hx : x ∈ m
  · simp [mul_ite, hx]
  · simp [mul_ite, hx]

private theorem blocksOf_valid {m : Multiset ℕ} {D : ℕ}
    (hp : ∀ x ∈ m, 0 < x) (h : Admits m D) : ValidBlockValues D (blocksOf m D) := by
  intro x hx
  have hx' : x ∈ m := by
    by_contra hn
    have hc := Multiset.count_pos.mpr hx
    rw [count_blocksOf, Multiset.count_eq_zero_of_notMem hn, Nat.zero_div] at hc
    omega
  exact ⟨hp x hx', (h x hx').1⟩

private theorem expand_blocksOf {m : Multiset ℕ} {D : ℕ}
    (hp : ∀ x ∈ m, 0 < x) (h : Admits m D) : expand D (blocksOf m D) = m := by
  apply Multiset.ext.mpr
  intro x
  rw [count_expand, count_blocksOf]
  by_cases hx : x ∈ m
  · exact Nat.mul_div_cancel' ((Nat.div_dvd_iff_dvd_mul (h x hx).1 (hp x hx)).mpr
      (h x hx).2)
  · simp [Multiset.count_eq_zero_of_notMem hx]

private theorem expand_injective {D : ℕ} (hD : 0 < D) {b c : Multiset ℕ}
    (hb : ValidBlockValues D b) (hc : ValidBlockValues D c)
    (he : expand D b = expand D c) : b = c := by
  apply Multiset.ext.mpr
  intro x
  by_cases hx : x ∈ b
  · have hp : 0 < D/x := Nat.div_pos (Nat.le_of_dvd hD (hb x hx).2) (hb x hx).1
    apply Nat.eq_of_mul_eq_mul_left hp
    simpa only [count_expand] using congrArg (Multiset.count x) he
  · have hy : x ∉ c := by
      intro hy
      have hxe : x ∈ expand D c := (mem_expand hD hc).mpr hy
      rw [← he] at hxe
      exact hx ((mem_expand hD hb).mp hxe)
    simp [Multiset.count_eq_zero_of_notMem hx, Multiset.count_eq_zero_of_notMem hy]

private theorem capable_of_admits {m : Multiset ℕ} {D : ℕ}
    (hp : ∀ x ∈ m, 0 < x) (hD : 0 < D) (h : Admits m D) : Capable m :=
  ⟨D, blocksOf m D, hD, blocksOf_valid hp h, expand_blocksOf hp h⟩

private theorem lcm_pos {m : Multiset ℕ} (hp : ∀ x ∈ m, 0 < x) : 0 < m.lcm := by
  apply Nat.pos_of_ne_zero
  exact (Multiset.lcm_ne_zero_iff m).mpr (fun h => (Nat.lt_irrefl 0) (hp 0 h))

private theorem lcm_smul (m : Multiset ℕ) {t : ℕ} (ht : 0 < t) :
    (t • m).lcm = m.lcm := by
  apply Nat.dvd_antisymm
  · exact Multiset.lcm_dvd.mpr (fun x hx => Multiset.dvd_lcm (Multiset.mem_of_mem_nsmul hx))
  · exact Multiset.lcm_dvd.mpr (fun x hx => Multiset.dvd_lcm
      ((Multiset.mem_nsmul_of_ne_zero ht.ne').mpr hx))

private theorem canonical {m : Multiset ℕ} (h : Capable m) : Admits m m.lcm := by
  obtain ⟨D, b, hpos, hb, he⟩ := h
  have hD : Admits m D := he ▸ admits_expand hpos hb
  have hL : m.lcm ∣ D := Multiset.lcm_dvd.mpr (fun x hx => (hD x hx).1)
  exact fun x hx => ⟨Multiset.dvd_lcm hx, hL.trans (hD x hx).2⟩

private theorem admits_smul {m : Multiset ℕ} {D t : ℕ} (h : Admits m D) :
    Admits (t • m) (t * D) := by
  intro x hx
  have hxm := Multiset.mem_of_mem_nsmul hx
  refine ⟨(h x hxm).1.trans (dvd_mul_left D t), ?_⟩
  rw [Multiset.count_nsmul, ← mul_assoc, mul_comm x t, mul_assoc]
  exact Nat.mul_dvd_mul_left t (h x hxm).2

private theorem normalize {m : Multiset ℕ} {D : ℕ}
    (hp : ∀ x ∈ m, 0 < x) (hD : 0 < D) (h : Admits m D) :
    ∃ t u, 0 < t ∧ m = t • u ∧ D = t * u.lcm ∧ Capable u := by
  have hL : m.lcm ∣ D := Multiset.lcm_dvd.mpr (fun x hx => (h x hx).1)
  obtain ⟨t, he⟩ := hL
  have ht : 0 < t := by nlinarith
  have hc : ∀ x ∈ m, t ∣ m.count x := by
    intro x hx
    have hxL := Multiset.dvd_lcm hx
    obtain ⟨k, hk⟩ := hxL
    have hd := (h x hx).2
    rw [he, hk] at hd
    have hxt : x * t ∣ x * m.count x :=
      (show x * t ∣ x * k * t by use k; ring).trans hd
    exact (Nat.dvd_of_mul_dvd_mul_left (hp x hx) hxt)
  obtain ⟨u, hu⟩ := Multiset.exists_smul_of_dvd_count m hc
  have hul : u.lcm = m.lcm := by rw [hu, lcm_smul u ht]
  have hup : ∀ x ∈ u, 0 < x := fun x hx => hp x
    (by rw [hu]; exact (Multiset.mem_nsmul_of_ne_zero ht.ne').mpr hx)
  refine ⟨t, u, ht, hu, ?_, capable_of_admits hup (lcm_pos hup) ?_⟩
  · rw [hul, he, mul_comm]
  · intro x hx
    have hxm : x ∈ m := by rw [hu]; exact (Multiset.mem_nsmul_of_ne_zero ht.ne').mpr hx
    refine ⟨Multiset.dvd_lcm hx, ?_⟩
    have hd := (h x hxm).2
    rw [hu, Multiset.count_nsmul, he, ← hul] at hd
    have hd' : t * u.lcm ∣ t * (x * u.count x) := by
      convert hd using 1 <;> ring
    exact Nat.dvd_of_mul_dvd_mul_left ht hd'

private def DivisorPartitions (n : ℕ) :=
  (d : {d : ℕ // d ∈ n.divisors}) × {p : Nat.Partition d.val // Capable p.parts}

private theorem quotient_pos {n d : ℕ} (hn : 0 < n) (hd : d ∈ n.divisors) :
    0 < n / d := Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd))
      (Nat.pos_of_mem_divisors hd)

private def liftPartition {n d : ℕ} (hd : d ∈ n.divisors) (p : Nat.Partition d) :
    Nat.Partition n where
  parts := (n / d) • p.parts
  parts_pos hx := p.parts_pos (Multiset.mem_of_mem_nsmul hx)
  parts_sum := by
    rw [Multiset.sum_nsmul, smul_eq_mul, p.parts_sum,
      Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]

private def liftSystem {n : ℕ} (hn : 0 < n) (a : DivisorPartitions n) : System n :=
  ⟨(liftPartition a.1.2 a.2.1, (n / a.1.1) * a.2.1.parts.lcm),
    Nat.mul_pos (quotient_pos hn a.1.2) (lcm_pos (fun _ hx => a.2.1.parts_pos hx)),
    admits_smul (canonical a.2.2)⟩

private theorem liftSystem_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (liftSystem hn) := by
  rintro ⟨⟨d, hd⟩, p⟩ ⟨⟨e, he⟩, q⟩ h
  have hm : (n/d) • p.1.parts = (n/e) • q.1.parts :=
    congrArg (fun s : System n => s.1.1.parts) h
  have hD : (n/d) * p.1.parts.lcm = (n/e) * q.1.parts.lcm :=
    congrArg (fun s : System n => s.1.2) h
  have hL : p.1.parts.lcm = q.1.parts.lcm := by
    simpa only [lcm_smul _ (quotient_pos hn hd), lcm_smul _ (quotient_pos hn he)]
      using congrArg Multiset.lcm hm
  rw [← hL] at hD
  have ht : n/d = n/e := Nat.eq_of_mul_eq_mul_right
    (lcm_pos (fun _ hx => p.1.parts_pos hx)) hD
  have hde : d = e := by
    apply Nat.eq_of_mul_eq_mul_left (quotient_pos hn hd)
    rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd), ht,
      Nat.div_mul_cancel (Nat.dvd_of_mem_divisors he)]
  subst e
  have hpq : p = q := by
    apply Subtype.ext
    apply Nat.Partition.ext
    exact (nsmul_right_injective (quotient_pos hn hd).ne') hm
  cases hpq
  rfl

private theorem liftSystem_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (liftSystem hn) := by
  rintro ⟨⟨p, D⟩, hD, h⟩
  obtain ⟨t, u, ht, hm, hDu, hu⟩ := normalize (fun _ hx => p.parts_pos hx) hD h
  have hsum : t * u.sum = n := by
    simpa only [hm, Multiset.sum_nsmul, smul_eq_mul] using p.parts_sum
  have hud : u.sum ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨⟨t, by simpa [mul_comm] using hsum.symm⟩, hn.ne'⟩
  have hup : 0 < u.sum := by nlinarith
  have htq : n / u.sum = t := by rw [← hsum, Nat.mul_div_cancel _ hup]
  let q : Nat.Partition u.sum := ⟨u, fun hx => p.parts_pos
    (by rw [hm]; exact (Multiset.mem_nsmul_of_ne_zero ht.ne').mpr hx), rfl⟩
  refine ⟨⟨⟨u.sum, hud⟩, ⟨q, hu⟩⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Nat.Partition.ext
    exact (by change (n / u.sum) • u = p.parts; rw [htq, ← hm])
  · change n / u.sum * u.lcm = D
    rw [htq]
    exact hDu.symm

private theorem encoded_divisor_sum (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, capablePartitionCount d) = Nat.card (System n) := by
  classical
  let e := Equiv.ofBijective (liftSystem hn)
    ⟨liftSystem_injective hn, liftSystem_surjective hn⟩
  have h := Nat.card_congr e
  change Nat.card (DivisorPartitions n) = _ at h
  rw [DivisorPartitions, Nat.card_sigma] at h
  exact (Finset.sum_subtype n.divisors (fun _ => Iff.rfl) capablePartitionCount).trans h

private def encodeSystem {n : ℕ} (s : ConstantEqualSumSystem n) : System n :=
  ⟨(⟨expand s.1.1 s.1.2,
      fun hx => (s.2.2.1 _ ((mem_expand s.2.1 s.2.2.1).mp hx)).1,
      (sum_expand s.2.2.1).trans s.2.2.2⟩, s.1.1),
    s.2.1, admits_expand s.2.1 s.2.2.1⟩

private theorem encodeSystem_injective (n : ℕ) :
    Function.Injective (encodeSystem (n := n)) := by
  rintro ⟨⟨D, b⟩, hD, hb, hbn⟩ ⟨⟨E, c⟩, hE, hc, hcn⟩ he
  have hDE : D = E := congrArg (fun s : System n => s.1.2) he
  subst E
  apply Subtype.ext
  refine Prod.ext rfl ?_
  exact expand_injective hD hb hc (congrArg (fun s : System n => s.1.1.parts) he)

private theorem encodeSystem_surjective (n : ℕ) :
    Function.Surjective (encodeSystem (n := n)) := by
  rintro ⟨⟨p, D⟩, hD, h⟩
  have hp : ∀ x ∈ p.parts, 0 < x := fun _ hx => p.parts_pos hx
  have hb := blocksOf_valid hp h
  have he := expand_blocksOf hp h
  have hn : D * (blocksOf p.parts D).card = n := by
    rw [← sum_expand hb, he, p.parts_sum]
  refine ⟨⟨(D, blocksOf p.parts D), hD, hb, hn⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext (Nat.Partition.ext he) rfl

/-- OEIS A383093: the divisor sum of capable partition counts is A323774.
The normalization divides multiplicities by D/lcm(support);
neither count is defined by a divisor sum. -/
theorem capable_divisor_sum (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, capablePartitionCount d) = constantEqualSumSystemCount n := by
  rw [constantEqualSumSystemCount, if_neg hn.ne']
  exact (encoded_divisor_sum n hn).trans
    (Nat.card_congr (Equiv.ofBijective (encodeSystem (n := n))
      ⟨encodeSystem_injective n, encodeSystem_surjective n⟩)).symm

#print axioms capable_divisor_sum

end D5.S1.Words.Compositions.ConstantEqualSumDivisorIdentity
