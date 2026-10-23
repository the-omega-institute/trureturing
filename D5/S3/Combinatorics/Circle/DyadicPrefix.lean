/- GID: D5/S3/Combinatorics/Circle/DyadicPrefix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/DyadicPrefix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Colex, mathlib/module/Mathlib.Data.Nat.GCD.Basic]
   utility: none
   digest: Binary quotient separation and an actual labelled dyadic occurrence prefix. -/

/-
   The source motivation is Damasdi–Frankl–Pach–Palvolgyi, “Monochromatic
   configurations on a circle”, arXiv:2504.10687v2, C3.1, DOI
   10.5070/C6.68671. This file proves only the arithmetic and local occurrence
   construction used at a two-run boundary. It does not prove arbitrary-start
   packet insertion or a compatible global root order. In the actual source
   (19,38,-51,25,50,-27,-54) at k=7,t=19,N=127,C=63, the first packet
   (19,38,-51) admits no complete legal ordering from the legal root start 26.
-/

module
public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic

/-! Binary digit selection and exact dyadic rounding for local two-run prefixes. -/

set_option autoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.DyadicPrefix

/-! The finite binary position construction. -/

def boundedBitMap (u : ℕ) (s : Finset ℕ) (hs : ∀ i ∈ s, i < u) : Finset (Fin u) :=
  let f : {i // i ∈ s} → Fin u := fun i => ⟨i.1, hs i.1 i.2⟩
  let hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact congrArg Fin.val hij
  s.attach.map ⟨f, hf⟩

def bitSubset (u x : ℕ) (hx : x < 2 ^ u) : Finset (Fin u) := by
  classical
  let s := x.bitIndices.toFinset.filter (fun i => i < u)
  apply boundedBitMap u s
  intro i hi
  exact (Finset.mem_filter.mp (show i ∈ x.bitIndices.toFinset.filter (fun k => k < u) by
    simpa only [s] using hi)).2

theorem bit_subset_mem {u x : ℕ} (hx : x < 2 ^ u) {i : Fin u} :
    i ∈ bitSubset u x hx ↔ x.testBit i.1 := by
  classical
  let s := x.bitIndices.toFinset.filter (fun j => j < u)
  have hbit (j : ℕ) (hj : j ∈ x.bitIndices) : j < u := by
    by_contra hju
    have hpow : 2 ^ u ≤ 2 ^ j := Nat.pow_le_pow_right (by omega)
      (Nat.le_of_not_gt hju)
    exact (not_le_of_gt hx) (hpow.trans (Nat.two_pow_le_of_mem_bitIndices hj))
  let hbound : ∀ j ∈ s, j < u := by
    intro j hj
    exact (Finset.mem_filter.mp (show j ∈ x.bitIndices.toFinset.filter (fun k => k < u) by
      simpa only [s] using hj)).2
  change i ∈ boundedBitMap u s hbound ↔ _
  unfold boundedBitMap
  change i ∈ s.attach.map _ ↔ _
  constructor
  · intro hi
    rcases Finset.mem_map.1 hi with ⟨j, hj, hji⟩
    have hval : j.1 = i.1 := congrArg Fin.val hji
    have hjS : j.1 ∈ s := j.2
    have hjbit := Nat.mem_bitIndices.mp (by simpa using (Finset.mem_filter.mp (show j.1 ∈
      x.bitIndices.toFinset.filter (fun k => k < u) by simpa only [s] using hjS)).1
      )
    simpa [hval] using hjbit
  · intro hi
    have hj : i.1 ∈ x.bitIndices := Nat.mem_bitIndices.mpr hi
    apply Finset.mem_map.2
    have his0 : i.1 ∈ x.bitIndices.toFinset := by simpa using hj
    have his : i.1 ∈ s := by
      change i.1 ∈ x.bitIndices.toFinset.filter (fun k => k < u)
      exact Finset.mem_filter.2 ⟨his0, hbit i.1 hj⟩
    refine ⟨⟨i.1, his⟩, ?_, ?_⟩
    · simp [his]
    · exact Fin.ext rfl

theorem bit_subset_sum {u x : ℕ} (hx : x < 2 ^ u) :
    ∑ i ∈ bitSubset u x hx, 2 ^ i.1 = x := by
  classical
  let s := x.bitIndices.toFinset.filter (fun i => i < u)
  have hs : s = x.bitIndices.toFinset := by
    apply Finset.filter_eq_self.2
    intro i hi
    by_contra hju
    have hpow : 2 ^ u ≤ 2 ^ i := Nat.pow_le_pow_right (by omega)
      (Nat.le_of_not_gt hju)
    exact (not_le_of_gt hx) (hpow.trans
      (Nat.two_pow_le_of_mem_bitIndices (by simpa using hi)))
  let hbound : ∀ i ∈ s, i < u := by
    intro i hi
    exact (Finset.mem_filter.mp (show i ∈ x.bitIndices.toFinset.filter (fun k => k < u) by
      simpa only [s] using hi)).2
  have hsum : (∑ i ∈ boundedBitMap u s hbound, 2 ^ i.1) =
      ∑ i ∈ s, 2 ^ i := by
    unfold boundedBitMap
    rw [Finset.sum_map]
    rw [← Finset.sum_attach s (fun i => 2 ^ i)]
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  rw [show bitSubset u x hx = boundedBitMap u s hbound by rfl]
  rw [hsum, hs]
  exact Finset.sum_toFinset_bitIndices_two_pow x

theorem bit_subset_top_mem {u x : ℕ} (hu : 0 < u)
    (hlo : 2 ^ (u - 1) ≤ x) (hhi : x < 2 ^ u) :
    ⟨u - 1, by omega⟩ ∈ bitSubset u x hhi := by
  rw [bit_subset_mem hhi]
  have hdiv : x / 2 ^ (u - 1) = 1 := by
    apply Nat.div_eq_of_lt_le
    · simpa using hlo
    · have hpow : 2 ^ u = 2 * 2 ^ (u - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hu]
      rw [hpow] at hhi
      simpa [Nat.mul_comm] using hhi
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]

private theorem weighted_bit_subset {u a x : ℕ} (ha : 0 < a) (hx : x < 2 ^ u) :
    ∑ i ∈ bitSubset u x hx, a * 2 ^ i.1 = a * x := by
  rw [← Finset.mul_sum]
  exact congrArg (fun z => a * z) (bit_subset_sum hx)

/-! The arithmetic separation. -/

private theorem quotient_core (a q x y d h n beta t : ℕ)
    (ha : 0 < a) (hy : 0 < y) (hd : 0 < d)
    (hxpos : 0 < x)
    (hdpow : d + 1 = 2 * y)
    (hx : x = h * d + beta) (hbeta : 0 < beta) (hbetale : beta ≤ y)
    (hq : q = 2 * a * n + 2 * t + 1) (ht : t < a)
    (hQ : d * q ≤ (2 * x - 1) * a) :
    y * q ≤ a * (x + n) := by
  have hxpos' : 1 ≤ 2 * x := by omega
  have hmul : (2 * x - 1) * a + a = 2 * x * a := by
    calc
      (2 * x - 1) * a + a = ((2 * x - 1) + 1) * a := by
        simp [Nat.add_mul]
      _ = 2 * x * a := by rw [Nat.sub_add_cancel hxpos']
  have hQ' : d * q + a ≤ 2 * x * a := by omega
  ring_nf at hQ'
  have hn : n ≤ h := by
    by_contra hnh
    have hnh' : h + 1 ≤ n := by omega
    subst q
    subst x
    clear hQ
    ring_nf at hQ'
    have hnmul : 2 * d * a * (h + 1) ≤ 2 * d * a * n :=
      Nat.mul_le_mul_left (2 * d * a) hnh'
    have hbetamul : 2 * a * beta ≤ 2 * a * y :=
      Nat.mul_le_mul_left (2 * a) hbetale
    nlinarith
  by_contra hgoal
  have hlt : a * (x + n) < y * q := Nat.lt_of_not_ge hgoal
  ring_nf at hlt
  by_cases hnh : n < h
  · have hnh' : n + 1 ≤ h := by omega
    have hnmul : 2 * d * a * (n + 1) ≤ 2 * d * a * h :=
      Nat.mul_le_mul_left (2 * d * a) hnh'
    have htmul : 2 * y * (t + 1) ≤ 2 * y * a :=
      Nat.mul_le_mul_left (2 * y) (by omega)
    have hbetamul : 2 * a * beta ≤ 2 * a * y :=
      Nat.mul_le_mul_left (2 * a) hbetale
    nlinarith
  · have : n = h := by omega
    subst n
    subst q
    subst x
    clear hQ
    have htmul : 2 * y * (t + 1) ≤ 2 * y * a :=
      Nat.mul_le_mul_left (2 * y) (by omega)
    have hbetamul : 2 * a * beta ≤ 2 * a * y :=
      Nat.mul_le_mul_left (2 * a) hbetale
    have hbetamul' : 2 * a * beta ≤ a * (d + 1) := by
      nlinarith [hbetamul, hdpow]
    have hA : 2 * d * t + d + a ≤ 2 * a * beta := by
      nlinarith [hQ']
    have hta_mul : d * (2 * t + 1) ≤ d * a := by
      nlinarith [hQ', hbetamul']
    have hta : 2 * t + 1 ≤ a := Nat.le_of_mul_le_mul_left hta_mul hd
    have hBA : 2 * d * t + 2 * t + 1 ≤ 2 * d * t + d + a := by
      omega
    have hB : 2 * d * t + d + 2 * t + 1 ≤ 2 * a * beta := by
      omega
    have htarget :
        (d + 1) * (2 * a * h + 2 * t + 1) ≤
          2 * a * (h * d + beta + h) := by
      nlinarith [hB]
    have htarget' :
        2 * y * (2 * a * h + 2 * t + 1) ≤
          2 * a * (h * d + beta + h) := by
      rw [← hdpow]
      exact htarget
    have hcancel :
        2 * (y * (2 * a * h + 2 * t + 1)) ≤
          2 * (a * (h * d + beta + h)) := by
      simpa [Nat.mul_assoc] using htarget'
    exact hgoal (Nat.le_of_mul_le_mul_left hcancel (by omega))

theorem quotient_separation (u v a q : ℕ) (hu : 0 < u) (hv : 0 < v)
    (ha : 0 < a) (hqodd : Odd q)
    (hPQ : (2 ^ v - 1) * q ≤ (2 ^ u - 1) * a) :
    2 ^ (v - 1) * q ≤
      a * ((2 ^ (u - 1) * a + (q - 1) / 2) / a) ∧
    a * ((2 ^ (u - 1) * a + (q - 1) / 2) / a) ≤
      2 ^ (u - 1) * a + (q - 1) / 2 := by
  refine ⟨?_, Nat.mul_div_le _ _⟩
  let x := 2 ^ (u - 1)
  let y := 2 ^ (v - 1)
  let d := 2 ^ v - 1
  let beta := if v = 1 then 1 else x % d
  let h := if v = 1 then x - 1 else x / d
  let n := ((q - 1) / 2) / a
  let t := ((q - 1) / 2) % a
  have hy : 0 < y := by positivity
  have hd : 0 < d := by
    dsimp [d]
    have hp : 1 < 2 ^ v := by
      have hpow : 2 ≤ 2 ^ v := by
        rw [show 2 = 2 ^ 1 by norm_num]
        exact Nat.pow_le_pow_right (by omega) hv
      omega
    omega
  have hdpow : d + 1 = 2 * y := by
    dsimp [d, y]
    calc
      2 ^ v - 1 + 1 = 2 ^ v := by
        apply Nat.sub_add_cancel
        have hpow : 0 < 2 ^ v := by positivity
        omega
      _ = 2 * 2 ^ (v - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hv]
  have hx : x = h * d + beta := by
    by_cases hv1 : v = 1
    · subst v
      simpa [h, beta, d] using
        (Nat.sub_add_cancel (by
          dsimp [x]
          have hpow : 0 < 2 ^ (u - 1) := by positivity
          omega)).symm
    · simp [h, beta, hv1]
      simpa [Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div x d).symm
  have hbeta : beta ≤ y := by
    by_cases hv1 : v = 1
    · subst v
      simp [d, beta, y]
    · have hr : (u - 1) % v < v := Nat.mod_lt _ hv
      have hmod : (2 ^ (u - 1) - 1) % (2 ^ v - 1) =
          2 ^ ((u - 1) % v) - 1 := by
        simpa using Nat.pow_sub_one_mod_pow_sub_one 2 v (u - 1)
      have hlt : 2 ^ ((u - 1) % v) < 2 ^ v - 1 := by
        have hrle : (u - 1) % v ≤ v - 1 := by omega
        have hpow : 2 ^ ((u - 1) % v) ≤ 2 ^ (v - 1) := by
          exact Nat.pow_le_pow_right (by omega) hrle
        have hvpow : 2 ^ v = 2 * 2 ^ (v - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hv]
        have hvminus : 1 ≤ v - 1 := by omega
        have hpow2 : 2 ≤ 2 ^ (v - 1) := by
          rw [show 2 = 2 ^ 1 by norm_num]
          exact Nat.pow_le_pow_right (by omega) hvminus
        have htwo : 2 ^ (v - 1) < 2 ^ v - 1 := by
          rw [hvpow]
          have : 0 < 2 ^ (v - 1) := by positivity
          omega
        omega
      have hrem : x % d = 2 ^ ((u - 1) % v) := by
        have hpos : 0 < 2 ^ (u - 1) := by positivity
        have hrewrite : 2 ^ (u - 1) = (2 ^ (u - 1) - 1) + 1 := by omega
        dsimp [x, d]
        rw [hrewrite, Nat.add_mod, hmod]
        have hd1 : 1 < 2 ^ v - 1 := by
          have : 0 < 2 ^ ((u - 1) % v) := by positivity
          omega
        have hd1 : 1 < 2 ^ v - 1 := by
          have hrpos : 0 < 2 ^ ((u - 1) % v) := by positivity
          omega
        have hone : 1 % (2 ^ v - 1) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [hone]
        have hs : 2 ^ ((u - 1) % v) - 1 + 1 =
            2 ^ ((u - 1) % v) := by
          apply Nat.sub_add_cancel
          have hpow : 0 < 2 ^ ((u - 1) % v) := by positivity
          omega
        rw [hs, Nat.mod_eq_of_lt hlt]
      simp only [beta, hv1, ↓reduceIte]
      change x % d ≤ y
      rw [hrem]
      dsimp [y]
      apply Nat.pow_le_pow_right (by omega)
      omega
  have hqhalf : q = 2 * ((q - 1) / 2) + 1 := by
    rcases hqodd with ⟨k, hk⟩
    have hkhalf : (q - 1) / 2 = k := by omega
    omega
  have hqt : q = 2 * a * n + 2 * t + 1 := by
    have hdiv0 : (q - 1) / 2 = a * n + t := by
      dsimp [n, t]
      simpa [Nat.add_comm, Nat.mul_comm] using
        (Nat.mod_add_div ((q - 1) / 2) a).symm
    rw [hqhalf, hdiv0]
    ring
  have ht : t < a := by dsimp [t]; exact Nat.mod_lt _ ha
  have hpowu : 2 ^ u = 2 * x := by
    dsimp [x]
    rw [← pow_succ', Nat.sub_add_cancel hu]
  have hQ : d * q ≤ (2 * x - 1) * a := by
    rw [hpowu] at hPQ
    simpa [d] using hPQ
  have hbetapos : 0 < beta := by
    by_cases hv1 : v = 1
    · simp [beta, hv1]
    · dsimp [beta]
      have hr : (u - 1) % v < v := Nat.mod_lt _ hv
      have hmod : (2 ^ (u - 1) - 1) % (2 ^ v - 1) =
          2 ^ ((u - 1) % v) - 1 := by
        simpa using Nat.pow_sub_one_mod_pow_sub_one 2 v (u - 1)
      have hlt : 2 ^ ((u - 1) % v) < 2 ^ v - 1 := by
        have hrle : (u - 1) % v ≤ v - 1 := by omega
        have hpow : 2 ^ ((u - 1) % v) ≤ 2 ^ (v - 1) := by
          exact Nat.pow_le_pow_right (by omega) hrle
        have hvpow : 2 ^ v = 2 * 2 ^ (v - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hv]
        have hvminus : 1 ≤ v - 1 := by omega
        have hpow2 : 2 ≤ 2 ^ (v - 1) := by
          rw [show 2 = 2 ^ 1 by norm_num]
          exact Nat.pow_le_pow_right (by omega) hvminus
        have htwo : 2 ^ (v - 1) < 2 ^ v - 1 := by
          rw [hvpow]
          have : 0 < 2 ^ (v - 1) := by positivity
          omega
        omega
      have hrem : x % d = 2 ^ ((u - 1) % v) := by
        have hpos : 0 < 2 ^ (u - 1) := by positivity
        have hrewrite : 2 ^ (u - 1) = (2 ^ (u - 1) - 1) + 1 := by omega
        dsimp [x, d]
        rw [hrewrite, Nat.add_mod, hmod]
        have hd1 : 1 < 2 ^ v - 1 := by
          have hrpos : 0 < 2 ^ ((u - 1) % v) := by positivity
          omega
        have hone : 1 % (2 ^ v - 1) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [hone]
        have hs : 2 ^ ((u - 1) % v) - 1 + 1 =
            2 ^ ((u - 1) % v) := by
          apply Nat.sub_add_cancel
          have hpow : 0 < 2 ^ ((u - 1) % v) := by positivity
          omega
        rw [hs, Nat.mod_eq_of_lt hlt]
      rw [hrem]
      positivity
  have hcore := quotient_core a q x y d h n beta t ha hy hd (by dsimp [x]; positivity)
    hdpow hx hbetapos hbeta
    hqt ht hQ
  have hdiv : (q - 1) / 2 = a * n + t := by
    simpa [Nat.add_comm, Nat.mul_comm] using
      (Nat.mod_add_div ((q - 1) / 2) a).symm
  have hnt : (a * n + t) / a = n := by
    apply Nat.div_eq_of_lt_le
    · simpa [Nat.mul_comm] using Nat.le_add_right (a * n) t
    · calc
        a * n + t < a * n + a := Nat.add_lt_add_left ht _
        _ = (n + 1) * a := by ring
  have hCdiv :
      (2 ^ (u - 1) * a + (q - 1) / 2) / a = 2 ^ (u - 1) + n := by
    rw [hdiv]
    rw [show 2 ^ (u - 1) * a = a * 2 ^ (u - 1) by ac_rfl]
    rw [Nat.add_comm (a * 2 ^ (u - 1)) (a * n + t)]
    rw [Nat.add_mul_div_left _ _ ha]
    rw [hnt]
    omega
  rw [hCdiv]
  simpa [x, y] using hcore

/-- The sign and position together identify the physical occurrence. -/
def occurrenceWeight {u v : ℕ} (a q : ℕ) : Fin u ⊕ Fin v → ℤ
  | .inl i => ((a * 2 ^ i.1 : ℕ) : ℤ)
  | .inr j => -((q * 2 ^ j.1 : ℕ) : ℤ)

/-- Selected positive labels followed by the actual top negative label. -/
def packetLabels {u v : ℕ} (hv : 0 < v) (order : List (Fin u)) :
    List (Fin u ⊕ Fin v) :=
  order.map Sum.inl ++ [Sum.inr ⟨v - 1, by omega⟩]

/-- Exact mass bounds, distinct physical labels, and every actual prefix. -/
def PrefixSelection (u v a q C : ℕ) (hu : 0 < u) (hv : 0 < v)
    (U : ℕ) (S : Finset (Fin u)) (order : List (Fin u)) : Prop :=
  max (2 ^ (u - 1) * a) (2 ^ (v - 1) * q) ≤ U ∧
  U ≤ min ((2 ^ u - 1) * a) C ∧
  (⟨u - 1, by omega⟩ ∈ S) ∧
  (∑ i ∈ S, a * 2 ^ i.1 = U) ∧
  order.Nodup ∧ order.toFinset = S ∧
  (∀ j, ((order.take j).map (fun i => a * 2 ^ i.1)).sum ≤ U) ∧
  (packetLabels hv order).Nodup ∧
  (∀ j, 0 ≤ (((packetLabels hv order).take j).map (occurrenceWeight a q)).sum ∧
    (((packetLabels hv order).take j).map (occurrenceWeight a q)).sum ≤ (C : ℤ)) ∧
  ((packetLabels hv order).map (occurrenceWeight a q)).sum =
    (U : ℤ) - ((2 ^ (v - 1) * q : ℕ) : ℤ) ∧
  U = min ((2 ^ u - 1) * a) (a * (C / a))

private theorem nat_prefix_sum_le (xs : List ℕ) (j : ℕ) :
    (xs.take j).sum ≤ xs.sum := by
  calc
    _ ≤ (xs.take j).sum + (xs.drop j).sum := Nat.le_add_right _ _
    _ = xs.sum := by rw [← List.sum_append, List.take_append_drop]

private theorem cast_weight_sum {u : ℕ} (a : ℕ) (xs : List (Fin u)) :
    (xs.map (fun i => ((a * 2 ^ i.1 : ℕ) : ℤ))).sum =
      (↑((xs.map (fun i => (a * 2 ^ i.1 : ℕ))).sum) : ℤ) := by
  induction xs with
  | nil => simp
  | cons i is ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      rw [ih]

/-- The arithmetic bound is realized by actual binary occurrence positions. -/
theorem occurrence_prefix (u v a q : ℕ) (hu : 0 < u) (hv : 0 < v)
    (ha : 0 < a) (hqodd : Odd q)
    (hPQ : (2 ^ v - 1) * q ≤ (2 ^ u - 1) * a) :
    ∃ U S order, PrefixSelection u v a q
      (2 ^ (u - 1) * a + (q - 1) / 2) hu hv U S order := by
  classical
  let L := 2 ^ (u - 1) * a
  let M := 2 ^ (v - 1) * q
  let C := L + (q - 1) / 2
  let P := (2 ^ u - 1) * a
  have hsep := (quotient_separation u v a q hu hv ha hqodd hPQ).1
  have hpowu : 2 ^ u = 2 * 2 ^ (u - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hu]
  have hxL : 2 ^ (u - 1) ≤ 2 ^ u - 1 := by
    rw [hpowu]
    have hp : 0 < 2 ^ (u - 1) := by positivity
    omega
  have hLCdiv : 2 ^ (u - 1) ≤ C / a := by
    apply (Nat.le_div_iff_mul_le ha).2
    dsimp [C, L]
    omega
  let x := min (2 ^ u - 1) (C / a)
  let U := a * x
  have hxlow : 2 ^ (u - 1) ≤ x := le_min hxL hLCdiv
  have hxhi : x < 2 ^ u :=
    lt_of_le_of_lt (min_le_left _ _) (Nat.sub_lt (by positivity) (by omega))
  have hUhi : U ≤ min P C := by
    apply le_min
    · simpa [U, x, P, Nat.mul_comm] using
        Nat.mul_le_mul_left a (min_le_left (2 ^ u - 1) (C / a))
    · exact (Nat.mul_le_mul_left a (min_le_right _ _)).trans (Nat.mul_div_le _ _)
  have hMleP : M ≤ P := by
    have hpowv : 2 ^ v = 2 * 2 ^ (v - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hv]
    have hp : 0 < 2 ^ (v - 1) := by positivity
    have hineq : 2 ^ (v - 1) ≤ 2 ^ v - 1 := by rw [hpowv]; omega
    exact (Nat.mul_le_mul_right q hineq).trans hPQ
  have hUlow : max L M ≤ U := by
    apply max_le
    · simpa [L, U, Nat.mul_comm] using Nat.mul_le_mul_left a hxlow
    · dsimp [U, x]
      rw [mul_min]
      apply le_min
      · simpa [P, Nat.mul_comm] using hMleP
      · exact hsep
  let S := bitSubset u x hxhi
  have hsum : ∑ i ∈ S, a * 2 ^ i.1 = U := weighted_bit_subset ha hxhi
  have htop : ⟨u - 1, by omega⟩ ∈ S := bit_subset_top_mem hu hxlow hxhi
  let order := S.toList
  have horder_sum : (order.map (fun i => a * 2 ^ i.1)).sum = U := by
    calc
      _ = ∑ i ∈ S, a * 2 ^ i.1 := by
        simpa [order] using S.sum_map_toList (fun i => a * 2 ^ i.1)
      _ = U := hsum
  have hprefix (j : ℕ) : ((order.take j).map (fun i => a * 2 ^ i.1)).sum ≤ U := by
    rw [← horder_sum]
    simpa using nat_prefix_sum_le (order.map (fun i => a * 2 ^ i.1)) j
  have hcast : (order.map (fun i => ((a * 2 ^ i.1 : ℕ) : ℤ))).sum = (U : ℤ) := by
    rw [cast_weight_sum, horder_sum]
  have hpacket_sum : ((packetLabels hv order).map (occurrenceWeight a q)).sum =
      (U : ℤ) - (M : ℤ) := by
    simp only [packetLabels, List.map_append, List.map_map, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, Function.comp_def, occurrenceWeight]
    rw [hcast]
    simp [M, Nat.mul_comm, sub_eq_add_neg]
  have hsafe (j : ℕ) :
      0 ≤ (((packetLabels hv order).take j).map (occurrenceWeight a q)).sum ∧
      (((packetLabels hv order).take j).map (occurrenceWeight a q)).sum ≤ (C : ℤ) := by
    by_cases hj : j ≤ order.length
    · have ht : (packetLabels hv order).take j = (order.take j).map Sum.inl := by
        dsimp [packetLabels]
        rw [List.take_append_of_le_length (by simpa using hj), List.map_take]
      rw [ht]
      simp only [List.map_map, Function.comp_def, occurrenceWeight]
      rw [cast_weight_sum]
      constructor
      · positivity
      · exact_mod_cast (hprefix j).trans (hUhi.trans (min_le_right _ _))
    · have hlen : (packetLabels hv order).length ≤ j := by
        simp only [packetLabels, List.length_append, List.length_map, List.length_singleton]
        omega
      rw [List.take_of_length_le hlen, hpacket_sum]
      have hm : M ≤ U := (le_max_right L M).trans hUlow
      have hc : U ≤ C := hUhi.trans (min_le_right _ _)
      constructor <;> omega
  refine ⟨U, S, order, hUlow, hUhi, htop, hsum, ?_, ?_, hprefix, ?_, hsafe,
    hpacket_sum, ?_⟩
  · exact S.nodup_toList
  · simp [order]
  · simp only [packetLabels, List.nodup_append]
    refine ⟨S.nodup_toList.map Sum.inl_injective, by simp, ?_⟩
    intro i hi j hj
    simp only [List.mem_map] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    simp only [List.mem_singleton] at hj
    subst j
    simp
  · change a * min (2 ^ u - 1) (C / a) =
      min ((2 ^ u - 1) * a) (a * (C / a))
    rw [mul_min, Nat.mul_comm a (2 ^ u - 1)]

/-- Original odd-capacity run equations supply every arithmetic hypothesis. -/
theorem two_run_prefix (u v a q b N C : ℕ) (hu : 0 < u) (hv : 0 < v)
    (ha : 0 < a) (hq : 0 < q) (hb : 0 < b) (hba : a ≤ b)
    (hN : N = 2 * C + 1)
    (h₁ : N = 2 ^ u * a + q) (h₂ : N = 2 ^ v * q + b) :
    Odd q ∧
    (((2 ^ u - 1) * a : ℕ) : ℤ) - (((2 ^ v - 1) * q : ℕ) : ℤ) = (b : ℤ) - a ∧
    (2 ^ v - 1) * q ≤ (2 ^ u - 1) * a ∧
    C = 2 ^ (u - 1) * a + (q - 1) / 2 ∧
    2 ^ (u - 1) * a ≤ C ∧ 2 ^ (v - 1) * q ≤ C ∧
    ∃ U S order, PrefixSelection u v a q C hu hv U S order := by
  have hpowu : 2 ^ u = 2 * 2 ^ (u - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hu]
  have hpowv : 2 ^ v = 2 * 2 ^ (v - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hv]
  have hqodd : Odd q := by
    apply Nat.odd_iff.mpr
    have hm := congrArg (fun n : ℕ => n % 2) (hN.symm.trans h₁)
    simpa [hpowu, Nat.add_mod, Nat.mul_mod] using hm.symm
  have hqhalf : q = 2 * ((q - 1) / 2) + 1 := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hC : C = 2 ^ (u - 1) * a + (q - 1) / 2 := by
    rw [hpowu] at h₁
    nlinarith [hN, hqhalf, h₁]
  have hsubu : (2 ^ u - 1) * a + a = 2 ^ u * a := by
    calc
      _ = (2 ^ u - 1 + 1) * a := by ring
      _ = _ := by rw [Nat.sub_add_cancel (Nat.one_le_two_pow : 1 ≤ 2 ^ u)]
  have hsubv : (2 ^ v - 1) * q + q = 2 ^ v * q := by
    calc
      _ = (2 ^ v - 1 + 1) * q := by ring
      _ = _ := by rw [Nat.sub_add_cancel (Nat.one_le_two_pow : 1 ≤ 2 ^ v)]
  have hbalance : (2 ^ u - 1) * a + a = (2 ^ v - 1) * q + b := by omega
  have hPQ : (2 ^ v - 1) * q ≤ (2 ^ u - 1) * a := by omega
  have hint : (((2 ^ u - 1) * a : ℕ) : ℤ) -
      (((2 ^ v - 1) * q : ℕ) : ℤ) = (b : ℤ) - a := by
    have he : (((2 ^ u - 1) * a : ℕ) : ℤ) + a =
        (((2 ^ v - 1) * q : ℕ) : ℤ) + b := by exact_mod_cast hbalance
    omega
  have hLC : 2 ^ (u - 1) * a ≤ C := by omega
  have hMC : 2 ^ (v - 1) * q ≤ C := by
    have hs := (quotient_separation u v a q hu hv ha hqodd hPQ)
    rw [← hC] at hs
    exact hs.1.trans hs.2
  refine ⟨hqodd, ?_, hPQ, hC, hLC, hMC, ?_⟩
  · exact hint
  · rw [hC]
    exact occurrence_prefix u v a q hu hv ha hqodd hPQ

end D5.S3.Combinatorics.Circle.DyadicPrefix
