/- GID: D5/S1/Words/Sumfree/StrictTwoSumfreePreperiodRefutation
   generality: I
   mirror-B: D5/B/S1/Words/Sumfree/StrictTwoSumfreePreperiodRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/Sumfree/StrictTwoSumfreePreperiodRefutation.claim; result=D5/S1/Words/Sumfree/StrictTwoSumfreePreperiodRefutation.result; claim=D5/S1/Words/Sumfree/StrictTwoSumfreePreperiodRefutation.claim
   digest: The strict greedy sequence with seeds 5 and 21 has no positive gap period after nine gaps. -/

set_option autoImplicit false
set_option warningAsError true

/-!
# The printed preperiod formula at seeds 5 and 21

Daan van Berkel and Wieb Bosma, arXiv:2609.18522v1, Introduction, Definition 8(e)
and (k1), and Conjecture 9. Trureturing issue #34312.
-/

namespace D5.S1.Words.Sumfree.StrictTwoSumfreePreperiodRefutation

/-- A candidate avoids sums of distinct entries in the prefix ending at index n+1. -/
private def Avoids (s : Nat → Nat) (n z : Nat) : Prop :=
  ¬ ∃ i j : Nat, i < j ∧ j ≤ n + 1 ∧ s i + s j = z

/-- The source recurrence with two prescribed seeds and the least admissible next entry. -/
private def SourceGreedy (f g : Nat) (s : Nat → Nat) : Prop :=
  s 0 = f ∧ s 1 = g ∧ (∀ n, s n < s (n + 1)) ∧
  ∀ n, Avoids s n (s (n + 2)) ∧
    ∀ z, s (n + 1) < z → Avoids s n z → s (n + 2) ≤ z

/-- Zero-based index n represents the source's difference at index n+1. -/
private def gap (s : Nat → Nat) (n : Nat) : Nat := s (n + 1) - s n

private def GapPeriodicFrom (s : Nat → Nat) (start period : Nat) : Prop :=
  ∀ n, start ≤ n → gap s n = gap s (n + period)

/-- Preperiod length is the least number of initial gaps that must be discarded. -/
private def HasGapPreperiod (s : Nat → Nat) (k : Nat) : Prop :=
  (∃ p, 0 < p ∧ GapPeriodicFrom s k p) ∧
    ∀ j, j < k → ¬ ∃ p, 0 < p ∧ GapPeriodicFrom s j p

/-- Definition 8(e) with correction (k1), for f ≥ 5, r = f+1 and h = 1. -/
private def definition8_e_k1 (f : Nat) : Nat :=
  (2 * f + 3) * 1 + (2 * f + 7) - (3 * f + (f + 1))

/-- The formula value at d = 21 - 5 = 6 + 1 * 10. -/
private def printedQ : Nat := definition8_e_k1 5

private theorem printedQ_eq9 : printedQ = 9 := by decide

/-- The specialization of Conjecture 9 using its displayed formula at f = 5, g = 21. -/
def claim : Prop :=
  ∀ s, SourceGreedy 5 21 s → HasGapPreperiod s printedQ

/-- The universal assertion of Conjecture 9, with Q denoting the Definition 8 function. -/
private def Conjecture9 (Q : Nat → Nat → Nat) : Prop :=
  ∀ f d, 0 < f → 0 < d → ∀ s, SourceGreedy f (f + d) s → HasGapPreperiod s (Q d f)

/-- The formula is required only on the Definition 8(e), (k1) branch used here. -/
private theorem full_conjecture_implies_claim {Q : Nat → Nat → Nat}
    (hfull : Conjecture9 Q)
    (hQ : ∀ f, 5 ≤ f → Q ((f + 1) + 1 * (2 * f)) f = definition8_e_k1 f) :
    claim := by
  intro s hs
  have hpre := hfull 5 16 (by decide) (by decide) s hs
  have hvalue : Q 16 5 = printedQ := hQ 5 (by decide)
  rwa [hvalue] at hpre

/-! ### Residue classification modulo 56 -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private def H : List Nat := [5,21,22,23,24,25,31,32,33,34,35,41,42,50,51]
private def B : List Nat := [61,70,78,79,80,87,88,89,90,97,98,106,107,116]
private def HB : List (Nat × Nat) := H.flatMap (fun h => B.map (fun b => (h,b)))
private def BB : List (Nat × Nat) := B.flatMap (fun b => B.map (fun c => (b,c)))
private def bRes (r : Nat) : Bool := B.any (fun b => decide (b % 56 = r))
private def pairRes (ps : List (Nat × Nat)) (r : Nat) : Bool :=
  ps.any (fun p => decide ((p.1+p.2) % 56 = r))
private def finitePartitionCert : Bool :=
  (List.range 56).all (fun r =>
    decide (bRes r = true ∨ pairRes HB r = true ∨ pairRes BB r = true))
private def finiteDisjointCert : Bool :=
  (List.range 56).all (fun r =>
    decide (bRes r = true → pairRes HB r = false ∧ pairRes BB r = false))
private theorem finite_partition_cert : finitePartitionCert = true := by decide
private theorem finite_disjoint_cert : finiteDisjointCert = true := by decide
private theorem partition (r : Nat) (hr : r < 56) :
    bRes r = true ∨ pairRes HB r = true ∨ pairRes BB r = true := by
  have hall : (List.range 56).all (fun r =>
      decide (bRes r = true ∨ pairRes HB r = true ∨ pairRes BB r = true)) = true := finite_partition_cert
  have hm : r ∈ List.range 56 := (List.mem_range.mpr hr)
  have hx := (List.all_eq_true.mp hall) r hm
  exact of_decide_eq_true hx
private theorem disjoint (r : Nat) (hr : r < 56) (hb : bRes r = true) :
    pairRes HB r = false ∧ pairRes BB r = false := by
  have hall : (List.range 56).all (fun r =>
      decide (bRes r = true → pairRes HB r = false ∧ pairRes BB r = false)) = true := finite_disjoint_cert
  have hm : r ∈ List.range 56 := (List.mem_range.mpr hr)
  have hx := (List.all_eq_true.mp hall) r hm
  exact (of_decide_eq_true hx) hb
private theorem hb_extract {r : Nat} (hh : pairRes HB r = true) :
    ∃ h b, h ∈ H ∧ b ∈ B ∧ (h+b) % 56 = r := by
  have hx := (List.any_eq_true.mp hh)
  rcases hx with ⟨p, hp, hv⟩
  have hmod : (p.1+p.2)%56 = r := of_decide_eq_true hv
  simp [HB] at hp
  rcases hp with ⟨h, hhmem, b, hbmem, rfl⟩
  exact ⟨h,b,hhmem,hbmem,hmod⟩
private theorem bb_extract {r : Nat} (hh : pairRes BB r = true) :
    ∃ b c, b ∈ B ∧ c ∈ B ∧ (b+c) % 56 = r := by
  have hx := (List.any_eq_true.mp hh)
  rcases hx with ⟨p, hp, hv⟩
  have hmod : (p.1+p.2)%56 = r := of_decide_eq_true hv
  simp [BB] at hp
  rcases hp with ⟨b, hbmem, c, hcmem, rfl⟩
  exact ⟨b,c,hbmem,hcmem,hmod⟩

private def inH (z : Nat) : Bool := H.any (fun h => decide (h = z))
private def inA (z : Nat) : Bool := inH z || (decide (61 ≤ z) && bRes (z % 56))
private theorem inA_h {h : Nat} (hm : h ∈ H) : inA h = true := by
  have hh : inH h = true := (List.any_eq_true.mpr ⟨h, hm, by simp⟩)
  simp [inA, hh]
private theorem inA_tail {b : Nat} (hm : b ∈ B) (t : Nat) : inA (b + 56*t) = true := by
  have hb : bRes (b % 56) = true := by
    apply List.any_eq_true.mpr
    exact ⟨b, hm, by simp⟩
  have hmod : (b + 56*t) % 56 = b % 56 := Nat.add_mul_mod_self_left b 56 t
  have hle0 : 61 ≤ b := by
    have hh := hm
    simp [B] at hh
    rcases hh with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst b <;> decide
  have hle : 61 ≤ b + 56*t := by
    exact Nat.le_trans hle0 (Nat.le_add_right b (56*t))
  simp [inA, hmod, hb, hle]

private theorem inA_iff {z : Nat} :
    inA z = true ↔ inH z = true ∨ (61 ≤ z ∧ bRes (z % 56) = true) := by
  simp [inA, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

private theorem inH_large_false {z : Nat} (hz : 288 ≤ z) : inH z = false := by
  have hn : ¬ inH z = true := by
    intro hh
    have hx := (List.any_eq_true.mp hh)
    rcases hx with ⟨h, hm, heq⟩
    have hev : h = z := of_decide_eq_true heq
    have hle : h ≤ 51 := by
      simp [H] at hm
      rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        subst h <;> decide
    have : z ≤ 51 := by simpa [hev] using hle
    exact (Nat.not_le_of_gt (by decide)) (Nat.le_trans hz this)
  exact Bool.eq_false_iff.mpr hn

private theorem large_inA_iff {z : Nat} (hz : 288 ≤ z) :
    inA z = true ↔ bRes (z % 56) = true := by
  have h61 : 61 ≤ z := Nat.le_trans (by decide) hz
  have hh := inH_large_false hz
  simp [inA, hh, h61]

private theorem memH_le {h : Nat} (hm : h ∈ H) : h ≤ 51 := by
  simp [H] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> decide

private theorem memB_ge {b : Nat} (hm : b ∈ B) : 61 ≤ b := by
  simp [B] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst b <;> decide

private def IsSum (z : Nat) : Prop :=
  ∃ x y, x < y ∧ inA x = true ∧ inA y = true ∧ x + y = z

private theorem hb_mark {h b r : Nat} (hh : h ∈ H) (hb : b ∈ B)
    (hm : (h+b)%56 = r) : pairRes HB r = true := by
  apply List.any_eq_true.mpr
  refine ⟨(h,b), ?_, ?_⟩
  · simp [HB, hh, hb]
  · exact of_decide_eq_true (by simpa using hm)

private theorem bb_mark {b c r : Nat} (hb : b ∈ B) (hc : c ∈ B)
    (hm : (b+c)%56 = r) : pairRes BB r = true := by
  apply List.any_eq_true.mpr
  refine ⟨(b,c), ?_, ?_⟩
  · simp [BB, hb, hc]
  · exact of_decide_eq_true (by simpa using hm)

private theorem sum_mod_hb {x y h b : Nat} (hx : x = h) (hy : y % 56 = b % 56) :
    (x+y)%56 = (h+b)%56 := by
  subst x
  calc
    (h+y)%56 = (h%56 + y%56)%56 := Nat.add_mod h y 56
    _ = (h%56 + b%56)%56 := by rw [hy]
    _ = (h+b)%56 := (Nat.add_mod h b 56).symm

private theorem sum_mod_bb {x y b c : Nat} (hx : x % 56 = b % 56) (hy : y % 56 = c % 56) :
    (x+y)%56 = (b+c)%56 := by
  calc
    (x+y)%56 = (x%56 + y%56)%56 := Nat.add_mod x y 56
    _ = (b%56 + c%56)%56 := by rw [hx,hy]
    _ = (b+c)%56 := (Nat.add_mod b c 56).symm

private theorem no_sum_large {z : Nat} (hz : 288 ≤ z) (ha : inA z = true) : ¬ IsSum z := by
  intro hs
  rcases hs with ⟨x,y,hxy,hx,hy,hxy_sum⟩
  have hzb : bRes (z%56) = true := (large_inA_iff hz).mp ha
  have hxi := (inA_iff.mp hx)
  have hyi := (inA_iff.mp hy)
  rcases hxi with hxh | hxt
  · rcases hyi with hyh | hyt
    · have hxl : x ≤ 51 := by
        rcases (List.any_eq_true.mp hxh) with ⟨h, hm, he⟩
        have : h=x := of_decide_eq_true he
        subst x
        exact memH_le hm
      have hyl : y ≤ 51 := by
        rcases (List.any_eq_true.mp hyh) with ⟨h, hm, he⟩
        have : h=y := of_decide_eq_true he
        subst y
        exact memH_le hm
      have hzle : z ≤ 102 := by
        rw [← hxy_sum]
        exact Nat.add_le_add hxl hyl
      exact (Nat.not_le_of_gt (by decide)) (Nat.le_trans hz hzle)
    · rcases (List.any_eq_true.mp hxh) with ⟨h, hhm, he⟩
      have hxeq : x = h := (of_decide_eq_true he).symm
      rcases hyt with ⟨hy61, hyr⟩
      rcases (List.any_eq_true.mp hyr) with ⟨b, hbm, hbe⟩
      have hyres : y%56 = b%56 := (of_decide_eq_true hbe).symm
      have hpair : pairRes HB (z%56) = true := by
        apply hb_mark hhm hbm
        rw [← hxy_sum]
        exact (sum_mod_hb hxeq hyres).symm
      have hdis := (disjoint (z%56) (Nat.mod_lt _ (by decide)) hzb).1
      exact (Bool.noConfusion (hdis ▸ hpair))
  · rcases hyi with hyh | hyt
    · rcases hxt with ⟨hx61, hxr⟩
      rcases (List.any_eq_true.mp hyh) with ⟨h, hhm, he⟩
      have hyeq : h = y := of_decide_eq_true he
      have hyl : y ≤ 51 := by subst y; exact memH_le hhm
      have hyx : y ≤ x := Nat.le_trans hyl (Nat.le_trans (by decide) hx61)
      exact (Nat.not_lt_of_ge hyx) hxy
    · rcases hxt with ⟨hx61, hxr⟩
      rcases hyt with ⟨hy61, hyr⟩
      rcases (List.any_eq_true.mp hxr) with ⟨b, hbm, hbe⟩
      rcases (List.any_eq_true.mp hyr) with ⟨c, hcm, hce⟩
      have hxres : x%56 = b%56 := (of_decide_eq_true hbe).symm
      have hyres : y%56 = c%56 := (of_decide_eq_true hce).symm
      have hpair : pairRes BB (z%56) = true := by
        apply bb_mark hbm hcm
        rw [← hxy_sum]
        exact (sum_mod_bb hxres hyres).symm
      have hdis := (disjoint (z%56) (Nat.mod_lt _ (by decide)) hzb).2
      exact (Bool.noConfusion (hdis ▸ hpair))

private theorem lift_sum {z s : Nat} (hs : s ≤ z) (hmod : z % 56 = s % 56) :
    ∃ t, z = s + 56*t := by
  let q := z / 56
  let k := s / 56
  have hq : k ≤ q := Nat.div_le_div_right hs
  have hmul : 56 * (q-k) = 56*q - 56*k := Nat.mul_sub_left_distrib 56 q k
  have hle : 56*k ≤ 56*q := Nat.mul_le_mul_left 56 hq
  have hadd : 56*k + 56*(q-k) = 56*q := by
    rw [hmul]
    exact Nat.add_sub_of_le hle
  refine ⟨q-k, ?_⟩
  calc
    z = z % 56 + 56 * q := by dsimp [q]; exact (Nat.mod_add_div z 56).symm
    _ = s % 56 + 56 * q := by rw [hmod]
    _ = s % 56 + (56*k + 56*(q-k)) := by rw [hadd]
    _ = (s % 56 + 56*k) + 56*(q-k) := by simp [Nat.add_assoc]
    _ = s + 56*(q-k) := by dsimp [k]; rw [Nat.mod_add_div]

private theorem memB_le {b : Nat} (hm : b ∈ B) : b ≤ 116 := by
  simp [B] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst b <;> decide

/-- Lift a residue-class witness. For two tail summands, the positive block shift
puts the second summand beyond the first block, ensuring distinctness. -/
private theorem sum_large {z : Nat} (hz : 288 ≤ z) (ha : inA z = false) : IsSum z := by
  have hbr : bRes (z%56) = false := by
    apply Bool.eq_false_iff.mpr
    intro hb
    have htrue : inA z = true := (large_inA_iff hz).mpr hb
    exact Bool.noConfusion (ha ▸ htrue)
  have part := partition (z%56) (Nat.mod_lt _ (by decide))
  rcases part with hb | hhb | hbb
  · exact False.elim (Bool.noConfusion (hbr ▸ hb))
  · rcases hb_extract hhb with ⟨h,b,hhm,hbm,hmod⟩
    have hsle : h+b ≤ z := by
      have hle : h+b ≤ 167 := Nat.add_le_add (memH_le hhm) (memB_le hbm)
      exact Nat.le_trans hle (Nat.le_trans (by decide) hz)
    have hlift := lift_sum hsle (hmod.symm)
    rcases hlift with ⟨t, ht⟩
    have hlt : h < b + 56*t := by
      have hbgt : 51 < b + 56*t :=
        Nat.lt_of_lt_of_le (by decide : 51 < 61)
          (Nat.le_trans (memB_ge hbm) (Nat.le_add_right b (56*t)))
      exact Nat.lt_of_le_of_lt (memH_le hhm) hbgt
    refine ⟨h, b+56*t, hlt, inA_h hhm, inA_tail hbm t, ?_⟩
    calc
      h + (b + 56*t) = h+b+56*t := by simp [Nat.add_assoc]
      _ = z := ht.symm
  · rcases bb_extract hbb with ⟨b,c,hbm,hcm,hmod⟩
    have hsle : b+c ≤ z := by
      have hle : b+c ≤ 232 := Nat.add_le_add (memB_le hbm) (memB_le hcm)
      exact Nat.le_trans hle (Nat.le_trans (by decide) hz)
    have hlift := lift_sum hsle (hmod.symm)
    rcases hlift with ⟨t, ht⟩
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · have hzle : z ≤ 232 := by
          rw [ht, ht0]
          exact Nat.add_le_add (memB_le hbm) (memB_le hcm)
        exact False.elim ((Nat.not_le_of_gt (by decide)) (Nat.le_trans hz hzle))
      · exact htpos
    have hlt : b < c + 56*t := by
      have hclow : 61 ≤ c := memB_ge hcm
      have hct : 56 ≤ 56*t := Nat.mul_le_mul_left 56 htpos
      have hbase : 117 ≤ c + 56 := Nat.le_trans (by decide) (Nat.add_le_add_right hclow 56)
      have hstep : c + 56 ≤ c + 56*t := Nat.add_le_add_left hct c
      have hy : 117 ≤ c + 56*t := Nat.le_trans hbase hstep
      exact Nat.lt_of_le_of_lt (memB_le hbm) (Nat.lt_of_lt_of_le (by decide : 116 < 117) hy)
    refine ⟨b, c+56*t, hlt, inA_tail hbm 0, inA_tail hcm t, ?_⟩
    calc
      b + (c + 56*t) = b+c+56*t := by simp [Nat.add_assoc]
      _ = z := ht.symm
private theorem tail_recurrence {z : Nat} (hz : 288 ≤ z) :
    inA z = true ↔ ¬ IsSum z := by
  constructor
  · intro ha
    exact no_sum_large hz ha
  · intro hn
    cases e : inA z with
    | false => exact False.elim (hn (sum_large hz e))
    | true => simp

/-! ### Kernel certificate for the greedy prefix through 288 -/

private def forbiddenIn (s : List Nat) (z : Nat) : Bool :=
  s.any (fun x => s.any (fun y => decide (x < y ∧ x+y = z)))
private def scanStep (z : Nat) (s : List Nat) : List Nat :=
  if z = 5 ∨ z = 21 then z :: s
  else if 21 < z ∧ forbiddenIn s z = false then z :: s
  else s
private def scan : Nat → List Nat
  | 0 => []
  | n+1 => scanStep n (scan n)

private def expected288 : List Nat :=
 [285,284,275,274,266,265,258,257,256,255,248,247,246,238,229,228,219,218,210,209,
 202,201,200,199,192,191,190,182,173,172,163,162,154,153,146,145,144,143,136,135,
 134,126,117,116,107,106,98,97,90,89,88,87,80,79,78,70,61,51,50,42,41,35,34,33,
 32,31,25,24,23,22,21,5]

private theorem scan_288 : scan 289 = expected288 := by decide

private def finiteMembershipCert : Bool :=
  (List.range 289).all (fun z => decide (z ∈ expected288 ↔ inA z = true))
private theorem finite_membership_cert : finiteMembershipCert = true := by decide

private theorem scanStep_mem_iff_of_lt {x z : Nat} {s : List Nat} (h : x < z) :
    x ∈ scanStep z s ↔ x ∈ s := by
  unfold scanStep
  split
  · simp [Nat.ne_of_lt h]
  · split <;> simp_all [Nat.ne_of_lt h]
private theorem scan_stable {n m x : Nat} (hn : n ≤ m) (hx : x < n) :
    (x ∈ scan n ↔ x ∈ scan m) := by
  induction hn with
  | refl => exact Iff.rfl
  | @step m hn ih =>
      rw [show scan (m+1) = scanStep m (scan m) by rfl]
      rw [scanStep_mem_iff_of_lt (Nat.lt_of_lt_of_le hx hn)]
      exact ih
private theorem finite_source_bridge {z : Nat} (hz : z < 289) :
    z ∈ scan (z+1) ↔ inA z = true := by
  have hs : z ∈ scan (z+1) ↔ z ∈ scan 289 :=
    scan_stable (Nat.succ_le_of_lt hz) (Nat.lt_succ_self z)
  rw [hs, scan_288]
  have hall : (List.range 289).all (fun z => decide (z ∈ expected288 ↔ inA z = true)) = true := finite_membership_cert
  have hm : z ∈ List.range 289 := List.mem_range.mpr hz
  have hx := (List.all_eq_true.mp hall) z hm
  exact of_decide_eq_true hx

/-- The explicit range is the finite head together with all translates of the first tail block. -/
private def A (z : Nat) : Prop := z ∈ H ∨ ∃ b t, b ∈ B ∧ z = b + 56*t

private theorem inA_iff_A {z : Nat} : inA z = true ↔ A z := by
  constructor
  · intro hz
    rcases (inA_iff.mp hz) with hh | ⟨hz61, hr⟩
    · rcases List.any_eq_true.mp hh with ⟨h, hm, he⟩
      have heq : h = z := of_decide_eq_true he
      exact Or.inl (by simpa [heq] using hm)
    · rcases List.any_eq_true.mp hr with ⟨b, hb, hbe⟩
      have hmod : z % 56 = b % 56 := (of_decide_eq_true hbe).symm
      have hle : b ≤ z := by
        have hbc := hb
        simp [B] at hbc
        rcases hbc with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
          subst b <;> omega
      rcases lift_sum hle hmod with ⟨t, ht⟩
      exact Or.inr ⟨b, t, hb, ht⟩
  · intro hz
    rcases hz with hm | ⟨b,t,hb,rfl⟩
    · exact inA_h hm
    · exact inA_tail hb t

private theorem f5_source_bridge :
    (∀ z, z < 289 → (z ∈ scan (z+1) ↔ A z)) ∧
    (∀ z, 288 ≤ z → (A z ↔ ¬ IsSum z)) := by
  constructor
  · intro z hz
    rw [finite_source_bridge hz]
    exact inA_iff_A
  · intro z hz
    rw [← inA_iff_A]
    exact tail_recurrence hz

private def IsSumA (z : Nat) : Prop :=
  ∃ x y, x < y ∧ A x ∧ A y ∧ x + y = z

private theorem isSumA_iff {z : Nat} : IsSumA z ↔ IsSum z := by
  constructor
  · rintro ⟨x,y,hxy,hx,hy,hs⟩
    exact ⟨x,y,hxy,(inA_iff_A.mpr hx),(inA_iff_A.mpr hy),hs⟩
  · rintro ⟨x,y,hxy,hx,hy,hs⟩
    exact ⟨x,y,hxy,(inA_iff_A.mp hx),(inA_iff_A.mp hy),hs⟩

private theorem f5_forced_seed_strict_rule :
    ∀ z, 22 ≤ z →
      ((z < 289 → (z ∈ scan (z+1) ↔ A z)) ∧
       (288 ≤ z → (A z ↔ ¬ IsSumA z))) := by
  intro z hz
  constructor
  · intro hsmall
    exact (f5_source_bridge.1 z hsmall)
  · intro hlarge
    rw [isSumA_iff]
    exact f5_source_bridge.2 z hlarge

/-! ### Ordered head and tail blocks -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def b : Nat → Nat
  | 0 => 61 | 1 => 70 | 2 => 78 | 3 => 79 | 4 => 80 | 5 => 87 | 6 => 88
  | 7 => 89 | 8 => 90 | 9 => 97 | 10 => 98 | 11 => 106 | 12 => 107 | 13 => 116
  | _ => 0

private def tailA (n : Nat) : Nat := b ((n-15) % 14) + 56 * ((n-15) / 14)

private theorem cases14 (r : Nat) (h : r < 14) :
    r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨
    r=8 ∨ r=9 ∨ r=10 ∨ r=11 ∨ r=12 ∨ r=13 := by omega

private theorem tail_gap_bound : ∀ n, 15 ≤ n → tailA (n+1) - tailA n ≤ 9 := by
  intro n hn
  let k := n - 15
  have hkn : n + 1 - 15 = k + 1 := by dsimp [k]; omega
  have hrem : k % 14 < 14 := by omega
  have hr : k % 14 = 0 ∨ k % 14 = 1 ∨ k % 14 = 2 ∨ k % 14 = 3 ∨ k % 14 = 4 ∨ k % 14 = 5 ∨ k % 14 = 6 ∨ k % 14 = 7 ∨ k % 14 = 8 ∨ k % 14 = 9 ∨ k % 14 = 10 ∨ k % 14 = 11 ∨ k % 14 = 12 ∨ k % 14 = 13 := cases14 _ hrem
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    first
    | have hnextrem : (k+1) % 14 = (k % 14) + 1 := by omega
      have hnextq : (k+1) / 14 = k / 14 := by omega
      dsimp [tailA]
      rw [hkn]
      change b ((k+1)%14) + 56*((k+1)/14) - (b (k%14) + 56*(k/14)) ≤ 9
      simp [h, hnextrem, hnextq, b]
      omega
    | have hnextrem : (k+1) % 14 = 0 := by omega
      have hnextq : (k+1) / 14 = k / 14 + 1 := by omega
      dsimp [tailA]
      rw [hkn]
      change b ((k+1)%14) + 56*((k+1)/14) - (b (k%14) + 56*(k/14)) ≤ 9
      simp [h, hnextrem, hnextq, b]
      omega
private def head : Nat → Nat
  | 0 => 5 | 1 => 21 | 2 => 22 | 3 => 23 | 4 => 24 | 5 => 25 | 6 => 31 | 7 => 32
  | 8 => 33 | 9 => 34 | 10 => 35 | 11 => 41 | 12 => 42 | 13 => 50 | 14 => 51
  | _ => 0

private def enumA (n : Nat) : Nat := if n < 15 then head n else tailA n

private theorem gap14 : gap enumA 14 = 10 := by decide

private theorem no_positive_gap_period
    {a : Nat → Nat} {p : Nat}
    (hp : 0 < p)
    (h10 : gap a 14 = 10)
    (hbound : ∀ n, 15 ≤ n → gap a n ≤ 9)
    (hper : ∀ z, 9 ≤ z → gap a z = gap a (z+p)) : False := by
  have hperiod := hper 14 (by omega)
  have hlater := hbound (14+p) (by omega)
  have hforced : gap a (14+p) = 10 := by
    calc
      gap a (14+p) = gap a 14 := hperiod.symm
      _ = 10 := h10
  omega

private theorem enumA_tail_gap : ∀ n, 15 ≤ n → gap enumA n = tailA (n+1) - tailA n := by
  intro n hn
  have h1 : ¬ n < 15 := by omega
  have h2 : ¬ n + 1 < 15 := by omega
  simp [gap, enumA, h1, h2]

private theorem enumA_gap_bound : ∀ n, 15 ≤ n → gap enumA n ≤ 9 := by
  intro n hn
  rw [enumA_tail_gap n hn]
  exact tail_gap_bound n hn

private theorem enumA_no_positive_gap_period {p : Nat}
    (hp : 0 < p)
    (hper : ∀ z, 9 ≤ z → gap enumA z = gap enumA (z+p)) : False := by
  exact no_positive_gap_period hp gap14 enumA_gap_bound hper

private theorem head_mem_H (r : Nat) (hr : r < 15) : head r ∈ H := by
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨
      r=8 ∨ r=9 ∨ r=10 ∨ r=11 ∨ r=12 ∨ r=13 ∨ r=14 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst r <;> simp [head, H]

private theorem b_mem_B (r : Nat) (hr : r < 14) : b r ∈ B := by
  have hc := cases14 r hr
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst r <;> simp [b, B]

private theorem b_surj {x : Nat} (hx : x ∈ B) : ∃ i, i < 14 ∧ b i = x := by
  simp [B] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst x; exact ⟨0, by decide, by decide⟩
  · subst x; exact ⟨1, by decide, by decide⟩
  · subst x; exact ⟨2, by decide, by decide⟩
  · subst x; exact ⟨3, by decide, by decide⟩
  · subst x; exact ⟨4, by decide, by decide⟩
  · subst x; exact ⟨5, by decide, by decide⟩
  · subst x; exact ⟨6, by decide, by decide⟩
  · subst x; exact ⟨7, by decide, by decide⟩
  · subst x; exact ⟨8, by decide, by decide⟩
  · subst x; exact ⟨9, by decide, by decide⟩
  · subst x; exact ⟨10, by decide, by decide⟩
  · subst x; exact ⟨11, by decide, by decide⟩
  · subst x; exact ⟨12, by decide, by decide⟩
  · subst x; exact ⟨13, by decide, by decide⟩

private theorem head_surj {x : Nat} (hx : x ∈ H) : ∃ i, i < 15 ∧ head i = x := by
  simp [H] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst x; exact ⟨0, by decide, by decide⟩
  · subst x; exact ⟨1, by decide, by decide⟩
  · subst x; exact ⟨2, by decide, by decide⟩
  · subst x; exact ⟨3, by decide, by decide⟩
  · subst x; exact ⟨4, by decide, by decide⟩
  · subst x; exact ⟨5, by decide, by decide⟩
  · subst x; exact ⟨6, by decide, by decide⟩
  · subst x; exact ⟨7, by decide, by decide⟩
  · subst x; exact ⟨8, by decide, by decide⟩
  · subst x; exact ⟨9, by decide, by decide⟩
  · subst x; exact ⟨10, by decide, by decide⟩
  · subst x; exact ⟨11, by decide, by decide⟩
  · subst x; exact ⟨12, by decide, by decide⟩
  · subst x; exact ⟨13, by decide, by decide⟩
  · subst x; exact ⟨14, by decide, by decide⟩

private theorem enumA_mem_A (n : Nat) : A (enumA n) := by
  by_cases hn : n < 15
  · have hm := head_mem_H n (by omega)
    exact Or.inl (by simpa [enumA, hn] using hm)
  · have hn15 : 15 ≤ n := by omega
    let k := n - 15
    have hr : k % 14 < 14 := Nat.mod_lt _ (by decide)
    have hbm := b_mem_B (k % 14) hr
    refine Or.inr ⟨b (k % 14), k / 14, hbm, ?_⟩
    simp [enumA, hn, tailA, k]

private theorem enumA_surjective {z : Nat} (hz : A z) : ∃ n, enumA n = z := by
  rcases hz with hm | ⟨x,t,hx,heq⟩
  · rcases head_surj hm with ⟨i,hi,hieq⟩
    exact ⟨i, by simp [enumA, hi, hieq]⟩
  · rcases b_surj hx with ⟨i,hi,hieq⟩
    refine ⟨15 + i + 14*t, ?_⟩
    have hsub : (15 + i + 14*t) - 15 = i + 14*t := by omega
    have hrem : (i + 14*t) % 14 = i := by omega
    have hdiv : (i + 14*t) / 14 = t := by omega
    have hn : ¬ (15 + i + 14*t < 15) := by omega
    rw [heq, ← hieq]
    simp [enumA, tailA, hsub, hrem, hdiv, hn, b]

private theorem tail_gap_pos : ∀ n, 15 ≤ n → 0 < tailA (n+1) - tailA n := by
  intro n hn
  let k := n - 15
  have hkn : n + 1 - 15 = k + 1 := by dsimp [k]; omega
  have hrem : k % 14 < 14 := by omega
  have hr : k % 14 = 0 ∨ k % 14 = 1 ∨ k % 14 = 2 ∨ k % 14 = 3 ∨ k % 14 = 4 ∨ k % 14 = 5 ∨ k % 14 = 6 ∨ k % 14 = 7 ∨ k % 14 = 8 ∨ k % 14 = 9 ∨ k % 14 = 10 ∨ k % 14 = 11 ∨ k % 14 = 12 ∨ k % 14 = 13 := cases14 _ hrem
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    first
    | have hnextrem : (k+1) % 14 = (k % 14) + 1 := by omega
      have hnextq : (k+1) / 14 = k / 14 := by omega
      dsimp [tailA]
      rw [hkn]
      change 0 < b ((k+1)%14) + 56*((k+1)/14) - (b (k%14) + 56*(k/14))
      simp [h, hnextrem, hnextq, b]
      omega
    | have hnextrem : (k+1) % 14 = 0 := by omega
      have hnextq : (k+1) / 14 = k / 14 + 1 := by omega
      dsimp [tailA]
      rw [hkn]
      change 0 < b ((k+1)%14) + 56*((k+1)/14) - (b (k%14) + 56*(k/14))
      simp [h, hnextrem, hnextq, b]
      omega

private theorem enumA_adjacent : ∀ n, enumA n < enumA (n+1) := by
  intro n
  by_cases hn : n < 14
  · have hc := cases14 n hn
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst n <;> decide
  · have hn14 : 14 ≤ n := by omega
    by_cases he : n = 14
    · subst n
      have h := gap14
      change enumA 15 - enumA 14 = 10 at h
      change enumA 14 < enumA 15
      omega
    · have hn15 : 15 ≤ n := by omega
      have hp := tail_gap_pos n hn15
      have heq := enumA_tail_gap n hn15
      have hgap : 0 < gap enumA n := by
        rw [heq]
        exact hp
      dsimp [gap] at hgap
      omega

private theorem printed_gap_period_impossible :
    ¬ ∃ p, 0 < p ∧ GapPeriodicFrom enumA printedQ p := by
  rw [printedQ_eq9]
  rintro ⟨p, hp, hper⟩
  exact enumA_no_positive_gap_period hp hper

/-! ### Identification with the source recurrence -/

private theorem scan_mem_lt {n x : Nat} (hx : x ∈ scan n) : x < n := by
  induction n with
  | zero => simp [scan] at hx
  | succ n ih =>
    change x ∈ scanStep n (scan n) at hx
    have fromCons (hm : x ∈ n :: scan n) : x < n + 1 := by
      rcases List.mem_cons.mp hm with he | hm
      · omega
      · exact Nat.lt_succ_of_lt (ih hm)
    unfold scanStep at hx
    split at hx
    · exact fromCons hx
    · split at hx
      · exact fromCons hx
      · exact Nat.lt_succ_of_lt (ih hx)

private theorem seed_membership {z : Nat} (hz : z ≤ 21) : A z ↔ z = 5 ∨ z = 21 := by
  constructor
  · intro hm
    rcases hm with hm | ⟨b, t, hb, he⟩
    · simp [H] at hm
      omega
    · have h := memB_ge hb
      omega
  · rintro (rfl | rfl) <;> exact Or.inl (by decide)

private theorem scan_prefix_iff {x z : Nat} (hx : x < z) (hz : z < 289) :
    x ∈ scan z ↔ A x :=
  (scan_stable (show x + 1 ≤ z from by omega) (Nat.lt_succ_self x)).symm.trans
    ((finite_source_bridge (show x < 289 from by omega)).trans inA_iff_A)

private theorem finite_sum_iff {z : Nat} (hz : z < 289) :
    forbiddenIn (scan z) z = true ↔ IsSumA z := by
  simp only [forbiddenIn, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, y, hy, hxy, hs⟩
    exact ⟨x, y, hxy, (scan_prefix_iff (scan_mem_lt hx) hz).mp hx,
      (scan_prefix_iff (scan_mem_lt hy) hz).mp hy, hs⟩
  · rintro ⟨x, y, hxy, hx, hy, hs⟩
    have hxz : x < z := by omega
    have hyz : y < z := by
      have hpos : 0 < x := by
        cases x with
        | zero =>
          have hseed := (seed_membership (by decide : 0 ≤ 21)).mp hx
          omega
        | succ x => exact Nat.zero_lt_succ x
      omega
    exact ⟨x, (scan_prefix_iff hxz hz).mpr hx, y, (scan_prefix_iff hyz hz).mpr hy, hxy, hs⟩

/-- The strict-sum recurrence at every integer above the second seed. -/
private theorem all_strict_rule {z : Nat} (hz : 21 < z) : A z ↔ ¬ IsSumA z := by
  have hrule := f5_forced_seed_strict_rule z (by omega)
  by_cases hlarge : 288 ≤ z
  · exact hrule.2 hlarge
  · have hsmall : z < 289 := by omega
    have hseed : ¬ (z = 5 ∨ z = 21) := by omega
    have hnot : z ∉ scan z := fun hm => Nat.lt_irrefl z (scan_mem_lt hm)
    have hstep : z ∈ scan (z+1) ↔ forbiddenIn (scan z) z = false := by
      change z ∈ scanStep z (scan z) ↔ _
      simp only [scanStep, hseed, ite_false, hz, true_and]
      split <;> simp_all
    exact (hrule.1 hsmall).symm.trans
      (hstep.trans (Bool.eq_false_iff.trans (not_congr (finite_sum_iff hsmall))))

private theorem outside_isSumA {z : Nat} (hz : 21 < z) (hnA : ¬ A z) : IsSumA z := by
  by_cases hlarge : 288 ≤ z
  · exact isSumA_iff.mpr (sum_large hlarge
      (Bool.eq_false_iff.mpr (fun ha => hnA (inA_iff_A.mp ha))))
  · have hsmall : z < 289 := by omega
    apply (finite_sum_iff hsmall).mp
    cases h : forbiddenIn (scan z) z with
    | true => rfl
    | false =>
      have hn : ¬ IsSumA z := fun hs => Bool.noConfusion
        (h.symm.trans ((finite_sum_iff hsmall).mpr hs))
      exact False.elim (hnA ((all_strict_rule hz).mpr hn))

private theorem increasing_of_adjacent {s : Nat → Nat} (hs : ∀ n, s n < s (n+1))
    {i j : Nat} (hij : i < j) : s i < s j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases he : i = j
    · simpa [he] using hs j
    · exact Nat.lt_trans (ih (by omega)) (hs j)

private theorem enumA_source_greedy : SourceGreedy 5 21 enumA := by
  refine ⟨by decide, by decide, enumA_adjacent, fun n => ⟨?_, ?_⟩⟩
  · rintro ⟨i, j, hij, _, hsum⟩
    have habove : 21 < enumA (n+2) := by
      have h := increasing_of_adjacent enumA_adjacent (show 1 < n+2 from by omega)
      change 21 < enumA (n+2) at h
      exact h
    exact (all_strict_rule habove).mp (enumA_mem_A _) ⟨enumA i, enumA j,
      increasing_of_adjacent enumA_adjacent hij, enumA_mem_A i, enumA_mem_A j, hsum⟩
  · intro z hz hav
    apply Nat.le_of_not_gt
    intro hnext
    have h21 : 21 ≤ enumA (n+1) := by
      cases n with
      | zero => decide
      | succ n =>
        have h := increasing_of_adjacent enumA_adjacent (show 1 < n+1+1 from by omega)
        change 21 < enumA (n+1+1) at h
        exact Nat.le_of_lt h
    have hbetween : ∀ i, z ≠ enumA i := by
      intro i he
      by_cases hi : i < n+1
      · have h := increasing_of_adjacent enumA_adjacent hi
        omega
      · by_cases hj : n+2 < i
        · have h := increasing_of_adjacent enumA_adjacent hj
          omega
        · have h : i = n+1 ∨ i = n+2 := by omega
          rcases h with rfl | rfl <;> omega
    have hnA : ¬ A z := fun hm => by
      obtain ⟨i, he⟩ := enumA_surjective hm
      exact hbetween i he.symm
    have hsum := outside_isSumA (show 21 < z from by omega) hnA
    obtain ⟨x, y, hxy, hx, hy, hs⟩ := hsum
    obtain ⟨i, rfl⟩ := enumA_surjective hx
    obtain ⟨j, rfl⟩ := enumA_surjective hy
    have hpos : 0 < enumA i := by
      cases i with
      | zero => decide
      | succ i =>
        have h := increasing_of_adjacent enumA_adjacent (Nat.zero_lt_succ i)
        change 5 < enumA (i+1) at h
        omega
    have hij : i < j := by
      apply Nat.lt_of_not_ge
      intro h
      rcases Nat.eq_or_lt_of_le h with rfl | h
      · exact Nat.lt_irrefl _ hxy
      · have h' := increasing_of_adjacent enumA_adjacent h
        omega
    have hprev : j ≤ n+1 := by
      apply Nat.le_of_not_gt
      intro h
      rcases Nat.eq_or_lt_of_le (show n+2 ≤ j from by omega) with rfl | h
      · omega
      · have h' := increasing_of_adjacent enumA_adjacent h
        omega
    exact hav ⟨i, j, hij, hprev, hs⟩

private theorem source_unique {s : Nat → Nat} (hs : SourceGreedy 5 21 s) : s = enumA := by
  funext k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => exact hs.1
    | succ k =>
      cases k with
      | zero => exact hs.2.1
      | succ n =>
        have hprefix (i : Nat) (hi : i ≤ n + 1) : s i = enumA i := ih i (by omega)
        have havoid (z : Nat) : Avoids s n z ↔ Avoids enumA n z := by
          unfold Avoids
          apply not_congr
          constructor
          · rintro ⟨i, j, hij, hj, hsum⟩
            exact ⟨i, j, hij, hj, by rwa [← hprefix i (by omega), ← hprefix j hj]⟩
          · rintro ⟨i, j, hij, hj, hsum⟩
            exact ⟨i, j, hij, hj, by rwa [hprefix i (by omega), hprefix j hj]⟩
        apply Nat.le_antisymm
        · apply (hs.2.2.2 n).2
          · rw [hprefix (n+1) (by omega)]
            exact enumA_adjacent (n+1)
          · exact (havoid _).mpr (enumA_source_greedy.2.2.2 n).1
        · apply (enumA_source_greedy.2.2.2 n).2
          · rw [← hprefix (n+1) (by omega)]
            exact hs.2.2.1 (n+1)
          · exact (havoid _).mp (hs.2.2.2 n).1

private theorem source_gap_refutation :
    ∀ s : Nat → Nat, SourceGreedy 5 21 s →
      ¬ ∃ p : Nat, 0 < p ∧ ∀ n, 9 ≤ n → gap s n = gap s (n+p) := by
  rintro s hs ⟨p, hp, hper⟩
  rw [source_unique hs] at hper
  apply printed_gap_period_impossible
  exact ⟨p, hp, fun n hn => hper n (printedQ_eq9 ▸ hn)⟩

/-- At gap 14 the difference is 10, while each subsequent gap is at most 9. -/
theorem result : Not claim := by
  intro hclaim
  have hpre := hclaim enumA enumA_source_greedy
  exact source_gap_refutation enumA enumA_source_greedy
    (printedQ_eq9 ▸ hpre.1)

end D5.S1.Words.Sumfree.StrictTwoSumfreePreperiodRefutation
