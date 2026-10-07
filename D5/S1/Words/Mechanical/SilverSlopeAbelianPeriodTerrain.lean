/- GID: D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodTerrain
   generality: I
   mirror-B: none(waiver:open-problem-stage-a)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Pell errors, approximation gaps, and convergent-period realisations. -/
/-
Judgement form:
  silver_q_realisation:
    proof_shape: content
    escape_witness: ∀ k, ∃ n i, 0<n ∧ minAbelianPeriod (lowerMechanicalFactor silverSlope 0 n
      i)=P (k + 1)
    Non-binding step: Constructs a factor with P(k+2)-1 blocks at arbitrary k and excludes
      every smaller period. No pinned factor/minimum-period theorem supplies this construction.
    Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
      (sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d);
      D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd
      (sha256:31fb069a0187ae500aa0a39e052a8deaceee7eb0f963bcc75879f9f575b26ff1);
      D5/S1/Words/Mechanical/MechanicalBalance
      (sha256:db7434e78bc669a2f0d5711175f8f744fc6dfba359dd5414cc8c05c753ad3399);
      D5/S1/Words/Mechanical/MechanicalFactorComplexity
      (sha256:9b83310d03f384fa38264d66462adfe64f238b0be826575d08630dad3141f15a)
admission_basis: escape-witness
Escape-audit registration is paused under CLAUDE.md §3.9.
-/
import D5.S1.Words.Mechanical.SilverSlopeAbelianPellArithmetic
import Mathlib.Data.Bool.Count
namespace D5.S1.Words.Mechanical
open D5.S1.Recurrence.PellCompanionGcd
open D5.S1.Words.Complexity
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
theorem silver_q_realisation (k : Nat) : ∃ n i, 0 < n ∧
    minAbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) = P (k + 1) := by
  have factor_count_true (n i : Nat) :
      (lowerMechanicalFactor silverSlope 0 n i).count true =
        lowerMechanicalWindowTrueCount silverSlope 0 i n := by
    classical
    have hof : lowerMechanicalFactor silverSlope 0 n i =
        (List.range n).map (fun j => lowerMechanicalWord silverSlope 0 (i+j)) := by
      unfold lowerMechanicalFactor
      rw [List.ofFn_eq_pmap]
      simp only [List.pmap_eq_map]
    rw [hof, List.count_eq_countP, List.countP_map]
    unfold lowerMechanicalWindowTrueCount
    rw [← List.toFinset_range]
    rw [List.Nodup.card_eq_countP List.nodup_range]
    congr 1
  have decomposition_error_bound (alpha rho : Real)
      (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) (n i m c : Nat)
      (head tail : List Bool) (blocks : List (List Bool))
      (hfactor : lowerMechanicalFactor alpha rho n i = head ++ blocks.flatten ++ tail)
      (hlengths : ∀ b ∈ blocks, b.length = m)
      (hcounts : ∀ b ∈ blocks, b.count true = c) :
      (blocks.length : Real) * |(m : Real) * alpha - c| < 1 := by
    have hlen : blocks.flatten.length = blocks.length * m := by
      rw [List.length_flatten, List.map_eq_replicate_iff.mpr hlengths, List.sum_replicate_nat]
    have hf_len := hlen
    have hn : n = head.length + blocks.length * m + tail.length := by
      have hh := congrArg List.length hfactor
      simpa [lowerMechanicalFactor, List.length_append, hf_len, Nat.add_assoc] using hh
    have hadd : ∀ a b j : Nat, lowerMechanicalFactor alpha rho (a + b) j =
        lowerMechanicalFactor alpha rho a j ++ lowerMechanicalFactor alpha rho b (j + a) := by
      intro a b j
      unfold lowerMechanicalFactor
      rw [List.ofFn_add]
      congr 1
      congr 1
      funext k
      congr 1
      simp [Nat.add_assoc]
    have hh : lowerMechanicalFactor alpha rho head.length i ++
        (lowerMechanicalFactor alpha rho (blocks.length * m) (i + head.length) ++
          lowerMechanicalFactor alpha rho tail.length (i + head.length + blocks.length * m)) =
        head ++ (blocks.flatten ++ tail) := by
      rw [← List.append_assoc, ← hadd]
      rw [show i + head.length + blocks.length * m = i + (head.length + blocks.length * m)
        by omega, ← hadd, ← hn]
      simpa [List.append_assoc] using hfactor
    have hrest := (List.append_inj hh (by simp [lowerMechanicalFactor])).2
    have hmiddle := (List.append_inj hrest (by simp [lowerMechanicalFactor, hf_len])).1
    have hbound  (alpha rho : Real)
      (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) (blocks : List (List Bool)) (m c i : Nat)
      (hfactor : blocks.flatten = lowerMechanicalFactor alpha rho (blocks.length * m) i)
      (hcounts : ∀ b ∈ blocks, b.count true = c) :
      (blocks.length : Real) * |(m : Real) * alpha - c| < 1 := by
      have htotal : blocks.flatten.count true = blocks.length * c := by
        rw [List.count_flatten, List.map_eq_replicate_iff.mpr hcounts, List.sum_replicate_nat]
      have hcount : ∀ n : Nat, (lowerMechanicalFactor alpha rho n i).count true =
          lowerMechanicalWindowTrueCount alpha rho i n := by
        intro n
        classical
        have hof : lowerMechanicalFactor alpha rho n i =
            (List.range n).map (fun j => lowerMechanicalWord alpha rho (i+j)) := by
          unfold lowerMechanicalFactor
          rw [List.ofFn_eq_pmap]
          simp only [List.pmap_eq_map]
        rw [hof, List.count_eq_countP, List.countP_map]
        unfold lowerMechanicalWindowTrueCount
        rw [← List.toFinset_range, List.Nodup.card_eq_countP List.nodup_range]
        congr 1
      have hc := htotal
      rw [hfactor, hcount] at hc
      have hfloor := lowerMechanicalWindowTrueCount_eq_floor (rho := rho) ha0 ha1 i (blocks.length * m)
      rw [hc] at hfloor
      have hr : (blocks.length : Real) * c =
          (⌊rho + ((i + blocks.length * m : Nat) : Real) * alpha⌋ : Real) -
            ⌊rho + (i : Real) * alpha⌋ := by exact_mod_cast hfloor
      have hrel : (blocks.length : Real) * ((m : Real) * alpha - c) =
          Int.fract (rho + ((i + blocks.length * m : Nat) : Real) * alpha) -
            Int.fract (rho + (i : Real) * alpha) := by
        unfold Int.fract
        push_cast at *
        nlinarith [hr]
      calc
        (blocks.length : Real) * |(m : Real) * alpha - c| =
            |(blocks.length : Real) * ((m : Real) * alpha - c)| := by
          rw [abs_mul, abs_of_nonneg (show (0 : Real) ≤ blocks.length from Nat.cast_nonneg _)]
        _ = |Int.fract (rho + ((i + blocks.length * m : Nat) : Real) * alpha) -
            Int.fract (rho + (i : Real) * alpha)| := by rw [hrel]
        _ < 1 := by
          apply abs_lt.mpr
          constructor <;> linarith [Int.fract_nonneg
              (rho + ((i + blocks.length * m : Nat) : Real) * alpha),
            Int.fract_lt_one (rho + ((i + blocks.length * m : Nat) : Real) * alpha),
            Int.fract_nonneg (rho + (i : Real) * alpha),
            Int.fract_lt_one (rho + (i : Real) * alpha)]
    exact hbound alpha rho ha0 ha1 blocks m c (i + head.length) hmiddle.symm hcounts

  have abelianPeriod_length {w : List Bool} (hw : 0 < w.length) :
      AbelianPeriod w w.length := by
    have emptyContained : ∀ p : Nat × Nat, 0 < p.1 + p.2 →
        (parikh []) < p := by
      intro p hp
      simp only [lt_iff_le_and_ne, Prod.le_def, and_assoc]
      refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩
      intro heq
      have hz : p.1 + p.2 = 0 := by
        simpa [parikh] using congrArg (fun z => z.1 + z.2) heq.symm
      omega
    have hsum : (parikh w).1 + (parikh w).2 = w.length := by
      change w.count false + w.count true = w.length
      exact List.count_false_add_count_true w
    have hpos : 0 < (parikh w).1 + (parikh w).2 := by omega
    refine ⟨hw, [], [], [w], ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · refine ⟨parikh w, ?_, ?_, ?_⟩
      · simp
      · exact emptyContained (parikh w) hpos
      · exact emptyContained (parikh w) hpos
  have parikh_length_lt {u : List Bool} {p : Nat × Nat} {m : Nat}
      (hp : (parikh u) < p)
      (hm : p.1 + p.2 = m) : u.length < m := by
    have hu : (parikh u).1 + (parikh u).2 = u.length := by
      change u.count false + u.count true = u.length
      exact List.count_false_add_count_true u
    simp only [lt_iff_le_and_ne, Prod.le_def, and_assoc] at hp
    rcases hp with ⟨h0, h1, hne⟩
    by_contra hn
    have hle : m ≤ u.length := by omega
    have heq0 : (parikh u).1 = p.1 := by omega
    have heq1 : (parikh u).2 = p.2 := by omega
    apply hne
    exact Prod.ext heq0 heq1
  have minAbelianPeriod_spec {w : List Bool} (hw : 0 < w.length) :
      AbelianPeriod w (minAbelianPeriod w) ∧
        ∀ m < minAbelianPeriod w, ¬ AbelianPeriod w m := by
    classical
    have hex : ∃ m, AbelianPeriod w m := ⟨w.length, abelianPeriod_length hw⟩
    rw [minAbelianPeriod]
    split
    · rename_i h
      exact ⟨Nat.find_spec h, fun m hm => Nat.find_min h hm⟩
    · rename_i h
      exact False.elim (h hex)
  have abelianPeriod_length_upper {w : List Bool} {m : Nat}
      (h : AbelianPeriod w m) :
      ∃ e : Nat, 0 < e ∧ w.length ≤ (e + 2) * m - 2 := by
    rcases h with ⟨hm, head, tail, blocks, hne, heq, hlen, hpar, hp⟩
    rcases hp with ⟨p, hbp, hhead, htail⟩
    have hp_len : p.1 + p.2 = m := by
      obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil blocks hne
      have hb_len := hlen b hb
      have hsum : (parikh b).1 + (parikh b).2 = b.length := by
        change b.count false + b.count true = b.length
        exact List.count_false_add_count_true b
      rw [hbp b hb] at hsum
      omega
    have hhead_len : head.length < m := parikh_length_lt hhead hp_len
    have htail_len : tail.length < m := parikh_length_lt htail hp_len
    have hblocks_len' : ∀ ls : List (List Bool),
        (∀ b ∈ ls, b.length = m) → ls.flatten.length = ls.length * m := by
      intro ls
      induction ls with
      | nil => simp
      | cons b bs ih =>
          intro hall
          have hb := hall b (by simp)
          have hrest : ∀ x ∈ bs, x.length = m := by
            intro x hx
            exact hall x (by simp [hx])
          have ih' := ih hrest
          simp only [List.flatten_cons, List.length_append, List.length_cons]
          rw [ih']
          rw [hb]
          simp [Nat.succ_mul, Nat.add_comm]
    have hblocks_len : blocks.flatten.length = blocks.length * m :=
      hblocks_len' blocks hlen
    have hblocks_pos : 0 < blocks.length := by
      apply Nat.pos_of_ne_zero
      intro hz
      apply hne
      exact List.eq_nil_of_length_eq_zero hz
    refine ⟨blocks.length, hblocks_pos, ?_⟩
    have hlen_eq := congrArg List.length heq
    simp only [List.length_append] at hlen_eq
    rw [hblocks_len] at hlen_eq
    rw [Nat.add_mul]
    have h2m : 2 ≤ 2 * m := by omega
    have hbig : 2 ≤ blocks.length * m + 2 * m :=
      h2m.trans (Nat.le_add_left _ _)
    omega
  have silverSlope_quadratic : silverSlope ^ 2 + 2 * silverSlope = 1 := by
    dsimp [silverSlope]
    have h : (Real.sqrt (2 : Real)) ^ 2 = 2 := by norm_num
    nlinarith
  have silverSlope_bounds : 0 ≤ silverSlope ∧ silverSlope < 1 := by
    dsimp [silverSlope]
    have hs : Real.sqrt (2 : Real) ^ 2 = 2 := by norm_num
    have hp : 0 < Real.sqrt (2 : Real) := Real.sqrt_pos.2 (by norm_num)
    constructor <;> nlinarith
  have silverSlope_lt_half : silverSlope < (1 / 2 : Real) := by
    dsimp [silverSlope]
    have hp : 0 < Real.sqrt (2 : Real) := Real.sqrt_pos.2 (by norm_num)
    have hs : (Real.sqrt (2 : Real)) ^ 2 = 2 := by norm_num
    have hp : 0 ≤ Real.sqrt (2 : Real) := Real.sqrt_nonneg _
    nlinarith
  have silverSlope_irrational : Irrational silverSlope := by
    simpa [silverSlope] using irrational_sqrt_two.sub_ratCast 1
  have silver_factor_complexity (n : Nat) :
      (lowerMechanicalFactorSet silverSlope 0 n).card = n + 1 := by
    exact lower_mechanical_factor_complexity
      silverSlope_bounds.1 silverSlope_bounds.2 silverSlope_irrational n
  have silver_sqrt_two_floor : ⌊Real.sqrt (2 : Real)⌋ = (1 : Int) := by
    have hs : (Real.sqrt (2 : Real)) ^ 2 = 2 := by norm_num
    have hsn : 0 ≤ Real.sqrt (2 : Real) := Real.sqrt_nonneg _
    rw [Int.floor_eq_iff]
    constructor <;> norm_num at *
  have silver_first_factor : lowerMechanicalFactor silverSlope 0 1 0 = [false] := by
    simp [lowerMechanicalFactor, lowerMechanicalWord,
      lowerMechanicalLetter, silverSlope, silver_sqrt_two_floor]
  have silver_base_period : AbelianPeriod [false] 1 := by
    refine ⟨by norm_num, [], [], [[false]], ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · refine ⟨(1, 0), ?_, ?_, ?_⟩
      · intro b hb
        simp at hb
        subst b
        rfl
      · norm_num [lt_iff_le_and_ne, Prod.le_def, and_assoc, parikh]
      · norm_num [lt_iff_le_and_ne, Prod.le_def, and_assoc, parikh]
  have silver_base_min_period : minAbelianPeriod [false] = 1 := by
    classical
    have hex : ∃ m, AbelianPeriod [false] m := ⟨1, silver_base_period⟩
    rw [minAbelianPeriod]
    split
    · rename_i h
      apply (Nat.find_eq_iff h).2
      constructor
      · exact silver_base_period
      · intro n hn
        have hn0 : n = 0 := by omega
        subst n
        simp [AbelianPeriod, AbelianDecomposition]
    · rename_i h
      exact False.elim (h hex)
  have silver_second_factor : lowerMechanicalFactor silverSlope 0 2 1 = [false, true] := by
    have hlow : (1 : Real) ≤ Real.sqrt 2 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have hupp : Real.sqrt 2 < (2 : Real) :=
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    have hmid : Real.sqrt 2 < (3 / 2 : Real) :=
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    have hlow4 : (4 / 3 : Real) ≤ Real.sqrt 2 := by
      rw [le_iff_lt_or_eq]
      left
      exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    have hupp5 : Real.sqrt 2 < (5 / 3 : Real) :=
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    have h1 : ⌊Real.sqrt (2 : Real) - 1⌋ = (0 : Int) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> nlinarith
    have h2 : ⌊2 * (Real.sqrt (2 : Real) - 1)⌋ = (0 : Int) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> nlinarith
    have h3 : ⌊3 * (Real.sqrt (2 : Real) - 1)⌋ = (1 : Int) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> nlinarith
    norm_num [lowerMechanicalFactor, lowerMechanicalWord,
      lowerMechanicalLetter, silverSlope, h1, h2, h3]
  have no_period_01 : ¬ AbelianPeriod [false, true] 1 := by
    intro h
    rcases h with ⟨hm, head, tail, blocks, hne, heq, hlen, heqpar, hp⟩
    rcases hp with ⟨p, hbp, hhead, htail⟩
    have hp_len : p.1 + p.2 = 1 := by
      obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil blocks hne
      have hb_len := hlen b hb
      have hsum : (parikh b).1 + (parikh b).2 = b.length := by
        change b.count false + b.count true = b.length
        exact List.count_false_add_count_true b
      rw [hbp b hb] at hsum
      omega
    have hheadlen := parikh_length_lt hhead hp_len
    have htaillen := parikh_length_lt htail hp_len
    have hheadnil : head = [] := by apply List.eq_nil_of_length_eq_zero; omega
    have htailnil : tail = [] := by apply List.eq_nil_of_length_eq_zero; omega
    subst head; subst tail
    have hflat : blocks.flatten = [false, true] := by simpa using heq.symm
    have hsum_one : ∀ ls : List (List Bool),
        (∀ b ∈ ls, b.length = 1) → (ls.map List.length).sum = ls.length := by
      intro ls
      induction ls with
      | nil => intro; simp
      | cons b bs ih =>
          intro hh
          have hb := hh b (by simp)
          have ih' := ih (by intro x hx; exact hh x (by simp [hx]))
          simp only [List.map, List.sum_cons, List.length_cons]
          omega
    have hsum := hsum_one blocks hlen
    have hflatlen : blocks.flatten.length = 2 := by rw [hflat]; rfl
    rw [List.length_flatten] at hflatlen
    have hblocks_len : blocks.length = 2 := by omega
    obtain ⟨b1, b2, hb12⟩ := (List.length_eq_two).mp hblocks_len
    subst blocks
    have hb1 := hlen b1 (by simp)
    have hb2 := hlen b2 (by simp)
    have hflat' : b1 ++ b2 = [false, true] := by simpa using hflat
    have hpar := heqpar b1 (by simp) b2 (by simp)
    cases b1 with
    | nil => simp at hb1
    | cons x xs =>
        have hxs : xs = [] := by simp at hb1; omega
        subst xs
        cases b2 with
        | nil => simp at hb2
        | cons y ys =>
            have hys : ys = [] := by simp at hb2; omega
            subst ys
            cases x <;> cases y <;> norm_num [parikh] at hpar <;> norm_num at hflat'
  have silver_period_01 : AbelianPeriod [false, true] 2 := by
    refine ⟨by norm_num, [], [], [[false, true]], ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · refine ⟨(1, 1), ?_, ?_, ?_⟩
      · intro b hb
        simp at hb
        subst b
        rfl
      · norm_num [lt_iff_le_and_ne, Prod.le_def, and_assoc, parikh]
      · norm_num [lt_iff_le_and_ne, Prod.le_def, and_assoc, parikh]
  have silver_min_period_01 : minAbelianPeriod [false, true] = 2 := by
    classical
    have hex : ∃ m, AbelianPeriod [false, true] m := ⟨2, silver_period_01⟩
    rw [minAbelianPeriod]
    split
    · rename_i h
      apply (Nat.find_eq_iff h).2
      constructor
      · exact silver_period_01
      · intro n hn
        have hn_cases : n = 0 ∨ n = 1 := by omega
        rcases hn_cases with rfl | rfl
        · simp [AbelianPeriod, AbelianDecomposition]
        · exact no_period_01
    · rename_i h
      exact False.elim (h hex)
  have silver_q0_witness : ∃ n i, 0 < n ∧
      minAbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) = P (0 + 1) := by
    refine ⟨1, 0, by norm_num, ?_⟩
    rw [silver_first_factor, silver_base_min_period]
    rfl
  have silver_q1_witness : ∃ n i, 0 < n ∧
      minAbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) = P (1 + 1) := by
    refine ⟨2, 1, by norm_num, ?_⟩
    rw [silver_second_factor, silver_min_period_01]
    rfl
  have silver_two_q0_witness : ∃ n i, 0 < n ∧
      minAbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) = 2 * P (0 + 1) := by
    simpa [P] using silver_q1_witness
  have silverSlope_cubic : silverSlope ^ 3 = 5 * silverSlope - 2 := by
    have hsq : silverSlope ^ 2 = 1 - 2 * silverSlope := by
      nlinarith [silverSlope_quadratic]
    calc
      silverSlope ^ 3 = silverSlope * silverSlope ^ 2 := by ring
      _ = silverSlope * (1 - 2 * silverSlope) := by rw [hsq]
      _ = 5 * silverSlope - 2 := by ring_nf; rw [hsq]; ring
  have silverPell_error_recurrence (k : Nat) :
      (P (k + 3) : Real) * silverSlope - P (k + 2) =
        silverSlope ^ 2 * ((P (k + 1) : Real) * silverSlope - P k) := by
    have hq : (P (k + 2) : Real) =
        2 * (P (k + 1) : Real) + P k := by
      exact_mod_cast (show P (k + 2) = 2 * P (k + 1) + P k from rfl)
    rw [show P (k + 3) = 2 * P (k + 2) + P (k + 1) by rfl]
    rw [show P (k + 2) = P (k + 2) by rfl]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [hq]
    ring_nf
    have hsq : silverSlope ^ 2 = 1 - 2 * silverSlope := by
      nlinarith [silverSlope_quadratic]
    rw [silverSlope_cubic, hsq]
    ring
  have silverPell_error_zero :
      (P (0 + 1) : Real) * silverSlope - P 0 = silverSlope := by
    norm_num [P, Nat.add_assoc]
  have silverPell_error_one :
      (P (1 + 1) : Real) * silverSlope - P 1 = -silverSlope ^ 2 := by
    norm_num [P, Nat.add_assoc]
    nlinarith [silverSlope_quadratic]
  have silverPell_error_abs (k : Nat) :
      |(P (k + 1) : Real) * silverSlope - P k| = silverSlope ^ (k + 1) := by
    rw [silverPell_error_formula, abs_mul]
    simp [abs_pow, abs_of_nonneg (pow_nonneg silverSlope_bounds.1 _)]
  have silverSlope_pos : 0 < silverSlope := by
    dsimp [silverSlope]
    have hs : (Real.sqrt (2 : Real)) ^ 2 = 2 := by norm_num
    have hp : 0 < Real.sqrt (2 : Real) := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  have silver_power_pos (k : Nat) : 0 < silverSlope ^ (k + 1) := by
    exact pow_pos silverSlope_pos (k + 1)
  have silver_power_lt_one (k : Nat) : silverSlope ^ (k + 1) < 1 := by
    apply pow_lt_one₀ silverSlope_bounds.1 silverSlope_bounds.2
    omega
  have silverPell_error_sign (k : Nat) :
      ((-1 : Real) ^ k) * silverSlope ^ (k + 1) =
        P (k + 1) * silverSlope - P k := by
    symm
    exact silverPell_error_formula k
  have silverPell_error_nonzero (k : Nat) :
      (P (k + 1) : Real) * silverSlope - P k ≠ 0 := by
    rw [silverPell_error_formula]
    apply mul_ne_zero
    · norm_num
    · exact ne_of_gt (silver_power_pos k)
  have silver_floor_q_even {k : Nat} (hk : Even k) :
      ⌊(P (k + 1) : Real) * silverSlope⌋ = (P k : Int) := by
    rw [Int.floor_eq_iff]
    have he := silverPell_error_formula k
    rw [hk.neg_one_pow] at he
    constructor <;> norm_num at * <;>
      nlinarith [silver_power_pos k, silver_power_lt_one k]
  have silver_floor_q_odd {k : Nat} (hk : Odd k) :
      ⌊(P (k + 1) : Real) * silverSlope⌋ = (P k : Int) - 1 := by
    rw [Int.floor_eq_iff]
    have he := silverPell_error_formula k
    rw [hk.neg_one_pow] at he
    constructor <;> norm_num at * <;>
      nlinarith [silver_power_pos k, silver_power_lt_one k]
  have silver_floor_mul_q_even {k j : Nat} (hk : Even k)
      (hj : (j : Real) * silverSlope ^ (k + 1) < 1) :
      ⌊((j * P (k + 1) : Nat) : Real) * silverSlope⌋ =
        (j * P k : Int) := by
    rw [Int.floor_eq_iff]
    have he := silverPell_error_formula k
    rw [hk.neg_one_pow] at he
    have he_mul := congrArg (fun x : Real => (j : Real) * x) he
    norm_num only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    constructor <;> norm_num at * <;>
      nlinarith [he_mul, silver_power_pos k, hj]
  have silver_floor_mul_q_odd {k j : Nat} (hk : Odd k)
      (hj : (j : Real) * silverSlope ^ (k + 1) < 1) :
      ⌊((j * P (k + 1) : Nat) : Real) * silverSlope⌋ =
        (j * P k : Int) - if j = 0 then 0 else 1 := by
    by_cases hj0 : j = 0
    · subst j
      simp
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      rw [Int.floor_eq_iff]
      have he := silverPell_error_formula k
      rw [hk.neg_one_pow] at he
      have he_mul := congrArg (fun x : Real => (j : Real) * x) he
      have hjr : (0 : Real) < j := by exact_mod_cast hjpos
      have hprod : 0 < (j : Real) * silverSlope ^ (k + 1) :=
        mul_pos hjr (silver_power_pos k)
      norm_num only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
      rw [if_neg hj0]
      constructor <;> norm_num at * <;>
        nlinarith [he_mul, hprod, hj]
  have lowerMechanicalFactor_succ (alpha rho : Real) (n i : Nat) :
      lowerMechanicalFactor alpha rho (n + 1) i =
        lowerMechanicalFactor alpha rho n i ++
          [lowerMechanicalWord alpha rho (i + n)] := by
    unfold lowerMechanicalFactor
    rw [List.ofFn_succ']
    simp
  have lowerMechanicalFactor_add (alpha rho : Real) (n m i : Nat) :
      lowerMechanicalFactor alpha rho (n + m) i =
        lowerMechanicalFactor alpha rho n i ++
          lowerMechanicalFactor alpha rho m (i + n) := by
    induction m with
    | zero => simp [lowerMechanicalFactor]
    | succ m ih =>
        rw [show n + (m + 1) = (n + m) + 1 by omega,
          lowerMechanicalFactor_succ, ih, lowerMechanicalFactor_succ]
        simp [Nat.add_assoc, List.append_assoc]
  have window_count_succ {alpha rho : Real} (i m : Nat) :
      lowerMechanicalWindowTrueCount alpha rho i (m + 1) =
        lowerMechanicalWindowTrueCount alpha rho i m +
          if lowerMechanicalWord alpha rho (i + m) = true then 1 else 0 := by
    classical
    unfold lowerMechanicalWindowTrueCount
    rw [Finset.range_add_one, Finset.filter_insert]
    have hm : m ∉ (Finset.range m).filter
        (fun k => lowerMechanicalWord alpha rho (i + k) = true) := by
      simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_irrefl, false_and,
        not_false_eq_true]
    by_cases h : lowerMechanicalWord alpha rho (i + m) = true
    · rw [if_pos h, Finset.card_insert_of_notMem hm, if_pos h]
    · rw [if_neg h, if_neg h, Nat.add_zero]
  have silver_even_q_block_count {k j : Nat} (hk : Even k)
      (hj : (j + 1 : Real) * silverSlope ^ (k + 1) < 1) :
      (lowerMechanicalFactor silverSlope 0 (P (k + 1)) (j * P (k + 1))).count true =
        P k := by
    have hj0 : (j : Real) * silverSlope ^ (k + 1) < 1 := by
      have hnonneg : 0 ≤ (j : Real) * silverSlope ^ (k + 1) :=
        mul_nonneg (Nat.cast_nonneg _) (le_of_lt (silver_power_pos k))
      nlinarith
    have hfloorj := silver_floor_mul_q_even (k := k) (j := j) hk hj0
    have hj' : ((j + 1 : Nat) : Real) * silverSlope ^ (k + 1) < 1 := by
      simpa using hj
    have hfloorj1 := silver_floor_mul_q_even (k := k) (j := j + 1) hk hj'
    have hc := factor_count_true (P (k + 1)) (j * P (k + 1))
    have hcI := congrArg (fun n : Nat => (n : Int)) hc
    rw [lowerMechanicalWindowTrueCount_eq_floor silverSlope_bounds.1 silverSlope_bounds.2] at hcI
    norm_num only [zero_add] at hcI
    norm_num only [Nat.cast_mul, Nat.cast_add, Int.cast_natCast] at hcI
    have hcastindex : (j : Real) * (P (k + 1) : Real) + P (k + 1) =
        (((j + 1) * P (k + 1) : Nat) : Real) := by
      push_cast
      ring
    rw [hcastindex] at hcI
    have hcastindex1 : (((j + 1) * P (k + 1) : Nat) : Real) =
        (j + 1 : Real) * P (k + 1) := by
      norm_num
    rw [hcastindex1] at hcI
    norm_num only [Nat.cast_mul] at hfloorj hfloorj1
    have hfloorj1' : ⌊((j : Real) + 1) * (P (k + 1) : Real) * silverSlope⌋ =
        ((j + 1 : Nat) * P k : Int) := by
      simpa [Nat.cast_add, Nat.cast_one, mul_assoc] using hfloorj1
    have hfloorj' : ⌊(j : Real) * (P (k + 1) : Real) * silverSlope⌋ =
        (j * P k : Int) := by
      simpa [Nat.cast_mul, mul_assoc] using hfloorj
    have hcI2 :
        (List.count true (lowerMechanicalFactor silverSlope 0 (P (k + 1)) (j * P (k + 1))) : Int) =
          ((j + 1 : Nat) * P k : Int) - (j * P k : Int) := by
      calc
        (List.count true (lowerMechanicalFactor silverSlope 0 (P (k + 1)) (j * P (k + 1))) : Int) =
            ⌊((j : Real) + 1) * (P (k + 1) : Real) * silverSlope⌋ -
              ⌊(j : Real) * (P (k + 1) : Real) * silverSlope⌋ := hcI
        _ = ((j + 1 : Nat) * P k : Int) - (j * P k : Int) := by
          rw [hfloorj1', hfloorj']
    have hnat : (j + 1) * P k - j * P k = P k := by
      rw [show j + 1 = Nat.succ j by omega, Nat.succ_mul]
      exact Nat.add_sub_cancel_left _ _
    have hcI3 := hcI2
    have hdiff : ((j + 1 : Nat) * P k : Int) - (j * P k : Int) =
        (P k : Int) := by
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hmul : (j : Int) * (P k : Int) + (P k : Int) =
          (j + 1 : Int) * (P k : Int) := by ring
      rw [← hmul]
      omega
    rw [hdiff] at hcI3
    exact_mod_cast hcI3
  have silver_odd_q_block_count {k j : Nat} (hk : Odd k) (hj : 0 < j)
      (hbound : (j + 1 : Real) * silverSlope ^ (k + 1) < 1) :
      (lowerMechanicalFactor silverSlope 0 (P (k + 1)) (j * P (k + 1))).count true =
        P k := by
    have hj0 : (j : Real) * silverSlope ^ (k + 1) < 1 := by
      have hnonneg : 0 ≤ (j : Real) * silverSlope ^ (k + 1) :=
        mul_nonneg (Nat.cast_nonneg _) (le_of_lt (silver_power_pos k))
      nlinarith
    have hfloorj := silver_floor_mul_q_odd (k := k) (j := j) hk hj0
    have hfloorj1 := silver_floor_mul_q_odd (k := k) (j := j + 1) hk (by simpa using hbound)
    have hc := factor_count_true (P (k + 1)) (j * P (k + 1))
    have hcI := congrArg (fun n : Nat => (n : Int)) hc
    rw [lowerMechanicalWindowTrueCount_eq_floor silverSlope_bounds.1 silverSlope_bounds.2] at hcI
    norm_num only [zero_add, Nat.cast_mul, Nat.cast_add, Int.cast_natCast] at hcI
    have hcast : (j : Real) * (P (k + 1) : Real) + P (k + 1) =
        ((j : Real) + 1) * (P (k + 1) : Real) := by ring
    rw [hcast] at hcI
    norm_num only [Nat.cast_mul] at hfloorj hfloorj1
    have hj' : 0 < j + 1 := by omega
    simp [Nat.ne_of_gt hj] at hfloorj
    simp [Nat.ne_of_gt hj'] at hfloorj1
    have hfloorj1' : ⌊((j : Real) + 1) * (P (k + 1) : Real) * silverSlope⌋ =
        ((j + 1 : Nat) * P k : Int) - 1 := by
      simpa [Nat.cast_add, Nat.cast_one, mul_assoc] using hfloorj1
    have hfloorj' : ⌊(j : Real) * (P (k + 1) : Real) * silverSlope⌋ =
        (j * P k : Int) - 1 := by
      simpa [Nat.cast_mul, mul_assoc] using hfloorj
    rw [hfloorj1', hfloorj'] at hcI
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcI
    have hmul : (j : Int) * (P k : Int) + (P k : Int) =
        (j + 1 : Int) * (P k : Int) := by ring
    rw [← hmul] at hcI
    have : (j + 1) * P k - j * P k = P k := by
      rw [show j + 1 = Nat.succ j by omega, Nat.succ_mul]
      exact Nat.add_sub_cancel_left _ _
    have hcI' : (List.count true (lowerMechanicalFactor silverSlope 0 (P (k + 1))
        (j * P (k + 1))) : Int) = (P k : Int) := by omega
    exact_mod_cast hcI'
  have silverSlope_gt_two_fifths : (2 / 5 : Real) < silverSlope := by
    dsimp [silverSlope]
    have hs : (7 / 5 : Real) < Real.sqrt 2 :=
      (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    nlinarith
  have silver_qnext_power_lt_one (k : Nat) :
      (P (k + 2) : Real) * silverSlope ^ (k + 1) < 1 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
        cases k with
        | zero =>
            norm_num [P]
            nlinarith [silverSlope_quadratic, silverSlope_lt_half]
        | succ k =>
            cases k with
            | zero =>
                norm_num [P]
                nlinarith [silverSlope_quadratic, silverSlope_lt_half,
                  silverSlope_gt_two_fifths]
            | succ k =>
                have hk1 := ih (k + 1) (by omega)
                have hk0 := ih k (by omega)
                rw [show P (k + 1 + 1 + 1 + 1) =
                  2 * P (k + 1 + 1 + 1) + P (k + 2) by rfl]
                have hrec :
                    (2 * (P (k + 1 + 1 + 1) : Real) + P (k + 2)) *
                        silverSlope ^ (k + 1 + 1 + 1) =
                      2 * silverSlope *
                          ((P (k + 1 + 1 + 1) : Real) * silverSlope ^ (k + 1 + 1)) +
                        silverSlope ^ 2 *
                          ((P (k + 2) : Real) * silverSlope ^ (k + 1)) := by
                  rw [pow_succ, pow_succ]
                  ring
                have hcastrec :
                    ((2 * P (k + 1 + 1 + 1) + P (k + 2) : Nat) : Real) =
                      2 * (P (k + 1 + 1 + 1) : Real) + P (k + 2) := by
                  norm_num
                rw [hcastrec, hrec]
                nlinarith [silverSlope_quadratic, silverSlope_pos]
  classical
  by_cases hk0 : k = 0
  · subst k
    exact silver_q0_witness
  have hk : 1 ≤ k := by omega
  let q := P (k + 1)
  let r := P k
  let E := P (k + 2) - 1
  let n := E * q
  let blocks : List (List Bool) := List.ofFn fun j : Fin E =>
    lowerMechanicalFactor silverSlope 0 q ((j + 1) * q)
  have hq : 0 < q := (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : 0 < P (k + 1))
  have hrq : r < q := (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : P k < P (k + 1))
  have hqn : q < P (k + 2) := by
    simpa [Nat.add_assoc, q] using (by have hs := (pell_companion_step (k + 1)).1; obtain ⟨j, hj⟩ := companion_odd (k + 1); omega : P (k + 1) < P (k + 1 + 1))
  have hE : 0 < E := by dsimp [E]; omega
  have hn : 0 < n := Nat.mul_pos hE hq
  have hflat : lowerMechanicalFactor silverSlope 0 n q = blocks.flatten := by
    dsimp [lowerMechanicalFactor, n, blocks]
    rw [List.ofFn_mul]
    congr 1
    congr 1
    funext j
    congr 1
    funext t
    congr 1
    simp only [Fin.val_mk]
    ring
  have hlengths : ∀ b ∈ blocks, b.length = q := by
    intro b hb
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    simp [lowerMechanicalFactor]
  have hcounts : ∀ b ∈ blocks, b.count true = r := by
    intro b hb
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    have hj : j.val + 2 ≤ P (k + 2) := by
      have hj := j.isLt
      dsimp [E] at hj
      omega
    have hjR : (j.val + 2 : Real) ≤ P (k + 2) := by exact_mod_cast hj
    have hbound : (j.val + 1 + 1 : Real) * silverSlope ^ (k + 1) < 1 := by
      have hh := mul_le_mul_of_nonneg_right hjR (le_of_lt (silver_power_pos k))
      linarith [silver_qnext_power_lt_one k]
    rcases Nat.even_or_odd k with heven | hodd
    · exact silver_even_q_block_count heven (by simpa using hbound)
    · exact silver_odd_q_block_count hodd (by omega) (by simpa using hbound)
  have hpar : ∀ b ∈ blocks, parikh b = (q - r, r) := by
    intro b hb
    have hb0 := List.count_false_add_count_true b
    have hb1 := hcounts b hb
    have hb2 := hlengths b hb
    apply Prod.ext
    · change b.count false = q - r
      omega
    · exact hb1
  have hempty : (parikh []) < (q - r, r) := by
    simp only [parikh, List.count_nil, lt_iff_le_and_ne, Prod.le_def, and_assoc, Prod.mk_le_mk]
    refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩
    intro heq
    have hf := congrArg Prod.fst heq
    have ht := congrArg Prod.snd heq
    simp only [Prod.fst, Prod.snd] at hf ht
    omega
  have hp : AbelianPeriod (lowerMechanicalFactor silverSlope 0 n q) q := by
    refine ⟨hq, [], [], blocks, ?_, ?_, hlengths, ?_, ?_⟩
    · intro hz
      have hl := congrArg List.length hz
      simp [blocks] at hl
      omega
    · simpa using hflat
    · intro a ha b hb
      rw [hpar a ha, hpar b hb]
    · exact ⟨(q - r, r), hpar, hempty, hempty⟩
  have herrlower : 1 ≤ (q + r : Nat) * silverSlope ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have heq := silverPell_error_formula (j + 1)
    have heprev := silverPell_error_formula j
    have hdet := silverPell_determinant j
    have hdetR : (P (j + 2) : Real) * P j -
        (P (j + 1) : Real) ^ 2 = (-1 : Real) ^ (j + 1) := by exact_mod_cast hdet
    have hsum : (P (j + 2) : Real) * silverSlope ^ (j + 1) +
        (P (j + 1) : Real) * silverSlope ^ (j + 2) = 1 := by
      rcases Nat.even_or_odd j with hj | hj
      · rw [hj.neg_one_pow] at heprev
        rw [(hj.add_odd odd_one).neg_one_pow] at heq hdetR
        simp only [Nat.add_assoc] at heq
        nlinarith [heq, heprev, hdetR]
      · rw [hj.neg_one_pow] at heprev
        rw [(hj.add_odd odd_one).neg_one_pow] at heq hdetR
        simp only [Nat.add_assoc] at heq
        nlinarith [heq, heprev, hdetR]
    dsimp [q, r]
    simp only [Nat.add_assoc, Nat.cast_add]
    have hpow : silverSlope ^ (j + 2) ≤ silverSlope ^ (j + 1) := by
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      nlinarith [silver_power_pos j, silverSlope_bounds.2]
    nlinarith [show (0 : Real) ≤ P (j + 1) from Nat.cast_nonneg _]
  have hex : ∃ m, AbelianPeriod (lowerMechanicalFactor silverSlope 0 n q) m := ⟨q, hp⟩
  refine ⟨n, q, hn, ?_⟩
  rw [minAbelianPeriod]
  split
  · rename_i h
    apply (Nat.find_eq_iff h).2
    refine ⟨hp, ?_⟩
    intro m hmq hmperiod
    rcases hmperiod with ⟨hm, head, tail, bs, hne, heq, hlen, hpar, p, hbp, hhead, htail⟩
    have hp_len : p.1 + p.2 = m := by
      obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil bs hne
      have hh := List.count_false_add_count_true b
      have hb0 := hlen b hb
      have hb1 := hbp b hb
      change b.count false + b.count true = b.length at hh
      have hf := congrArg Prod.fst hb1
      have ht := congrArg Prod.snd hb1
      simp only [parikh, Prod.fst, Prod.snd] at hf ht
      omega
    have hheadlen := parikh_length_lt hhead hp_len
    have htaillen := parikh_length_lt htail hp_len
    have herror := decomposition_error_bound silverSlope 0
      silverSlope_bounds.1 silverSlope_bounds.2 n q m p.2 head tail bs
      (by simpa [lowerMechanicalFactor] using heq) hlen (by
        intro b hb
        simpa [parikh] using congrArg Prod.snd (hbp b hb))
    have hbest : silverSlope ^ k ≤ |(m : Real) * silverSlope - p.2| := by
      have hh := silver_best_approximation (k - 1) m hm (by
        simpa [show k - 1 + 2 = k + 1 by omega, q] using hmq) (p.2 : Int)
      simpa [show k - 1 + 1 = k by omega] using hh
    have he_small : bs.length < q + r := by
      by_contra hh
      have hhR : ((q + r : Nat) : Real) ≤ bs.length := by exact_mod_cast (show q+r ≤ bs.length by omega)
      have hh1 := mul_le_mul_of_nonneg_right hhR (le_of_lt (pow_pos silverSlope_pos k))
      have hh2 := mul_le_mul_of_nonneg_left hbest (Nat.cast_nonneg bs.length)
      linarith [herrlower]
    have hlenflat : bs.flatten.length = bs.length * m := by
      have hh : ∀ ls : List (List Bool), (∀ b ∈ ls, b.length = m) → ls.flatten.length = ls.length * m := by
        intro ls
        induction ls with
        | nil => simp
        | cons b ls ih =>
            intro hall
            have hb := hall b (by simp)
            have ht := ih (fun v hv => hall v (by simp [hv]))
            simp [List.flatten_cons, List.length_append, hb, ht, Nat.succ_mul, Nat.add_comm]
      exact hh bs hlen
    have hwordlen : n = head.length + bs.length * m + tail.length := by
      have hh := congrArg List.length heq
      simpa [lowerMechanicalFactor, List.length_append, hlenflat, Nat.add_assoc] using hh
    have he2 : bs.length + 2 ≤ q + r + 1 := by omega
    have hm2 : m ≤ q - 1 := by omega
    have hmul := Nat.mul_le_mul he2 hm2
    have hqnext : P (k + 2) = 2*q+r := (show P (k + 2) = 2 * P (k + 1) + P k from rfl)
    have hEeq : E + 1 = 2*q+r := by dsimp [E]; omega
    have hn_eq : n = E*q := rfl
    nlinarith [Nat.sub_add_cancel (show 1 ≤ q by omega)]
  · rename_i h
    exact False.elim (h hex)
#print axioms silver_q_realisation
end D5.S1.Words.Mechanical
