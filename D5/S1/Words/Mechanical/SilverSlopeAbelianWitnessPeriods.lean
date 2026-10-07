/- GID: D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessPeriods
   generality: I
   mirror-B: none(waiver:open-problem-stage-a)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Uniform head, block, and tail counts for the two silver witness families. -/
/-
Judgement form:
  silver_w2_period:
    proof_shape: content
    escape_witness: silverPell_error_formula k: (P (k + 1) : Real)*silverSlope-P k=(-1
      : Real)^k*silverSlope^(k+1)
    Non-binding step: The identity is live in hcount_data, which computes the head,
      every interior block, and tail counts for arbitrary k. No frozen/upstream W2 count
      construction was found.
    Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
      (sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d);
      D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd
      (sha256:31fb069a0187ae500aa0a39e052a8deaceee7eb0f963bcc75879f9f575b26ff1);
      D5/S1/Words/Mechanical/MechanicalBalance
      (sha256:db7434e78bc669a2f0d5711175f8f744fc6dfba359dd5414cc8c05c753ad3399);
      D5/S1/Words/Mechanical/MechanicalFactorComplexity
      (sha256:9b83310d03f384fa38264d66462adfe64f238b0be826575d08630dad3141f15a)
  silver_wr_period:
    proof_shape: content
    escape_witness: silverPell_error_formula k: (P (k + 1) : Real)*silverSlope-P k=(-1
      : Real)^k*silverSlope^(k+1)
    Non-binding step: Its live signed identity yields the parity-dependent uniform block counts
       then the actual decomposition. No existing Wr construction was found.
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
theorem silver_w2_period (k : Nat) (hk : 1 ≤ k) :
    AbelianPeriod (lowerMechanicalFactor silverSlope 0
      (2 * P (k + 1) * (P (k + 1) + P k) + P (k + 1) - 1)
      (2 * P (k + 1) + P k)) (2 * P (k + 1)) := by
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
  have period_of_counts (h e l m c i : Nat) (hm : 0 < m) (he : 0 < e)
      (hc : c ≤ m) (hh : h < m) (hl : l < m)
      (hb : ∀ j < e, (lowerMechanicalFactor silverSlope 0 m (i + h + j * m)).count true = c)
      (hhc : (lowerMechanicalFactor silverSlope 0 h i).count true ≤ c)
      (hhf : h - (lowerMechanicalFactor silverSlope 0 h i).count true ≤ m - c)
      (hlc : (lowerMechanicalFactor silverSlope 0 l (i + h + e * m)).count true ≤ c)
      (hlf : l - (lowerMechanicalFactor silverSlope 0 l (i + h + e * m)).count true ≤ m - c) :
      AbelianPeriod (lowerMechanicalFactor silverSlope 0 (h + e * m + l) i) m := by
    classical
    have lowerMechanicalFactor_add : ∀ n m i : Nat,
        lowerMechanicalFactor silverSlope 0 (n+m) i =
          lowerMechanicalFactor silverSlope 0 n i ++ lowerMechanicalFactor silverSlope 0 m (i+n) := by
      intro n m i
      unfold lowerMechanicalFactor
      rw [List.ofFn_add]
      congr 1
      congr 1
      funext j
      congr 1
      simp [Nat.add_assoc]
    let blocks : List (List Bool) := List.ofFn fun j : Fin e =>
      lowerMechanicalFactor silverSlope 0 m (i + h + j * m)
    have hflat : blocks.flatten = lowerMechanicalFactor silverSlope 0 (e * m) (i + h) := by
      dsimp [blocks, lowerMechanicalFactor]
      rw [List.ofFn_mul]
      congr 1
      congr 1
      funext j
      congr 1
      funext t
      congr 1
      simp
      ring
    have hbp : ∀ b ∈ blocks, parikh b = (m-c,c) := by
      intro b hbmem
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hbmem
      have hbc := hb j.val j.isLt
      have hlen : (lowerMechanicalFactor silverSlope 0 m (i+h+j.val*m)).length = m := by
        simp [lowerMechanicalFactor]
      have hsum := List.count_false_add_count_true
        (lowerMechanicalFactor silverSlope 0 m (i+h+j.val*m))
      apply Prod.ext
      · simp only [parikh, Prod.fst]
        omega
      · exact hbc
    have hcontained : ∀ a : Nat, ∀ v : List Bool, v.length = a → a < m →
        v.count true ≤ c → a - v.count true ≤ m-c →
        (parikh v) < (m-c,c) := by
      intro a v hva ham hvc hvf
      have hs := List.count_false_add_count_true v
      simp only [lt_iff_le_and_ne, Prod.le_def, and_assoc]
      refine ⟨?_,hvc,?_⟩
      · change v.count false ≤ m-c
        omega
      · intro heq
        have hf := congrArg Prod.fst heq
        have ht := congrArg Prod.snd heq
        simp only [parikh, Prod.fst, Prod.snd] at hf ht
        omega
    refine ⟨hm,lowerMechanicalFactor silverSlope 0 h i,
      lowerMechanicalFactor silverSlope 0 l (i+h+e*m),blocks,?_,?_,?_,?_,?_⟩
    · intro hz
      have hs := congrArg List.length hz
      simp [blocks] at hs
      omega
    · rw [lowerMechanicalFactor_add, lowerMechanicalFactor_add]
      change blocks.flatten = lowerMechanicalFactor silverSlope 0 (e * m) (i + h) at hflat
      rw [← hflat]
      simp [Nat.add_assoc]
    · intro b hbmem
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hbmem
      simp [lowerMechanicalFactor]
    · intro a ha b hbmem
      rw [hbp a ha,hbp b hbmem]
    · refine ⟨(m-c,c),hbp,?_,?_⟩
      · exact hcontained h _ (by simp [lowerMechanicalFactor]) hh hhc hhf
      · exact hcontained l _ (by simp [lowerMechanicalFactor]) hl hlc hlf

  let q := P (k + 1)
  let t := P k
  let r := q+t
  let Q := 2*q+t
  let a := silverSlope
  let d := a^(k+1)
  have hquadratic : a^2+2*a=1 := by
    dsimp only [a,silverSlope]
    have hsq : (Real.sqrt (2:Real))^2=2 := by norm_num
    nlinarith
  have ha0 : 0 < a := by
    have hroot : -1 ≤ a := by dsimp [a,silverSlope];nlinarith [Real.sqrt_nonneg (2:Real)]
    nlinarith only [hquadratic,hroot]
  have ha1 : a < 1/2 := by nlinarith only [hquadratic,ha0]
  have hd0 : 0 < d := pow_pos ha0 _
  have mechanical_count_floor : ∀ n i : Nat,
      ((lowerMechanicalFactor silverSlope 0 n i).count true : Int) =
        ⌊((i+n:Nat):Real)*silverSlope⌋-⌊(i:Real)*silverSlope⌋ := by
    intro n i
    rw [factor_count_true]
    simpa using lowerMechanicalWindowTrueCount_eq_floor
      (rho:=0) ha0.le (show a<1 by linarith) i n
  have hd1 : d < a := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    have hp : a^j ≤ 1 := pow_le_one₀ ha0.le (by linarith)
    have hp0 : 0 ≤ a^j := pow_nonneg ha0.le _
    dsimp [d]
    rw [show j+1+1 = j+2 by omega, pow_add]
    nlinarith
  have hq0 : 0 < q := (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : 0 < P (k + 1))
  have ht0 : 0 < t := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    exact (by have hs := (pell_companion_step j).1; obtain ⟨j, hj⟩ := companion_odd j; omega : 0 < P (j + 1))
  have htq : t < q := (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : P k < P (k + 1))
  have hr0 : 0 < r := by dsimp [r]; omega
  have hq2 : 2 ≤ q := by omega
  have hm : (Q : Real) * d + a * q * d = 1 := by
    have hm := silver_phase_mass k
    have hQr : P (k + 2) = Q := by cases k <;> rfl
    rw [hQr] at hm
    change ((Q : Real)+a*q)*d = 1 at hm
    nlinarith
  have he := silverPell_error_formula k
  change (q : Real)*a-t = (-1:Real)^k*d at he
  have hQr : (Q : Real) = 2*q+t := by dsimp [Q]; push_cast; rfl
  have hrr : (r : Real) = q+t := by dsimp [r]; push_cast; rfl
  have hcount_data :
      (lowerMechanicalFactor silverSlope 0 q Q).count true =
        (if Even k then t+1 else t-1) ∧
      (∀ j < r-1, (lowerMechanicalFactor silverSlope 0 (2*q) (Q+q+j*(2*q))).count true = 2*t) ∧
      (lowerMechanicalFactor silverSlope 0 (2*q-1) (Q+q+(r-1)*(2*q))).count true =
        (if Even k then 2*t else 2*t-1) := by
    have hmqr : 1 ≤ 2*q := by omega
    rcases Nat.even_or_odd k with hp | hp
    · rw [if_pos hp,if_pos hp]
      rw [hp.neg_one_pow] at he
      norm_num at he
      have hQe : (Q : Real)*a = q-a*d := by
        have hs := hquadratic
        change a^2+2*a=1 at hs
        rw [hQr]
        nlinarith [he]
      have hmuld := congrArg (fun x : Real => x*d) he
      have hrd : 2*(r : Real)*d = 1-d^2 := by
        rw [hrr]
        nlinarith [hmuld]
      have hfQ : ⌊(Q : Real)*a⌋ = (q:Int)-1 := by
        rw [Int.floor_eq_iff,hQe]
        push_cast
        constructor <;> nlinarith
      have hf : ∀ j ≤ r-1, ⌊((Q+(2*j+1)*q : Nat):Real)*a⌋ =
          (q:Int)+(2*(j:Int)+1)*t := by
        intro j hj
        have hjr : (2*(j:Real)+1)*d < 1 := by
          have hjR : (j:Real)+1 ≤ r := by exact_mod_cast (show j+1≤r by omega)
          nlinarith [hrd]
        have hx : ((Q+(2*j+1)*q : Nat):Real)*a =
            (q:Real)+(2*(j:Real)+1)*t + (2*(j:Real)+1-a)*d := by
          push_cast
          linear_combination (2*(j:Real)+1)*he+hQe
        rw [Int.floor_eq_iff,hx]
        push_cast
        constructor <;> nlinarith
      have hfN : ⌊((Q+(2*q*r+q-1):Nat):Real)*a⌋ =
          (q:Int)+(2*(r:Int)+1)*t := by
        have hsub : 1 ≤ 2*q*r+q := by omega
        have hx : ((Q+(2*q*r+q-1):Nat):Real)*a =
            (q:Real)+(2*(r:Real)+1)*t -a + (2*(r:Real)+1-a)*d := by
          rw [Nat.cast_add,Nat.cast_sub hsub]
          push_cast
          linear_combination (2*(r:Real)+1)*he+hQe
        rw [Int.floor_eq_iff,hx]
        push_cast
        constructor <;> nlinarith [hrd]
      have hfhead : ⌊((Q+q:Nat):Real)*a⌋ = (q:Int)+t := by
        simpa using hf 0 (by omega)
      have hcH := mechanical_count_floor q Q
      change ((lowerMechanicalFactor silverSlope 0 q Q).count true:Int) =
          ⌊((Q+q:Nat):Real)*a⌋-⌊(Q:Real)*a⌋ at hcH
      rw [hfhead,hfQ] at hcH
      refine ⟨?_,?_,?_⟩
      · have hh : ((lowerMechanicalFactor silverSlope 0 q Q).count true:Int) = (t:Int)+1 := by omega
        exact_mod_cast hh
      · intro j hj
        have hidx : Q+q+j*(2*q) = Q+(2*j+1)*q := by ring
        have hidx' : Q+q+j*(2*q)+2*q = Q+(2*(j+1)+1)*q := by ring
        have hcB := mechanical_count_floor (2*q) (Q+q+j*(2*q))
        change ((lowerMechanicalFactor silverSlope 0 (2*q) (Q+q+j*(2*q))).count true:Int) =
            ⌊((Q+q+j*(2*q)+2*q:Nat):Real)*a⌋-⌊((Q+q+j*(2*q):Nat):Real)*a⌋ at hcB
        rw [hidx',hidx,hf j (by omega),hf (j+1) (by omega)] at hcB
        rw [← hidx] at hcB
        push_cast at hcB
        have hh : ((lowerMechanicalFactor silverSlope 0 (2*q) (Q+q+j*(2*q))).count true:Int) = 2*t := by nlinarith
        exact_mod_cast hh
      · have hidx : Q+q+(r-1)*(2*q) = Q+(2*(r-1)+1)*q := by ring
        have hidx' : Q+q+(r-1)*(2*q)+(2*q-1) = Q+(2*q*r+q-1) := by
          have hs := Nat.sub_add_cancel (show 1≤r by omega)
          have hss := Nat.sub_add_cancel (show 1≤2*q by omega)
          have hsss := Nat.sub_add_cancel (show 1≤2*q*r+q by omega)
          nlinarith
        have hcT := mechanical_count_floor (2*q-1) (Q+q+(r-1)*(2*q))
        change ((lowerMechanicalFactor silverSlope 0 (2*q-1) (Q+q+(r-1)*(2*q))).count true:Int) =
            ⌊((Q+q+(r-1)*(2*q)+(2*q-1):Nat):Real)*a⌋-
              ⌊((Q+q+(r-1)*(2*q):Nat):Real)*a⌋ at hcT
        rw [hidx',hidx,hfN,hf (r-1) le_rfl] at hcT
        rw [← hidx] at hcT
        have hcast : ((r-1:Nat):Int) = (r:Int)-1 := by omega
        rw [hcast] at hcT
        have hh : ((lowerMechanicalFactor silverSlope 0 (2*q-1) (Q+q+(r-1)*(2*q))).count true:Int) = 2*t := by nlinarith
        exact_mod_cast hh
    · have hpnot : ¬Even k := Nat.not_even_iff_odd.mpr hp
      rw [if_neg hpnot,if_neg hpnot]
      rw [hp.neg_one_pow] at he
      norm_num at he
      have hQe : (Q : Real)*a = q+a*d := by
        have hs := hquadratic
        change a^2+2*a=1 at hs
        rw [hQr]
        nlinarith [he]
      have hmuld := congrArg (fun x : Real => x*d) he
      have hrd : 2*(r : Real)*d = 1+d^2 := by
        rw [hrr]
        nlinarith [hmuld]
      have hfQ : ⌊(Q : Real)*a⌋ = (q:Int) := by
        rw [Int.floor_eq_iff,hQe]
        push_cast
        constructor <;> nlinarith
      have hf : ∀ j ≤ r-1, ⌊((Q+(2*j+1)*q : Nat):Real)*a⌋ =
          (q:Int)+(2*(j:Int)+1)*t-1 := by
        intro j hj
        have hjr : (2*(j:Real)+1-a)*d < 1 := by
          have hjR : (j:Real)+1 ≤ r := by exact_mod_cast (show j+1≤r by omega)
          nlinarith [hrd]
        have hx : ((Q+(2*j+1)*q : Nat):Real)*a =
            (q:Real)+(2*(j:Real)+1)*t - (2*(j:Real)+1-a)*d := by
          push_cast
          linear_combination (2*(j:Real)+1)*he+hQe
        rw [Int.floor_eq_iff,hx]
        push_cast
        constructor <;> nlinarith
      have hfN : ⌊((Q+(2*q*r+q-1):Nat):Real)*a⌋ =
          (q:Int)+(2*(r:Int)+1)*t-2 := by
        have hsub : 1 ≤ 2*q*r+q := by omega
        have hx : ((Q+(2*q*r+q-1):Nat):Real)*a =
            (q:Real)+(2*(r:Real)+1)*t-a-(2*(r:Real)+1-a)*d := by
          rw [Nat.cast_add,Nat.cast_sub hsub]
          push_cast
          linear_combination (2*(r:Real)+1)*he+hQe
        rw [Int.floor_eq_iff,hx]
        push_cast
        constructor <;> nlinarith [hrd]
      have hfhead : ⌊((Q+q:Nat):Real)*a⌋ = (q:Int)+t-1 := by
        simpa using hf 0 (by omega)
      have hcH := mechanical_count_floor q Q
      change ((lowerMechanicalFactor silverSlope 0 q Q).count true:Int) =
          ⌊((Q+q:Nat):Real)*a⌋-⌊(Q:Real)*a⌋ at hcH
      rw [hfhead,hfQ] at hcH
      have hcastt : ((t-1:Nat):Int) = (t:Int)-1 := by omega
      refine ⟨?_,?_,?_⟩
      · have hh : ((lowerMechanicalFactor silverSlope 0 q Q).count true:Int) = ((t-1:Nat):Int) := by omega
        exact_mod_cast hh
      · intro j hj
        have hidx : Q+q+j*(2*q) = Q+(2*j+1)*q := by ring
        have hidx' : Q+q+j*(2*q)+2*q = Q+(2*(j+1)+1)*q := by ring
        have hcB := mechanical_count_floor (2*q) (Q+q+j*(2*q))
        change ((lowerMechanicalFactor silverSlope 0 (2*q) (Q+q+j*(2*q))).count true:Int) =
            ⌊((Q+q+j*(2*q)+2*q:Nat):Real)*a⌋-⌊((Q+q+j*(2*q):Nat):Real)*a⌋ at hcB
        rw [hidx',hidx,hf j (by omega),hf (j+1) (by omega)] at hcB
        rw [← hidx] at hcB
        push_cast at hcB
        have hh : ((lowerMechanicalFactor silverSlope 0 (2*q) (Q+q+j*(2*q))).count true:Int) = 2*t := by nlinarith
        exact_mod_cast hh
      · have hidx : Q+q+(r-1)*(2*q) = Q+(2*(r-1)+1)*q := by ring
        have hidx' : Q+q+(r-1)*(2*q)+(2*q-1) = Q+(2*q*r+q-1) := by
          have hs := Nat.sub_add_cancel (show 1≤r by omega)
          have hss := Nat.sub_add_cancel (show 1≤2*q by omega)
          have hsss := Nat.sub_add_cancel (show 1≤2*q*r+q by omega)
          nlinarith
        have hcT := mechanical_count_floor (2*q-1) (Q+q+(r-1)*(2*q))
        change ((lowerMechanicalFactor silverSlope 0 (2*q-1) (Q+q+(r-1)*(2*q))).count true:Int) =
            ⌊((Q+q+(r-1)*(2*q)+(2*q-1):Nat):Real)*a⌋-
              ⌊((Q+q+(r-1)*(2*q):Nat):Real)*a⌋ at hcT
        rw [hidx',hidx,hfN,hf (r-1) le_rfl] at hcT
        rw [← hidx] at hcT
        have hcast : ((r-1:Nat):Int) = (r:Int)-1 := by omega
        rw [hcast] at hcT
        have hcast2t : ((2*t-1:Nat):Int) = 2*(t:Int)-1 := by omega
        have hh : ((lowerMechanicalFactor silverSlope 0 (2*q-1) (Q+q+(r-1)*(2*q))).count true:Int) = ((2*t-1:Nat):Int) := by nlinarith
        exact_mod_cast hh
  obtain ⟨hhead,hblocks,htail⟩ := hcount_data
  have hlen : q+(r-1)*(2*q)+(2*q-1) = 2*q*r+q-1 := by
    have hs := Nat.sub_add_cancel (show 1≤r by omega)
    have hss := Nat.sub_add_cancel (show 1≤2*q by omega)
    have hsss := Nat.sub_add_cancel (show 1≤2*q*r+q by omega)
    nlinarith
  have hp := period_of_counts q (r-1) (2*q-1) (2*q) (2*t) Q
    (by omega) (by dsimp [r]; omega) (by omega) (by omega) (by omega)
    hblocks (by rw [hhead]; split <;> omega) (by rw [hhead]; split <;> omega)
    (by rw [htail]; split <;> omega) (by rw [htail]; split <;> omega)
  rw [hlen] at hp
  exact hp
#print axioms silver_w2_period

set_option maxHeartbeats 2000000 in
theorem silver_wr_period (k : Nat) (hk : 1 ≤ k) :
    AbelianPeriod (lowerMechanicalFactor silverSlope 0
      ((2 * P (k + 1) + 1) * (P (k + 1) + P k) -
        (if k % 2 = 1 then 1 else 2))
      (if k % 2 = 1 then 0 else P (k + 1) + 1))
      (P (k + 1) + P k) := by
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
  have period_of_counts (h e l m c i : Nat) (hm : 0 < m) (he : 0 < e)
      (hc : c ≤ m) (hh : h < m) (hl : l < m)
      (hb : ∀ j < e, (lowerMechanicalFactor silverSlope 0 m (i + h + j * m)).count true = c)
      (hhc : (lowerMechanicalFactor silverSlope 0 h i).count true ≤ c)
      (hhf : h - (lowerMechanicalFactor silverSlope 0 h i).count true ≤ m - c)
      (hlc : (lowerMechanicalFactor silverSlope 0 l (i + h + e * m)).count true ≤ c)
      (hlf : l - (lowerMechanicalFactor silverSlope 0 l (i + h + e * m)).count true ≤ m - c) :
      AbelianPeriod (lowerMechanicalFactor silverSlope 0 (h + e * m + l) i) m := by
    classical
    have lowerMechanicalFactor_add : ∀ n m i : Nat,
        lowerMechanicalFactor silverSlope 0 (n+m) i =
          lowerMechanicalFactor silverSlope 0 n i ++ lowerMechanicalFactor silverSlope 0 m (i+n) := by
      intro n m i
      unfold lowerMechanicalFactor
      rw [List.ofFn_add]
      congr 1
      congr 1
      funext j
      congr 1
      simp [Nat.add_assoc]
    let blocks : List (List Bool) := List.ofFn fun j : Fin e =>
      lowerMechanicalFactor silverSlope 0 m (i + h + j * m)
    have hflat : blocks.flatten = lowerMechanicalFactor silverSlope 0 (e * m) (i + h) := by
      dsimp [blocks, lowerMechanicalFactor]
      rw [List.ofFn_mul]
      congr 1
      congr 1
      funext j
      congr 1
      funext t
      congr 1
      simp
      ring
    have hbp : ∀ b ∈ blocks, parikh b = (m-c,c) := by
      intro b hbmem
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hbmem
      have hbc := hb j.val j.isLt
      have hlen : (lowerMechanicalFactor silverSlope 0 m (i+h+j.val*m)).length = m := by
        simp [lowerMechanicalFactor]
      have hsum := List.count_false_add_count_true
        (lowerMechanicalFactor silverSlope 0 m (i+h+j.val*m))
      apply Prod.ext
      · simp only [parikh, Prod.fst]
        omega
      · exact hbc
    have hcontained : ∀ a : Nat, ∀ v : List Bool, v.length = a → a < m →
        v.count true ≤ c → a - v.count true ≤ m-c →
        (parikh v) < (m-c,c) := by
      intro a v hva ham hvc hvf
      have hs := List.count_false_add_count_true v
      simp only [lt_iff_le_and_ne, Prod.le_def, and_assoc]
      refine ⟨?_,hvc,?_⟩
      · change v.count false ≤ m-c
        omega
      · intro heq
        have hf := congrArg Prod.fst heq
        have ht := congrArg Prod.snd heq
        simp only [parikh, Prod.fst, Prod.snd] at hf ht
        omega
    refine ⟨hm,lowerMechanicalFactor silverSlope 0 h i,
      lowerMechanicalFactor silverSlope 0 l (i+h+e*m),blocks,?_,?_,?_,?_,?_⟩
    · intro hz
      have hs := congrArg List.length hz
      simp [blocks] at hs
      omega
    · rw [lowerMechanicalFactor_add, lowerMechanicalFactor_add]
      change blocks.flatten = lowerMechanicalFactor silverSlope 0 (e * m) (i + h) at hflat
      rw [← hflat]
      simp [Nat.add_assoc]
    · intro b hbmem
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hbmem
      simp [lowerMechanicalFactor]
    · intro a ha b hbmem
      rw [hbp a ha,hbp b hbmem]
    · refine ⟨(m-c,c),hbp,?_,?_⟩
      · exact hcontained h _ (by simp [lowerMechanicalFactor]) hh hhc hhf
      · exact hcontained l _ (by simp [lowerMechanicalFactor]) hl hlc hlf

  let q := P (k + 1)
  let t := P k
  let r := q+t
  let Q := 2*q+t
  let a := silverSlope
  let d := a^(k+1)
  have hquadratic : a^2+2*a=1 := by
    dsimp only [a,silverSlope]
    have hsq : (Real.sqrt (2:Real))^2=2 := by norm_num
    nlinarith
  have ha0 : 0 < a := by
    have hroot : -1 ≤ a := by dsimp [a,silverSlope];nlinarith [Real.sqrt_nonneg (2:Real)]
    nlinarith only [hquadratic,hroot]
  have ha1 : a < 1/2 := by nlinarith only [hquadratic,ha0]
  have hd0 : 0 < d := pow_pos ha0 _
  have mechanical_count_floor : ∀ n i : Nat,
      ((lowerMechanicalFactor silverSlope 0 n i).count true : Int) =
        ⌊((i+n:Nat):Real)*silverSlope⌋-⌊(i:Real)*silverSlope⌋ := by
    intro n i
    rw [factor_count_true]
    simpa using lowerMechanicalWindowTrueCount_eq_floor
      (rho:=0) ha0.le (show a<1 by linarith) i n
  have hd1 : d < a := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    have hp : a^j ≤ 1 := pow_le_one₀ ha0.le (by linarith)
    have hp0 : 0 ≤ a^j := pow_nonneg ha0.le _
    dsimp [d]
    rw [show j+1+1 = j+2 by omega, pow_add]
    nlinarith
  have hq0 : 0 < q := (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : 0 < P (k + 1))
  have ht0 : 0 < t := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    exact (by have hs := (pell_companion_step j).1; obtain ⟨j, hj⟩ := companion_odd j; omega : 0 < P (j + 1))
  have htq : t < q := (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : P k < P (k + 1))
  have hr0 : 0 < r := by dsimp [r]; omega
  have hq2 : 2 ≤ q := by omega
  have hm : (Q : Real) * d + a * q * d = 1 := by
    have hm := silver_phase_mass k
    have hQr : P (k + 2) = Q := by cases k <;> rfl
    rw [hQr] at hm
    change ((Q : Real)+a*q)*d = 1 at hm
    nlinarith
  have he := silverPell_error_formula k
  change (q : Real)*a-t = (-1:Real)^k*d at he
  have hQr : (Q : Real) = 2*q+t := by dsimp [Q]; push_cast; rfl
  have hrr : (r : Real) = q+t := by dsimp [r]; push_cast; rfl
  let c := q-t
  let delta := (1+a)*d
  have hc0 : 0 < c := by dsimp [c]; omega
  have hdc0 : 0 < delta := by dsimp [delta]; positivity
  have hcr : (c:Real) = (q:Real)-t := by dsimp [c]; rw [Nat.cast_sub (by omega)]
  have hci : (c:Int) = (q:Int)-t := by dsimp [c]; omega
  have hs := hquadratic
  change a^2+2*a=1 at hs
  rcases Nat.even_or_odd k with hp | hp
  · have hpar : k%2 ≠ 1 := by
      have hp0 := Nat.even_iff.mp hp
      omega
    rw [if_neg hpar,if_neg hpar]
    rw [hp.neg_one_pow] at he
    norm_num at he
    have hQe : (Q:Real)*a = q-a*d := by
      rw [hQr]
      linear_combination (q:Real)*hs-a*he
    have hre : (r:Real)*a = c-delta := by
      rw [hrr,hcr]
      dsimp [delta]
      linear_combination (q:Real)*hs-(a+1)*he
    have hmuld := congrArg (fun x:Real => x*d) he
    have hqd : 2*(q:Real)*delta = 1+d^2 := by
      dsimp [delta]
      nlinarith [hmuld]
    have hfS : ⌊((q+1:Nat):Real)*a⌋ = (t:Int) := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> nlinarith [he]
    have hf : ∀ j ≤ 2*q-1, ⌊((Q+j*r:Nat):Real)*a⌋ =
        (q:Int)+(j:Int)*c-1 := by
      intro j hj
      have hjR : (j:Real)+1 ≤ 2*q := by exact_mod_cast (show j+1≤2*q by omega)
      have hh : a*d+(j:Real)*delta < 1 := by
        dsimp [delta] at *
        nlinarith [hqd]
      have hh0 : 0 < a*d+(j:Real)*delta := by positivity
      have hx : ((Q+j*r:Nat):Real)*a = (q:Real)+(j:Real)*c-(a*d+(j:Real)*delta) := by
        push_cast
        linear_combination hQe+(j:Real)*hre
      rw [Int.floor_eq_iff,hx]
      push_cast
      constructor <;> linarith
    have hfN : ⌊((q+1+((2*q+1)*r-2):Nat):Real)*a⌋ =
        (t:Int)+(2*(q:Int)+1)*c-2 := by
      have hsub : 2 ≤ (2*q+1)*r := by dsimp [r]; nlinarith
      have hx : ((q+1+((2*q+1)*r-2):Nat):Real)*a =
          (t:Real)+(2*(q:Real)+1)*c-1-a-a*d-d^2 := by
        rw [Nat.cast_add,Nat.cast_sub hsub]
        push_cast
        linear_combination he+(2*(q:Real)+1)*hre-hqd
      rw [Int.floor_eq_iff,hx]
      push_cast
      constructor <;> nlinarith
    have hhidx : q+1+(r-1) = Q := by dsimp [Q,r]; omega
    have htid : q+1+(r-1)+(2*q-1)*r = Q+(2*q-1)*r := by omega
    have hnidx : q+1+(r-1)+(2*q-1)*r+(r-1) = q+1+((2*q+1)*r-2) := by
      have hs1:=Nat.sub_add_cancel (show 1≤r by omega)
      have hs2:=Nat.sub_add_cancel (show 1≤2*q by omega)
      have hs3:=Nat.sub_add_cancel (show 2≤(2*q+1)*r by dsimp [r]; nlinarith)
      nlinarith
    have hhead : (lowerMechanicalFactor silverSlope 0 (r-1) (q+1)).count true = c-1 := by
      have hfQ : ⌊(Q:Real)*a⌋ = (q:Int)-1 := by simpa using hf 0 (by omega)
      have hh:=mechanical_count_floor (r-1) (q+1)
      change ((lowerMechanicalFactor silverSlope 0 (r-1) (q+1)).count true:Int)=
        ⌊((q+1+(r-1):Nat):Real)*a⌋-⌊((q+1:Nat):Real)*a⌋ at hh
      rw [hhidx,hfQ,hfS] at hh
      have hh' : ((lowerMechanicalFactor silverSlope 0 (r-1) (q+1)).count true:Int)=((c-1:Nat):Int) := by omega
      exact_mod_cast hh'
    have hblocks : ∀ j < 2*q-1,
        (lowerMechanicalFactor silverSlope 0 r (q+1+(r-1)+j*r)).count true = c := by
      intro j hj
      have hsidx : q+1+(r-1)+j*r = Q+j*r := by omega
      have heidx : q+1+(r-1)+j*r+r = Q+(j+1)*r := by rw [hsidx]; ring
      have hh:=mechanical_count_floor r (q+1+(r-1)+j*r)
      change ((lowerMechanicalFactor silverSlope 0 r (q+1+(r-1)+j*r)).count true:Int)=
        ⌊((q+1+(r-1)+j*r+r:Nat):Real)*a⌋-⌊((q+1+(r-1)+j*r:Nat):Real)*a⌋ at hh
      rw [heidx,hsidx,hf j (by omega),hf (j+1) (by omega)] at hh
      rw [← hsidx] at hh
      push_cast at hh
      have hh' : ((lowerMechanicalFactor silverSlope 0 r (q+1+(r-1)+j*r)).count true:Int)=(c:Int) := by
        try simp only [Nat.zero_add]
        nlinarith
      exact_mod_cast hh'
    have htail : (lowerMechanicalFactor silverSlope 0 (r-1) (q+1+(r-1)+(2*q-1)*r)).count true = c-1 := by
      have hh:=mechanical_count_floor (r-1) (q+1+(r-1)+(2*q-1)*r)
      change ((lowerMechanicalFactor silverSlope 0 (r-1) (q+1+(r-1)+(2*q-1)*r)).count true:Int)=
        ⌊((q+1+(r-1)+(2*q-1)*r+(r-1):Nat):Real)*a⌋-
          ⌊((q+1+(r-1)+(2*q-1)*r:Nat):Real)*a⌋ at hh
      rw [hnidx,htid,hfN,hf (2*q-1) le_rfl] at hh
      rw [← htid] at hh
      have hccsub : ((c-1:Nat):Int) = (c:Int)-1 := by omega
      have hcsub : ((2*q-1:Nat):Int)=2*(q:Int)-1 := by omega
      rw [hcsub] at hh
      have hh' : ((lowerMechanicalFactor silverSlope 0 (r-1) (q+1+(r-1)+(2*q-1)*r)).count true:Int)=((c-1:Nat):Int) := by
        try simp only [Nat.zero_add]
        nlinarith
      exact_mod_cast hh'
    have hlen : (r-1)+(2*q-1)*r+(r-1) = (2*q+1)*r-2 := by
      have hs1:=Nat.sub_add_cancel (show 1≤r by omega)
      have hs2:=Nat.sub_add_cancel (show 1≤2*q by omega)
      have hs3:=Nat.sub_add_cancel (show 2≤(2*q+1)*r by dsimp [r]; nlinarith)
      nlinarith
    have hpc := period_of_counts (r-1) (2*q-1) (r-1) r c (q+1)
      hr0 (by omega) (by dsimp [c,r]; omega) (by omega) (by omega) hblocks
      (by rw [hhead];omega) (by rw [hhead];dsimp [c,r];omega)
      (by rw [htail];omega) (by rw [htail];dsimp [c,r];omega)
    rw [hlen] at hpc
    exact hpc
  · have hpar : k%2=1 := Nat.odd_iff.mp hp
    rw [if_pos hpar,if_pos hpar]
    rw [hp.neg_one_pow] at he
    norm_num at he
    have hre : (r:Real)*a = c+delta := by
      rw [hrr,hcr]
      dsimp [delta]
      linear_combination (q:Real)*hs-(a+1)*he
    have hmuld := congrArg (fun x:Real => x*d) he
    have hqd : 2*(q:Real)*delta = 1-d^2 := by
      dsimp [delta]
      nlinarith [hmuld]
    have hf : ∀ j ≤ 2*q, ⌊((j*r:Nat):Real)*a⌋ = (j:Int)*c := by
      intro j hj
      have hjR : (j:Real) ≤ 2*q := by exact_mod_cast hj
      have hh : (j:Real)*delta < 1 := by nlinarith [hqd]
      have hh0 : 0 ≤ (j:Real)*delta := by positivity
      have hx : ((j*r:Nat):Real)*a = (j:Real)*c+(j:Real)*delta := by
        push_cast
        linear_combination (j:Real)*hre
      rw [Int.floor_eq_iff,hx]
      push_cast
      constructor <;> linarith
    have hfN : ⌊(((2*q+1)*r-1:Nat):Real)*a⌋ = (2*(q:Int)+1)*c := by
      have hsub : 1 ≤ (2*q+1)*r := by dsimp [r]; nlinarith
      have hx : (((2*q+1)*r-1:Nat):Real)*a =
          (2*(q:Real)+1)*c+1-d^2+delta-a := by
        rw [Nat.cast_sub hsub]
        push_cast
        linear_combination (2*(q:Real)+1)*hre+hqd
      have hb : delta-d^2 < a := by
        have hp : 0 < (a-d)*(1-d) := mul_pos (by linarith) (by linarith)
        dsimp [delta]
        nlinarith
      rw [Int.floor_eq_iff,hx]
      push_cast
      constructor <;> nlinarith
    have hblocks : ∀ j < 2*q,
        (lowerMechanicalFactor silverSlope 0 r (0+0+j*r)).count true = c := by
      intro j hj
      have hh:=mechanical_count_floor r (0+0+j*r)
      change ((lowerMechanicalFactor silverSlope 0 r (0+0+j*r)).count true:Int)=
        ⌊((0+0+j*r+r:Nat):Real)*a⌋-⌊((0+0+j*r:Nat):Real)*a⌋ at hh
      simp only [Nat.zero_add] at hh
      rw [show j*r+r=(j+1)*r by ring,hf j (by omega),hf (j+1) (by omega)] at hh
      push_cast at hh
      have hh' : ((lowerMechanicalFactor silverSlope 0 r (0+0+j*r)).count true:Int)=(c:Int) := by
        try simp only [Nat.zero_add]
        nlinarith
      exact_mod_cast hh'
    have htail : (lowerMechanicalFactor silverSlope 0 (r-1) (0+0+(2*q)*r)).count true = c := by
      have hh:=mechanical_count_floor (r-1) (0+0+(2*q)*r)
      change ((lowerMechanicalFactor silverSlope 0 (r-1) (0+0+(2*q)*r)).count true:Int)=
        ⌊((0+0+(2*q)*r+(r-1):Nat):Real)*a⌋-⌊((0+0+(2*q)*r:Nat):Real)*a⌋ at hh
      simp only [Nat.zero_add] at hh
      have hnidx : (2*q)*r+(r-1)=(2*q+1)*r-1 := by
        have hs:=Nat.sub_add_cancel (show 1≤r by omega)
        have hss:=Nat.sub_add_cancel (show 1≤(2*q+1)*r by dsimp [r];nlinarith)
        nlinarith
      rw [hnidx,hfN,hf (2*q) le_rfl] at hh
      push_cast at hh
      have hh' : ((lowerMechanicalFactor silverSlope 0 (r-1) (0+0+(2*q)*r)).count true:Int)=(c:Int) := by
        try simp only [Nat.zero_add]
        nlinarith
      exact_mod_cast hh'
    have hlen : 0+(2*q)*r+(r-1) = (2*q+1)*r-1 := by
      have hs:=Nat.sub_add_cancel (show 1≤r by omega)
      have hss:=Nat.sub_add_cancel (show 1≤(2*q+1)*r by dsimp [r];nlinarith)
      nlinarith
    have hpc := period_of_counts 0 (2*q) (r-1) r c 0
      hr0 (by omega) (by dsimp [c,r];omega) hr0 (by omega) hblocks
      (by simp [lowerMechanicalFactor]) (by simp)
      (by rw [htail]) (by rw [htail];dsimp [c,r];omega)
    rw [hlen] at hpc
    exact hpc
#print axioms silver_wr_period
end D5.S1.Words.Mechanical
