/- GID: D5/S1/Words/Mechanical/SilverSlopeAbelianUpperInclusion
   generality: I
   mirror-B: none(waiver:open-problem-stage-a)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Singular-window packing excludes every noncandidate minimum period. -/
/-
Judgement form:
  silver_noncandidate_exclusion:
    proof_shape: content
    escape_witness: silver_no_q_length: if k≥1, P(k+1)<n, and period P(k+1) is absent,
      then (P(k+1)-1)*P(k+2)+P(k+1)≤n
    Non-binding step: The new packing lower bound is on the actual live path and contradicts the
      approximation-gap block budget. No pinned AbelianPeriod counterpart supplies it.
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
import D5.S1.Words.Mechanical.SilverSlopeAbelianSingularPacking
namespace D5.S1.Words.Mechanical
open D5.S1.Recurrence.PellCompanionGcd
open D5.S1.Words.Complexity
set_option maxHeartbeats 2000000 in
theorem silver_noncandidate_exclusion (k n i m : Nat) (hk : 1≤k)
    (hm : P (k + 1)≤m) (hmQ : m<P (k + 2))
    (hne1 : m≠P (k + 1)) (hne2 : m≠2*P (k + 1))
    (hner : m≠P (k + 1)+P k)
    (hn : P (k + 1)<n)
    (hnotq : ¬ AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) (P (k + 1))) :
    ¬ AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) m := by
  have period_constraints (n i m : Nat)
      (hp : AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) m) :
      ∃ h e l c : Nat, h < m ∧ l < m ∧ 0 < e ∧ c ≤ m ∧
        n = h+e*m+l ∧
        ⌊((i+h+e*m:Nat):Real)*silverSlope⌋ - ⌊((i+h:Nat):Real)*silverSlope⌋ = (e:Int)*c ∧
        (e:Real)*|(m:Real)*silverSlope-c| < 1 := by
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
    have silverSlope_bounds : 0 ≤ silverSlope ∧ silverSlope < 1 := by
      dsimp [silverSlope]
      have hsq : (Real.sqrt (2:Real))^2=2 := by norm_num
      have hp:=Real.sqrt_nonneg (2:Real)
      constructor <;> nlinarith
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
    have mechanical_count_floor : ∀ n i : Nat,
        ((lowerMechanicalFactor silverSlope 0 n i).count true : Int) =
          ⌊((i+n:Nat):Real)*silverSlope⌋-⌊(i:Real)*silverSlope⌋ := by
      intro n i
      rw [factor_count_true]
      simpa using lowerMechanicalWindowTrueCount_eq_floor
        (rho:=0) silverSlope_bounds.1 silverSlope_bounds.2 i n
    rcases hp with ⟨hm,head,tail,bs,hne,heq,hlen,hpar,p,hbp,hhead,htail⟩
    have hp_len : p.1+p.2=m := by
      obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil bs hne
      have hsum := List.count_false_add_count_true b
      have hb0 := hlen b hb
      have hb1 := hbp b hb
      have hf := congrArg Prod.fst hb1
      have ht := congrArg Prod.snd hb1
      simp only [parikh, Prod.fst, Prod.snd] at hf ht
      omega
    have hh := parikh_length_lt hhead hp_len
    have hl := parikh_length_lt htail hp_len
    have he : 0<bs.length := List.length_pos_iff.mpr hne
    have hbslen : bs.flatten.length = bs.length*m := by
      rw [List.length_flatten, List.map_eq_replicate_iff.mpr hlen, List.sum_replicate_nat]
    have hn : n=head.length+bs.length*m+tail.length := by
      have hn:=congrArg List.length heq
      simpa [lowerMechanicalFactor,List.length_append,hbslen,Nat.add_assoc] using hn
    have hmiddle : bs.flatten=lowerMechanicalFactor silverSlope 0 (bs.length*m) (i+head.length) := by
      have hs : lowerMechanicalFactor silverSlope 0 head.length i ++
          (lowerMechanicalFactor silverSlope 0 (bs.length*m) (i+head.length) ++
          lowerMechanicalFactor silverSlope 0 tail.length (i+head.length+bs.length*m)) =
          head ++ (bs.flatten ++ tail) := by
        rw [← List.append_assoc,← lowerMechanicalFactor_add]
        rw [show i+head.length+bs.length*m=i+(head.length+bs.length*m) by omega,
          ← lowerMechanicalFactor_add,←hn]
        simpa [List.append_assoc,lowerMechanicalFactor] using heq
      have hrest := (List.append_inj hs (by simp [lowerMechanicalFactor])).2
      have hmid := (List.append_inj hrest (by simp [lowerMechanicalFactor,hbslen])).1
      exact hmid.symm
    have hcounts : ∀ b∈bs,b.count true=p.2 := by
      intro b hb
      exact congrArg Prod.snd (hbp b hb)
    have htotal : bs.flatten.count true = bs.length*p.2 := by
      rw [List.count_flatten, List.map_eq_replicate_iff.mpr hcounts, List.sum_replicate_nat]
    rw [hmiddle] at htotal
    have hfloor := mechanical_count_floor (bs.length*m) (i+head.length)
    rw [htotal] at hfloor
    refine ⟨head.length,bs.length,tail.length,p.2,hh,hl,he,by omega,hn,?_,?_⟩
    · simpa [Nat.cast_mul,Nat.add_assoc] using hfloor.symm
    · have hr : (⌊((i+head.length+bs.length*m:Nat):Real)*silverSlope⌋ : Real) -
            ⌊((i+head.length:Nat):Real)*silverSlope⌋ = (bs.length:Real)*p.2 := by
          exact_mod_cast hfloor.symm
      have hrel : (bs.length:Real)*((m:Real)*silverSlope-p.2) =
          Int.fract (((i+head.length+bs.length*m:Nat):Real)*silverSlope) -
            Int.fract (((i+head.length:Nat):Real)*silverSlope) := by
        unfold Int.fract
        push_cast at *
        nlinarith [hr]
      rw [show (bs.length:Real)*|(m:Real)*silverSlope-p.2| =
      |(bs.length:Real)*((m:Real)*silverSlope-p.2)| by
        rw [abs_mul, abs_of_nonneg (show (0:Real) ≤ bs.length from Nat.cast_nonneg bs.length)], hrel]
      apply abs_lt.mpr
      constructor <;> linarith [
        Int.fract_nonneg (((i+head.length+bs.length*m:Nat):Real)*silverSlope),
        Int.fract_lt_one (((i+head.length+bs.length*m:Nat):Real)*silverSlope),
        Int.fract_nonneg (((i+head.length:Nat):Real)*silverSlope),
        Int.fract_lt_one (((i+head.length:Nat):Real)*silverSlope)]

  intro hp
  have hpack := silver_no_q_length k n i hk hn hnotq
  obtain ⟨h,e,l,c,hh,hl,he0,hc,hlen,hfloor,herror⟩ := period_constraints n i m hp
  have hupper : n+2≤(e+2)*m := by nlinarith only [hlen,hh,hl]
  have ha0 : 0<silverSlope := by
    dsimp [silverSlope]
    have hs : (Real.sqrt (2:Real))^2=2 := by norm_num
    have hh := Real.sqrt_nonneg (2:Real)
    nlinarith
  have ha1 : silverSlope<1/2 := by
    dsimp [silverSlope]
    have hs : (Real.sqrt (2:Real))^2=2 := by norm_num
    have hh := Real.sqrt_nonneg (2:Real)
    nlinarith
  by_cases hk3 : 3≤k
  · let q := P (k + 1)
    let t := P k
    let Q := P (k + 2)
    let d := silverSlope^(k+1)
    let g := d+silverSlope^k
    have hdiff : 7≤q-t := by
      have hd : ∀ j, 7≤P (j + 4)-P (j+3) := by
        intro j
        induction j with
        | zero => norm_num [P,Nat.add_assoc]
        | succ j ih =>
          have hr : P (j+1+3 + 1)=2*P (j + 4)+P (j + 3) := by
            change P ((j+3)+2)=2*P ((j+3)+1)+P (j + 3)
            rfl
          have ht : P (j+1+3)=P (j + 4) := rfl
          rw [hr,ht]
          omega
      obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hk3
      have hj' : k=j+3 := by omega
      dsimp [q,t]
      rw [hj']
      exact hd j
    have hd0 : 0<d := pow_pos ha0 _
    have hquad : silverSlope^2+2*silverSlope=1 := by
      dsimp [silverSlope]
      have hs : (Real.sqrt (2:Real))^2=2 := by norm_num
      nlinarith
    have hprev : silverSlope^k=(2+silverSlope)*d := by
      dsimp [d]
      rw [pow_succ]
      linear_combination -(silverSlope^k)*hquad
    have hQr : (Q:Real)=2*q+t := by
      have hrec : Q=2*q+t := by cases k <;> rfl
      exact_mod_cast hrec
    have hmass := silver_phase_mass k
    change ((Q:Real)+silverSlope*q)*d=1 at hmass
    have htq := (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : P k < P (k + 1))
    have hdiffR : (7:Real)≤(q:Real)-t := by
      have hdN : t+7≤q := by omega
      have hdR : (t:Real)+7≤q := by exact_mod_cast hdN
      linarith
    have hbound : 1<((q:Real)-2)*g := by
      dsimp [g]
      rw [hprev]
      have hpos : 0<((q:Real)-t-6-2*silverSlope)*d := by
        have hh : 0<(q:Real)-t-6-2*silverSlope := by linarith
        exact mul_pos hh hd0
      rw [hQr] at hmass
      nlinarith only [hmass,hpos]
    have hg0 : 0<g := by dsimp [g];positivity
    have herr : g≤|(m:Real)*silverSlope-c| := by
      have hb := silver_gap_approximation (k-1) m
        (by simpa [show k-1+2=k+1 by omega] using hm)
        (by simpa [show k-1+3=k+2 by omega] using hmQ)
        (by simpa [show k-1+2=k+1 by omega] using hne1)
        (by simpa [show k-1+2=k+1 by omega] using hne2)
        (by
          have hprevQ : P (k-1 + 1)=P k := by
            obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
            rfl
          simpa [show k-1+2=k+1 by omega,hprevQ] using hner) (c:Int)
      simpa [show k-1+1=k by omega,show k-1+2=k+1 by omega,g,d] using hb
    have hesmall : e<q-2 := by
      by_contra hge
      have heR : (q:Real)-2≤e := by
        have heN : q≤e+2 := by omega
        have heNR : (q:Real)≤(e:Real)+2 := by exact_mod_cast heN
        linarith
      have hmul := mul_le_mul_of_nonneg_right heR hg0.le
      have hmul' := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg e)
      linarith
    have hmul := Nat.mul_le_mul_right m (show e+2≤q-1 by omega)
    have hmulQ := Nat.mul_le_mul_left (q-1) (show m≤Q by omega)
    change (q-1)*Q+q≤n at hpack
    omega
  · have hkcases : k=1 ∨ k=2 := by omega
    rcases hkcases with rfl | rfl
    · norm_num [P,Nat.add_assoc] at hm hmQ hne1 hne2 hner
      omega
    · norm_num [P,Nat.add_assoc] at hm hmQ hne1 hne2 hner hpack
      have hmCases : m=6 ∨ m=8 ∨ m=9 ∨ m=11 := by omega
      have haL : (207/500:Real)<silverSlope := by
        dsimp [silverSlope]
        have hs : (Real.sqrt (2:Real))^2=2 := by norm_num
        have hh := Real.sqrt_nonneg (2:Real)
        nlinarith
      have haU : silverSlope<(83/200:Real) := by
        dsimp [silverSlope]
        have hs : (Real.sqrt (2:Real))^2=2 := by norm_num
        have hh := Real.sqrt_nonneg (2:Real)
        nlinarith
      rcases hmCases with rfl | rfl | rfl | rfl
      · have herr : (2/5:Real)≤|(6:Real)*silverSlope-c| := by
          by_cases hc2 : c≤2
          · have hcR : (c:Real)≤2 := by exact_mod_cast hc2
            rw [abs_of_nonneg (by linarith)]
            linarith
          · have hcR : (3:Real)≤c := by exact_mod_cast (show 3≤c by omega)
            rw [abs_of_neg (by linarith)]
            linarith
        have he3 : e≤2 := by
          by_contra hn
          have heR : (3:Real)≤e := by exact_mod_cast (show 3≤e by omega)
          have hh := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg e)
          norm_num at herror
          nlinarith
        omega
      · have herr : (3/10:Real)≤|(8:Real)*silverSlope-c| := by
          by_cases hc3 : c≤3
          · have hcR : (c:Real)≤3 := by exact_mod_cast hc3
            rw [abs_of_nonneg (by linarith)]
            linarith
          · have hcR : (4:Real)≤c := by exact_mod_cast (show 4≤c by omega)
            rw [abs_of_neg (by linarith)]
            linarith
        have he4 : e≤3 := by
          by_contra hn
          have heR : (4:Real)≤e := by exact_mod_cast (show 4≤e by omega)
          have hh := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg e)
          norm_num at herror
          nlinarith
        omega
      · have herr : (1/4:Real)≤|(9:Real)*silverSlope-c| := by
          by_cases hc3 : c≤3
          · have hcR : (c:Real)≤3 := by exact_mod_cast hc3
            rw [abs_of_nonneg (by linarith)]
            linarith
          · have hcR : (4:Real)≤c := by exact_mod_cast (show 4≤c by omega)
            rw [abs_of_neg (by linarith)]
            linarith
        have he4 : e≤3 := by
          by_contra hn
          have heR : (4:Real)≤e := by exact_mod_cast (show 4≤e by omega)
          have hh := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg e)
          norm_num at herror
          nlinarith
        omega
      · have herr : (2/5:Real)≤|(11:Real)*silverSlope-c| := by
          by_cases hc4 : c≤4
          · have hcR : (c:Real)≤4 := by exact_mod_cast hc4
            rw [abs_of_nonneg (by linarith)]
            linarith
          · have hcR : (5:Real)≤c := by exact_mod_cast (show 5≤c by omega)
            rw [abs_of_neg (by linarith)]
            linarith
        have he3 : e≤2 := by
          by_contra hn
          have heR : (3:Real)≤e := by exact_mod_cast (show 3≤e by omega)
          have hh := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg e)
          norm_num at herror
          nlinarith
        omega
#print axioms silver_noncandidate_exclusion
end D5.S1.Words.Mechanical
