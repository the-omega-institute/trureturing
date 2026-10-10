/- GID: D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessExclusions
   generality: I
   mirror-B: none(waiver:open-problem-stage-a)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Pell phase restrictions exclude every competing shorter witness period. -/
/-
Judgement form:
  silver_no_q_period:
    proof_shape: content
    escape_witness: silverPell_error_formula k: (P (k + 1) : Real)*silverSlope-P k=(-1
      : Real)^k*silverSlope^(k+1)
    Non-binding step: The signed all-index error identity is live in the
      endpoint-phase/head-alignment exclusions; after inlining it includes a new recurrence
      identity.
    Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
      (sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d);
      D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd
      (sha256:31fb069a0187ae500aa0a39e052a8deaceee7eb0f963bcc75879f9f575b26ff1);
      D5/S1/Words/Mechanical/MechanicalBalance
      (sha256:db7434e78bc669a2f0d5711175f8f744fc6dfba359dd5414cc8c05c753ad3399);
      D5/S1/Words/Mechanical/MechanicalFactorComplexity
      (sha256:9b83310d03f384fa38264d66462adfe64f238b0be826575d08630dad3141f15a)
  silver_w2_no_r_period:
    proof_shape: content
    escape_witness: silver_best_approximation (k-1) j hj hjq z: silverSlope^k ≤ |(j :
      Real)*silverSlope-z| for 0<j<P (k + 1)
    Non-binding step: This live arbitrary-integer exclusion closes the head-alignment
      contradictions; its new integer-coordinate proof is not an upstream normalization fact.
    Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
      (sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d);
      D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd
      (sha256:31fb069a0187ae500aa0a39e052a8deaceee7eb0f963bcc75879f9f575b26ff1);
      D5/S1/Words/Mechanical/MechanicalBalance
      (sha256:db7434e78bc669a2f0d5711175f8f744fc6dfba359dd5414cc8c05c753ad3399);
      D5/S1/Words/Mechanical/MechanicalFactorComplexity
      (sha256:9b83310d03f384fa38264d66462adfe64f238b0be826575d08630dad3141f15a)
  silver_short_period_exclusion:
    proof_shape: content
    escape_witness: silver_gap_approximation (k-1) m ... c: silverSlope^(k+1)+silverSlope^k ≤ |(m
      : Real)*silverSlope-c| away from q,2q,q+qPrev
    Non-binding step: The live gap branch, together with the best-approximation branch, supplies
      the lower error bound; inlining retains the all-integer exclusion.
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
theorem silver_no_q_period (k n i : Nat) (hk : 1 ≤ k)
    (hn : 2*P (k + 1)*(P (k + 1)+P k)+P (k + 1)-1 ≤ n)
    (hi : Even k → i=2*P (k + 1)+P k ∨ i=P (k + 1)+1) :
    ¬ AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) (P (k + 1)) := by
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
  have hs := hquadratic
  change a^2+2*a=1 at hs
  have hprev : a^k=(2+a)*d := by
    dsimp [d]
    rw [pow_succ]
    linear_combination -(a^k)*hs
  intro hp
  obtain ⟨h,e,l,c,hh,hl,he0,hc,hnlen,hfloor,herror⟩ := period_constraints n i q hp
  have hen : 2*r ≤ e := by
    change 2*q*r+q-1 ≤ n at hn
    have hsub := Nat.sub_add_cancel (show 1≤2*q*r+q by omega)
    by_contra hne
    have hn' : e+1≤2*r := by omega
    nlinarith
  have he2 : 2≤e := by dsimp [r] at hen;omega
  have hclose : |(q:Real)*a-c| < 1/2 := by
    have he2R : (2:Real)≤e := by exact_mod_cast he2
    nlinarith [abs_nonneg ((q:Real)*a-c)]
  have heabs : |(q:Real)*a-t|=d := by
    rw [he,abs_mul]
    simp [abs_pow,abs_of_pos hd0]
  have hcEq : c=t := by
    have hband:=abs_le.mp (le_of_eq heabs)
    have hbandc:=abs_lt.mp hclose
    rcases lt_trichotomy c t with hct | hct | hct
    · have hR : (c:Real)+1≤t := by exact_mod_cast (show c+1≤t by omega)
      nlinarith
    · exact hct
    · have hR : (t:Real)+1≤c := by exact_mod_cast (show t+1≤c by omega)
      nlinarith
  subst c
  let x := Int.fract (((i+h:Nat):Real)*a)
  let y := Int.fract (((i+h+e*q:Nat):Real)*a)
  have hx0 : 0≤x := Int.fract_nonneg _
  have hx1 : x<1 := Int.fract_lt_one _
  have hy0 : 0≤y := Int.fract_nonneg _
  have hy1 : y<1 := Int.fract_lt_one _
  have hfloorR : (⌊((i+h+e*q:Nat):Real)*a⌋:Real)-⌊((i+h:Nat):Real)*a⌋ = (e:Real)*t := by
    exact_mod_cast hfloor
  have hphase : y-x = (e:Real)*((q:Real)*a-t) := by
    dsimp only [x,y,Int.fract]
    push_cast at hfloorR ⊢
    nlinarith [hfloorR]
  have henR : 2*(r:Real)≤e := by exact_mod_cast hen
  rcases Nat.even_or_odd k with hpar | hpar
  · rw [hpar.neg_one_pow] at he
    norm_num at he
    have hmuld:=congrArg (fun z:Real=>z*d) he
    have hrd : 2*(r:Real)*d=1-d^2 := by rw [hrr];nlinarith [hmuld]
    have hxsmall : x<d^2 := by nlinarith [hphase]
    have hQe : (Q:Real)*a=q-a*d := by
      rw [hQr]
      linear_combination (q:Real)*hs-a*he
    have hbest : ∀ j : Nat, 0<j → j<q → ∀ z:Int, (2+a)*d≤|(j:Real)*a-z| := by
      intro j hj hjq z
      have hb:=silver_best_approximation (k-1) j hj
        (by simpa [show k-1+2=k+1 by omega,q] using hjq) z
      rw [show k-1+1=k by omega] at hb
      change a^k ≤ |(j:Real)*a-z| at hb
      rw [hprev] at hb
      exact hb
    rcases hi hpar with hiQ | hiq
    · change i=Q at hiQ
      subst i
      let z : Int := ⌊((Q+h:Nat):Real)*a⌋-(q:Int)
      have hz : (h:Real)*a-z=x+a*d := by
        dsimp only [z,x,Int.fract]
        push_cast
        nlinarith [hQe]
      by_cases hh0 : h=0
      · subst h
        norm_num only [Nat.cast_zero,zero_mul] at hz
        have hz0 : (0:Real)< -(z:Real) := by nlinarith [hz]
        have hz1 : -(z:Real)<1 := by nlinarith [hz]
        have hz0I : (0:Int)< -z := by exact_mod_cast hz0
        have hz1I : -z<(1:Int) := by exact_mod_cast hz1
        omega
      · have hb:=hbest h (by omega) hh z
        rw [hz,abs_of_nonneg (by positivity)] at hb
        nlinarith
    · change i=q+1 at hiq
      subst i
      let j:=h+1
      have hj0 : 0<j := by dsimp [j];omega
      have hjq : j≤q := by dsimp [j];omega
      by_cases hjEq : j=q
      · have hidx : q+1+h=2*q := by dsimp [j] at hjEq;omega
        have hf : ⌊((2*q:Nat):Real)*a⌋=2*(t:Int) := by
          rw [Int.floor_eq_iff]
          push_cast
          constructor <;> nlinarith [he]
        have hxEq : x=2*d := by
          dsimp only [x,Int.fract]
          rw [hidx,hf]
          push_cast
          nlinarith [he]
        nlinarith
      · let z : Int := ⌊((q+1+h:Nat):Real)*a⌋-(t:Int)
        have hz : (j:Real)*a-z=x-d := by
          dsimp only [z,x,Int.fract,j]
          push_cast
          nlinarith [he]
        have hb:=hbest j hj0 (by omega) z
        rw [hz,abs_of_nonpos (by nlinarith)] at hb
        nlinarith
  · rw [hpar.neg_one_pow] at he
    norm_num at he
    have hmuld:=congrArg (fun z:Real=>z*d) he
    have hrd : 2*(r:Real)*d=1+d^2 := by rw [hrr];nlinarith [hmuld]
    nlinarith [hphase]
#print axioms silver_no_q_period

set_option maxHeartbeats 2000000 in
theorem silver_w2_no_r_period (k : Nat) (hk : 1 ≤ k) :
    ¬ AbelianPeriod (lowerMechanicalFactor silverSlope 0
      (2*P (k + 1)*(P (k + 1)+P k)+P (k + 1)-1)
      (2*P (k + 1)+P k)) (P (k + 1)+P k) := by
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
  let n:=2*q*r+q-1
  let C:=q-t
  let delta:=(1+a)*d
  have hC0 : 0<C := by dsimp [C];omega
  have hCr : (C:Real)=(q:Real)-t := by dsimp [C];rw [Nat.cast_sub (by omega)]
  have hCi : (C:Int)=(q:Int)-t := by dsimp [C];omega
  have hd2 : d≤a^2 := by
    obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
    have hp : a^j≤1 := pow_le_one₀ ha0.le (by linarith)
    dsimp [d]
    rw [show j+1+1=j+2 by omega,pow_add]
    nlinarith [sq_nonneg a]
  have hdelta0 : 0<delta := by dsimp [delta];positivity
  have hdelta1 : delta<1/2 := by dsimp [delta];nlinarith
  have hs:=hquadratic
  change a^2+2*a=1 at hs
  have hprev : a^k=(2+a)*d := by
    dsimp [d]
    rw [pow_succ]
    linear_combination -(a^k)*hs
  have hbest : ∀ j : Nat, 0<j → j<q → ∀ z:Int, (2+a)*d≤|(j:Real)*a-z| := by
    intro j hj hjq z
    have hb:=silver_best_approximation (k-1) j hj
      (by simpa [show k-1+2=k+1 by omega,q] using hjq) z
    rw [show k-1+1=k by omega] at hb
    change a^k≤|(j:Real)*a-z| at hb
    rw [hprev] at hb
    exact hb
  intro hp
  obtain ⟨h,e,l,c,hh,hl,he0,hc,hnlen,hfloor,herror⟩:=period_constraints n Q r hp
  have hen : 2*q-1≤e := by
    have hsub:=Nat.sub_add_cancel (show 1≤2*q*r+q by omega)
    change 2*q*r+q-1=h+e*r+l at hnlen
    by_contra hne
    have hn':e+2≤2*q := by omega
    nlinarith
  have he2 : 2≤e := by omega
  have hclose : |(r:Real)*a-c|<1/2 := by
    have he2R : (2:Real)≤e := by exact_mod_cast he2
    nlinarith [abs_nonneg ((r:Real)*a-c)]
  have hphases : (r:Real)*a-C=-( (-1:Real)^k)*delta := by
    rw [hrr,hCr]
    dsimp [delta]
    linear_combination (q:Real)*hs-(a+1)*he
  have heabs : |(r:Real)*a-C|=delta := by
    rw [hphases,abs_mul,abs_neg]
    simp [abs_pow,abs_of_pos hdelta0]
  have hcEq : c=C := by
    have hband:=abs_le.mp (le_of_eq heabs)
    have hbandc:=abs_lt.mp hclose
    rcases lt_trichotomy c C with hct | hct | hct
    · have hR : (c:Real)+1≤C := by exact_mod_cast (show c+1≤C by omega)
      nlinarith
    · exact hct
    · have hR : (C:Real)+1≤c := by exact_mod_cast (show C+1≤c by omega)
      nlinarith
  subst c
  let x:=Int.fract (((Q+h:Nat):Real)*a)
  let y:=Int.fract (((Q+h+e*r:Nat):Real)*a)
  have hx0 : 0≤x := Int.fract_nonneg _
  have hx1 : x<1 := Int.fract_lt_one _
  have hy0 : 0≤y := Int.fract_nonneg _
  have hy1 : y<1 := Int.fract_lt_one _
  have hfloorR : (⌊((Q+h+e*r:Nat):Real)*a⌋:Real)-⌊((Q+h:Nat):Real)*a⌋ = (e:Real)*C := by exact_mod_cast hfloor
  have hphase : y-x=(e:Real)*((r:Real)*a-C) := by
    dsimp only [x,y,Int.fract]
    push_cast at hfloorR ⊢
    linear_combination -hfloorR
  have henR : 2*(q:Real)-1≤e := by
    have hh : 2*(q:Real)≤e+1 := by exact_mod_cast (show 2*q≤e+1 by omega)
    linarith
  rcases Nat.even_or_odd k with hpar | hpar
  · rw [hpar.neg_one_pow] at he hphases
    norm_num at he hphases
    have hmuld:=congrArg (fun z:Real=>z*d) he
    have hqd : 2*(q:Real)*delta=1+d^2 := by dsimp [delta];nlinarith [hmuld]
    have hgeq : q≤h := by
      by_contra hne
      have hhq : h+1≤q := by omega
      have hbig : 2*q≤e := by
        have hsub:=Nat.sub_add_cancel (show 1≤2*q*r+q by omega)
        change 2*q*r+q-1=h+e*r+l at hnlen
        by_contra hne
        have hn':e+1≤2*q := by omega
        nlinarith
      have hbigR : 2*(q:Real)≤e := by exact_mod_cast hbig
      nlinarith [hphase]
    have hxlarge : 1+d^2-delta≤x := by nlinarith [hphase]
    let j:=h-q
    have hjEq : h=q+j := by dsimp [j];omega
    have hjq : j<q := by dsimp [r] at hh;omega
    have hQe : (Q:Real)*a=q-a*d := by
      rw [hQr]
      linear_combination (q:Real)*hs-a*he
    let z : Int := ⌊((Q+h:Nat):Real)*a⌋-(q:Int)-(t:Int)+1
    have hz : (j:Real)*a-z=x-1-(1-a)*d := by
      dsimp only [z,x,Int.fract]
      rw [hjEq]
      push_cast
      linear_combination -hQe-he
    have hzneg : x-1-(1-a)*d<0 := by
      nlinarith only [hx1,ha0,ha1,hd0]
    have hzbound : - (x-1-(1-a)*d) ≤ 2*d-d^2 := by
      dsimp only [delta] at hxlarge
      nlinarith only [hxlarge]
    by_cases hj0 : j=0
    · rw [hj0] at hz
      norm_num only [Nat.cast_zero,zero_mul] at hz
      have hz0 : (0:Real)<(z:Real) := by linarith only [hz,hzneg]
      have hz1 : (z:Real)<1 := by nlinarith only [hz,hzbound,hd0,hd1,ha1]
      have hz0I : (0:Int)<z := by exact_mod_cast hz0
      have hz1I : z<(1:Int) := by exact_mod_cast hz1
      omega
    · have hb:=hbest j (by omega) hjq z
      rw [hz,abs_of_neg hzneg] at hb
      nlinarith only [hb,hzbound,ha0,hd0]
  · rw [hpar.neg_one_pow] at he hphases
    norm_num at he hphases
    have hmuld:=congrArg (fun z:Real=>z*d) he
    have hqd : 2*(q:Real)*delta=1-d^2 := by dsimp [delta];nlinarith [hmuld]
    have hQe : (Q:Real)*a=q+a*d := by
      rw [hQr]
      linear_combination (q:Real)*hs-a*he
    by_cases hhq : h<q
    · have hbig : 2*q≤e := by
        have hsub:=Nat.sub_add_cancel (show 1≤2*q*r+q by omega)
        change 2*q*r+q-1=h+e*r+l at hnlen
        by_contra hne
        have hn':e+1≤2*q := by omega
        nlinarith
      have hbigR : 2*(q:Real)≤e := by exact_mod_cast hbig
      have hxsmall : x<d^2 := by nlinarith [hphase]
      let z : Int := ⌊((Q+h:Nat):Real)*a⌋-(q:Int)
      have hz : (h:Real)*a-z=x-a*d := by
        dsimp only [z,x,Int.fract]
        push_cast
        linear_combination -hQe
      have hzneg : x-a*d<0 := by nlinarith only [hxsmall,hd1,hd0]
      by_cases hh0 : h=0
      · subst h
        norm_num only [Nat.cast_zero,zero_mul] at hz
        have hz0 : (0:Real)<(z:Real) := by linarith only [hz,hzneg]
        have hz1 : (z:Real)<1 := by nlinarith only [hz,hx0,ha1,ha0,hd0,hd1]
        have hz0I : (0:Int)<z := by exact_mod_cast hz0
        have hz1I : z<(1:Int) := by exact_mod_cast hz1
        omega
      · have hb:=hbest h (by omega) hhq z
        rw [hz,abs_of_neg hzneg] at hb
        nlinarith only [hb,hx0,hd0]
    · have hxsmall : x<d^2+delta := by
        have hp : y-x=(e:Real)*delta := by rw [hphases] at hphase;exact hphase
        nlinarith only [hp,hy1,hqd,henR,hdelta0]
      let j:=h-q
      have hjEq : h=q+j := by dsimp [j];omega
      have hjq : j<q := by dsimp [r] at hh;omega
      let z : Int := ⌊((Q+h:Nat):Real)*a⌋-(q:Int)-(t:Int)
      have hz : (j:Real)*a-z=x+(1-a)*d := by
        dsimp only [z,x,Int.fract]
        rw [hjEq]
        push_cast
        linear_combination -hQe-he
      have hzpos : 0<x+(1-a)*d := by nlinarith only [hx0,ha1,hd0]
      by_cases hj0 : j=0
      · rw [hj0] at hz
        norm_num only [Nat.cast_zero,zero_mul] at hz
        have hz0 : (0:Real)< -(z:Real) := by linarith only [hz,hzpos]
        have hz1 : -(z:Real)<1 := by
          dsimp only [delta] at hxsmall
          nlinarith only [hz,hxsmall,hd0,hd2,ha0,ha1,hs]
        have hz0I : (0:Int)< -z := by exact_mod_cast hz0
        have hz1I : -z<(1:Int) := by exact_mod_cast hz1
        omega
      · have hb:=hbest j (by omega) hjq z
        rw [hz,abs_of_pos hzpos] at hb
        dsimp only [delta] at hxsmall
        nlinarith only [hb,hxsmall,hd1,hd0]
#print axioms silver_w2_no_r_period

set_option maxHeartbeats 2000000 in
theorem silver_short_period_exclusion (k n i m : Nat) (hk : 1 ≤ k)
    (hn : 2*P (k + 1)*(P (k + 1)+P k)+P (k + 1)-1 ≤ n)
    (hm0 : 0<m) (hmlt : m<2*P (k + 1))
    (hmq : m≠P (k + 1)) (hmr : m≠P (k + 1)+P k) :
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
  have hs := hquadratic
  change a^2+2*a=1 at hs
  have hprev : a^k=(2+a)*d := by
    dsimp [d]
    rw [pow_succ]
    linear_combination -(a^k)*hs
  have htprev : P (k-1 + 1)=t := by
    obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
    simp [t,Nat.add_assoc]
  intro hp
  obtain ⟨h,e,l,c,hh,hl,he0,hc,hnlen,hfloor,herror⟩:=period_constraints n i m hp
  have hen : r≤e := by
    change 2*q*r+q-1≤n at hn
    change m<2*q at hmlt
    have hsub:=Nat.sub_add_cancel (show 1≤2*q*r+q by omega)
    by_contra hne
    have heR : e+2≤r+1 := by omega
    have hmR : m≤2*q-1 := by omega
    have hmul:=Nat.mul_le_mul heR hmR
    have hsM:=Nat.sub_add_cancel (show 1≤2*q by omega)
    have hid:=congrArg (fun z:Nat => (r+1)*z) hsM
    have hn2 : n+2≤(e+2)*m := by nlinarith only [hnlen,hh,hl]
    have hrq : q≤r := by dsimp [r];omega
    nlinarith only [hn,hsub,hmul,hid,hn2,hrq]
  have herr : a^k≤|(m:Real)*a-c| := by
    by_cases hmq' : m<q
    · have hb:=silver_best_approximation (k-1) m hm0
        (by simpa [show k-1+2=k+1 by omega,q] using hmq') (c:Int)
      simpa [show k-1+1=k by omega] using hb
    · have hb:=silver_gap_approximation (k-1) m
        (by simpa [show k-1+2=k+1 by omega,q] using (show q≤m by omega))
        (by
          rw [show k-1+3=k+2 by omega]
          have hQrec : P (k + 2)=2*q+t := by cases k <;> rfl
          rw [hQrec];omega)
        (by simpa [show k-1+2=k+1 by omega] using hmq)
        (by rw [show k-1+2=k+1 by omega];change m≠2*q;omega)
        (by simpa [show k-1+2=k+1 by omega,show k-1+1=k by omega] using hmr) (c:Int)
      rw [show k-1+1=k by omega,show k-1+2=k+1 by omega] at hb
      change d+a^k≤|(m:Real)*a-c| at hb
      linarith
  have hrbound : 1<(r:Real)*a^k := by
    have htR : (0:Real)<t := by exact_mod_cast ht0
    have htd : 0<(1+a)*(t:Real)*d := by positivity
    rw [hprev,hrr]
    nlinarith [hm,hQr]
  have henR : (r:Real)≤e := by exact_mod_cast hen
  have hb1:=mul_le_mul_of_nonneg_right henR (pow_nonneg ha0.le k)
  have hb2:=mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg e)
  linarith
#print axioms silver_short_period_exclusion
end D5.S1.Words.Mechanical
