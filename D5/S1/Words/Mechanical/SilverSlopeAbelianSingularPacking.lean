/- GID: D5/S1/Words/Mechanical/SilverSlopeAbelianSingularPacking
   generality: I
   mirror-B: none(waiver:open-problem-stage-a)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Separation and packing of singular silver convergent windows. -/
/-
Judgement form:
  silver_singular_separation:
    proof_shape: content
    escape_witness: silver_best_approximation k m hm hmq z: silverSlope^(k+1) ≤ |(m :
      Real)*silverSlope-z| for every 0<m<P(k+2) and every integer z
    Non-binding step: The proof applies this live inequality to m=v-u and the floor difference;
      the phase intervals then force separation. Its inlined integer-coordinate proof is
      substantive.
    Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
      (sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d);
      D5/S1/Words/Mechanical/MechanicalBalance
      (sha256:db7434e78bc669a2f0d5711175f8f744fc6dfba359dd5414cc8c05c753ad3399);
      D5/S1/Words/Mechanical/MechanicalFactorComplexity
      (sha256:9b83310d03f384fa38264d66462adfe64f238b0be826575d08630dad3141f15a)
  silver_no_q_length:
    proof_shape: content
    escape_witness: silver_singular_separation: for singular length-P(k+1) windows at u<v,
      P(k+2)≤v-u
    Non-binding step: The result consumes this new separation in its residue-witness
      packing/injectivity proof. Fintype.card_le_of_injective alone cannot provide the singular
      residue witnesses.
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
theorem silver_singular_separation (k u v : Nat) (hk : 1 ≤ k) (huv : u < v)
    (hu : (lowerMechanicalFactor silverSlope 0 (P (k + 1)) u).count true ≠ P k)
    (hv : (lowerMechanicalFactor silverSlope 0 (P (k + 1)) v).count true ≠ P k) :
    P (k + 2) ≤ v-u := by
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

  let a := silverSlope
  let d := a^(k+1)
  let q := P (k + 1)
  let t := P k
  have ha0 : 0<a := by
    dsimp [a,silverSlope]
    have h := Real.sqrt_nonneg (2:Real)
    have hs : (Real.sqrt (2:Real))^2=2 := by norm_num
    nlinarith
  have ha1 : a<1/2 := by
    dsimp [a,silverSlope]
    have h := Real.sqrt_nonneg (2:Real)
    have hs : (Real.sqrt (2:Real))^2=2 := by norm_num
    nlinarith
  have hd0 : 0<d := pow_pos ha0 _
  have hd1 : d<1 := pow_lt_one₀ ha0.le (by linarith) (by omega)
  have he := silverPell_error_formula k
  change (q:Real)*a-t=(-1:Real)^k*d at he
  have hc : ∀ j : Nat, ((lowerMechanicalFactor silverSlope 0 q j).count true:Int)=
      ⌊((j+q:Nat):Real)*a⌋-⌊(j:Real)*a⌋ := by
    intro j
    rw [factor_count_true]
    simpa using lowerMechanicalWindowTrueCount_eq_floor (rho:=0) ha0.le (by linarith) j q
  have hsing : ∀ j : Nat, (lowerMechanicalFactor silverSlope 0 q j).count true≠t →
      (Even k → 1-d≤Int.fract ((j:Real)*a)) ∧
      (Odd k → Int.fract ((j:Real)*a)<d) := by
    intro j hj
    have hx0 := Int.fract_nonneg ((j:Real)*a)
    have hx1 := Int.fract_lt_one ((j:Real)*a)
    have hfloor : ∀ err : Real, (q:Real)*a=t+err →
        0≤Int.fract ((j:Real)*a)+err → Int.fract ((j:Real)*a)+err<1 →
        (lowerMechanicalFactor silverSlope 0 q j).count true=t := by
      intro err heq h0 h1
      have hf : ⌊((j+q:Nat):Real)*a⌋=⌊(j:Real)*a⌋+(t:Int) := by
        apply Int.floor_eq_iff.mpr
        dsimp only [Int.fract] at h0 h1
        push_cast
        constructor <;> nlinarith only [heq,h0,h1]
      have hcc := hc j
      rw [hf] at hcc
      have hcc' : ((lowerMechanicalFactor silverSlope 0 q j).count true:Int)=(t:Int) := by omega
      exact_mod_cast hcc'
    constructor
    · intro hp
      have hep : (q:Real)*a=t+d := by rw [hp.neg_one_pow] at he;linarith
      by_contra hn
      exact hj (hfloor d hep (by linarith) (by linarith))
    · intro hp
      have hep : (q:Real)*a=t-d := by rw [hp.neg_one_pow] at he;linarith
      by_contra hn
      exact hj (hfloor (-d) (by linarith) (by linarith) (by linarith))
  have hux := hsing u hu
  have hvx := hsing v hv
  have hdiff : |Int.fract ((v:Real)*a)-Int.fract ((u:Real)*a)|<d := by
    have hu0 := Int.fract_nonneg ((u:Real)*a)
    have hu1 := Int.fract_lt_one ((u:Real)*a)
    have hv0 := Int.fract_nonneg ((v:Real)*a)
    have hv1 := Int.fract_lt_one ((v:Real)*a)
    apply abs_lt.mpr
    rcases Nat.even_or_odd k with hp | hp
    · have hh := hux.1 hp
      have hh' := hvx.1 hp
      constructor <;> linarith
    · have hh := hux.2 hp
      have hh' := hvx.2 hp
      constructor <;> linarith
  by_contra hn
  have hb := silver_best_approximation k (v-u) (by omega) (by omega)
    (⌊(v:Real)*a⌋-⌊(u:Real)*a⌋)
  have heq : ((v-u:Nat):Real)*a-(⌊(v:Real)*a⌋-⌊(u:Real)*a⌋:Int)=
      Int.fract ((v:Real)*a)-Int.fract ((u:Real)*a) := by
    rw [Nat.cast_sub (by omega)]
    dsimp only [Int.fract]
    push_cast
    ring
  change d≤|((v-u:Nat):Real)*a-(⌊(v:Real)*a⌋-⌊(u:Real)*a⌋:Int)| at hb
  rw [heq] at hb
  linarith
#print axioms silver_singular_separation

set_option maxHeartbeats 2000000 in
theorem silver_no_q_length (k n i : Nat) (hk : 1≤k) (hn : P (k + 1)<n)
    (hnot : ¬ AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) (P (k + 1))) :
    (P (k + 1)-1)*P (k + 2)+P (k + 1) ≤ n := by
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

  classical
  let a := silverSlope
  let d := a^(k+1)
  let q := P (k + 1)
  let t := P k
  let Q := P (k + 2)
  have hq0 : 0<q := (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : 0 < P (k + 1))
  have ht0 : 0<t := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
    exact (by have hs := (pell_companion_step j).1; obtain ⟨j, hj⟩ := companion_odd j; omega : 0 < P (j + 1))
  have htq : t<q := (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : P k < P (k + 1))
  have hq2 : 2≤q := by omega
  have hQq : q<Q := by
    have h := (by have hs := (pell_companion_step (k+1)).1; obtain ⟨j, hj⟩ := companion_odd (k+1); omega : P (k+1) < P (k+1 + 1))
    simpa [Nat.add_assoc,q,Q] using h
  have ha0 : 0<a := by
    dsimp [a,silverSlope]
    have h := Real.sqrt_nonneg (2:Real)
    have hs : (Real.sqrt (2:Real))^2=2 := by norm_num
    nlinarith
  have ha1 : a<1/2 := by
    dsimp [a,silverSlope]
    have h := Real.sqrt_nonneg (2:Real)
    have hs : (Real.sqrt (2:Real))^2=2 := by norm_num
    nlinarith
  have hd0 : 0<d := pow_pos ha0 _
  have hda : d<a := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
    have hp : a^j≤1 := pow_le_one₀ ha0.le (by linarith)
    have hp0 : 0≤a^j := pow_nonneg ha0.le _
    dsimp [d]
    rw [show j+1+1=j+2 by omega,pow_add]
    nlinarith
  have he := silverPell_error_formula k
  change (q:Real)*a-t=(-1:Real)^k*d at he
  have hqR : (q:Real)*a < t+a ∧ t-a<(q:Real)*a := by
    have hb : |(q:Real)*a-t|=d := by
      rw [he,abs_mul]
      simp [abs_pow,abs_of_pos hd0]
    have hh := abs_le.mp hb.le
    constructor <;> linarith
  have hc : ∀ h j : Nat, ((lowerMechanicalFactor silverSlope 0 h j).count true:Int)=
      ⌊((j+h:Nat):Real)*a⌋-⌊(j:Real)*a⌋ := by
    intro h j
    rw [factor_count_true]
    simpa using lowerMechanicalWindowTrueCount_eq_floor (rho:=0) ha0.le (by linarith) j h
  have hshort : ∀ h j : Nat, h<q →
      (lowerMechanicalFactor silverSlope 0 h j).count true≤t ∧
      h-(lowerMechanicalFactor silverSlope 0 h j).count true≤q-t := by
    intro h j hh
    let c := (lowerMechanicalFactor silverSlope 0 h j).count true
    have hfloor := hc h j
    have hfloorR : (c:Real)=
        (⌊((j+h:Nat):Real)*a⌋:Real)-(⌊(j:Real)*a⌋:Real) := by exact_mod_cast hfloor
    have hf0 := Int.floor_le (((j+h:Nat):Real)*a)
    have hf1 := Int.lt_floor_add_one (((j+h:Nat):Real)*a)
    have hg0 := Int.floor_le ((j:Real)*a)
    have hg1 := Int.lt_floor_add_one ((j:Real)*a)
    have hjh : ((j+h:Nat):Real)=(j:Real)+h := by push_cast;rfl
    rw [hjh] at hf0 hf1 hfloorR
    have hlow : (h:Real)*a-1<c := by nlinarith only [hfloorR,hf1,hg0]
    have hupp : (c:Real)<(h:Real)*a+1 := by nlinarith only [hfloorR,hf0,hg1]
    have hhR : (h:Real)+1≤q := by exact_mod_cast (show h+1≤q by omega)
    have hct : (c:Real)<(t:Real)+1 := by nlinarith only [hupp,hhR,ha0,hqR.1]
    have hcf : (h:Real)-(c:Real)<(q:Real)-t+1 := by
      nlinarith only [hlow,hhR,ha0,ha1,hqR.2,hda]
    have hctN : c<t+1 := by exact_mod_cast hct
    have hclen : c≤h := by
      exact (List.count_le_length (a:=true) (l:=lowerMechanicalFactor silverSlope 0 h j)).trans_eq (by simp [lowerMechanicalFactor])
    have htqR : (t:Real)≤q := by exact_mod_cast htq.le
    have hcfN : h-c<q-t+1 := by
      exact_mod_cast (show ((h-c:Nat):Real)<((q-t+1:Nat):Real) by
        rw [Nat.cast_sub hclen,Nat.cast_add,Nat.cast_sub htq.le]
        norm_num
        exact hcf)
    constructor <;> omega
  have hregular_period : ∀ h : Nat, h<q → h+q≤n →
      (∀ j, h+j*q+q≤n → (lowerMechanicalFactor silverSlope 0 q (i+h+j*q)).count true=t) →
      AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) q := by
    intro h hh hfit hall
    let e := (n-h)/q
    let l := (n-h)%q
    have he0 : 0<e := Nat.div_pos (by omega) hq0
    have hl : l<q := Nat.mod_lt _ hq0
    have hnlen : h+e*q+l=n := by
      have hdiv := Nat.mod_add_div (n-h) q
      have hdiv' : l+e*q=n-h := by simpa [e,l,Nat.mul_comm] using hdiv
      omega
    rw [←hnlen]
    apply period_of_counts h e l q t i hq0 he0 htq.le hh hl
    · intro j hj
      apply hall j
      have hmul := Nat.mul_le_mul_right q (show j+1≤e by omega)
      nlinarith only [hnlen,hmul]
    · exact (hshort h i hh).1
    · exact (hshort h i hh).2
    · exact (hshort l (i+h+e*q) hl).1
    · exact (hshort l (i+h+e*q) hl).2
  have hnshort : 2*q-1≤n := by
    by_contra hsmall
    have hchoose : ∃ h : Nat, h≤1 ∧
        (lowerMechanicalFactor silverSlope 0 q (i+h)).count true=t := by
      by_cases h0 : (lowerMechanicalFactor silverSlope 0 q i).count true=t
      · exact ⟨0,by omega,by simpa using h0⟩
      · by_cases h1 : (lowerMechanicalFactor silverSlope 0 q (i+1)).count true=t
        · exact ⟨1,by omega,h1⟩
        · have hsep := silver_singular_separation k i (i+1) hk (by omega) h0 h1
          change Q ≤ (i+1)-i at hsep
          omega
    obtain ⟨h,hh,hcount⟩ := hchoose
    apply hnot
    apply hregular_period h (by omega) (by change q<n at hn;omega)
    intro j hj
    have hj0 : j=0 := by
      by_contra hjne
      have hmul : q≤j*q := by nlinarith [show 1≤j by omega]
      omega
    simpa [hj0] using hcount
  have hres : ∀ h : Fin q, ∃ s : Nat, s≤n-q ∧ s%q=h.val ∧
      (lowerMechanicalFactor silverSlope 0 q (i+s)).count true≠t := by
    intro h
    by_contra hnone
    have hall : ∀ j, h.val+j*q+q≤n →
        (lowerMechanicalFactor silverSlope 0 q (i+h.val+j*q)).count true=t := by
      intro j hj
      by_contra hsing
      apply hnone
      refine ⟨h.val+j*q,by omega,?_,?_⟩
      · simp [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt h.isLt]
      · simpa [Nat.add_assoc] using hsing
    apply hnot
    exact hregular_period h.val h.isLt (by omega) hall
  choose s hsbound hsmod hsing using hres
  let f : Fin q → Fin ((n-q)/Q+1) := fun h =>
    ⟨s h/Q,by have hb:=Nat.div_le_div_right (c:=Q) (hsbound h);omega⟩
  have hfinj : Function.Injective f := by
    intro h j heq
    have heqdiv : s h/Q=s j/Q := congrArg Fin.val heq
    by_cases hsj : s h=s j
    · apply Fin.ext
      rw [←hsmod h,←hsmod j,hsj]
    · have hsep : Q≤s h-s j ∨ Q≤s j-s h := by
        rcases lt_or_gt_of_ne hsj with hlt | hgt
        · right
          have hh := silver_singular_separation k (i+s h) (i+s j) hk
            (by omega) (hsing h) (hsing j)
          simpa only [Nat.add_sub_add_left] using hh
        · left
          have hh := silver_singular_separation k (i+s j) (i+s h) hk
            (by omega) (hsing j) (hsing h)
          simpa only [Nat.add_sub_add_left] using hh
      have hhmod := Nat.mod_lt (s h) (show 0<Q by omega)
      have hjmod := Nat.mod_lt (s j) (show 0<Q by omega)
      have hhdiv := Nat.mod_add_div (s h) Q
      have hjdiv := Nat.mod_add_div (s j) Q
      rw [heqdiv] at hhdiv
      rcases hsep with hsep | hsep <;> omega
  have hcard := Fintype.card_le_of_injective f hfinj
  simp only [Fintype.card_fin] at hcard
  have hmul := Nat.mul_le_mul_right Q (show q-1≤(n-q)/Q by omega)
  have hdiv := Nat.div_mul_le_self (n-q) Q
  change (q-1)*Q+q≤n
  omega
#print axioms silver_no_q_length
end D5.S1.Words.Mechanical
