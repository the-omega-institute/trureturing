/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original memory languages retain literal positive-growth codebooks and exact nesting. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
open Filter Topology
open scoped ENNReal NNReal Matrix.Norms.Operator

/-- No run reaches the high length K; this is the original low cap K-1. -/
def LowCapLanguage (K : ℕ) : Set (ℤ → CuLetter) :=
  {ω | ∀ i : ℤ, ¬ ∀ k : Fin K, ω (i+(k : ℕ)) = .c}

/-- The complete low-cap language enters both actual retained memory models,
independently of the real threshold and of the guard's strictness. -/
theorem original_low_cap_inclusion (side : MemorySide) (n K : ℕ) (d : ℝ)
    (positive : 0 < K) : LowCapLanguage K ⊆ MemoryLanguage side n K d := by
  intro ω hω
  have cap : ∀ i : ℤ, ¬ ∀ k : Fin (K+1), ω (i+(k : ℕ))=.c := by
    intro i run
    exact hω i (fun k => run ⟨k.val,by omega⟩)
  have nohigh : ∀ i : ℤ, ¬ ∀ k : Fin K, ω (i-(k : ℕ))=.c := by
    have e : K-1+1=K := by omega
    have h : ∀ i : ℤ, ¬ ∀ k : Fin ((K-1)+1), ω (i+(k : ℕ))=.c := by
      rw [e]; exact hω
    have hr := (forbidden_run_reversal (K-1) ω).mp h
    rw [e] at hr
    exact hr
  cases side <;> exact ⟨cap,fun i run => False.elim (nohigh i run)⟩

/-- The two literal five-letter words each have original weight fifty-eight. -/
def lowBlock (b : Bool) : List CuLetter :=
  if b then [.c,.u,.u,.c,.u] else [.c,.u,.c,.u,.u]

/-- A single bilateral concatenation realizes arbitrary binary choices at the
fixed five-letter cuts, including negative block indices. -/
def lowSequence (choices : ℤ → Bool) (i : ℤ) : CuLetter :=
  if i % 5 = 0 ∨ i % 5 = (if choices (i / 5) then 3 else 2) then .c else .u

/-- Every arbitrary bilateral concatenation has no adjacent c, and hence
belongs to the low cap for every K at least two. -/
theorem literal_bilateral_low_codebook (choices : ℤ → Bool) (K : ℕ) (hK : 2 ≤ K) :
    (∀ (j : ℤ) (k : Fin 5),
      lowSequence choices (5*j+(k : ℕ)) = (lowBlock (choices j))[k]'(by cases choices j <;> simpa [lowBlock] using k.isLt)) ∧
    lowSequence choices ∈ LowCapLanguage K := by
  have digits (j : ℤ) (k : Fin 5) :
      lowSequence choices (5*j+(k : ℕ)) = (lowBlock (choices j))[k]'(by cases choices j <;> simpa [lowBlock] using k.isLt) := by
    have div : (5*j+(k : ℕ))/5=j := by omega
    have mod : (5*j+(k : ℕ))%5=(k : ℕ) := by omega
    simp only [lowSequence,div,mod]
    fin_cases k <;> cases choices j <;> simp [lowBlock]
  refine ⟨digits,?_⟩
  intro i run
  have first := run ⟨0,by omega⟩
  have next := run ⟨1,by omega⟩
  simp only [Nat.cast_zero,add_zero,Nat.cast_one] at first next
  have fc : i%5=0 ∨ i%5=(if choices (i/5) then 3 else 2) := by
    by_contra h
    rw [lowSequence,if_neg h] at first
    cases first
  have nc : (i+1)%5=0 ∨ (i+1)%5=(if choices ((i+1)/5) then 3 else 2) := by
    by_contra h
    rw [lowSequence,if_neg h] at next
    cases next
  have rem : i%5<4 := by
    cases h1 : choices (i/5) <;>
      simp only [h1,Bool.false_eq_true,ite_false,ite_true] at fc <;> omega
  have quo : i/5=(i+1)/5 := by omega
  rw [← quo] at nc
  cases h1 : choices (i/5) <;>
    simp only [h1,Bool.false_eq_true,ite_false,ite_true] at fc nc <;> omega

/-- The seed envelopes are monotone in memory, bracket the actual bilateral
state, and have the original contraction width. -/
theorem original_memory_envelopes (ω : ℤ → CuLetter) (i : ℤ) (n : ℕ) :
    finitePast ω i n 0 ≤ finitePast ω i (n+1) 0 ∧
    finitePast ω i (n+1) (hSide .high) ≤ finitePast ω i n (hSide .high) ∧
    finitePast ω i n 0 ≤ pastState ω i ∧
    pastState ω i ≤ finitePast ω i n (hSide .high) ∧
    finitePast ω i n (hSide .high)-finitePast ω i n 0 ≤ hSide .high*rho^n := by
  rcases bilateral_past_state with ⟨difference,contraction,bounds,limits,_⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have gp : 0 < g := by dsimp [g,t]; nlinarith
  have g1 : g < 1 := by dsimp [g,t]; nlinarith
  have rp : 0 ≤ rho := (pow_pos gp 6).le
  have cp : 0 ≤ chi := (pow_pos gp 20).le
  have r1 : rho ≤ 1 := (pow_lt_one₀ gp.le g1 (by decide : (6 : ℕ) ≠ 0)).le
  have c1 : chi ≤ 1 := (pow_lt_one₀ gp.le g1 (by decide : (20 : ℕ) ≠ 0)).le
  have hp : 0 ≤ hSide .high := (bounds ω i).1.trans (bounds ω i).2
  have mapMono (a : CuLetter) : Monotone (letterMap a) := by
    intro x y hxy
    cases a <;> simp only [letterMap]
    · exact mul_le_mul_of_nonneg_left hxy cp
    · exact add_le_add_right (mul_le_mul_of_nonneg_left hxy rp) _
  have mapBounds (a : CuLetter) : 0 ≤ letterMap a 0 ∧
      letterMap a (hSide .high) ≤ hSide .high := by
    cases a <;> simp only [letterMap,mul_zero,add_zero]
    · exact ⟨le_rfl,(mul_le_mul_of_nonneg_right c1 hp).trans_eq (one_mul _)⟩
    · constructor
      · unfold aSide; exact mul_nonneg (sub_nonneg.mpr r1) hp
      · unfold aSide; nlinarith
  have lowerStep (j : ℤ) (m : ℕ) : finitePast ω j m 0 ≤ finitePast ω j (m+1) 0 := by
    induction m generalizing j with
    | zero => exact (mapBounds _).1
    | succ m ih => exact mapMono _ (ih (j-1))
  have upperStep (j : ℤ) (m : ℕ) :
      finitePast ω j (m+1) (hSide .high) ≤ finitePast ω j m (hSide .high) := by
    induction m generalizing j with
    | zero => exact (mapBounds _).2
    | succ m ih => exact mapMono _ (ih (j-1))
  have lm : Monotone (fun m => finitePast ω i m 0) := monotone_nat_of_le_succ (lowerStep i)
  have um : Antitone (fun m => finitePast ω i m (hSide .high)) :=
    antitone_nat_of_succ_le (upperStep i)
  have ll := limits ω i 0 le_rfl hp
  have ul := limits ω i (hSide .high) hp le_rfl
  refine ⟨lowerStep i n,upperStep i n,?_,?_,?_⟩
  · exact ge_of_tendsto ll (eventually_atTop.mpr ⟨n,fun m hm => lm hm⟩)
  · exact le_of_tendsto ul (eventually_atTop.mpr ⟨n,fun m hm => um hm⟩)
  · rw [difference,sub_zero]
    exact (mul_le_mul_of_nonneg_right (contraction ω i n).2 hp).trans_eq (mul_comm _ _)

/-- Actual lower, auxiliary and upper languages have the original nesting.
No desired inclusion is supplied as a premise. -/
theorem original_memory_language_nesting (n K : ℕ) (d : ℝ) :
    MemoryLanguage .lower n K d ⊆ MemoryLanguage .lower (n+1) K d ∧
    MemoryLanguage .lower (n+1) K d ⊆ AuxiliaryLanguage K d ∧
    AuxiliaryLanguage K d ⊆ MemoryLanguage .upper (n+1) K d ∧
    MemoryLanguage .upper (n+1) K d ⊆ MemoryLanguage .upper n K d := by
  refine ⟨?_,?_,?_,?_⟩
  · intro ω hω
    refine ⟨hω.1,fun i run => (hω.2 i run).trans_le (original_memory_envelopes ω i n).1⟩
  · intro ω hω
    refine ⟨hω.1,fun i run => ((hω.2 i run).trans_le
      (original_memory_envelopes ω i (n+1)).2.2.1).le⟩
  · intro ω hω
    refine ⟨hω.1,fun i run => (hω.2 i run).trans
      (original_memory_envelopes ω i (n+1)).2.2.2.1⟩
  · intro ω hω
    refine ⟨hω.1,fun i run => (hω.2 i run).trans (original_memory_envelopes ω i n).2.1⟩

/-- The closed upper-memory languages intersect in exactly the original
auxiliary language; true guard equality is retained at every memory length. -/
theorem original_upper_memory_intersection (K : ℕ) (d : ℝ) :
    {ω | ∀ n : ℕ, K ≤ n → ω ∈ MemoryLanguage .upper n K d} = AuxiliaryLanguage K d := by
  ext ω
  constructor
  · intro hω
    refine ⟨(hω K le_rfl).1,?_⟩
    intro i run
    have hp : 0 ≤ hSide .high := (bilateral_past_state.2.2.1 ω i).1.trans
      (bilateral_past_state.2.2.1 ω i).2
    apply ge_of_tendsto (bilateral_past_state.2.2.2.1 ω i (hSide .high) hp le_rfl)
    exact eventually_atTop.mpr ⟨K,fun n hn => (hω n hn).2 i run⟩
  · intro hω n hn
    exact ⟨hω.1,fun i run => (hω.2 i run).trans
      (original_memory_envelopes ω i n).2.2.2.1⟩


/-- At every multiple of the actual block weight there are at least 2^q
original factors. The binary choices are constructed and are not an entropy
premise. Both memory sides and every real threshold are included. -/
theorem original_literal_codebook_growth (side : MemorySide) (n K : ℕ) (d : ℝ)
    (hK : 2 ≤ K) (q : ℕ) :
    2^q ≤ factorCount (MemoryLanguage side n K d) (q*58) := by
  classical
  let X := MemoryLanguage side n K d
  have blockWeight (b : Bool) : wordWeight (lowBlock b)=58 := by cases b <;> rfl
  let block : Bool → {w : List CuLetter // wordWeight w=58} :=
    fun b => ⟨lowBlock b,blockWeight b⟩
  have blockInj : Function.Injective block := by
    intro a b eq
    have he := congrArg Subtype.val eq
    cases a <;> cases b <;> simp_all [block,lowBlock]
  let word (bits : Fin q → Bool) := ((List.ofFn (fun i => block (bits i))).map Subtype.val).flatten
  have wordInj : Function.Injective word := by
    intro a b he
    have blocks := equal_weight_concatenation_injective 58 (by decide) he
    have functions := List.ofFn_injective blocks
    funext i
    exact blockInj (congrFun functions i)
  have weight (bits : Fin q → Bool) : wordWeight (word bits)=q*58 := by
    have sum (bs : List {w : List CuLetter // wordWeight w=58}) :
        wordWeight ((bs.map Subtype.val).flatten)=bs.length*58 := by
      induction bs with
      | nil => simp [wordWeight]
      | cons b bs ih =>
        simp only [List.map_cons,List.flatten_cons,word_weight_geometry.1,b.property,
          ih,List.length_cons]
        omega
    simpa [word] using sum (List.ofFn (fun i => block (bits i)))
  have occurs (bits : Fin q → Bool) : ∃ ω ∈ X, Occurs ω (word bits) := by
    let choices : ℤ → Bool := fun j => if hj : 0 ≤ j ∧ j < q then
      bits ⟨j.toNat,by omega⟩ else false
    let W : ℤ → List CuLetter := fun j => lowBlock (choices j)
    have length (j : ℤ) : (W j).length=5 := by dsimp [W,lowBlock]; split_ifs <;> rfl
    have positive : ∀ j, 0 < (W j).length := fun j => by rw [length]; decide
    have cut (j : ℤ) : blockCut W j=5*j := by
      have step := (positive_block_tiling W positive).2.1
      have forwards (m : ℕ) : blockCut W (m : ℤ)=5*(m : ℤ) := by
        induction m with
        | zero => rfl
        | succ m ih => rw [Nat.cast_add,Nat.cast_one,step,ih,length]; ring
      have backwards (m : ℕ) : blockCut W (-(m : ℤ))=5*(-(m : ℤ)) := by
        induction m with
        | zero => rfl
        | succ m ih =>
          have hs := step (-((m+1 : ℕ) : ℤ))
          have hi : -((m+1 : ℕ) : ℤ)+1=-(m : ℤ) := by omega
          rw [hi,ih,length] at hs
          omega
      cases j with
      | ofNat m => exact forwards m
      | negSucc m => exact backwards (m+1)
    have member := (literal_bilateral_low_codebook choices K hK).2
    have tiles : ∀ j (k : Fin (W j).length),
        lowSequence choices (blockCut W j+(k : ℕ))=(W j)[k] := by
      intro j k
      rw [cut]
      exact (literal_bilateral_low_codebook choices K hK).1 j ⟨k.val,by rw [← length j]; exact k.isLt⟩
    have window (a : ℤ) (m : ℕ) : blockWindow W a m =
        ((choiceWindow choices a m).map lowBlock).flatten := by
      induction m generalizing a with
      | zero => rfl
      | succ m ih => simp only [blockWindow,choiceWindow,List.map_cons,List.flatten_cons,W,ih]
    have actual : blockWindow W 0 q=word bits := by
      rw [window,choice_window_ofFn]
      have restrict : (fun i : Fin q => choices (0+(i : ℕ))) = bits := by
        funext i
        simp [choices,show (0 : ℤ) ≤ (i : ℕ) by positivity,
          show ((i : ℕ) : ℤ) < q by exact_mod_cast i.isLt]
      simp only [Nat.cast_zero,zero_add] at restrict
      simp only [List.map_ofFn]
      dsimp [word,block]
      simp only [List.map_ofFn]
      congr 2
      funext i
      simpa only [zero_add,Function.comp_apply] using congrArg lowBlock (congrFun restrict i)
    refine ⟨lowSequence choices,original_low_cap_inclusion side n K d (by omega) member,?_⟩
    have h : Occurs (lowSequence choices) (blockWindow W 0 q) :=
      ⟨blockCut W 0,tiled_window_occurs W positive (lowSequence choices) tiles 0 q⟩
    rw [actual] at h
    exact h
  let inject : (Fin q → Bool) → FactorDictionary X (q*58) :=
    fun bits => ⟨word bits,occurs bits,weight bits⟩
  have inj : Function.Injective inject := fun a b he => wordInj (congrArg Subtype.val he)
  letI : Finite (FactorDictionary X (q*58)) := (factor_dictionary_bound X (q*58)).1
  have count := Nat.card_le_card_of_injective inject inj
  simpa [factorCount,Nat.card_eq_fintype_card,Fintype.card_fun,X] using count

/-- The original weighted factor rate is uniformly positive, with the literal
bound one binary bit per fifty-eight actual source steps. -/
theorem original_positive_weighted_rate (side : MemorySide) (n K : ℕ) (d : ℝ)
    (hK : 2 ≤ K) :
    (1 : ℝ)/58 ≤ weightedFactorRate (MemoryLanguage side n K d) := by
  have bound := factor_rate_of_power_count (MemoryLanguage side n K d) 2 58
    (by decide) (original_literal_codebook_growth side n K d hK)
  simpa only [max_eq_right (by decide : 1 ≤ (2 : ℕ)),Nat.cast_ofNat,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] using bound


private theorem factor_count_mono {X Y : Set (ℤ → CuLetter)} (incl : X ⊆ Y) (T : ℕ) :
    factorCount X T ≤ factorCount Y T := by
  classical
  let inject : FactorDictionary X T → FactorDictionary Y T := fun w =>
    ⟨w.val,by rcases w.property.1 with ⟨ω,hω,occ⟩; exact ⟨ω,incl hω,occ⟩,w.property.2⟩
  letI : Finite (FactorDictionary Y T) := (factor_dictionary_bound Y T).1
  exact Nat.card_le_card_of_injective inject (fun _ _ he =>
    Subtype.ext (congrArg (fun w : FactorDictionary Y T => w.val) he))

private theorem weighted_factor_rate_mono {X Y : Set (ℤ → CuLetter)} (incl : X ⊆ Y) :
    weightedFactorRate X ≤ weightedFactorRate Y := by
  apply le_of_forall_gt
  intro t ht
  obtain ⟨s,hs,st⟩ := exists_between ht
  have sp : 0 < s := (factor_rate_nonneg Y).trans_lt hs
  have cy := (factor_rate_convergence Y s sp).1 hs
  have cx : Summable (fun T : ℕ => (factorCount X T : ℝ)*((2 : ℝ)^(-s))^T) := by
    apply cy.of_norm_bounded
    intro T
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast factor_count_mono incl T) (by positivity)
  exact ((factor_rate_convergence X s sp).2 cx).trans_lt st

/-- The rates use the actual nested bilateral languages, giving the lower and
upper monotonicities and the auxiliary-language sandwich. -/
theorem original_memory_rate_nesting (n K : ℕ) (d : ℝ) :
    weightedFactorRate (MemoryLanguage .lower n K d) ≤
      weightedFactorRate (MemoryLanguage .lower (n+1) K d) ∧
    weightedFactorRate (MemoryLanguage .lower (n+1) K d) ≤
      weightedFactorRate (AuxiliaryLanguage K d) ∧
    weightedFactorRate (AuxiliaryLanguage K d) ≤
      weightedFactorRate (MemoryLanguage .upper (n+1) K d) ∧
    weightedFactorRate (MemoryLanguage .upper (n+1) K d) ≤
      weightedFactorRate (MemoryLanguage .upper n K d) := by
  have h := original_memory_language_nesting n K d
  exact ⟨weighted_factor_rate_mono h.1,weighted_factor_rate_mono h.2.1,
    weighted_factor_rate_mono h.2.2.1,weighted_factor_rate_mono h.2.2.2⟩

/-- The original all-u vertex and its edge are retained for arbitrary memory.
Its actual k-step monomial supplies z to the power 6k. -/
theorem original_all_u_cycle (side : MemorySide) (n K : ℕ) (d z : ℝ) (hz : 0 ≤ z) :
    ∃ v : CoreVertex side n K d,
      MemoryEdge side K d v.val .u v.val ∧
      ∀ k : ℕ, (z^6)^k ≤ pathMass side n K d z k := by
  classical
  let v : MemoryVertex n := fun _ => .u
  have edge : MemoryEdge side K d v .u v := by
    refine ⟨?_,?_,?_⟩
    · funext k; simp [v,memoryShift]
    · simp [memoryRun]
    · simp [memoryRun]
  let vertex : CoreVertex side n K d :=
    ⟨v,⟨fun _ => v,fun _ => .u,fun _ => edge,rfl⟩⟩
  refine ⟨vertex,edge,?_⟩
  intro k
  let choices : Fin k → CuLetter × CoreVertex side n K d := fun _ => (.u,vertex)
  have walk (m : ℕ) : CorePath side K d m vertex (fun _ => (.u,vertex)) := by
    induction m with
    | zero => trivial
    | succ m ih => exact ⟨edge,ih⟩
  have weight (m : ℕ) : wordWeight (List.replicate m CuLetter.u)=6*m := by
    induction m with
    | zero => rfl
    | succ m ih => simp [List.replicate_succ,wordWeight,ih]; omega
  have term : coreMonomial side K d z k vertex choices=(z^6)^k := by
    rw [coreMonomial,if_pos (walk k)]
    simp only [choices,List.ofFn_const,weight,pow_mul]
  have nonneg (v : CoreVertex side n K d)
      (ch : Fin k → CuLetter × CoreVertex side n K d) :
      0 ≤ coreMonomial side K d z k v ch := by
    unfold coreMonomial; split_ifs <;> positivity
  calc
    (z^6)^k = coreMonomial side K d z k vertex choices := term.symm
    _ ≤ ∑ ch, coreMonomial side K d z k vertex ch :=
      Finset.single_le_sum (fun ch _ => nonneg vertex ch) (Finset.mem_univ choices)
    _ ≤ ∑ v, ∑ ch, coreMonomial side K d z k v ch :=
      Finset.single_le_sum (fun v _ => Finset.sum_nonneg (fun ch _ => nonneg v ch))
        (Finset.mem_univ vertex)
    _ = pathMass side n K d z k := by
      unfold pathMass
      apply Finset.sum_congr rfl
      intro v _
      exact ((original_weighted_adjacency_paths side n K d z).2 k v).symm

private theorem radius_le_of_power_bound
    {A : Type*} [NormedRing A] [CompleteSpace A] [NormedAlgebra ℂ A]
    (a : A) (r B : ℝ) (rp : 0 < r)
    (bound : ∀ k : ℕ, ‖a^k‖ ≤ B*r^k) : spectralRadius ℂ a ≤ ENNReal.ofReal r := by
  by_contra hn
  have gap : ENNReal.ofReal r < spectralRadius ℂ a := lt_of_not_ge hn
  obtain ⟨q,above,below⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp gap
  have qr : r < (q : ℝ) := (ENNReal.ofReal_lt_coe_iff rp.le).mp above
  have growth := tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div rp).mpr qr)
  have large : ∀ᶠ k : ℕ in atTop, B < ((q : ℝ)/r)^k := growth.eventually (eventually_gt_atTop B)
  have gelfand := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a
  have lower : ∀ᶠ k : ℕ in atTop, (q : ℝ)^k < ‖a^k‖ := by
    filter_upwards [gelfand.eventually (eventually_gt_nhds below),eventually_gt_atTop (0 : ℕ)] with k hk kp
    rw [one_div,ENNReal.lt_rpow_inv_iff (Nat.cast_pos.mpr kp)] at hk
    rw [ENNReal.rpow_natCast] at hk
    exact_mod_cast hk
  obtain ⟨k,hk,hlarge⟩ := (lower.and large).exists
  have upper := bound k
  have hrk : 0 < r^k := pow_pos rp k
  have divbound : ((q : ℝ)/r)^k ≤ B := by
    rw [div_pow,div_le_iff₀ hrk]
    exact hk.le.trans upper
  exact (not_lt_of_ge divbound) hlarge

/-- The actual all-u cycle forces the original spectral radius to be at least
z^6, so every positive z has positive spectral radius. -/
theorem original_spectral_positive (side : MemorySide) (n K : ℕ) (d z : ℝ)
    (hz : 0 < z) : ENNReal.ofReal (z^6) ≤ weightedRadius side n K d z := by
  classical
  by_contra hn
  have gap : weightedRadius side n K d z < ENNReal.ofReal (z^6) := lt_of_not_ge hn
  obtain ⟨r,above,below⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp gap
  obtain ⟨B,bp,estimate⟩ := geometric_bound_supplier (complexAdjacency side n K d z) r above
  have rp : 0 < (r : ℝ) := by
    have positive : (0 : ℝ≥0∞) < (r : ℝ≥0∞) :=
      lt_of_le_of_lt (zero_le : (0 : ℝ≥0∞) ≤ weightedRadius side n K d z) above
    exact_mod_cast positive
  have small : (r : ℝ) < z^6 := by
    exact (ENNReal.coe_lt_ofReal).mp below
  let C := (Fintype.card (CoreVertex side n K d) : ℝ)*B
  obtain ⟨v,edge,cycle⟩ := original_all_u_cycle side n K d z hz.le
  have upper (k : ℕ) : (z^6)^k ≤ C*(r : ℝ)^k := by
    exact (cycle k).trans ((path_mass_norm_bounds side n K d z hz.le k).2.2.trans
      (by dsimp [C]; nlinarith [estimate k]))
  have growth := tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div rp).mpr small)
  obtain ⟨k,hk⟩ := (growth.eventually (eventually_gt_atTop C)).exists
  have bound : ((z^6)/(r : ℝ))^k ≤ C := by
    rw [div_pow,div_le_iff₀ (pow_pos rp k)]
    exact upper k
  exact (not_lt_of_ge bound) hk


/-- The real value of the finite original complex spectral radius. -/
noncomputable def radiusValue (side : MemorySide) (n K : ℕ) (d z : ℝ) : ℝ :=
  (weightedRadius side n K d z).toReal

private theorem radius_finite (side : MemorySide) (n K : ℕ) (d z : ℝ) :
    weightedRadius side n K d z ≠ ⊤ := by
  letI : Nonempty (CoreVertex side n K d) :=
    ⟨(original_all_u_cycle side n K d 0 le_rfl).choose⟩
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top
    (spectrum.spectralRadius_le_nnnorm (complexAdjacency side n K d z))

private theorem radius_value_eq (side : MemorySide) (n K : ℕ) (d z : ℝ) :
    ENNReal.ofReal (radiusValue side n K d z) = weightedRadius side n K d z :=
  ENNReal.ofReal_toReal (radius_finite side n K d z)

private theorem radius_mass_comparison (side : MemorySide) (n K : ℕ) (d x y s : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (sp : 0 < s)
    (compare : ∀ k, pathMass side n K d x k ≤ s^k*pathMass side n K d y k) :
    radiusValue side n K d x ≤ s*radiusValue side n K d y := by
  classical
  by_contra hn
  have gap : s*radiusValue side n K d y < radiusValue side n K d x := lt_of_not_ge hn
  let r := (radiusValue side n K d y+radiusValue side n K d x/s)/2
  have yp : 0 ≤ radiusValue side n K d y := ENNReal.toReal_nonneg
  have above : radiusValue side n K d y < r := by
    dsimp [r]; have h := (lt_div_iff₀ sp).mpr (by simpa only [mul_comm] using gap); linarith
  have rp : 0 < r := yp.trans_lt above
  have below : s*r < radiusValue side n K d x := by
    dsimp [r]; have h := (lt_div_iff₀ sp).mpr (by simpa only [mul_comm] using gap)
    have h' := (mul_lt_mul_of_pos_left h sp)
    rw [mul_div_cancel₀ _ sp.ne'] at h'
    have cancel : s*(radiusValue side n K d x/s)=radiusValue side n K d x :=
      mul_div_cancel₀ _ sp.ne'
    nlinarith only [gap,cancel]
  let rate : ℝ≥0 := ⟨r,rp.le⟩
  have spectral : weightedRadius side n K d y < (rate : ℝ≥0∞) := by
    apply (ENNReal.toReal_lt_toReal (radius_finite side n K d y) ENNReal.coe_ne_top).mp
    rw [ENNReal.coe_toReal]
    exact above
  obtain ⟨B,bp,estimate⟩ := geometric_bound_supplier (complexAdjacency side n K d y) rate spectral
  let C := (Fintype.card (CoreVertex side n K d) : ℝ)*B
  have bound (k : ℕ) : ‖complexAdjacency side n K d x ^ k‖ ≤ C*(s*r)^k := by
    calc
      _ ≤ pathMass side n K d x k := (path_mass_norm_bounds side n K d x hx k).2.1
      _ ≤ s^k*pathMass side n K d y k := compare k
      _ ≤ s^k*((Fintype.card (CoreVertex side n K d) : ℝ)*
          ‖complexAdjacency side n K d y ^ k‖) :=
        mul_le_mul_of_nonneg_left (path_mass_norm_bounds side n K d y hy k).2.2 (pow_nonneg sp.le k)
      _ ≤ s^k*((Fintype.card (CoreVertex side n K d) : ℝ)*(B*r^k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (estimate k) (by positivity))
          (pow_nonneg sp.le k)
      _ = C*(s*r)^k := by rw [mul_pow]; dsimp [C]; ring
  have rad := radius_le_of_power_bound (complexAdjacency side n K d x) (s*r) C
    (mul_pos sp rp) bound
  have realbound : radiusValue side n K d x ≤ s*r := by
    simpa [radiusValue,weightedRadius,ENNReal.toReal_ofReal (mul_pos sp rp).le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top rad
  exact (not_lt_of_ge realbound) below

theorem word_weight_bounds (w : List CuLetter) :
    6*w.length ≤ wordWeight w ∧ wordWeight w ≤ 20*w.length := by
  induction w with
  | nil => simp [wordWeight]
  | cons a w ih => cases a <;> simp only [wordWeight,List.length_cons] <;> omega

private theorem mass_monomial_comparison (side : MemorySide) (n K : ℕ) (d x y s : ℝ)
    (weights : ∀ w : List CuLetter, x^wordWeight w ≤ s^w.length*y^wordWeight w) :
    ∀ k, pathMass side n K d x k ≤ s^k*pathMass side n K d y k := by
  classical
  intro k
  have eq (z : ℝ) : pathMass side n K d z k =
      ∑ v : CoreVertex side n K d, ∑ ch : Fin k → CuLetter × CoreVertex side n K d,
        coreMonomial side K d z k v ch := by
    unfold pathMass
    apply Finset.sum_congr rfl
    intro v _
    exact (original_weighted_adjacency_paths side n K d z).2 k v
  rw [eq x,eq y,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ch _
  unfold coreMonomial
  split_ifs
  · simpa only [List.length_ofFn] using weights (List.ofFn (fun i => (ch i).1))
  · simp

/-- Every actual path exponent lies between 6k and 20k. Its spectral radius
therefore satisfies the corresponding scaling bounds on the full retained
matrix, without selecting a strongly connected component. -/
theorem original_radius_scaling (side : MemorySide) (n K : ℕ) (d x y : ℝ)
    (xp : 0 < x) (xy : x ≤ y) :
    (y/x)^6*radiusValue side n K d x ≤ radiusValue side n K d y ∧
    radiusValue side n K d y ≤ (y/x)^20*radiusValue side n K d x := by
  have yp : 0 < y := xp.trans_le xy
  have big : 1 ≤ y/x := (le_div_iff₀ xp).mpr (by simpa using xy)
  have small : x/y ≤ 1 := (div_le_iff₀ yp).mpr (by simpa using xy)
  have qpos : 0 < y/x := div_pos yp xp
  have ppos : 0 < x/y := div_pos xp yp
  have upweights (w : List CuLetter) : y^wordWeight w ≤ ((y/x)^20)^w.length*x^wordWeight w := by
    have hb := pow_le_pow_right₀ big (word_weight_bounds w).2
    calc
      _ = (y/x)^wordWeight w*x^wordWeight w := by rw [div_pow]; field_simp
      _ ≤ (y/x)^(20*w.length)*x^wordWeight w := mul_le_mul_of_nonneg_right hb (pow_nonneg xp.le _)
      _ = _ := by rw [pow_mul]
  have downweights (w : List CuLetter) : x^wordWeight w ≤ ((x/y)^6)^w.length*y^wordWeight w := by
    have hb := pow_le_pow_of_le_one ppos.le small (word_weight_bounds w).1
    calc
      _ = (x/y)^wordWeight w*y^wordWeight w := by rw [div_pow]; field_simp
      _ ≤ (x/y)^(6*w.length)*y^wordWeight w := mul_le_mul_of_nonneg_right hb (pow_nonneg yp.le _)
      _ = _ := by rw [pow_mul]
  have up := radius_mass_comparison side n K d y x ((y/x)^20) yp.le xp.le (pow_pos qpos _)
    (mass_monomial_comparison side n K d y x ((y/x)^20) upweights)
  have down := radius_mass_comparison side n K d x y ((x/y)^6) xp.le yp.le (pow_pos ppos _)
    (mass_monomial_comparison side n K d x y ((x/y)^6) downweights)
  have inverse : (y/x)^6*(x/y)^6=1 := by rw [← mul_pow]; field_simp
  refine ⟨?_,up⟩
  calc
    (y/x)^6*radiusValue side n K d x ≤ (y/x)^6*((x/y)^6*radiusValue side n K d y) :=
      mul_le_mul_of_nonneg_left down (pow_nonneg qpos.le _)
    _ = _ := by rw [← mul_assoc,inverse,one_mul]

/-- Positivity of the actual all-u cycle and the minimum edge weight make the
full original spectral radius strictly increasing for positive z. -/
theorem original_radius_strict_increase (side : MemorySide) (n K : ℕ) (d : ℝ) :
    StrictMonoOn (radiusValue side n K d) (Set.Ioi 0) := by
  intro x xp y yp xy
  have positive : 0 < radiusValue side n K d x := by
    have h := ENNReal.toReal_mono (radius_finite side n K d x)
      (original_spectral_positive side n K d x xp)
    have p : 0 < x^6 := pow_pos xp _
    rw [ENNReal.toReal_ofReal p.le] at h
    exact p.trans_le h
  have scale := (original_radius_scaling side n K d x y xp xy.le).1
  have one : 1 < (y/x)^6 := one_lt_pow₀ ((one_lt_div xp).mpr xy) (by decide)
  have grows := mul_lt_mul_of_pos_right one positive
  simpa only [one_mul] using grows.trans_le scale


/-- At zero the actual matrix is zero; the same polynomial matrix is continuous
as a matrix-valued function of the real weight parameter. -/
theorem original_adjacency_zero_continuous (side : MemorySide) (n K : ℕ) (d : ℝ) :
    complexAdjacency side n K d 0 = 0 ∧ Continuous (complexAdjacency side n K d) := by
  classical
  constructor
  · ext v t
    simp only [complexAdjacency,weightedAdjacency,Matrix.map_apply,Matrix.zero_apply,map_sum]
    apply Finset.sum_eq_zero
    intro a _
    cases a <;> simp [letterWeight]
  · apply continuous_pi
    intro v
    apply continuous_pi
    intro t
    change Continuous (fun z : ℝ => (algebraMap ℝ ℂ)
      (∑ a : CuLetter, if MemoryEdge side K d v.val a t.val then z^letterWeight a else 0))
    apply Complex.continuous_ofReal.comp
    change Continuous (fun z : ℝ => ∑ a : CuLetter,
      if MemoryEdge side K d v.val a t.val then z^letterWeight a else 0)
    apply continuous_finsetSum
    intro a _
    by_cases edge : MemoryEdge side K d v.val a t.val
    · simp only [edge,ite_true]; fun_prop
    · simp only [edge,ite_false]; exact continuous_const

/-- Spectral continuity for the original retained graph follows from its
actual edge exponents and nonnegative path comparisons. Reducibility and
bridges are retained. No matrix-continuity premise is imposed. -/
theorem original_radius_continuous (side : MemorySide) (n K : ℕ) (d : ℝ) :
    ContinuousOn (radiusValue side n K d) (Set.Ici 0) := by
  intro r hr
  have comparison (x : ℝ) (xp : 0 < x) (rp : 0 < r) :
      min ((x/r)^6) ((x/r)^20)*radiusValue side n K d r ≤ radiusValue side n K d x ∧
      radiusValue side n K d x ≤ max ((x/r)^6) ((x/r)^20)*radiusValue side n K d r := by
    by_cases order : r ≤ x
    · have scale := original_radius_scaling side n K d r x rp order
      have q : 1 ≤ x/r := (le_div_iff₀ rp).mpr (by simpa using order)
      have powers : (x/r)^6 ≤ (x/r)^20 := pow_le_pow_right₀ q (by decide)
      simpa only [min_eq_left powers,max_eq_right powers] using scale
    · have order' : x ≤ r := (lt_of_not_ge order).le
      have scale := original_radius_scaling side n K d x r xp order'
      have qp : 0 < x/r := div_pos xp rp
      have qsmall : x/r ≤ 1 := (div_le_iff₀ rp).mpr (by simpa using order')
      have powers : (x/r)^20 ≤ (x/r)^6 := pow_le_pow_of_le_one qp.le qsmall (by decide)
      rw [min_eq_right powers,max_eq_left powers]
      have inverse (m : ℕ) : (x/r)^m*(r/x)^m=1 := by rw [← mul_pow]; field_simp; simp
      constructor
      · calc
          _ ≤ (x/r)^20*((r/x)^20*radiusValue side n K d x) :=
            mul_le_mul_of_nonneg_left scale.2 (pow_nonneg qp.le _)
          _ = _ := by rw [← mul_assoc,inverse,one_mul]
      · calc
          _ = (x/r)^6*((r/x)^6*radiusValue side n K d x) := by rw [← mul_assoc,inverse,one_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_left scale.1 (pow_nonneg qp.le _)
  by_cases zero : r=0
  · subst r
    have mat := original_adjacency_zero_continuous side n K d
    have atzero : radiusValue side n K d 0=0 := by
      simp only [radiusValue,weightedRadius,mat.1,spectrum.spectralRadius_zero,ENNReal.toReal_zero]
    have upper (z : ℝ) : radiusValue side n K d z ≤ ‖complexAdjacency side n K d z‖ := by
      letI : Nonempty (CoreVertex side n K d) :=
        ⟨(original_all_u_cycle side n K d 0 le_rfl).choose⟩
      have bound : weightedRadius side n K d z ≤ (‖complexAdjacency side n K d z‖₊ : ℝ≥0∞) :=
        spectrum.spectralRadius_le_nnnorm (complexAdjacency side n K d z)
      simpa only [radiusValue,weightedRadius,ENNReal.coe_toReal,coe_nnnorm] using
        ENNReal.toReal_mono ENNReal.coe_ne_top bound
    have limit : Tendsto (fun z => ‖complexAdjacency side n K d z‖) (𝓝 0) (𝓝 0) := by
      simpa only [mat.1,norm_zero] using mat.2.norm.tendsto 0
    have squeeze : Tendsto (radiusValue side n K d) (𝓝 0) (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds limit
        (fun _ => ENNReal.toReal_nonneg) upper
    change Tendsto (radiusValue side n K d) (nhdsWithin 0 (Set.Ici 0))
      (𝓝 (radiusValue side n K d 0))
    rw [atzero]
    exact squeeze.mono_left nhdsWithin_le_nhds
  · have rp : 0 < r := lt_of_le_of_ne hr (Ne.symm zero)
    let lower : ℝ → ℝ := fun x => min ((x/r)^6) ((x/r)^20)*radiusValue side n K d r
    let upper : ℝ → ℝ := fun x => max ((x/r)^6) ((x/r)^20)*radiusValue side n K d r
    have lowerLimit : Tendsto lower (𝓝 r) (𝓝 (radiusValue side n K d r)) := by
      have continuous : Continuous lower := by dsimp [lower]; fun_prop
      have eval : lower r=radiusValue side n K d r := by simp [lower,div_self rp.ne']
      simpa only [eval] using continuous.tendsto r
    have upperLimit : Tendsto upper (𝓝 r) (𝓝 (radiusValue side n K d r)) := by
      have continuous : Continuous upper := by dsimp [upper]; fun_prop
      have eval : upper r=radiusValue side n K d r := by simp [upper,div_self rp.ne']
      simpa only [eval] using continuous.tendsto r
    have bounds : ∀ᶠ x in 𝓝 r, lower x ≤ radiusValue side n K d x ∧
        radiusValue side n K d x ≤ upper x := by
      filter_upwards [eventually_gt_nhds rp] with x xp
      exact comparison x xp rp
    exact (tendsto_of_tendsto_of_tendsto_of_le_of_le' lowerLimit upperLimit
      (bounds.mono (fun _ h => h.1)) (bounds.mono (fun _ h => h.2))).mono_left nhdsWithin_le_nhds

/-- Literal codebook growth forces the full original spectral radius at one to
exceed one for every n at least K at least two. -/
theorem original_spectral_at_one (side : MemorySide) (n K : ℕ) (d : ℝ)
    (hK : 2 ≤ K) (memory : K ≤ n) : 1 < radiusValue side n K d 1 := by
  let z := (2 : ℝ)^(-(1/116 : ℝ))
  have zp : 0 < z := Real.rpow_pos_of_pos (by norm_num) _
  have zs : z < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have radius : 1 ≤ weightedRadius side n K d z := by
    by_contra hn
    have small : weightedRadius side n K d z < 1 := lt_of_not_ge hn
    have summable := (original_factor_series_boundary side n K d z (by omega) memory zp.le).mpr small
    have rate := (factor_rate_convergence (MemoryLanguage side n K d) (1/116) (by norm_num)).2 summable
    have positive := original_positive_weighted_rate side n K d hK
    linarith
  have realradius : 1 ≤ radiusValue side n K d z := by
    simpa only [ENNReal.toReal_one,radiusValue] using ENNReal.toReal_mono
      (radius_finite side n K d z) radius
  exact realradius.trans_lt (original_radius_strict_increase side n K d zp (by norm_num) zs)

/-- The original n>=K>=2 retained matrix has one and only one positive interior
radius-one root. The K=1 closed endpoint remains a separate theorem. -/
theorem original_interior_root (side : MemorySide) (n K : ℕ) (d : ℝ)
    (hK : 2 ≤ K) (memory : K ≤ n) :
    ∃! z : ℝ, 0 < z ∧ z < 1 ∧ weightedRadius side n K d z=1 := by
  have zero : radiusValue side n K d 0=0 := by
    simp only [radiusValue,weightedRadius,(original_adjacency_zero_continuous side n K d).1,
      spectrum.spectralRadius_zero,ENNReal.toReal_zero]
  have one := original_spectral_at_one side n K d hK memory
  have continuous := (original_radius_continuous side n K d).mono
    (show Set.Icc (0 : ℝ) 1 ⊆ Set.Ici 0 from fun _ h => h.1)
  obtain ⟨z,hz,root⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) continuous
    (show (1 : ℝ) ∈ Set.Icc (radiusValue side n K d 0) (radiusValue side n K d 1) from
      ⟨by rw [zero]; norm_num,one.le⟩)
  have zp : 0 < z := by
    by_contra hn
    have eq : z=0 := le_antisymm (le_of_not_gt hn) hz.1
    rw [eq,zero] at root
    norm_num at root
  have zs : z < 1 := by
    by_contra hn
    have eq : z=1 := le_antisymm hz.2 (le_of_not_gt hn)
    rw [eq] at root
    rw [root] at one
    exact (lt_irrefl (1 : ℝ)) one
  have spectral : weightedRadius side n K d z=1 := by
    rw [← radius_value_eq side n K d z,root]
    norm_num
  refine ⟨z,⟨zp,zs,spectral⟩,?_⟩
  intro y hy
  apply (original_radius_strict_increase side n K d).injOn hy.1 zp
  change (weightedRadius side n K d y).toReal = (weightedRadius side n K d z).toReal
  rw [hy.2.2,spectral]


/-- The unique interior root gives the actual max-one, sparse weighted factor
rate, using the already established full factor-series abscissa. -/
theorem original_weighted_interior_root (side : MemorySide) (n K : ℕ) (d : ℝ)
    (hK : 2 ≤ K) (memory : K ≤ n) :
    ∃! z : ℝ, 0 < z ∧ z < 1 ∧ weightedRadius side n K d z=1 ∧
      weightedFactorRate (MemoryLanguage side n K d) = -Real.logb 2 z := by
  obtain ⟨z,hz,unique⟩ := original_interior_root side n K d hK memory
  let gamma := -Real.logb 2 z
  have gp : 0 < gamma := neg_pos.mpr (Real.logb_neg (by norm_num) hz.1 hz.2.1)
  have binary : (2 : ℝ)^(-gamma)=z := by
    dsimp [gamma]
    rw [neg_neg]
    exact Real.rpow_logb (by norm_num) (by norm_num) hz.1
  have realroot : radiusValue side n K d z=1 := by
    simp only [radiusValue,hz.2.2,ENNReal.toReal_one]
  have boundary (s : ℝ) : weightedRadius side n K d ((2 : ℝ)^(-s)) < 1 ↔ gamma < s := by
    let w := (2 : ℝ)^(-s)
    have wp : 0 < w := Real.rpow_pos_of_pos (by norm_num) _
    have ordering : w < z ↔ gamma < s := by
      change (2 : ℝ)^(-s) < z ↔ gamma < s
      rw [← binary,Real.rpow_lt_rpow_left_iff (by norm_num)]
      exact neg_lt_neg_iff
    have radii : weightedRadius side n K d w < 1 ↔ radiusValue side n K d w < 1 := by
      have h := ENNReal.toReal_lt_toReal (radius_finite side n K d w) (by simp : (1 : ℝ≥0∞) ≠ ⊤)
      simpa only [ENNReal.toReal_one,radiusValue] using h.symm
    rw [radii]
    constructor
    · intro small
      apply ordering.mp
      by_contra hn
      have opposite := (original_radius_strict_increase side n K d).monotoneOn
        hz.1 wp (le_of_not_gt hn)
      rw [realroot] at opposite
      exact (not_lt_of_ge opposite) small
    · intro above
      have grow := original_radius_strict_increase side n K d wp hz.1 (ordering.mpr above)
      simpa only [realroot] using grow
  have seteq : {s : ℝ | 0 < s ∧ weightedRadius side n K d ((2 : ℝ)^(-s)) < 1} = Set.Ioi gamma := by
    ext s
    constructor
    · intro hs; exact (boundary s).mp hs.2
    · intro hs; exact ⟨gp.trans hs,(boundary s).mpr hs⟩
  have rate : weightedFactorRate (MemoryLanguage side n K d) = gamma := by
    rw [original_weighted_rate_abscissa side n K d (by omega) memory,seteq,csInf_Ioi]
  refine ⟨z,⟨hz.1,hz.2.1,hz.2.2,rate⟩,?_⟩
  intro y hy
  exact unique y ⟨hy.1,hy.2.1,hy.2.2.1⟩

/-- Both root families have the actual auxiliary-rate sandwich and the original
opposite n-monotonicities, obtained from the proven language inclusions. -/
theorem original_root_rate_families (K : ℕ) (d : ℝ) (hK : 2 ≤ K) :
    ∃ roots : MemorySide → ℕ → ℝ,
      (∀ side n, K ≤ n → 0 < roots side n ∧ roots side n < 1 ∧
        weightedRadius side n K d (roots side n)=1 ∧
        weightedFactorRate (MemoryLanguage side n K d) = -Real.logb 2 (roots side n)) ∧
      (∀ n, K ≤ n → -Real.logb 2 (roots .lower n) ≤ weightedFactorRate (AuxiliaryLanguage K d) ∧
        weightedFactorRate (AuxiliaryLanguage K d) ≤ -Real.logb 2 (roots .upper n)) ∧
      MonotoneOn (fun n => -Real.logb 2 (roots .lower n)) (Set.Ici K) ∧
      AntitoneOn (fun n => -Real.logb 2 (roots .upper n)) (Set.Ici K) := by
  classical
  let roots : MemorySide → ℕ → ℝ := fun side n => if hn : K ≤ n then
    (original_weighted_interior_root side n K d hK hn).choose else 1
  have properties (side : MemorySide) (n : ℕ) (hn : K ≤ n) :
      0 < roots side n ∧ roots side n < 1 ∧ weightedRadius side n K d (roots side n)=1 ∧
        weightedFactorRate (MemoryLanguage side n K d) = -Real.logb 2 (roots side n) := by
    simpa only [roots,dif_pos hn] using
      (original_weighted_interior_root side n K d hK hn).choose_spec.1
  have lower : Monotone (fun n => weightedFactorRate (MemoryLanguage .lower n K d)) :=
    monotone_nat_of_le_succ (fun n => (original_memory_rate_nesting n K d).1)
  have upper : Antitone (fun n => weightedFactorRate (MemoryLanguage .upper n K d)) :=
    antitone_nat_of_succ_le (fun n => (original_memory_rate_nesting n K d).2.2.2)
  refine ⟨roots,properties,?_,?_,?_⟩
  · intro n hn
    have nest := original_memory_language_nesting n K d
    have lowerIncl := nest.1.trans nest.2.1
    have upperIncl : AuxiliaryLanguage K d ⊆ MemoryLanguage .upper n K d := by
      rw [← original_upper_memory_intersection K d]
      intro ω hω
      exact hω n hn
    rw [← (properties .lower n hn).2.2.2,← (properties .upper n hn).2.2.2]
    exact ⟨weighted_factor_rate_mono lowerIncl,weighted_factor_rate_mono upperIncl⟩
  · intro n hn m hm order
    dsimp only
    rw [← (properties .lower n hn).2.2.2,← (properties .lower m hm).2.2.2]
    exact lower order
  · intro n hn m hm order
    dsimp only
    rw [← (properties .upper n hn).2.2.2,← (properties .upper m hm).2.2.2]
    exact upper order

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
