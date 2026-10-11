/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One reset gives distinct extendible factors at the exact codebook weight. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
import Mathlib.Data.Fintype.Option

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion

def FactorDictionary (X : Set (ℤ → CuLetter)) (T : ℕ) :=
  {w : List CuLetter // (∃ ω ∈ X, Occurs ω w) ∧ wordWeight w = T}

noncomputable def factorCount (X : Set (ℤ → CuLetter)) (T : ℕ) : ℕ :=
  Nat.card (FactorDictionary X T)

noncomputable def weightedFactorRate (X : Set (ℤ → CuLetter)) : ℝ :=
  Filter.limsup (fun T : ℕ =>
    Real.logb 2 ((max 1 (factorCount X T) : ℕ) : ℝ) / (T : ℝ)) Filter.atTop

def resetFactor (R : Return) (words : List (List Return)) : List CuLetter :=
  (words.map (fun xs => executionWord (R :: xs))).flatten

/-- Positive original letter weights determine empty words and bound letter length. -/
theorem word_weight_geometry :
    (∀ w v, wordWeight (w ++ v) = wordWeight w + wordWeight v) ∧
    (∀ w, w.length ≤ wordWeight w) ∧
    (∀ w, wordWeight w = 0 → w = []) := by
  have length (w : List CuLetter) : w.length ≤ wordWeight w := by
    induction w with
    | nil => simp [wordWeight]
    | cons a w ih => cases a <;> simp only [wordWeight,List.length_cons] <;> omega
  refine ⟨?_,length,?_⟩
  · intro w v
    induction w with
    | nil => simp [wordWeight]
    | cons a w ih => cases a <;> simp [wordWeight,ih,Nat.add_assoc]
  · intro w hw
    exact List.eq_nil_of_length_eq_zero (by have := length w; omega)

/-- The full weighted factor dictionary is finite, including weight zero.
Padding with missing letters gives an explicit finite upper bound. -/
theorem factor_dictionary_bound (X : Set (ℤ → CuLetter)) (T : ℕ) :
    Finite (FactorDictionary X T) ∧ factorCount X T ≤ 3^(T+1) := by
  classical
  let f : FactorDictionary X T → (Fin (T+1) → Option CuLetter) :=
    fun w i => w.val[i.val]?
  have inj : Function.Injective f := by
    intro w v he
    apply Subtype.ext
    apply List.ext_getElem?
    intro i
    by_cases hi : i < T+1
    · exact congrFun he ⟨i,hi⟩
    · have wl := word_weight_geometry.2.1 w.val
      have vl := word_weight_geometry.2.1 v.val
      rw [w.property.2] at wl
      rw [v.property.2] at vl
      simp only [List.getElem?_eq_none (by omega : w.val.length ≤ i),
        List.getElem?_eq_none (by omega : v.val.length ≤ i)]
  letI : Finite (FactorDictionary X T) := Finite.of_injective f inj
  refine ⟨inferInstance,?_⟩
  have count := Nat.card_le_card_of_injective f inj
  have letters : Fintype.card CuLetter = 2 := by decide
  simpa [factorCount,Nat.card_fun,Nat.card_fin,Nat.card_eq_fintype_card,
    Fintype.card_option,letters] using count

/-- Equal positive weighted blocks have unique cuts, even with unequal letter lengths. -/
theorem equal_weight_concatenation_injective (L : ℕ) (positive : 0 < L) :
    Function.Injective (fun words : List {w : List CuLetter // wordWeight w = L} =>
      (words.map Subtype.val).flatten) := by
  have head (w v : List CuLetter) (hw : wordWeight w = L) (hv : wordWeight v = L)
      (s t : List CuLetter) (he : w ++ s = v ++ t) : w = v := by
    rcases List.append_eq_append_iff.mp he with ⟨a,ha,_⟩ | ⟨a,ha,_⟩
    · have az : wordWeight a = 0 := by
        have h := congrArg wordWeight ha
        rw [word_weight_geometry.1,hw,hv] at h
        omega
      simpa only [word_weight_geometry.2.2 a az,List.append_nil] using ha.symm
    · have az : wordWeight a = 0 := by
        have h := congrArg wordWeight ha
        rw [word_weight_geometry.1,hw,hv] at h
        omega
      simpa only [word_weight_geometry.2.2 a az,List.append_nil] using ha
  intro words
  induction words with
  | nil =>
    intro other he
    cases other with
    | nil => rfl
    | cons w ws =>
      have hz := congrArg wordWeight he
      simp only [List.map_nil,List.flatten_nil,List.map_cons,List.flatten_cons,
        wordWeight,word_weight_geometry.1,w.property] at hz
      omega
  | cons w ws ih =>
    intro other he
    cases other with
    | nil =>
      have hz := congrArg wordWeight he
      simp only [List.map_nil,List.flatten_nil,List.map_cons,List.flatten_cons,
        wordWeight,word_weight_geometry.1,w.property] at hz
      omega
    | cons v vs =>
      have hv := head w.val v.val w.property v.property _ _ he
      have eq : w = v := Subtype.ext hv
      subst v
      have tail := List.append_cancel_left (by
        simpa only [List.map_cons,List.flatten_cons] using he)
      exact congrArg (List.cons w) (ih tail)

/-- Original execution parsing, followed by weighted cuts, recovers every reset choice. -/
theorem reset_factor_parser (R : Return) (N : ℕ) (p : List Return → Prop) :
    Function.Injective (fun words : List {xs : List Return // p xs ∧ listWeight xs = N} =>
      resetFactor R (words.map Subtype.val)) ∧
    ∀ words : List {xs : List Return // p xs ∧ listWeight xs = N},
      wordWeight (resetFactor R (words.map Subtype.val)) =
        words.length * (N + 20 * R.r + 6 * R.m) := by
  let V := {xs : List Return // p xs ∧ listWeight xs = N}
  let L := N + 20 * R.r + 6 * R.m
  have wp (v : V) : wordWeight (executionWord (R :: v.val)) = L := by
    rw [complete_execution_word_parser.2.2.2.1]
    simp only [listWeight,v.property.2,L]
    omega
  let encode : V → {w : List CuLetter // wordWeight w = L} :=
    fun v => ⟨executionWord (R :: v.val),wp v⟩
  have einj : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    exact (List.cons.inj (complete_execution_word_parser.2.2.1
      (congrArg Subtype.val h))).2
  have lp : 0 < L := by have := R.r_pos; dsimp [L]; omega
  constructor
  · intro x y he
    have e : ((x.map encode).map Subtype.val).flatten =
        ((y.map encode).map Subtype.val).flatten := by
      simpa only [List.map_map,Function.comp_def,encode,resetFactor] using he
    have h := equal_weight_concatenation_injective L lp e
    exact (List.map_inj_right (fun x y h => einj h)).mp h
  · intro words
    induction words with
    | nil => simp [resetFactor,wordWeight]
    | cons v vs ih =>
      simp only [List.map_cons,resetFactor,List.flatten_cons,List.map_cons,
        word_weight_geometry.1,List.length_cons] at ih ⊢
      rw [wp,ih]
      dsimp [L]
      ring

/-- All letters of a consecutive block window occur in the one prescribed tiling. -/
theorem tiled_window_occurs (W : ℤ → List CuLetter)
    (positive : ∀ j, 0 < (W j).length) (ω : ℤ → CuLetter)
    (tiles : ∀ j (k : Fin (W j).length),
      ω (blockCut W j + (k : ℕ)) = (W j)[k]) (a : ℤ) (q : ℕ) :
    ∀ k : Fin (blockWindow W a q).length,
      ω (blockCut W a + (k : ℕ)) = (blockWindow W a q)[k] := by
  have step := (positive_block_tiling W positive).2.1
  induction q generalizing a with
  | zero => intro k; exact Fin.elim0 k
  | succ q ih =>
    intro k
    change ω (blockCut W a + (k.val : ℤ)) =
      (W a ++ blockWindow W (a+1) q)[k.val]
    by_cases hk : k.val < (W a).length
    · rw [List.getElem_append_left hk]
      exact tiles a ⟨k.val,hk⟩
    · have bound : k.val - (W a).length < (blockWindow W (a+1) q).length := by
        have h := k.isLt
        simp only [blockWindow,List.length_append] at h
        omega
      have h := ih (a+1) ⟨k.val-(W a).length,bound⟩
      have idx : blockCut W (a+1) + ((k.val-(W a).length : ℕ) : ℤ) =
          blockCut W a + (k.val : ℤ) := by rw [step]; omega
      rw [idx] at h
      rw [List.getElem_append_right (by omega : (W a).length ≤ k.val)]
      exact h

/-- Integer choices restrict to the exact finite ordered block window. -/
theorem choice_window_ofFn {V : Type*} (choices : ℤ → V) (a : ℤ) (q : ℕ) :
    choiceWindow choices a q = List.ofFn (fun i : Fin q => choices (a+(i : ℕ))) := by
  induction q generalizing a with
  | zero => simp [choiceWindow]
  | succ q ih =>
    rw [choiceWindow,List.ofFn_succ,ih]
    simp only [Fin.val_zero,Nat.cast_zero,add_zero,Fin.val_succ,Nat.cast_add,Nat.cast_one]
    congr 2
    funext i
    congr 1
    omega

open Filter in
/-- Counts at all multiples of one positive weight give the original real limsup bound. -/
theorem factor_rate_of_power_count (X : Set (ℤ → CuLetter)) (a L : ℕ)
    (positive : 0 < L) (counts : ∀ q, a^q ≤ factorCount X (q*L)) :
    Real.logb 2 ((max 1 a : ℕ) : ℝ) / (L : ℝ) ≤ weightedFactorRate X := by
  let r (T : ℕ) := Real.logb 2 ((max 1 (factorCount X T) : ℕ) : ℝ) / (T : ℝ)
  have bounded : IsBoundedUnder (· ≤ ·) atTop r := by
    apply isBoundedUnder_of_eventually_le (a := (4 : ℝ))
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    have tp : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
    have t1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have cb := (factor_dictionary_bound X T).2
    have one : 1 ≤ 3^(T+1) := Nat.one_le_pow _ _ (by decide)
    have hb : ((max 1 (factorCount X T) : ℕ) : ℝ) ≤ (3 : ℝ)^(T+1) := by
      exact_mod_cast max_le one cb
    have log := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
      (by exact_mod_cast (show 0 < max 1 (factorCount X T) by omega)) hb
    rw [Real.logb_pow] at log
    have three : Real.logb 2 3 ≤ (2 : ℝ) := by
      have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
        (by norm_num : (0 : ℝ)<3) (by norm_num : (3 : ℝ)≤2^2)
      simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one,
        Nat.cast_ofNat] using h
    dsimp [r]
    rw [div_le_iff₀ tp]
    have mult := mul_le_mul_of_nonneg_left three (by positivity : (0 : ℝ)≤(T+1 : ℕ))
    simp only [Nat.cast_add,Nat.cast_one] at log mult
    nlinarith
  have rp (T : ℕ) : 0 ≤ r T := div_nonneg
    (Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.le_max_left 1 (factorCount X T)))
    (by positivity)
  by_cases ha : a = 0
  · simp only [ha,max_eq_left (by omega : (0 : ℕ)≤1),Nat.cast_one,Real.logb_one,zero_div]
    exact le_limsup_of_frequently_le (Frequently.of_forall rp) bounded
  have ap : 0 < a := Nat.pos_of_ne_zero ha
  have lp : (0 : ℝ)<(L : ℝ) := by exact_mod_cast positive
  have frequent : ∃ᶠ T in atTop,
      Real.logb 2 ((max 1 a : ℕ) : ℝ)/(L : ℝ) ≤ r T := by
    apply frequently_atTop.mpr
    intro t
    let q := t+1
    have qp : 0 < q := by dsimp [q]; omega
    have qpR : (0 : ℝ)<(q : ℝ) := by exact_mod_cast qp
    refine ⟨q*L,?_,?_⟩
    · have h := Nat.mul_le_mul_left q (show 1≤L by omega)
      dsimp [q] at *
      omega
    · have h := (counts q).trans (Nat.le_max_right 1 (factorCount X (q*L)))
      have log := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
        (pow_pos (by exact_mod_cast ap : (0 : ℝ)<(a : ℝ)) q)
        (by exact_mod_cast h : (a : ℝ)^q ≤ ((max 1 (factorCount X (q*L)) : ℕ) : ℝ))
      rw [Real.logb_pow] at log
      rw [max_eq_right (by omega : 1≤a)]
      dsimp [r]
      rw [div_le_div_iff₀ lp (by positivity)]
      simp only [Nat.cast_mul]
      have result := mul_le_mul_of_nonneg_right log lp.le
      nlinarith only [result]
  exact le_limsup_of_frequently_le frequent bounded

set_option maxHeartbeats 1000000 in
-- The bilateral source supplies every finite choice on the same reset and memory.
/-- The full original weak codebook yields exactly a^q different extendible
lower-memory factors of weight q(N+20+6m(R)), and the corresponding weighted rate. -/
theorem same_reset_factor_cardinality (o : Ownership) (b : ℝ) (K : ℕ)
    (hK : 2 ≤ K)
    (hqb : lam - g^2*chi^K*hSide .high < b)
    (hbp : b < lam - g^2*chi^K*(aSide .high/(1-rho*chi^K))) :
    ∃ R : Return, R.r = 1 ∧
    (max (max (xSide .high) (ySide .high)) ((lam-b)/g^2/chi^K) <
      hSide .high-rho^R.m*(hSide .high-chi*aSide .high)) ∧
    ∀ (sourceModel : Model) (N : ℕ), 0 < N →
    let d := (lam-b)/g^2/chi^K
    let delta := hSide .high-rho^R.m*(hSide .high-chi*aSide .high)-initial .high sourceModel
    let V := {xs : List Return //
      GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs = N}
    let L := N+20+6*R.m
    0 < delta ∧ 0 < delta*g^N ∧
    0 < min (b-actualAutomaticCost K) (g^2*chi^K*(delta*g^N))/2 ∧ Finite V ∧
    (∀ (targetModel : Model) (words : List V),
      let execution := resetConcatenation R (words.map Subtype.val)
      GuardTrace K (d+delta*g^N) false .high execution (initial .high targetModel) ∧
      ActualPairSupply targetModel o
        (b-min (b-actualAutomaticCost K) (g^2*chi^K*(delta*g^N))/2) .strict execution) ∧
    ∃ n : ℕ, K ≤ n ∧ hSide .high*rho^n < chi^(K-1)*(delta*g^N) ∧
      (∀ choices : ℤ → V,
        let W := fun j => executionWord (R::(choices j).val)
        ∃ ω : ℤ → CuLetter,
          ω ∈ AuxiliaryLanguage K (d+delta*g^N) ∧ ω ∈ LowerMemoryLanguage n K d ∧
          (∀ j (k : Fin (W j).length), ω (blockCut W j+(k : ℕ))=(W j)[k]) ∧
          (∀ j, GuardTrace K (d+delta*g^N) false .high (R::(choices j).val)
            (pastState ω (blockCut W j)))) ∧
      (∀ q : ℕ,
        let f := fun z : Fin q → V => resetFactor R (List.ofFn (fun i => (z i).val))
        Function.Injective f ∧
        (∀ z, wordWeight (f z) = q*L ∧
          ∃ ω ∈ LowerMemoryLanguage n K d, Occurs ω (f z)) ∧
        (∃ family : Finset (List CuLetter), family.card = Nat.card V^q ∧
          (∀ w, w ∈ family ↔ ∃ z, f z = w) ∧
          (∀ w ∈ family, wordWeight w = q*L ∧
            ∃ ω ∈ LowerMemoryLanguage n K d, Occurs ω w)) ∧
        Nat.card V^q ≤ factorCount (LowerMemoryLanguage n K d) (q*L)) ∧
      Real.logb 2 ((max 1 (Nat.card V) : ℕ) : ℝ)/(L : ℝ) ≤
        weightedFactorRate (LowerMemoryLanguage n K d) := by
  classical
  obtain ⟨R,hr,hB,codebooks⟩ := bilateral_reset_codebook o b K hK hqb hbp
  refine ⟨R,hr,hB,?_⟩
  intro sourceModel N hN
  dsimp only
  let d := (lam-b)/g^2/chi^K
  let delta := hSide .high-rho^R.m*(hSide .high-chi*aSide .high)-initial .high sourceModel
  let V := {xs : List Return //
    GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs = N}
  let L := N+20+6*R.m
  obtain ⟨dp,gp,ep,joint,n,hn,small,realize⟩ := codebooks sourceModel N hN
  have finite : Finite V := by
    let f : V → FactorDictionary (AuxiliaryLanguage K d) N := fun xs =>
      ⟨executionWord xs.val, by
        have pad := D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.auxiliary_lower_padding
          K d sourceModel xs.val (by omega) xs.property.1
        exact ⟨⟨_,pad.2.2.1,pad.2.2.2.1⟩,
          complete_execution_word_parser.2.2.2.1 xs.val |>.trans xs.property.2⟩⟩
    letI := (factor_dictionary_bound (AuxiliaryLanguage K d) N).1
    exact Finite.of_injective f (by
      intro x y he
      apply Subtype.ext
      exact complete_execution_word_parser.2.2.1 (congrArg Subtype.val he))
  letI : Finite V := finite
  letI : Fintype V := Fintype.ofFinite V
  have emptyLower : (fun _ : ℤ => CuLetter.u) ∈ LowerMemoryLanguage n K d := by
    constructor
    · intro i hs
      have h := hs ⟨0,by omega⟩
      cases h
    · intro i hs
      have h := hs ⟨0,by omega⟩
      cases h
  have packet (q : ℕ) :
      let f := fun z : Fin q → V => resetFactor R (List.ofFn (fun i => (z i).val))
      Function.Injective f ∧
      (∀ z, wordWeight (f z) = q*L ∧
        ∃ ω ∈ LowerMemoryLanguage n K d, Occurs ω (f z)) ∧
      (∃ family : Finset (List CuLetter), family.card = Nat.card V^q ∧
        (∀ w, w ∈ family ↔ ∃ z, f z = w) ∧
        (∀ w ∈ family, wordWeight w = q*L ∧
          ∃ ω ∈ LowerMemoryLanguage n K d, Occurs ω w)) ∧
      Nat.card V^q ≤ factorCount (LowerMemoryLanguage n K d) (q*L) := by
    dsimp only
    let f := fun z : Fin q → V => resetFactor R (List.ofFn (fun i => (z i).val))
    have parser := reset_factor_parser R N
      (fun xs => GuardTrace K d false .high xs (initial .high sourceModel))
    have injection : Function.Injective f := by
      intro z z' he
      have mapped : resetFactor R ((List.ofFn z).map Subtype.val) =
          resetFactor R ((List.ofFn z').map Subtype.val) := by
        simpa only [List.map_ofFn,Function.comp_def,f] using he
      exact List.ofFn_injective (parser.1 mapped)
    have factors (z : Fin q → V) : wordWeight (f z) = q*L ∧
        ∃ ω ∈ LowerMemoryLanguage n K d, Occurs ω (f z) := by
      constructor
      · have weight := parser.2 (List.ofFn z)
        simpa only [List.map_ofFn,Function.comp_def,List.length_ofFn,hr,Nat.mul_one,L,f] using weight
      · cases q with
        | zero =>
          refine ⟨fun _ => .u,emptyLower,0,?_⟩
          intro k
          have hz : (f z).length = 0 := by simp [f,resetFactor]
          exact False.elim (by have := k.isLt; omega)
        | succ q =>
          let choices : ℤ → V := fun j =>
            if hj : j.toNat < q+1 then z ⟨j.toNat,hj⟩ else z ⟨0,by omega⟩
          let W := fun j => executionWord (R::(choices j).val)
          obtain ⟨ω,_,lower,tiles,_⟩ := realize choices
          have positive (j : ℤ) : 0 < (W j).length := by
            dsimp [W]
            simp only [executionWord,List.length_append,List.length_replicate]
            have := R.r_pos
            omega
          have window (a : ℤ) (m : ℕ) : blockWindow W a m =
              resetFactor R ((choiceWindow choices a m).map Subtype.val) := by
            induction m generalizing a with
            | zero => rfl
            | succ m ih => simp only [blockWindow,choiceWindow,List.map_cons,
                resetFactor,List.flatten_cons,ih,W]
          have restricted : choiceWindow choices 0 (q+1) = List.ofFn z := by
            rw [choice_window_ofFn]
            congr 1
            funext i
            simp only [choices,zero_add,Int.toNat_natCast,dif_pos i.isLt]
          have exactWindow : blockWindow W 0 (q+1) = f z := by
            rw [window,restricted]
            simp only [List.map_ofFn,Function.comp_def,f]
          refine ⟨ω,lower,?_⟩
          have occurrence : Occurs ω (blockWindow W 0 (q+1)) := by
            refine ⟨0,?_⟩
            have letters := tiled_window_occurs W positive ω tiles 0 (q+1)
            have origin : blockCut W 0 = 0 := rfl
            simpa only [origin] using letters
          exact exactWindow ▸ occurrence
    let family := (Finset.univ : Finset (Fin q → V)).image f
    have count : family.card = Nat.card V^q := by
      rw [Finset.card_image_of_injective _ injection]
      simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.card_eq_fintype_card]
    have members (w) : w ∈ family ↔ ∃ z, f z = w := by simp [family]
    have valid (w) (hw : w ∈ family) : wordWeight w = q*L ∧
        ∃ ω ∈ LowerMemoryLanguage n K d, Occurs ω w := by
      obtain ⟨z,rfl⟩ := (members w).mp hw
      exact factors z
    refine ⟨injection,factors,⟨family,count,members,valid⟩,?_⟩
    let dictionaryMap : (Fin q → V) → FactorDictionary (LowerMemoryLanguage n K d) (q*L) :=
      fun z => ⟨f z,(factors z).2,(factors z).1⟩
    letI := (factor_dictionary_bound (LowerMemoryLanguage n K d) (q*L)).1
    have bound := Nat.card_le_card_of_injective dictionaryMap (by
      intro x y he
      exact injection (congrArg Subtype.val he))
    simpa only [Nat.card_fun,Nat.card_fin,factorCount] using bound
  refine ⟨dp,gp,ep,finite,joint,n,hn,small,realize,packet,?_⟩
  apply factor_rate_of_power_count _ (Nat.card V) L (by dsimp [L]; omega)
  intro q
  exact (packet q).2.2.2

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
