/- GID: D5/S1/Digit/Infinite/ResetCodebookWeighted
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/ResetCodebookWeighted
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal-weight codebooks yield distinct factors with periodic reset realizations. -/

import D5.S1.Digit.Infinite.ResetCodebookIndexed
import D5.S0.Computability.Coding.PrefixFreeCode
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.List
import Mathlib.Topology.Order.LiminfLimsup
local notation "g_bounds" => And.intro (And.left (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra)) (And.left (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra)))
local notation "g_relation" => (And.left D5.S1.Digit.Infinite.SixWindowForcing.algebra)
local notation "g_eq" => (And.left (And.right (And.right (And.right D5.S1.Digit.Infinite.OddColorThreeSource.golden_relations))))
local notation "t_sq" => (And.right (And.right (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra))))
local notation "t_linear" => (And.left (And.right (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra))))
local notation "BReturn" => fun (N : ℕ) => {a : D5.S1.Digit.Infinite.ResetCodebook.Return // Prod.fst (Subtype.val a) ≤ N ∧ Prod.snd (Subtype.val a) ≤ N}
local notation "Factors" => fun (lang : Set (ℤ → Bool)) (N : ℕ) =>
  {w : List Bool // D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight w=N ∧ ∃ omega∈lang, D5.S1.Digit.Infinite.ResetCodebook.Statement.factor w omega}
local notation "Words" => fun (V : Set (List Bool)) => {w : List Bool // w∈V}
local notation "WeakBook" => fun (anchor : Bool) (K N : ℕ) (d : ℝ) =>
  {v : List D5.S1.Digit.Infinite.ResetCodebook.Return // v∈D5.S1.Digit.Infinite.ResetCodebook.Statement.codebook anchor K N d}
local notation "Vertex" => fun (lang : Set (ℤ → Bool)) (n : ℕ) =>
  {v : Fin n → Bool // ∃ w∈lang, ∃ i : ℤ, D5.S1.Digit.Infinite.ResetCodebook.Transfer.history n w i=v}
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ResetCodebook
open D5.S0.Computability.Coding.PrefixFreeCode
private lemma weight_cons (a : D5.S1.Digit.Infinite.ResetCodebook.Return) (as : List D5.S1.Digit.Infinite.ResetCodebook.Return) :
    D5.S1.Digit.Infinite.ResetCodebook.Statement.weight (a::as) =
      (6*a.val.1 + 20*a.val.2) + D5.S1.Digit.Infinite.ResetCodebook.Statement.weight as := by
  simp [D5.S1.Digit.Infinite.ResetCodebook.Statement.weight]
private lemma weight_item_bound {N : ℕ} {as : List D5.S1.Digit.Infinite.ResetCodebook.Return}
    (hw : D5.S1.Digit.Infinite.ResetCodebook.Statement.weight as = N) :
    ∀ a, a ∈ as → a.val.1 ≤ N ∧ a.val.2 ≤ N := by
  intro a ha
  have hmem : 6*a.val.1 + 20*a.val.2 ∈ as.map
      (fun x => 6*x.val.1 + 20*x.val.2) := by
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hle := List.le_sum_of_mem hmem
  have hsum : (as.map (fun x => 6*x.val.1 + 20*x.val.2)).sum = N := by
    simpa [D5.S1.Digit.Infinite.ResetCodebook.Statement.weight] using hw
  rw [hsum] at hle
  constructor <;> omega
private lemma length_le_weight (as : List D5.S1.Digit.Infinite.ResetCodebook.Return) :
    as.length ≤ D5.S1.Digit.Infinite.ResetCodebook.Statement.weight as := by
  induction as with
  | nil => simp [D5.S1.Digit.Infinite.ResetCodebook.Statement.weight]
  | cons a as ih =>
      rw [weight_cons, List.length_cons]
      have ha : 1 ≤ a.val.1 := a.property.1
      have hih : as.length ≤ D5.S1.Digit.Infinite.ResetCodebook.Statement.weight as := ih
      omega
private lemma weight_length_bound {N : ℕ} {as : List D5.S1.Digit.Infinite.ResetCodebook.Return}
    (hw : D5.S1.Digit.Infinite.ResetCodebook.Statement.weight as = N) : as.length ≤ N := by
  rw [← hw]
  exact length_le_weight as
private lemma finite_weight_lists (N : ℕ) :
    ({as : List D5.S1.Digit.Infinite.ResetCodebook.Return | D5.S1.Digit.Infinite.ResetCodebook.Statement.weight as = N}).Finite := by
  letI : Finite (BReturn N) := by
    let enc : BReturn N → Fin (N+1) × Fin (N+1) := fun a =>
      (⟨a.1.val.1, by omega⟩, ⟨a.1.val.2, by omega⟩)
    refine Finite.of_injective enc ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have h1 := congrArg Prod.fst hab
    have h2 := congrArg Prod.snd hab
    simp only [enc, Fin.mk.injEq] at h1 h2
    exact Prod.ext h1 h2
  let S : Set (List D5.S1.Digit.Infinite.ResetCodebook.Return) :=
    {as | as.length ≤ N ∧ ∀ a, a ∈ as → Prod.fst (Subtype.val a) ≤ N ∧ Prod.snd (Subtype.val a) ≤ N}
  have hS : S.Finite := by
    let encItem : D5.S1.Digit.Infinite.ResetCodebook.Return → Option (BReturn N) := fun a =>
      if h : a.val.1 ≤ N ∧ a.val.2 ≤ N then some ⟨a,h⟩ else none
    let enc : List D5.S1.Digit.Infinite.ResetCodebook.Return → List (Option (BReturn N)) := List.map encItem
    have himage : (enc '' S).Finite := by
      have hlen : enc '' S ⊆ {xs : List (Option (BReturn N)) | xs.length ≤ N} := by
        intro xs hxs
        rcases hxs with ⟨as, has, rfl⟩
        have has' : as.length ≤ N ∧
            ∀ a, a ∈ as → a.val.1 ≤ N ∧ a.val.2 ≤ N := by
          simpa [S] using has
        simpa [enc] using has'.1
      exact (List.finite_length_le (Option (BReturn N)) N).subset hlen
    apply Set.Finite.of_finite_image himage
    intro as has bs hbs hab
    have has' : as.length ≤ N ∧ (∀ a, a ∈ as → a.val.1 ≤ N ∧ a.val.2 ≤ N) := by
      simpa [S] using has
    have hbs' : bs.length ≤ N ∧ (∀ a, a ∈ bs → a.val.1 ≤ N ∧ a.val.2 ≤ N) := by
      simpa [S] using hbs
    clear has hbs
    have hmap : ∀ a ha, encItem a = some ⟨a,ha⟩ := by
      intro a ha
      simp [encItem, ha]
    induction as generalizing bs with
    | nil =>
        cases bs <;> simp [enc] at hab
        all_goals rfl
    | cons a as ih =>
        cases bs with
        | nil => simp [enc] at hab
        | cons b bs =>
            simp only [enc, List.map] at hab
            have ha := has'.2 a (by simp)
            have hb := hbs'.2 b (by simp)
            have hab0 : a = b := by
              have hh := congrArg List.head? hab
              simp only [List.head?_cons] at hh
              rw [hmap a ha, hmap b hb] at hh
              have hsub : (⟨a, ha⟩ : BReturn N) = ⟨b, hb⟩ :=
                Option.some.inj (Option.some.inj hh)
              exact Subtype.ext_iff.mp hsub
            subst b
            have htail : as ∈ S := by
              constructor
              · have hlen := has'.1
                simp only [List.length_cons] at hlen
                omega
              · intro x hx
                exact has'.2 x (by simp [hx])
            have hbtail : bs ∈ S := by
              constructor
              · have hlen := hbs'.1
                simp only [List.length_cons] at hlen
                omega
              · intro x hx
                exact hbs'.2 x (by simp [hx])
            have habtail : enc as = enc bs :=
              (List.cons.inj hab).2
            exact congrArg (fun xs => a :: xs) (ih habtail htail hbtail)
  apply hS.subset
  intro as has
  exact ⟨weight_length_bound has, weight_item_bound has⟩
/-- The complete weak codebook at weight N is finite. -/
theorem codebook_finite (anchor : Bool) (K N : ℕ) (d : ℝ) :
    (D5.S1.Digit.Infinite.ResetCodebook.Statement.codebook anchor K N d).Finite := by
  exact (finite_weight_lists N).subset (by
    intro as has
    change D5.S1.Digit.Infinite.ResetCodebook.Statement.weight as = N
    exact has.1)
private lemma boolWeight_pos (c : Bool) : 0 < (if c then 20 else 6 : ℕ) := by
  cases c <;> norm_num
private lemma letterWeight_append (u v : List Bool) :
    D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight (u ++ v) =
      D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight u + D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight v := by
  simp [D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight, List.map_append, List.sum_append]
private lemma letterWeight_pos {w : List Bool} (hw : w ≠ []) :
    0 < D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight w := by
  induction w with
  | nil => contradiction
  | cons c w ih =>
      simp only [D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight, List.map_cons, List.sum_cons]
      have hc := boolWeight_pos c
      omega
/-- A fixed positive weight makes the supplied Boolean code prefix-free. -/
private theorem weighted_prefix_free (N : ℕ) (S : Set (List Bool))
    (hweight : ∀ w ∈ S, D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight w = N) :
    IsPrefixFree S := by
  intro u hu v hv huv
  obtain ⟨t, rfl⟩ := huv
  by_cases ht : t = []
  · simpa [ht]
  · have hsum := letterWeight_append u t
    have huN := hweight u hu
    have huvN := hweight (u ++ t) hv
    have hpos := letterWeight_pos ht
    rw [huN] at hsum
    rw [huvN] at hsum
    omega
private lemma codeword_weight (as : List D5.S1.Digit.Infinite.ResetCodebook.Return) :
    D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight (D5.S1.Digit.Infinite.ResetCodebook.Statement.letters as) =
      D5.S1.Digit.Infinite.ResetCodebook.Statement.weight as := by
  induction as with
  | nil => simp [D5.S1.Digit.Infinite.ResetCodebook.Statement.letters, D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight,
      D5.S1.Digit.Infinite.ResetCodebook.Statement.weight]
  | cons a as ih =>
      simp only [D5.S1.Digit.Infinite.ResetCodebook.Statement.letters, List.flatMap_cons]
      rw [letterWeight_append]
      have hhead : D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight
          (List.replicate a.val.2 true ++ List.replicate a.val.1 false) =
          20*a.val.2 + 6*a.val.1 := by
        simp [D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight, List.map_append, List.sum_append,
          List.sum_replicate]
        ring
      rw [hhead]
      change 20*a.val.2 + 6*a.val.1 +
        D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight (D5.S1.Digit.Infinite.ResetCodebook.Statement.letters as) =
        (6*a.val.1 + 20*a.val.2) + D5.S1.Digit.Infinite.ResetCodebook.Statement.weight as
      rw [ih]
      ring
end D5.S1.Digit.Infinite.ResetCodebook.Coding
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ResetCodebook
open D5.S0.Computability.Coding.PrefixFreeCode
lemma letter_length_le_weight (w : List Bool) :
    w.length ≤ Statement.letterWeight w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
      change w.length+1 ≤ (if c then 20 else 6) + Statement.letterWeight w
      have hc := boolWeight_pos c
      omega
private lemma finite_letter_weight (N : ℕ) :
    ({w : List Bool | Statement.letterWeight w=N}).Finite := by
  apply (List.finite_length_le Bool N).subset
  intro w hw
  have hb := letter_length_le_weight w
  exact hw ▸ hb
private lemma letterWeight_flatten (ws : List (List Bool)) :
    Statement.letterWeight ws.flatten = (ws.map Statement.letterWeight).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [List.flatten_cons, letterWeight_append, ih]; rfl
/-- Parsing takes place in the codebook itself, before any language realization is chosen. -/
private theorem weighted_parse_injective
    (V : Set (List Bool)) (L : ℕ) (hL : 0 < L)
    (hweight : ∀ w∈V, Statement.letterWeight w=L) (k : ℕ) :
    Function.Injective (fun f : Fin k → Words V =>
      (List.ofFn (fun i => (f i).val)).flatten) := by
  have hpf := weighted_prefix_free L V hweight
  have hnil : [] ∉ V := by
    intro hn
    have hh := hweight [] hn
    simp only [Statement.letterWeight, List.map_nil, List.sum_nil] at hh
    omega
  have hud := uniquelyDecodable_of_isPrefixFree hpf hnil
  intro f g hfg
  have hmem (q : Fin k → Words V) :
      ∀ w∈List.ofFn (fun i => (q i).val), w∈V := by
    intro w hw
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hw
    exact hi ▸ (q i).property
  have he := hud _ _ (hmem f) (hmem g) hfg
  have he' : (fun i => (f i).val) = (fun i => (g i).val) := List.ofFn_injective he
  funext i
  apply Subtype.ext
  exact congrFun he' i
private lemma concatenated_weight
    (V : Set (List Bool)) (L k : ℕ)
    (hweight : ∀ w∈V, Statement.letterWeight w=L) (f : Fin k → Words V) :
    Statement.letterWeight (List.ofFn (fun i => (f i).val)).flatten = k*L := by
  rw [letterWeight_flatten, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]
  simp_rw [hweight _ (f _).property]
  simp
/-- The realization premise says every finite parsed word occurs in one actual member of lang.
The same word supplies both its weight and its occurrence certificate. -/
private theorem weighted_factor_count
    (V : Set (List Bool)) (lang : Set (ℤ → Bool)) (L : ℕ)
    (hV : V.Finite) (hL : 0 < L)
    (hweight : ∀ w∈V, Statement.letterWeight w=L)
    (hext : ∀ (k : ℕ) (f : Fin k → Words V),
      ∃ omega∈lang, Statement.factor (List.ofFn (fun i => (f i).val)).flatten omega)
    (k : ℕ) :
    (Nat.card (Words V))^k ≤ Statement.factorCount lang (k*L) := by
  letI : Finite (Words V) := hV.to_subtype
  letI : Finite (Factors lang (k*L)) :=
    ((finite_letter_weight (k*L)).subset (by intro w hw; exact hw.1)).to_subtype
  let enc : (Fin k → Words V) → Factors lang (k*L) := fun f =>
    ⟨(List.ofFn (fun i => (f i).val)).flatten,
      concatenated_weight V L k hweight f, hext k f⟩
  have hinj : Function.Injective enc := by
    intro f g hfg
    apply weighted_parse_injective V L hL hweight k
    exact congrArg Subtype.val hfg
  have hc := Nat.card_le_card_of_injective enc hinj
  simpa only [Nat.card_fun, Nat.card_fin, Statement.factorCount] using hc
private lemma reset_codeword_weight (M : ℕ) (hM : 1 ≤ M) (v : List Return) :
    Statement.letterWeight (Statement.letters (Statement.reset M hM::v)) =
      20+6*M+Statement.weight v := by
  rw [codeword_weight, weight_cons]
  simp only [Statement.reset]
  omega
end D5.S1.Digit.Infinite.ResetCodebook.Coding
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ResetCodebook
private def leading (b : Bool) : List Bool → ℕ
  | [] => 0
  | c::cs => if c=b then leading b cs+1 else 0
private lemma leading_replicate (b : Bool) (n : ℕ) (w : List Bool) :
    leading b (List.replicate n b++w) = n+leading b w := by
  induction n with
  | zero => simp [leading]
  | succ n ih => simp [List.replicate_succ, leading, ih]; omega
private lemma leading_false_letters (as : List Return) : leading false (Statement.letters as)=0 := by
  cases as with
  | nil => rfl
  | cons a as =>
      obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero
        (show a.val.2≠0 by have := a.property.2; omega)
      simp [Statement.letters,hr,List.replicate_succ,leading]
private lemma leading_true_letters (a : Return) (as : List Return) :
    leading true (Statement.letters (a::as))=a.val.2 := by
  simp only [Statement.letters, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.append_assoc]
  change leading true (List.replicate a.val.2 true ++
    (List.replicate a.val.1 false ++ Statement.letters as)) = _
  rw [leading_replicate]
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (show a.val.1≠0 by have := a.property.1; omega)
  simp [hm,List.replicate_succ,leading]
private lemma drop_high_letters (a : Return) (as : List Return) :
    (Statement.letters (a::as)).drop a.val.2 =
      List.replicate a.val.1 false ++ Statement.letters as := by
  simp only [Statement.letters, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.append_assoc]
  change (List.replicate a.val.2 true ++
    (List.replicate a.val.1 false ++ Statement.letters as)).drop a.val.2 = _
  simp [Statement.letters]
private lemma leading_low_letters (a : Return) (as : List Return) :
    leading false ((Statement.letters (a::as)).drop a.val.2)=a.val.1 := by
  rw [drop_high_letters, leading_replicate, leading_false_letters]
  omega
/-- The two positive run lengths recover every Return without merging neighboring pairs. -/
private theorem letters_injective : Function.Injective Statement.letters := by
  intro as
  induction as with
  | nil =>
      intro bs hb
      cases bs with
      | nil => rfl
      | cons b bs =>
          have hh := congrArg List.length hb
          have hpos := b.property
          simp only [Statement.letters,List.flatMap_nil,List.flatMap_cons,
            List.length_append,List.length_replicate,List.length_nil] at hh
          omega
  | cons a as ih =>
      intro bs hab
      cases bs with
      | nil =>
          have hh := congrArg List.length hab
          have hpos := a.property
          simp only [Statement.letters,List.flatMap_nil,List.flatMap_cons,
            List.length_append,List.length_replicate,List.length_nil] at hh
          omega
      | cons b bs =>
          have hr := congrArg (leading true) hab
          rw [leading_true_letters,leading_true_letters] at hr
          have hl := congrArg (fun w => leading false (w.drop a.val.2)) hab
          rw [leading_low_letters,hr,leading_low_letters] at hl
          have he : a=b := by
            apply Subtype.ext
            exact Prod.ext hl hr
          subst b
          have htail : Statement.letters as=Statement.letters bs := by
            change _ ++ Statement.letters as = _ ++ Statement.letters bs at hab
            exact List.append_cancel_left hab
          exact congrArg (fun xs => a::xs) (ih htail)
private noncomputable def resetImage (anchor : Bool) (K M N : ℕ) (d : ℝ) (hM : 1≤M) :
    Set (List Bool) :=
  (fun v => Statement.letters (Statement.reset M hM::v)) ''
    Statement.codebook anchor K N d
private lemma reset_encoder_injective (M : ℕ) (hM : 1≤M) :
    Function.Injective (fun v : List Return => Statement.letters (Statement.reset M hM::v)) := by
  intro v u he
  exact (List.cons.inj (letters_injective he)).2
private noncomputable def resetBookEquiv
    (anchor : Bool) (K M N : ℕ) (d : ℝ) (hM : 1≤M) :
    WeakBook anchor K N d ≃ Words (resetImage anchor K M N d hM) := by
  apply Equiv.ofBijective (fun v =>
    ⟨Statement.letters (Statement.reset M hM::v.val),v.val,v.property,rfl⟩)
  constructor
  · intro v u he
    apply Subtype.ext
    exact reset_encoder_injective M hM (congrArg Subtype.val he)
  · intro w
    obtain ⟨v,hv,he⟩ := w.property
    exact ⟨⟨v,hv⟩,Subtype.ext he⟩
private lemma resetImage_weight (anchor : Bool) (K M N : ℕ) (d : ℝ) (hM : 1≤M) :
    ∀ w∈resetImage anchor K M N d hM,
      Statement.letterWeight w=N+20+6*M := by
  rintro w ⟨v,hv,rfl⟩
  rw [reset_codeword_weight,hv.1]
  omega
/-- Counts the original complete weak book, provided its finite words extend in the given language. -/
private theorem weak_book_factor_count
    (anchor : Bool) (K M N : ℕ) (d : ℝ) (hM : 1≤M)
    (lang : Set (ℤ → Bool))
    (hext : ∀ (k : ℕ) (f : Fin k → Words (resetImage anchor K M N d hM)),
      ∃ omega∈lang, Statement.factor (List.ofFn (fun i => (f i).val)).flatten omega)
    (k : ℕ) :
    (Nat.card (WeakBook anchor K N d))^k ≤ Statement.factorCount lang (k*(N+20+6*M)) := by
  have hf := (codebook_finite anchor K N d).image
    (fun v => Statement.letters (Statement.reset M hM::v))
  have hc := weighted_factor_count (resetImage anchor K M N d hM) lang (N+20+6*M)
    hf (by omega) (resetImage_weight anchor K M N d hM) hext k
  rw [← Nat.card_congr (resetBookEquiv anchor K M N d hM)] at hc
  exact hc
end D5.S1.Digit.Infinite.ResetCodebook.Coding
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ResetCodebook Filter
private noncomputable def weightedReadout (lang : Set (ℤ → Bool)) (n : ℕ) : ℝ :=
  Real.log (max 1 (Statement.factorCount lang n):ℝ)/Real.log 2/(n:ℝ)
private lemma power_count_log_bound
    (lang : Set (ℤ → Bool)) (a L k : ℕ) (ha : 0<a) (hL : 0<L) (hk : 0<k)
    (hc : a^k ≤ Statement.factorCount lang (k*L)) :
    Real.log (a:ℝ)/Real.log 2/(L:ℝ) ≤ weightedReadout lang (k*L) := by
  have ha' : 0<(a:ℝ) := by exact_mod_cast ha
  have hL' : 0<(L:ℝ) := by exact_mod_cast hL
  have hk' : 0<(k:ℝ) := by exact_mod_cast hk
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hcast : (a:ℝ)^k ≤ (max 1 (Statement.factorCount lang (k*L)):ℝ) := by
    exact_mod_cast hc.trans (le_max_right _ _)
  have hlog := Real.log_le_log (pow_pos ha' k) hcast
  rw [Real.log_pow] at hlog
  have he : Real.log (a:ℝ)/Real.log 2/(L:ℝ) =
      ((k:ℝ)*Real.log (a:ℝ))/Real.log 2/((k:ℝ)*(L:ℝ)) := by
    field_simp
  rw [he]
  unfold weightedReadout
  rw [Nat.cast_mul]
  exact div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right hlog h2.le) (mul_pos hk' hL').le
/-- The real-valued limsup uses an explicit boundedness premise. -/
private theorem weighted_rate_from_counts
    (lang : Set (ℤ → Bool)) (a L : ℕ) (ha : 0<a) (hL : 0<L)
    (hc : ∀ k, a^k ≤ Statement.factorCount lang (k*L))
    (hb : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (weightedReadout lang)) :
    Real.log (a:ℝ)/Real.log 2/(L:ℝ) ≤ Statement.rate lang := by
  apply Filter.le_limsup_of_frequently_le _ hb
  rw [Filter.frequently_atTop]
  intro m
  refine ⟨(m+1)*L, ?_, ?_⟩
  · have hL1 : 1 ≤ L := hL
    nlinarith
  · exact power_count_log_bound lang a L (m+1) ha hL (by omega) (hc (m+1))
end D5.S1.Digit.Infinite.ResetCodebook.Coding
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ResetCodebook Filter
private lemma factorCount_le_pow (lang : Set (ℤ → Bool)) (n : ℕ) :
    Statement.factorCount lang n ≤ 3^n := by
  letI : Finite (Factors lang n) :=
    ((finite_letter_weight n).subset (by intro w hw; exact hw.1)).to_subtype
  let enc : Factors lang n → (Fin n → Option Bool) := fun w j => w.val[j.val]?
  have hinj : Function.Injective enc := by
    intro u v huv
    apply Subtype.ext
    apply List.ext_getElem?
    intro j
    by_cases hj : j<n
    · exact congrFun huv ⟨j,hj⟩
    · have hu : u.val.length≤n := by
        have hh := letter_length_le_weight u.val
        rw [u.property.1] at hh
        exact hh
      have hv : v.val.length≤n := by
        have hh := letter_length_le_weight v.val
        rw [v.property.1] at hh
        exact hh
      rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
  have hc := Nat.card_le_card_of_injective enc hinj
  simpa [Statement.factorCount,Nat.card_fun,Nat.card_eq_fintype_card] using hc
private lemma weightedReadout_bound (lang : Set (ℤ → Bool)) (n : ℕ) :
    weightedReadout lang n ≤ Real.log 3/Real.log 2 := by
  by_cases hn : n=0
  · subst n
    unfold weightedReadout
    simp only [Nat.cast_zero,div_zero]
    positivity
  · have hn' : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    have hc : max 1 (Statement.factorCount lang n) ≤ 3^n := by
      exact max_le (one_le_pow₀ (by norm_num)) (factorCount_le_pow lang n)
    have hcast : (max 1 (Statement.factorCount lang n):ℝ) ≤ (3:ℝ)^n := by
      exact_mod_cast hc
    have hpos : 0<(max 1 (Statement.factorCount lang n):ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by omega : 0<1) (le_max_left _ _)
    have hlog := Real.log_le_log hpos hcast
    rw [Real.log_pow] at hlog
    unfold weightedReadout
    have hm := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hlog h2.le) hn'.le
    apply hm.trans_eq
    field_simp
lemma weightedReadout_bounded (lang : Set (ℤ → Bool)) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (weightedReadout lang) := by
  exact ⟨Real.log 3/Real.log 2,
    Filter.eventually_map.mpr (Filter.Eventually.of_forall (weightedReadout_bound lang))⟩
/-- Exact explicit weighted-language rate, conditional only on actual word extension. -/
private theorem weak_book_language_rate
    (anchor : Bool) (K M N : ℕ) (d : ℝ) (hM : 1≤M)
    (hne : (Statement.codebook anchor K N d).Nonempty)
    (lang : Set (ℤ → Bool))
    (hext : ∀ (k : ℕ) (f : Fin k → Words (resetImage anchor K M N d hM)),
      ∃ omega∈lang, Statement.factor (List.ofFn (fun i => (f i).val)).flatten omega) :
    Real.log (Nat.card (WeakBook anchor K N d):ℝ)/Real.log 2/(N+20+6*M:ℝ)
      ≤ Statement.rate lang := by
  letI : Nonempty (WeakBook anchor K N d) := hne.to_subtype
  letI : Finite (WeakBook anchor K N d) := (codebook_finite anchor K N d).to_subtype
  have hc := weak_book_factor_count anchor K M N d hM lang hext
  have hr := weighted_rate_from_counts lang (Nat.card (WeakBook anchor K N d))
    (N+20+6*M) Nat.card_pos (by omega) hc (weightedReadout_bounded lang)
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hr
end D5.S1.Digit.Infinite.ResetCodebook.Coding
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
namespace D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ResetCodebook
private noncomputable def periodicWord (u : List Bool) (i : ℤ) : Bool :=
  u[(i%(u.length:ℤ)).toNat]?.getD false
private lemma periodicWord_block (u : List Bool) (t : ℤ) :
    ∀ j : Fin u.length, periodicWord u (t*(u.length:ℤ)+(j.val:ℤ))=u[j.val] := by
  intro j
  have hm : (t*(u.length:ℤ)+(j.val:ℤ))%(u.length:ℤ)=(j.val:ℤ) := by
    rw [Int.add_emod, Int.mul_emod]
    simp only [Int.emod_self, mul_zero, Int.zero_emod, zero_add]
    have hj : (j.val:ℤ) < (u.length:ℤ) := by exact_mod_cast j.isLt
    rw [Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le j.val) hj,
      Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le j.val) hj]
  simp [periodicWord,hm,List.getElem?_eq_getElem j.isLt]
private lemma periodicWord_cover (u : List Bool) (hn : 0 < u.length) (i : ℤ) :
    ∃ t : ℤ, t*(u.length:ℤ)  ≤  i ∧ i < (t+1)*(u.length:ℤ) := by
  have hm : 0 < (u.length:ℤ) := by exact_mod_cast hn
  have ha := Int.emod_nonneg i (ne_of_gt hm)
  have hb := Int.emod_lt_of_pos i hm
  have he := Int.emod_add_ediv_mul i (u.length:ℤ)
  refine ⟨i/(u.length:ℤ), ?_, ?_⟩
  · omega
  · rw [add_mul,one_mul]
    omega
private lemma weak_append (K : ℕ) (q : ℝ) (as bs : List Return) (z : ℝ)
    (ha : Statement.weak K q as z)
    (hb : Statement.weak K q bs (execute false as z)) :
    Statement.weak K q (as++bs) z := by
  induction as generalizing z with
  | nil => exact hb
  | cons a as ih =>
      rw [weak_run] at ha
      rw [List.cons_append,weak_run]
      exact ⟨ha.1,ha.2.1,ih _ ha.2.2 hb⟩
/-- All finite codeword lists share the strengthened guard for every legal cut state. -/
private lemma finite_reset_weak_state
    (anchor : Bool) (K M N : ℕ) (d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M)
    (hreset : initial false anchor < Statement.B M)
    (vs : List (List Return))
    (hvs : ∀ v∈vs, v∈Statement.codebook anchor K N d)
    (z : ℝ) (hz : A false ≤ z) (hh : z ≤ h false) :
    Statement.weak K (d+(Statement.B M-initial false anchor)*g^N)
      ((vs.map (fun v => Statement.reset M hM::v)).flatten) z := by
  have hp := parameters false
  have hA := A_nonneg
  induction vs generalizing z with
  | nil => trivial
  | cons v vs ih =>
      have hv := hvs v (by simp)
      have hr := run_bounds false (Statement.reset M hM) z (hA.trans hz) hh
      have hresetz : Statement.B M  ≤  run false (Statement.reset M hM) z := by
        rw [run_closed]
        exact reset_lifts M z hz
      have hweak := weak_gain K d (Statement.B M-initial false anchor)
        (initial false anchor) (run false (Statement.reset M hM) z) v
        (sub_pos.mpr hreset) (by linarith) hv.2
      have hweight : Statement.weight v=N := hv.1
      rw [hweight] at hweak
      have hw : Statement.weak K (d+(Statement.B M-initial false anchor)*g^N)
          (Statement.reset M hM::v) z := by
        rw [weak_run]
        refine ⟨by change 1 ≤ K; omega,?_,hweak⟩
        intro heq
        change 1=K at heq
        omega
      have hexf := execute_floor false (Statement.reset M hM::v) z hz hh
      have hexh := (execute_bounds false (Statement.reset M hM::v) z (hA.trans hz) hh).2
      have htail := ih (fun x hx => hvs x (by simp [hx])) _ hexf hexh
      simp only [List.map_cons,List.flatten_cons]
      exact weak_append K _ _ _ z hw htail
private lemma letters_flatten (vs : List (List Return)) :
    Statement.letters vs.flatten = (vs.map Statement.letters).flatten := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.flatten_cons,Statement.letters,List.flatMap_append,List.map_cons]
      exact congrArg (fun u => Statement.letters v++u) ih
/-- A finite list is realized by periodic repetition of its literal Boolean word.
The margin remains the original codebook margin, rather than shrinking with the list length. -/
private theorem periodic_reset_word_membership
    (anchor : Bool) (K M N n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M)
    (hreset : initial false anchor < Statement.B M)
    (hcut : h false*rho^n < chi^(K-1)*(Statement.B M-initial false anchor)*g^N)
    (vs : List (List Return)) (hne : vs≠[])
    (hvs : ∀ v∈vs, v∈Statement.codebook anchor K N d) :
    let u := (vs.map (fun v => Statement.letters (Statement.reset M hM::v))).flatten
    periodicWord u ∈ Statement.lowerLanguage K n d ∧ Statement.factor u (periodicWord u) := by
  let exec := (vs.map (fun v => Statement.reset M hM::v)).flatten
  let u := Statement.letters exec
  have hu : u = (vs.map (fun v => Statement.letters (Statement.reset M hM::v))).flatten := by
    dsimp [u,exec]
    rw [letters_flatten,List.map_map]
    rfl
  have hexe : ∃ a as, exec=a::as := by
    cases vs with
    | nil => contradiction
    | cons v vs => exact ⟨Statement.reset M hM,v++(vs.map (fun v => Statement.reset M hM::v)).flatten,rfl⟩
  obtain ⟨a,as,hex⟩ := hexe
  obtain ⟨u',hu'⟩ := letters_end_false a as
  have hend : u=u'++[false] := by dsimp [u]; rw [hex,hu']
  have hlen : 0 < u.length := by rw [hend,List.length_append]; simp
  have hprev (t : ℤ) : periodicWord u (t*(u.length:ℤ)-1)=false := by
    have hi : u'.length < u.length := by rw [hend,List.length_append]; simp
    have hh := periodicWord_block u (t-1) ⟨u'.length,hi⟩
    have he : (t-1)*(u.length:ℤ)+(u'.length:ℤ)=t*(u.length:ℤ)-1 := by
      have hl : (u.length:ℤ)=(u'.length:ℤ)+1 := by simp [hend]
      rw [hl]; ring
    rw [he] at hh
    simpa [hend] using hh
  have hfloor (t : ℤ) : A false ≤ stateRec (periodicWord u) (t*(u.length:ℤ)) := by
    have hs := stateRec_next (periodicWord u) (t*(u.length:ℤ)-1)
    rw [sub_add_cancel,hprev t] at hs
    have hn := (stateRec_interval (periodicWord u) (t*(u.length:ℤ)-1)).1
    have hp := parameters false
    rw [hs]
    change A false  ≤  A false+rho*stateRec (periodicWord u) (t*(u.length:ℤ)-1)
    exact le_add_of_nonneg_right (mul_nonneg hp.1.le hn)
  have hcm : Statement.cap K (periodicWord u) ∧
      ∀ i, Statement.high K (periodicWord u) i →
        chi^(K-1)*d+chi^(K-1)*(Statement.B M-initial false anchor)*g^N  ≤
          stateRec (periodicWord u) i := by
    have hg (i : ℤ) := periodicWord_cover u hlen i
    have hlocal (t : ℤ) := weak_word_local_guard (periodicWord u) (t*(u.length:ℤ)) K
      (d+(Statement.B M-initial false anchor)*g^N) exec
      (finite_reset_weak_state anchor K M N d hK hM hreset vs hvs _ (hfloor t)
        (stateRec_interval (periodicWord u) _).2)
      (hprev t) (periodicWord_block u t)
    constructor
    · intro i
      obtain ⟨t,hti,hit⟩ := hg i
      apply (hlocal t i hti _).1
      rw [add_mul,one_mul] at hit
      exact hit
    · intro i hi
      obtain ⟨t,hti,hit⟩ := hg i
      have hh := (hlocal t i hti (by rw [add_mul,one_mul] at hit; exact hit)).2 hi
      nlinarith [hh]
  have hm : periodicWord u∈Statement.lowerLanguage K n d := by
    rw [lowerLanguage_eq_XMinus]
    apply aux_mem_XMinus K n (chi^(K-1)*d) _ (periodicWord u) hcm.1 hcm.2 _ hcut
    have hg : 0 < g := by have := g_bounds; linarith
    exact mul_pos (mul_pos (pow_pos (parameters false).2.2.1 _) (sub_pos.mpr hreset)) (pow_pos hg _)
  have hf : Statement.factor u (periodicWord u) := by
    refine ⟨0,?_⟩
    simpa using periodicWord_block u 0
  simpa only [hu] using And.intro hm hf
end D5.S1.Digit.Infinite.ResetCodebook.Coding
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
namespace D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ResetCodebook
/-- Every finite parsed list occurs in an actual member of the same chosen lower language. -/
private theorem reset_words_extension
    (anchor : Bool) (K M N n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M)
    (hreset : initial false anchor < Statement.B M)
    (hcut : h false*rho^n < chi^(K-1)*(Statement.B M-initial false anchor)*g^N)
    (hne : (Statement.codebook anchor K N d).Nonempty) :
    ∀ (k : ℕ) (f : Fin k → Words (resetImage anchor K M N d hM)),
      ∃ omega∈Statement.lowerLanguage K n d,
        Statement.factor (List.ofFn (fun i => (f i).val)).flatten omega := by
  intro k f
  let e := resetBookEquiv anchor K M N d hM
  let g : Fin k → WeakBook anchor K N d := fun i => e.symm (f i)
  let vs := List.ofFn (fun i => (g i).val)
  have hvs : ∀ v∈vs, v∈Statement.codebook anchor K N d := by
    intro v hv
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hv
    exact hi ▸ (g i).property
  by_cases hk : k=0
  · subst k
    obtain ⟨v0,hv0⟩ := hne
    have hp := periodic_reset_word_membership anchor K M N n d hK hM hreset hcut
      [v0] (by simp) (by intro v hv; simpa using (List.mem_singleton.mp hv ▸ hv0))
    refine ⟨periodicWord (Statement.letters (Statement.reset M hM::v0)),?_,?_⟩
    · simpa using hp.1
    · simp only [List.ofFn_zero,List.flatten_nil]
      refine ⟨0,?_⟩
      intro j
      exact Fin.elim0 j
  · have hnon : vs≠[] := by
      intro he
      have hh := congrArg List.length he
      simp [vs] at hh
      exact hk hh
    have hp := periodic_reset_word_membership anchor K M N n d hK hM hreset hcut vs hnon hvs
    have hu :
        (vs.map (fun v => Statement.letters (Statement.reset M hM::v))).flatten =
          (List.ofFn (fun i => (f i).val)).flatten := by
      dsimp [vs]
      rw [List.map_ofFn]
      congr 1
      apply congrArg List.ofFn
      funext i
      have he := congrArg Subtype.val (e.apply_symm_apply (f i))
      exact he
    refine ⟨periodicWord
      (vs.map (fun v => Statement.letters (Statement.reset M hM::v))).flatten,hp.1,?_⟩
    rw [← hu]
    exact hp.2
/-- The count and rate use the original complete weak codebook. -/
theorem complete_lower_language_count_and_rate
    (anchor : Bool) (K M N n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M)
    (hreset : initial false anchor < Statement.B M)
    (hcut : h false*rho^n < chi^(K-1)*(Statement.B M-initial false anchor)*g^N)
    (hne : (Statement.codebook anchor K N d).Nonempty) :
    (∀ k, (Nat.card (WeakBook anchor K N d))^k ≤
      Statement.factorCount (Statement.lowerLanguage K n d) (k*(N+20+6*M))) ∧
    Real.log (Nat.card (WeakBook anchor K N d):ℝ)/Real.log 2/(N+20+6*M:ℝ)
      ≤ Statement.rate (Statement.lowerLanguage K n d) := by
  have hext := reset_words_extension anchor K M N n d hK hM hreset hcut hne
  exact ⟨weak_book_factor_count anchor K M N d hM _ hext,
    weak_book_language_rate anchor K M N d hM hne _ hext⟩
end D5.S1.Digit.Infinite.ResetCodebook.Coding
