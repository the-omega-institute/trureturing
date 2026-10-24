/- GID: D5/S0/Automata/TwoStateCertificateWidth
   generality: G
   mirror-B: D5/B/S0/Automata/TwoStateCertificateWidth
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Total two-state short-word samples have alphabet-linear certificate width. -/

import D5.S0.Automata.TwoStateShortWordSampleBound
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Finite.List

/-! Original-word obstruction minima, native cycle samples and exact alphabet transport. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.TwoStateCertificateWidth

open D5.S0.Automata.DFAOStateLowerBound
open D5.S0.Automata.FiniteSampleRestriction
open D5.S0.Automata.TwoStateShortWordSampleBound

/-- Only the listed words are observed; the machine is total on every input. -/
def Realizable {A : Type} (D : Finset (List A)) (t : List A → Bool) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (M : DFAO A Bool S),
    Fintype.card S ≤ 2 ∧ ∀ w ∈ D, M.evalOutput w = t w

private theorem restrict {A : Type} {D E : Finset (List A)} {t : List A → Bool}
    (h : Realizable D t) (sub : E ⊆ D) : Realizable E t := by
  obtain ⟨S, inst, M, hc, hM⟩ := h
  exact ⟨S, inst, M, hc, fun w hw => hM w (sub hw)⟩

private theorem bad_card_exists {A : Type} {D : Finset (List A)} {t : List A → Bool}
    (h : ¬ Realizable D t) :
    ∃ n : ℕ, ∃ E : Finset (List A), E ⊆ D ∧ ¬ Realizable E t ∧ E.card = n :=
  ⟨D.card, D, Finset.Subset.refl D, h, rfl⟩

/-- The least number of original observations with no model, or infinity. -/
noncomputable def omega2 {A : Type} (D : Finset (List A)) (t : List A → Bool) : ℕ∞ :=
  by
    classical
    exact if h : Realizable D t then ⊤ else Nat.find (bad_card_exists h)

private theorem omega_spec {A : Type} (D : Finset (List A)) (t : List A → Bool)
    (h : ¬ Realizable D t) :
    ∃ E : Finset (List A), E ⊆ D ∧ ¬ Realizable E t ∧
      omega2 D t = (E.card : ℕ∞) ∧
      ∀ F : Finset (List A), F ⊆ D → ¬ Realizable F t → E.card ≤ F.card := by
  classical
  obtain ⟨E, hE, bad, card⟩ := Nat.find_spec (bad_card_exists h)
  refine ⟨E, hE, bad, ?_, ?_⟩
  · simp only [omega2, dite_eq_right h, card]
  · intro F hF badF
    rw [card]
    exact Nat.find_min' (bad_card_exists h) ⟨F, hF, badF, rfl⟩

/-- The range includes only unrealizable short samples on the exact alphabet. -/
def obstructionRange (k : ℕ) : Set ℕ :=
  {n | ∃ (D : Finset (List (Fin k))) (t : List (Fin k) → Bool),
    (∀ w ∈ D, w.length ≤ 2) ∧ ¬ Realizable D t ∧ omega2 D t = (n : ℕ∞)}

/-- Supremum of the actual finite obstruction widths. -/
noncomputable def H2 (k : ℕ) : ℕ∞ :=
  sSup {x : ℕ∞ | ∃ (D : Finset (List (Fin k))) (t : List (Fin k) → Bool),
    (∀ w ∈ D, w.length ≤ 2) ∧ ¬ Realizable D t ∧ omega2 D t = x}

private theorem upper_core (k : ℕ) (D : Finset (List (Fin k)))
    (t : List (Fin k) → Bool) (hlen : ∀ w ∈ D, w.length ≤ 2)
    (bad : ¬ Realizable D t) :
    ∃ E : Finset (List (Fin k)), E ⊆ D ∧ ¬ Realizable E t ∧ E.card ≤ 16 * (k + 1) := by
  classical
  let target : {w // w ∈ D} → Bool := fun w => t w.val
  have bn : ∀ e, ¬ ∃ x y : Fin k → Bool,
      CorrectOnFamily (normalized e x y) Subtype.val target := by
    rintro e ⟨x,y,hxy⟩
    exact bad ⟨Bool,inferInstance,normalized e x y,by decide,
      fun w hw => hxy ⟨w,hw⟩⟩
  choose E hcard hbad using fun e => branch_core k D target hlen e (bn e)
  let U := E false ∪ E true
  let F := U.image Subtype.val
  have hc : F.card ≤ 16 * (k + 1) := by
    have hU := Finset.card_union_le (E false) (E true)
    have h0 := hcard false
    have h1 := hcard true
    have hF := Finset.card_image_le (s := U) (f := Subtype.val)
    dsimp [F, U] at *
    omega
  refine ⟨F, ?_, ?_, hc⟩
  · intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact i.property
  · rintro ⟨S, inst, M, hS, hM⟩
    let := inst
    obtain ⟨e,x,y,hagree⟩ := normalize_two_states M hS
    apply hbad e
    refine ⟨x,y,?_⟩
    intro i
    have hi : i.val ∈ U := by
      cases e
      · exact Finset.mem_union_left _ i.property
      · exact Finset.mem_union_right _ i.property
    exact (hagree _).trans (hM _ (Finset.mem_image.mpr ⟨i.val,hi,rfl⟩))

/-- The two symbol roles occupy disjoint summands. -/
abbrev RoleAlphabet (m : ℕ) := Fin m ⊕ Fin m

/-- A suffix identifies the edge; the Boolean identifies its endpoint. -/
def cycleWord {m : ℕ} (p : Fin m × Bool) : List (RoleAlphabet m) :=
  [Sum.inl (if p.2 then finRotate m p.1 else p.1), Sum.inr p.1]

noncomputable def cycleDomain (m : ℕ) : Finset (List (RoleAlphabet m)) :=
  Finset.univ.image cycleWord

noncomputable def cycleLabel {m : ℕ} (w : List (RoleAlphabet m)) : Bool :=
  decide (∃ i : Fin m, w = cycleWord (i,true))

private theorem rotate_ne {m : ℕ} (hm : 2 ≤ m) (i : Fin m) : finRotate m i ≠ i := by
  have := i.neZero
  rw [finRotate_apply]
  intro h
  have hh : (1 : Fin m) = 0 := add_left_cancel (show i + 1 = i + 0 by simpa using h)
  have hv := congrArg Fin.val hh
  have hmod : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
  change 1 % m = 0 at hv
  omega

private theorem word_injective {m : ℕ} (hm : 2 ≤ m) :
    Function.Injective (@cycleWord m) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  have hh : (if b then finRotate m i else i) =
      (if c then finRotate m j else j) ∧ i = j := by
    simpa only [cycleWord, List.cons.injEq, Sum.inl.injEq, Sum.inr.injEq,
      and_true] using h
  obtain ⟨hh,rfl⟩ := hh
  have hn := rotate_ne hm i
  cases b <;> cases c
  · rfl
  · exact (hn hh.symm).elim
  · exact (hn hh).elim
  · rfl

private theorem label_word {m : ℕ} (hm : 2 ≤ m) (p : Fin m × Bool) :
    cycleLabel (cycleWord p) = p.2 := by
  classical
  have hi := word_injective hm
  rcases p with ⟨i,b⟩
  cases b <;> simp [cycleLabel, hi.eq_iff]

private def cutPosition {m : ℕ} (j i : Fin m) : Fin m :=
  ⟨if j.val < i.val then i.val - (j.val+1) else i.val + (m-(j.val+1)), by
    split_ifs <;> omega⟩

private theorem cut_adj {m : ℕ} (j i : Fin (m + 1)) (hi : i ≠ j) :
    (SimpleGraph.pathGraph (m + 1)).Adj (cutPosition j i)
      (cutPosition j (finRotate (m + 1) i)) := by
  rw [SimpleGraph.pathGraph_adj]
  left
  have hr := coe_finRotate i
  have hij : i.val ≠ j.val := fun h => hi (Fin.ext h)
  have hl : (i = Fin.last m) ↔ i.val = m := by simp [Fin.ext_iff]
  dsimp [cutPosition]
  split_ifs at hr ⊢ <;> simp_all only [Fin.val_last] <;> omega

private def cutMachine {m : ℕ} (j : Fin m) : DFAO (RoleAlphabet m) Bool Bool :=
  let c : Fin m → Bool := fun i => SimpleGraph.pathGraph.bicoloring m (cutPosition j i)
  { start := false
    step := fun q a => match a with
      | Sum.inl i => c i
      | Sum.inr i => if i = j then true else if q = c i then false else true
    accept := ∅
    output := id }

private theorem cycle_local (n : ℕ) (E : Finset (List (RoleAlphabet (2 * n + 3))))
    (sub : E ⊆ cycleDomain (2 * n + 3)) (small : E.card ≤ n) :
    Realizable E cycleLabel := by
  classical
  let m := 2 * n + 3
  have hm : 2 ≤ m := by omega
  have hj : ∃ j : Fin m, cycleWord (j,false) ∉ E := by
    by_contra h
    push Not at h
    have hs : (Finset.univ.image (fun i : Fin m => cycleWord (i,false))) ⊆ E := by
      intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      exact h i
    have hinj : Function.Injective (fun i : Fin m => cycleWord (i,false)) :=
      fun i j h => congrArg Prod.fst (word_injective hm h)
    have hc := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _ hinj] at hc
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨j,hj⟩ := hj
  refine ⟨Bool,inferInstance,cutMachine j,by decide,?_⟩
  intro w hw
  obtain ⟨⟨i,b⟩, _, rfl⟩ := Finset.mem_image.mp (sub hw)
  rw [label_word hm]
  have hc : ∀ i : Fin m, i ≠ j →
      SimpleGraph.pathGraph.bicoloring m (cutPosition j i) ≠
      SimpleGraph.pathGraph.bicoloring m (cutPosition j (finRotate m i)) := by
    intro i hi
    exact (SimpleGraph.pathGraph.bicoloring m).valid (cut_adj j i hi)
  cases b with
  | false =>
    have hi : i ≠ j := by rintro rfl; exact hj hw
    simp [DFAO.evalOutput, DFA.eval, DFA.evalFrom, cutMachine, cycleWord, hi]
  | true =>
    by_cases hi : i = j
    · subst i
      simp [DFAO.evalOutput, DFA.eval, DFA.evalFrom, cutMachine, cycleWord]
    · have hh := (hc i hi).symm
      simp only [m, finRotate_apply] at hh
      simp [DFAO.evalOutput, DFA.eval, DFA.evalFrom, cutMachine, cycleWord, hi, hh]

private theorem cycle_bad (n : ℕ) :
    ¬ Realizable (cycleDomain (2 * n + 3)) cycleLabel := by
  classical
  let m := 2 * n + 3
  have hm : 2 ≤ m := by omega
  rintro ⟨S,inst,M,hS,hM⟩
  let := inst
  have separate : ∀ i : Fin m,
      M.step M.start (Sum.inl i) ≠ M.step M.start (Sum.inl (finRotate m i)) := by
    intro i he
    have h0 := hM (cycleWord (i,false)) (Finset.mem_image.mpr ⟨(i,false),by simp,rfl⟩)
    have h1 := hM (cycleWord (i,true)) (Finset.mem_image.mpr ⟨(i,true),by simp,rfl⟩)
    rw [label_word hm] at h0 h1
    simp only [cycleWord, Bool.false_eq_true, ite_false, ite_true,
      DFAO.evalOutput, DFA.eval, DFA.evalFrom, List.foldl_cons, List.foldl_nil] at h0 h1
    rw [he] at h0
    exact Bool.false_ne_true (h0.symm.trans h1)
  let coloring : (SimpleGraph.cycleGraph m).Coloring S :=
    SimpleGraph.Coloring.mk (fun i => M.step M.start (Sum.inl i)) (by
      intro i j hadj
      have := i.neZero
      change i - j = 1 ∨ j - i = 1 at hadj
      rcases hadj with h | h
      · have hj : i = finRotate m j := by
          rw [finRotate_apply, ← h]
          abel
        rw [hj]
        exact (separate j).symm
      · have hj : j = finRotate m i := by
          rw [finRotate_apply, ← h]
          abel
        rw [hj]
        exact separate i)
  have hc := (coloring.colorable.mono hS).chromaticNumber_le
  rw [SimpleGraph.chromaticNumber_cycleGraph_of_odd m hm ⟨n+1, by omega⟩] at hc
  norm_num at hc


/-- Alphabet extension keeps the same states, initial state and outputs. -/
noncomputable def extendMachine {A B S : Type} (f : A → B)
    (M : DFAO A Bool S) : DFAO B Bool S :=
  { start := M.start
    step := fun q => Function.extend f (M.step q) (fun _ => q)
    accept := M.accept
    output := M.output }

private theorem extend_eval {A B S : Type} (f : A → B) (hf : Function.Injective f)
    (M : DFAO A Bool S) (w : List A) :
    (extendMachine f M).evalOutput (w.map f) = M.evalOutput w := by
  have same : (extendMachine f M).toDFA.comap f = M.toDFA := by
    have hs : (fun q a => Function.extend f (M.step q) (fun _ => q) (f a)) = M.step :=
      funext fun q => funext fun a => hf.extend_apply (M.step q) (fun _ => q) a
    exact congrArg (fun step => DFA.mk step M.start M.accept) hs
  change M.output ((extendMachine f M).toDFA.eval (w.map f)) = M.output (M.toDFA.eval w)
  rw [← DFA.eval_comap (extendMachine f M).toDFA f w, same]

/-- Labels on image words, with arbitrary default false elsewhere. -/
noncomputable def imageLabel {A B : Type} (f : A → B) (t : List A → Bool) :
    List B → Bool := Function.extend (List.map f) t (fun _ => false)

private theorem image_models {A B : Type} [DecidableEq B] (f : A → B) (hf : Function.Injective f)
    (D : Finset (List A)) (t : List A → Bool) :
    Realizable (D.image (List.map f)) (imageLabel f t) ↔ Realizable D t := by
  classical
  constructor
  · rintro ⟨S,inst,M,hS,hM⟩
    let N : DFAO A Bool S := { M.toDFA.comap f with output := M.output }
    refine ⟨S,inst,N,hS,?_⟩
    intro w hw
    have he := hM (w.map f) (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
    rw [imageLabel, hf.list_map.extend_apply] at he
    simpa only [DFAO.evalOutput, N, DFA.eval_comap] using he
  · rintro ⟨S,inst,M,hS,hM⟩
    refine ⟨S,inst,extendMachine f M,hS,?_⟩
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    rw [extend_eval f hf, hM v hv, imageLabel, hf.list_map.extend_apply]

private theorem image_subset {A B : Type} [DecidableEq B] (f : A → B) (hf : Function.Injective f)
    (D : Finset (List A)) (F : Finset (List B)) (sub : F ⊆ D.image (List.map f)) :
    ∃ E : Finset (List A), E ⊆ D ∧ E.image (List.map f) = F ∧ E.card = F.card := by
  classical
  let E := D.filter (fun w => w.map f ∈ F)
  have he : E.image (List.map f) = F := by
    ext w
    constructor
    · intro h
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hv).2
    · intro h
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (sub h)
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv,h⟩, rfl⟩
  refine ⟨E,Finset.filter_subset _ _,he,?_⟩
  rw [← he, Finset.card_image_of_injective _ hf.list_map]

private theorem lower_sample (k : ℕ) (hk : 6 ≤ k) :
    ∃ (D : Finset (List (Fin k))) (t : List (Fin k) → Bool),
      (∀ w ∈ D, w.length ≤ 2) ∧ ¬ Realizable D t ∧
      ((k-2)/4 : ℕ) ≤ (omega2 D t : ℕ∞) := by
  classical
  let n := (k-6)/4
  let m := 2 * n + 3
  have hmk : 2*m ≤ k := by
    have hr := Nat.mod_add_div (k-6) 4
    have hs := Nat.mod_lt (k-6) (by decide : 0 < 4)
    dsimp [m,n]
    omega
  have hfloor : n+1 = (k-2)/4 := by
    have hr := Nat.mod_add_div (k-6) 4
    have hs := Nat.mod_lt (k-6) (by decide : 0 < 4)
    have hr' := Nat.mod_add_div (k-2) 4
    have hs' := Nat.mod_lt (k-2) (by decide : 0 < 4)
    dsimp [n]
    omega
  let f : RoleAlphabet m → Fin k := fun a => (finSumFinEquiv a).castLE (by omega)
  have hf : Function.Injective f := by
    intro a b h
    apply finSumFinEquiv.injective
    have hv : (f a).val = (f b).val := congrArg (fun z : Fin k => z.val) h
    exact Fin.ext hv
  let D := (cycleDomain m).image (List.map f)
  let t := imageLabel f (@cycleLabel m)
  have bad : ¬ Realizable D t := fun h => cycle_bad n ((image_models f hf _ _).mp h)
  refine ⟨D,t,?_,bad,?_⟩
  · intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hv
    simp [cycleWord]
  · obtain ⟨F,hF,badF,ho,hmin⟩ := omega_spec D t bad
    rw [ho]
    apply ENat.natCast_le_natCast.mpr
    by_contra hh
    have hc : F.card ≤ n := by omega
    obtain ⟨E,hE,he,hcard⟩ := image_subset f hf (cycleDomain m) F hF
    have model := cycle_local n E hE (by omega)
    apply badF
    rw [← he]
    exact (image_models f hf E _).mpr model

/-- An arbitrary partial labeling is extended only to write a total function. -/
noncomputable def completeLabel {A : Type} (D : Finset (List A))
    (t : {w // w ∈ D} → Bool) : List A → Bool := by
  classical
  exact fun w => if h : w ∈ D then t ⟨w,h⟩ else false

private theorem partial_native {A : Type} (D : Finset (List A))
    (t : {w // w ∈ D} → Bool) :
    Realizable D (completeLabel D t) ↔
      ∃ (S : Type) (_ : Fintype S) (M : DFAO A Bool S),
        Fintype.card S ≤ 2 ∧ CorrectOnFamily M Subtype.val t := by
  classical
  constructor
  · rintro ⟨S,inst,M,hS,hM⟩
    exact ⟨S,inst,M,hS,fun w => by simpa [completeLabel, w.property] using hM w.val w.property⟩
  · rintro ⟨S,inst,M,hS,hM⟩
    exact ⟨S,inst,M,hS,fun w hw => by simpa [completeLabel,hw] using hM ⟨w,hw⟩⟩

private theorem range_bound (k : ℕ) : ∀ n ∈ obstructionRange k, n ≤ 16*(k + 1) := by
  rintro n ⟨D,t,hlen,bad,heq⟩
  obtain ⟨E,hE,badE,ho,hmin⟩ := omega_spec D t bad
  obtain ⟨F,hF,badF,hcard⟩ := upper_core k D t hlen bad
  have hn : E.card = n := ENat.natCast_inj.mp (ho.symm.trans heq)
  have hh := hmin F hF badF
  omega

/-- The exact short-word width is a finite attained maximum with linear bounds.
The minimum law and partial-label interpretation refer to original words. -/
theorem two_state_certificate_width (k : ℕ) (hk : 6 ≤ k) :
    (∀ (D : Finset (List (Fin k))) (t : {w // w ∈ D} → Bool),
      Realizable D (completeLabel D t) ↔
      ∃ (S : Type) (_ : Fintype S) (M : DFAO (Fin k) Bool S),
        Fintype.card S ≤ 2 ∧ CorrectOnFamily M Subtype.val t) ∧
    (∀ (D : Finset (List (Fin k))) (t : List (Fin k) → Bool),
      (Realizable D t → omega2 D t = ⊤ ∧
        ∀ E : Finset (List (Fin k)), E ⊆ D → Realizable E t) ∧
      (¬ Realizable D t → ∃ E : Finset (List (Fin k)), E ⊆ D ∧ ¬ Realizable E t ∧
        omega2 D t = (E.card : ℕ∞) ∧
        ∀ F : Finset (List (Fin k)), F ⊆ D → ¬ Realizable F t → E.card ≤ F.card)) ∧
    {w : List (Fin k) | w.length ≤ 2}.Finite ∧
    (obstructionRange k).Finite ∧ (obstructionRange k).Nonempty ∧
    ∃ h : ℕ, IsGreatest (obstructionRange k) h ∧ H2 k = (h : ℕ∞) ∧
      (k-2)/4 ≤ h ∧ h ≤ 16*(k + 1) := by
  classical
  refine ⟨partial_native, ?_, List.finite_length_le (Fin k) 2, ?_, ?_⟩
  · intro D t
    exact ⟨fun h => ⟨by simp [omega2,h], fun E hE => restrict h hE⟩, omega_spec D t⟩
  · exact (Set.finite_Iic (16*(k + 1))).subset (range_bound k)
  · obtain ⟨D,t,hlen,bad,hlow⟩ := lower_sample k hk
    obtain ⟨E,hE,badE,ho,hmin⟩ := omega_spec D t bad
    have he : E.card ∈ obstructionRange k := ⟨D,t,hlen,bad,ho⟩
    have nonempty : (obstructionRange k).Nonempty := ⟨E.card,he⟩
    refine ⟨nonempty,?_⟩
    have finite : (obstructionRange k).Finite :=
      (Set.finite_Iic (16*(k + 1))).subset (range_bound k)
    let S := finite.toFinset
    have hS : S.Nonempty := by simpa [S] using nonempty
    let h := S.max' hS
    have greatest : IsGreatest (obstructionRange k) h := by
      simpa [S,h] using S.isGreatest_max' hS
    have hH : H2 k = (h : ℕ∞) := by
      apply le_antisymm
      · apply sSup_le
        rintro x ⟨F,u,hshort,hbad,hx⟩
        obtain ⟨G,hG,badG,hminG,_⟩ := omega_spec F u hbad
        have hmem : G.card ∈ obstructionRange k := ⟨F,u,hshort,hbad,hminG⟩
        rw [← hx, hminG]
        exact ENat.natCast_le_natCast.mpr (greatest.2 hmem)
      · obtain ⟨F,u,hshort,hbad,hx⟩ := greatest.1
        exact le_sSup ⟨F,u,hshort,hbad,hx⟩
    refine ⟨h,greatest,hH,?_,range_bound k h greatest.1⟩
    have hminmax := greatest.2 he
    rw [ho] at hlow
    have hle := ENat.natCast_le_natCast.mp hlow
    omega

#print axioms two_state_certificate_width

end D5.S0.Automata.TwoStateCertificateWidth
