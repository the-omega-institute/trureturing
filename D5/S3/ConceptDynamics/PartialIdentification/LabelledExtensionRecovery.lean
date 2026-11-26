/- GID: D5/S3/ConceptDynamics/PartialIdentification/LabelledExtensionRecovery
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/LabelledExtensionRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite and countable past-finite histories have exact chain-fiber label recovery. -/

import D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
import Mathlib.Order.OrderIsoNat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Label recovery for finite induced extensions and complete countable past-finite histories. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.LabelledExtensionRecovery

open EnabledPathSwapConnectivity

universe u v

variable {E : Type u} [PartialOrder E] {A : Type v}

private theorem recover (label : E → A) (l m : List E)
    (hl : l.Pairwise (fun a b => ¬ b ≤ a))
    (hm : m.Pairwise (fun a b => ¬ b ≤ a)) (hp : l.Perm m)
    (hc : ∀ a ∈ l, ∀ b ∈ l, label a = label b → a ≤ b ∨ b ≤ a)
    (hw : l.map label = m.map label) : l = m := by
  induction l generalizing m with
  | nil => exact (List.perm_nil.mp hp.symm).symm
  | cons a t ih =>
    cases m with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hw
    | cons b s =>
      have hablabel : label a = label b := (List.cons.inj hw).1
      have hb : b ∈ a :: t := hp.mem_iff.mpr (List.mem_cons_self ..)
      have ha : a ∈ b :: s := hp.mem_iff.mp (List.mem_cons_self ..)
      have hab : a = b := by
        by_contra hne
        have hbt : b ∈ t := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
        have has : a ∈ s := (List.mem_cons.mp ha).resolve_left hne
        rcases hc a (List.mem_cons_self ..) b hb hablabel with h | h
        · exact (List.pairwise_cons.mp hm).1 a has h
        · exact (List.pairwise_cons.mp hl).1 b hbt h
      subst b
      congr 1
      exact ih s (List.pairwise_cons.mp hl).2 (List.pairwise_cons.mp hm).2
        (List.Perm.cons_inv hp)
        (fun x hx y hy => hc x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
        (List.cons.inj hw).2

private theorem extension_map_iff (F : Finset E) (l : List {e // e ∈ F}) :
    ExtensionList (∅ : Set {e // e ∈ F}) Set.univ l ↔
      ExtensionList (∅ : Set E) (F : Set E) (l.map Subtype.val) := by
  classical
  simp only [ExtensionList, Set.mem_empty_iff_false, not_false_eq_true, and_true,
    Set.mem_univ, iff_true]
  constructor
  · rintro ⟨hn, he, hp⟩
    refine ⟨hn.map Subtype.val_injective, ?_, ?_⟩
    · intro e
      constructor
      · intro h
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp h
        exact x.property
      · intro h
        exact List.mem_map.mpr ⟨⟨e, h⟩, he _, rfl⟩
    · exact List.pairwise_map.mpr hp
  · rintro ⟨hn, he, hp⟩
    refine ⟨List.Nodup.of_map Subtype.val hn, ?_, List.pairwise_map.mp hp⟩
    intro e
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp ((he e.val).mpr e.property)
    exact (Subtype.ext hxe) ▸ hx

private theorem lift_extension (F : Finset E) (l : List E)
    (hl : ExtensionList (∅ : Set E) (F : Set E) l) :
    ∃ t : List {e // e ∈ F},
      ExtensionList (∅ : Set {e // e ∈ F}) Set.univ t ∧ t.map Subtype.val = l := by
  let t : List {e // e ∈ F} := l.attach.map fun x => ⟨x.val, ((hl.2.1 x.val).mp x.property).1⟩
  have ht : t.map Subtype.val = l := by simp [t, List.map_map]
  exact ⟨t, (extension_map_iff F t).mpr (ht.symm ▸ hl), ht⟩

private theorem extension_append {I K J : Set E} (hK : IsLowerSet K)
    (hIK : I ⊆ K) (hKJ : K ⊆ J) {p q : List E}
    (hp : ExtensionList I K p) (hq : ExtensionList K J q) :
    ExtensionList I J (p ++ q) := by
  refine ⟨List.nodup_append.mpr ⟨hp.1, hq.1, ?_⟩, ?_, ?_⟩
  · intro x hx y hy hxy
    subst y
    exact ((hq.2.1 x).mp hy).2 ((hp.2.1 x).mp hx).1
  · intro x
    constructor
    · intro hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨hxK, hxI⟩ := (hp.2.1 x).mp hx
        exact ⟨hKJ hxK, hxI⟩
      · obtain ⟨hxJ, hxK⟩ := (hq.2.1 x).mp hx
        exact ⟨hxJ, fun hxI => hxK (hIK hxI)⟩
    · rintro ⟨hxJ, hxI⟩
      by_cases hxK : x ∈ K
      · exact List.mem_append_left _ ((hp.2.1 x).mpr ⟨hxK, hxI⟩)
      · exact List.mem_append_right _ ((hq.2.1 x).mpr ⟨hxJ, hxK⟩)
  · exact List.pairwise_append.mpr ⟨hp.2.2, hq.2.2, fun x hx y hy h =>
      ((hq.2.1 y).mp hy).2 (hK h ((hp.2.1 x).mp hx).1)⟩

private theorem incomparable_collision [Finite E] (a b : E)
    (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) :
    ∃ p s : List E,
      ExtensionList (∅ : Set E) Set.univ (p ++ a :: b :: s) ∧
      ExtensionList (∅ : Set E) Set.univ (p ++ b :: a :: s) := by
  classical
  let K : Set E := {x | x < a ∨ x < b}
  have hK : IsLowerSet K := by
    intro x y hyx hx
    exact hx.elim (fun h => Or.inl (lt_of_le_of_lt hyx h))
      (fun h => Or.inr (lt_of_le_of_lt hyx h))
  have ha : a ∉ K := by
    rintro (h | h)
    · exact lt_irrefl _ h
    · exact hab h.le
  have hb : b ∉ K := by
    rintro (h | h)
    · exact hba h.le
    · exact lt_irrefl _ h
  have insert_lower : ∀ x ∈ ({a, b} : Set E), IsLowerSet (insert x K) := by
    intro x hx y z hzy hy
    rcases hy with hy | hy
    · subst y
      by_cases hzx : z = x
      · exact Or.inl hzx
      · right
        rcases hx with rfl | hx
        · exact Or.inl (lt_of_le_of_ne hzy hzx)
        · have hxb : x = b := by simpa using hx
          subst x
          exact Or.inr (lt_of_le_of_ne hzy hzx)
    · exact Or.inr (hK hzy hy)
  have hKab : IsLowerSet (insert a (insert b K)) := by
    intro x y hyx hx
    rcases hx with hx | hx
    · subst x
      by_cases hya : y = a
      · exact Or.inl hya
      · exact Or.inr (Or.inr (Or.inl (lt_of_le_of_ne hyx hya)))
    · exact Or.inr (insert_lower b (by simp) hyx hx)
  obtain ⟨p, hp⟩ := (EnabledPathSwapConnectivity.result (∅ : Set E) K
    (by simp [IsLowerSet]) hK (Set.empty_subset _)).2.1
  have hpe := (EnabledPathSwapConnectivity.result (∅ : Set E) K
    (by simp [IsLowerSet]) hK (Set.empty_subset _)).1 p |>.mp hp
  obtain ⟨s, hs⟩ := (EnabledPathSwapConnectivity.result (insert a (insert b K)) Set.univ
    hKab (by simp [IsLowerSet]) (Set.subset_univ _)).2.1
  have hse := (EnabledPathSwapConnectivity.result (insert a (insert b K)) Set.univ
    hKab (by simp [IsLowerSet]) (Set.subset_univ _)).1 s |>.mp hs
  have habne : a ≠ b := fun h => hab (h ▸ le_rfl)
  have pair_ab : ExtensionList K (insert a (insert b K)) [a, b] := by
    refine ⟨by simp [habne], ?_, by simp [hba]⟩
    intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, ha⟩
      · exact ⟨Or.inr (Or.inl rfl), hb⟩
    · rintro ⟨hx, hxK⟩
      exact hx.elim Or.inl (fun h => h.elim Or.inr (fun h => (hxK h).elim))
  have pair_ba : ExtensionList K (insert a (insert b K)) [b, a] := by
    refine ⟨by simp [Ne.symm habne], ?_, by simp [hab]⟩
    intro x
    simpa only [List.mem_cons, List.not_mem_nil, or_false, false_or, or_comm] using pair_ab.2.1 x
  have hsub : K ⊆ insert a (insert b K) := fun _ h => Or.inr (Or.inr h)
  have left := extension_append hK (Set.empty_subset _) hsub hpe pair_ab
  have right := extension_append hK (Set.empty_subset _) hsub hpe pair_ba
  refine ⟨p, s, ?_, ?_⟩
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      extension_append hKab (Set.empty_subset _) (Set.subset_univ _) left hse
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      extension_append hKab (Set.empty_subset _) (Set.subset_univ _) right hse

/-- Label observation distinguishes all complete induced-order extensions exactly
when every equal-label fiber in the finite support is a chain. -/
theorem result (F : Finset E) (label : E → A) :
    (∀ a ∈ F, ∀ b ∈ F, label a = label b → a ≤ b ∨ b ≤ a) ↔
    (∀ l m : List E,
      ExtensionList (∅ : Set E) (F : Set E) l →
      ExtensionList (∅ : Set E) (F : Set E) m →
      l.map label = m.map label → l = m) := by
  classical
  constructor
  · intro hc l m hl hm hw
    obtain ⟨t, ht, htl⟩ := lift_extension F l hl
    obtain ⟨s, hs, hsm⟩ := lift_extension F m hm
    have hp : t.Perm s := (List.perm_ext_iff_of_nodup ht.1 hs.1).mpr
      (fun e => (ht.2.1 e).trans (hs.2.1 e).symm)
    have hts : t = s := recover (fun e => label e.val) t s ht.2.2 hs.2.2 hp
      (fun a _ b _ => hc a.val a.property b.val b.property)
      (by simpa only [← htl, ← hsm, List.map_map, Function.comp_def] using hw)
    exact htl.symm.trans ((congrArg (List.map Subtype.val) hts).trans hsm)
  · intro hi a ha b hb hablabel
    by_contra hc
    have hab : ¬ a ≤ b := fun h => hc (Or.inl h)
    have hba : ¬ b ≤ a := fun h => hc (Or.inr h)
    let x : {e // e ∈ F} := ⟨a, ha⟩
    let y : {e // e ∈ F} := ⟨b, hb⟩
    obtain ⟨p, s, hl, hm⟩ := incomparable_collision x y hab hba
    have heq := hi _ _ ((extension_map_iff F _).mp hl)
      ((extension_map_iff F _).mp hm) (by simp [hablabel, x, y])
    have eqsub : p ++ x :: y :: s = p ++ y :: x :: s :=
      (List.map_injective_iff.mpr Subtype.val_injective) heq
    have hxy : x = y := (List.cons.inj (List.append_cancel_left eqsub)).1
    exact hab (le_of_eq (congrArg Subtype.val hxy))

/-- A complete enumeration of the events compatible with their partial order. -/
def History (E : Type u) [PartialOrder E] :=
  {e : ℕ ≃ E // ∀ i j : ℕ, i < j → ¬ e j ≤ e i}

private theorem history_exists [Countable E] [Infinite E]
    (hpast : ∀ x : E, (Set.Iio x).Finite) : Nonempty (History E) := by
  classical
  obtain ⟨code, hcode⟩ := exists_injective_nat E
  have hc : ∀ x : E, (Set.Iic x).Finite := by
    intro x
    apply ((hpast x).insert x).subset
    intro y hy
    rcases eq_or_lt_of_le hy with h | h
    · exact Or.inl h
    · exact Or.inr h
  let past (x : E) : Finset E := (hc x).toFinset
  have mem_past (x y : E) : y ∈ past x ↔ y ≤ x := by simp [past]
  let rank (x : E) : ℕ := ∑ y ∈ past x, (code y + 1)
  have code_le (x : E) : code x ≤ rank x := by
    exact le_trans (Nat.le_succ _)
      (Finset.single_le_sum (f := fun y => code y + 1) (fun _ _ => Nat.zero_le _)
        ((mem_past x x).mpr le_rfl))
  have rank_lt {x y : E} (hxy : x < y) : rank x < rank y := by
    have hsub : insert y (past x) ⊆ past y := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact (mem_past _ _).mpr le_rfl
      · exact (mem_past y z).mpr (((mem_past x z).mp hz).trans hxy.le)
    have hy : y ∉ past x := by simpa [mem_past] using not_le_of_gt hxy
    have hs := Finset.sum_le_sum_of_subset (f := fun z => code z + 1) hsub
    rw [Finset.sum_insert hy] at hs
    dsimp [rank]
    exact lt_of_lt_of_le (Nat.lt_add_of_pos_left (Nat.succ_pos _)) hs
  let key (x : E) : ℕ := Nat.pair (rank x) (code x)
  have hkey : Function.Injective key := by
    intro x y h
    exact hcode (Nat.pair_eq_pair.mp h).2
  have key_lt {x y : E} (hxy : x < y) : key x < key y := by
    have hr := rank_lt hxy
    calc
      key x < (rank x + 1) ^ 2 := by
        simpa only [key, max_eq_left (code_le x)] using
          Nat.pair_lt_max_add_one_sq (rank x) (code x)
      _ ≤ rank y ^ 2 := Nat.pow_le_pow_left (Nat.succ_le_of_lt hr) 2
      _ ≤ key y := le_trans (Nat.le_add_right _ _)
        (by simpa only [key, max_eq_left (code_le y)] using
          Nat.max_sq_add_min_le_pair (rank y) (code y))
  let r := Equiv.ofInjective key hkey
  let : Infinite (Set.range key) := Infinite.of_injective r r.injective
  let t := Nat.Subtype.orderIsoOfNat (Set.range key)
  let e : ℕ ≃ E := t.toEquiv.trans r.symm
  have he (n : ℕ) : key (e n) = (t n).val :=
    Equiv.apply_ofInjective_symm hkey (t n)
  refine ⟨⟨e, ?_⟩⟩
  intro i j hij hji
  have hne : e j ≠ e i := fun h => (ne_of_gt hij) (e.injective h)
  have hlt := key_lt (lt_of_le_of_ne hji hne)
  rw [he, he] at hlt
  exact (not_lt_of_gt (t.strictMono hij)) hlt

private theorem history_recover (label : E → A)
    (hc : ∀ a b : E, label a = label b → a ≤ b ∨ b ≤ a)
    (s t : History E) (hw : (fun n => label (s.val n)) = fun n => label (t.val n)) :
    s = t := by
  have later : ∀ (s t : History E) (n : ℕ),
      (∀ i < n, s.val i = t.val i) → s.val n ≠ t.val n → n < t.val.symm (s.val n) := by
    intro s t n hpre hne
    by_contra hn
    have hj : t.val.symm (s.val n) ≤ n := Nat.le_of_not_gt hn
    rcases lt_or_eq_of_le hj with hj | hj
    · have heq := hpre _ hj
      have hsn : s.val (t.val.symm (s.val n)) = s.val n := by simpa using heq
      exact (ne_of_lt hj) (s.val.injective hsn)
    · apply hne
      have := t.val.apply_symm_apply (s.val n)
      rw [hj] at this
      exact this.symm
  apply Subtype.ext
  apply Equiv.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_contra hne
    have hst := later s t n ih hne
    have hts := later t s n (fun i hi => (ih i hi).symm) (Ne.symm hne)
    rcases hc (s.val n) (t.val n) (congrFun hw n) with h | h
    · exact t.property n _ hst (by simpa using h)
    · exact s.property n _ hts (by simpa using h)

private theorem history_append (F : Finset E) (hF : IsLowerSet (F : Set E))
    (l : List E) (hl : ExtensionList (∅ : Set E) (F : Set E) l)
    (t : History {x : E // x ∉ F}) :
    ∃ h : History E, (∀ i (hi : i < l.length), h.val i = l[i]) ∧
      (∀ n, h.val (l.length + n) = (t.val n).val) := by
  classical
  let f (n : ℕ) : E := if hn : n < l.length then l[n] else (t.val (n - l.length)).val
  have head (i : ℕ) (hi : i < l.length) : f i = l[i] := dite_eq_left hi
  have tail (n : ℕ) : f (l.length + n) = (t.val n).val := by simp [f]
  have mem_head (i : ℕ) (hi : i < l.length) : f i ∈ F := by
    rw [head i hi]
    exact ((hl.2.1 _).mp (List.getElem_mem hi)).1
  have not_mem_tail (i : ℕ) (hi : ¬ i < l.length) : f i ∉ F := by
    simpa only [f, dite_eq_right hi] using (t.val (i - l.length)).property
  have hinj : Function.Injective f := by
    intro i j hij
    by_cases hi : i < l.length <;> by_cases hj : j < l.length
    · rw [head i hi, head j hj] at hij
      exact hl.1.getElem_inj_iff.mp hij
    · exact ((not_mem_tail j hj) (hij ▸ mem_head i hi)).elim
    · exact ((not_mem_tail i hi) (hij.symm ▸ mem_head j hj)).elim
    · have ht : t.val (i - l.length) = t.val (j - l.length) :=
        Subtype.ext (by simpa only [f, dite_eq_right hi, dite_eq_right hj] using hij)
      have := t.val.injective ht
      omega
  have hsurj : Function.Surjective f := by
    intro x
    by_cases hx : x ∈ F
    · have hxl := (hl.2.1 x).mpr ⟨hx, by simp⟩
      obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxl
      exact ⟨i, (head i hi).trans hix⟩
    · obtain ⟨n, hn⟩ := t.val.surjective ⟨x, hx⟩
      exact ⟨l.length + n, (tail n).trans (congrArg Subtype.val hn)⟩
  let e : ℕ ≃ E := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have he : ∀ i j, i < j → ¬ e j ≤ e i := by
    intro i j hij hji
    change f j ≤ f i at hji
    by_cases hj : j < l.length
    · have hi : i < l.length := hij.trans hj
      rw [head i hi, head j hj] at hji
      exact (List.pairwise_iff_getElem.mp hl.2.2 i j hi hj hij) hji
    · by_cases hi : i < l.length
      · exact not_mem_tail j hj (hF hji (mem_head i hi))
      · have hij' : i - l.length < j - l.length := by omega
        apply t.property _ _ hij'
        change (t.val (j - l.length)).val ≤ (t.val (i - l.length)).val
        simpa only [f, dite_eq_right hi, dite_eq_right hj] using hji
  exact ⟨⟨e, he⟩, head, tail⟩

private theorem history_collision [Countable E] [Infinite E]
    (hpast : ∀ x : E, (Set.Iio x).Finite) (label : E → A)
    (a b : E) (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) (hlab : label a = label b) :
    ∃ s t : History E, s ≠ t ∧ (fun n => label (s.val n)) = fun n => label (t.val n) := by
  classical
  have hclosed (x : E) : (Set.Iic x).Finite := by
    apply ((hpast x).insert x).subset
    intro y hy
    exact (eq_or_lt_of_le hy).imp_right id
  let F : Finset E := ((hclosed a).union (hclosed b)).toFinset
  have memF (x : E) : x ∈ F ↔ x ≤ a ∨ x ≤ b := by simp [F]
  have hF : IsLowerSet (F : Set E) := by
    intro x y hyx hx
    exact (memF y).mpr (((memF x).mp hx).imp (hyx.trans ·) (hyx.trans ·))
  let x : {e // e ∈ F} := ⟨a, (memF a).mpr (Or.inl le_rfl)⟩
  let y : {e // e ∈ F} := ⟨b, (memF b).mpr (Or.inr le_rfl)⟩
  obtain ⟨p, q, hl, hm⟩ := incomparable_collision x y hab hba
  let l := (p ++ x :: y :: q).map Subtype.val
  let m := (p ++ y :: x :: q).map Subtype.val
  have hel : ExtensionList (∅ : Set E) (F : Set E) l := (extension_map_iff F _).mp hl
  have hem : ExtensionList (∅ : Set E) (F : Set E) m := (extension_map_iff F _).mp hm
  have hlen : l.length = m.length := by simp [l, m]
  have hw : l.map label = m.map label := by simp [l, m, List.map_append, hlab, x, y]
  let C := {z : E // z ∉ F}
  have hinfinite : Infinite C := Set.infinite_coe_iff.mpr (F.finite_toSet.infinite_compl)
  let : Infinite C := hinfinite
  have hcpast : ∀ z : C, (Set.Iio z).Finite := by
    intro z
    exact (hpast z.val).preimage (fun _ _ _ _ h => Subtype.val_injective h)
  obtain ⟨r⟩ := history_exists hcpast
  obtain ⟨s, hshead, hstail⟩ := history_append F hF l hel r
  obtain ⟨t, hthead, httail⟩ := history_append F hF m hem r
  refine ⟨s, t, ?_, ?_⟩
  · intro heq
    have hidxl : p.length < l.length := by simp [l]
    have hidxm : p.length < m.length := by omega
    have h := (hshead p.length hidxl).symm.trans
      ((congrArg (fun h : History E => h.val p.length) heq).trans (hthead p.length hidxm))
    have he : a = b := by simpa [l, m, x, y] using h
    exact hab (le_of_eq he)
  · funext n
    by_cases hn : n < l.length
    · have hnm : n < m.length := by omega
      rw [hshead n hn, hthead n hnm]
      have h := congrArg (fun z : List A => z[n]?) hw
      simpa [List.getElem?_eq_getElem, hn, hnm] using h
    · have hnm : ¬ n < m.length := by omega
      have hn' : n = l.length + (n - l.length) := by omega
      have hn'' : n = m.length + (n - l.length) := by omega
      exact congrArg label (((congrArg s.val hn').trans (hstail _)).trans
        (((congrArg t.val hn'').trans (httail _)).symm))

/-- Every countably infinite past-finite partial order has a complete natural
history. Labels recover all such histories exactly when their fibers are chains. -/
theorem infinite_result [Countable E] [Infinite E]
    (hpast : ∀ x : E, (Set.Iio x).Finite) (label : E → A) :
    Nonempty (History E) ∧
      ((∀ a b : E, label a = label b → a ≤ b ∨ b ≤ a) ↔
        Function.Injective (fun e : History E => fun n : ℕ => label (e.val n))) := by
  refine ⟨history_exists hpast, ?_⟩
  constructor
  · intro hc s t hw
    exact history_recover label hc s t hw
  · intro hi a b hlab
    by_contra hc
    have hab : ¬ a ≤ b := fun h => hc (Or.inl h)
    have hba : ¬ b ≤ a := fun h => hc (Or.inr h)
    obtain ⟨s, t, hne, hw⟩ := history_collision hpast label a b hab hba hlab
    exact hne (hi hw)

#print axioms infinite_result

#print axioms result

end D5.S3.ConceptDynamics.PartialIdentification.LabelledExtensionRecovery
