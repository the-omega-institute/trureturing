/- GID: D5/S1/Recurrence/Invariants/PopovUrnNormalization
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/PopovUrnNormalization
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fintype]
   utility: none
   digest: First-use words classify chronological urn histories under arbitrary relabelings. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fintype

/-!
# First-use normalization of chronological urn histories

Urn and slot permutations fix every marble position. A first-use word
records the unique chronological rank of each occupied compartment.
-/

namespace PopovUrnShift

set_option autoImplicit false

/-! ## The raw histories and their first-use normalization -/

/-- The distinct values of a finite chronological assignment. -/
def used {t : ℕ} {α : Type} [DecidableEq α] (x : Fin t → α) : Finset α :=
  Finset.univ.image x

theorem mem_used {t : ℕ} {α : Type} [DecidableEq α] {x : Fin t → α} {a : α} :
    a ∈ used x ↔ ∃ i, x i = a := by
  simp [used]

@[simp] private theorem used_zero {α : Type} [DecidableEq α] (x : Fin 0 → α) :
    used x = ∅ := by
  simp [used]

theorem used_init {t : ℕ} {α : Type} [DecidableEq α] (x : Fin (t + 1) → α) :
    used x = insert (x (Fin.last t)) (used (Fin.init x)) := by
  ext a
  simp only [mem_used, Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    exact Fin.lastCases (motive := fun i => x i = x (Fin.last t) ∨ ∃ j, Fin.init x j = x i)
      (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last t, rfl⟩
    · exact ⟨i.castSucc, rfl⟩

theorem used_card_le {t : ℕ} {α : Type} [DecidableEq α] (x : Fin t → α) :
    (used x).card ≤ t := by
  simpa [used] using Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := x)

abbrev Address (A m : ℕ) := Fin A × Fin m

def Full {A m : ℕ} (s : Finset (Address A m)) (u : Fin A) : Prop :=
  ∀ c : Fin m, (u, c) ∈ s

def Started {A m : ℕ} (s : Finset (Address A m)) (u : Fin A) : Prop :=
  ∃ c : Fin m, (u, c) ∈ s

/-- A repeat requires a full urn and opening an urn requires every started urn to be full. -/
def RawMove {A m : ℕ} (s : Finset (Address A m)) (a : Address A m) : Prop :=
  (a ∈ s → Full s a.1) ∧
    (¬ Started s a.1 → ∀ u, Started s u → Full s u)

/-- The two raw urn rules tested against the actual preceding occupied sets. -/
def RawLegal {A m : ℕ} : {t : ℕ} → (Fin t → Address A m) → Prop
  | 0, _ => True
  | t + 1, x => RawLegal (Fin.init x) ∧ RawMove (used (Fin.init x)) (x (Fin.last t))

abbrev Raw (A m t : ℕ) := {x : Fin t → Address A m // RawLegal x}

/-- The old ranks available from a prefix with exactly `p` occupied compartments. -/
def threshold (m p : ℕ) : ℕ := m * (p / m)

/-- A fresh move introduces the next rank and an old move uses a compartment of a full urn. -/
def Move (m p a : ℕ) : Prop := a = p ∨ a < threshold m p

theorem threshold_le (m p : ℕ) : threshold m p ≤ p :=
  Nat.mul_div_le p m

/-- Canonical first-use words, given by their terminal rank and the legal moves of each prefix. -/
def Legal (m : ℕ) : {t : ℕ} → (Fin t → ℕ) → Prop
  | 0, _ => True
  | t + 1, x => Legal m (Fin.init x) ∧ Move m (used (Fin.init x)).card (x (Fin.last t))

abbrev Word (m t : ℕ) := {x : Fin t → ℕ // Legal m x}

theorem used_range {m t : ℕ} {x : Fin t → ℕ} (h : Legal m x) :
    used x = Finset.range (used x).card := by
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨hp, ha⟩ := h
    have hr := ih hp
    rw [used_init x]
    cases ha with
    | inl ha =>
      rw [ha]
      have hn : (used (Fin.init x)).card ∉ used (Fin.init x) := by
        intro hc
        have he : (used (Fin.init x)).card ∈ Finset.range (used (Fin.init x)).card :=
          (congrArg (fun s : Finset ℕ => (used (Fin.init x)).card ∈ s) hr).mp hc
        exact (Nat.lt_irrefl _) (Finset.mem_range.mp he)
      rw [Finset.card_insert_of_notMem hn]
      exact (congrArg (insert (used (Fin.init x)).card) hr).trans (by
        ext i
        simp only [Finset.mem_insert, Finset.mem_range]
        omega)
    | inr ha =>
      have hmem : x (Fin.last t) ∈ used (Fin.init x) := by
        exact hr.symm ▸ Finset.mem_range.mpr (ha.trans_le (threshold_le _ _))
      rw [Finset.insert_eq_of_mem hmem]
      exact hr

theorem word_rank_le {m t : ℕ} {x : Fin t → ℕ} (h : Legal m x) (i : Fin t) :
    x i ≤ i.val := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    refine Fin.lastCases (motive := fun j => x j ≤ j.val) ?_ (fun j => ih h.1 j) i
    have hb := used_card_le (Fin.init x)
    rcases h.2 with he | ho
    · exact he.trans_le hb
    · exact (ho.trans_le (threshold_le _ _)).le.trans hb

/-- The actual prefix restriction to the first `s` chronological marbles. -/
def restrictPrefix {t : ℕ} {α : Type} (x : Fin t → α) {s : ℕ} (hs : s ≤ t) : Fin s → α :=
  fun i => x (i.castLE hs)

theorem legal_prefix {m t s : ℕ} {x : Fin t → ℕ} (hx : Legal m x) (hs : s ≤ t) :
    Legal m (restrictPrefix x hs) := by
  induction t with
  | zero =>
    have : s = 0 := by omega
    subst s
    trivial
  | succ t ih =>
    by_cases e : s = t + 1
    · subst s
      exact hx
    · have hst : s ≤ t := by omega
      exact ih hx.1 hst

private theorem actual_word_prefix_interval {m t s : ℕ} {x : Fin t → ℕ}
    (hx : Legal m x) (hs : s ≤ t) :
    used (restrictPrefix x hs) = Finset.range (used (restrictPrefix x hs)).card :=
  used_range (legal_prefix hx hs)

/-- An arbitrary urn permutation and an arbitrary slot permutation in each original urn. -/
structure Relabel (A m : ℕ) where
  urn : Equiv.Perm (Fin A)
  slot : Fin A → Equiv.Perm (Fin m)

namespace Relabel

def apply {A m : ℕ} (e : Relabel A m) (a : Address A m) : Address A m :=
  (e.urn a.1, e.slot a.1 a.2)

def refl (A m : ℕ) : Relabel A m :=
  ⟨Equiv.refl _, fun _ => Equiv.refl _⟩

def symm {A m : ℕ} (e : Relabel A m) : Relabel A m :=
  ⟨e.urn.symm, fun u => (e.slot (e.urn.symm u)).symm⟩

def trans {A m : ℕ} (e f : Relabel A m) : Relabel A m :=
  ⟨e.urn.trans f.urn, fun u => (e.slot u).trans (f.slot (e.urn u))⟩

@[simp] private theorem refl_apply {A m : ℕ} (a : Address A m) : (refl A m).apply a = a := by
  cases a
  rfl

@[simp] private theorem symm_apply {A m : ℕ} (e : Relabel A m) (a : Address A m) :
    e.symm.apply (e.apply a) = a := by
  rcases a with ⟨u, c⟩
  simp [symm, apply]

@[simp] private theorem apply_symm {A m : ℕ} (e : Relabel A m) (a : Address A m) :
    e.apply (e.symm.apply a) = a := by
  rcases a with ⟨u, c⟩
  simp [symm, apply]

@[simp] private theorem trans_apply {A m : ℕ} (e f : Relabel A m) (a : Address A m) :
    (e.trans f).apply a = f.apply (e.apply a) := rfl

private theorem injective {A m : ℕ} (e : Relabel A m) : Function.Injective e.apply :=
  Function.LeftInverse.injective (symm_apply e)

end Relabel

/-- Orbit under the raw source relabelings, with every marble position fixed. -/
def Orbit {A m t : ℕ} (x y : Fin t → Address A m) : Prop :=
  ∃ e : Relabel A m, ∀ i, e.apply (x i) = y i

private theorem orbit_equivalence {A m t : ℕ} :
    Equivalence (Orbit (A := A) (m := m) (t := t)) where
  refl x := ⟨Relabel.refl A m, fun i => Relabel.refl_apply (x i)⟩
  symm := by
    rintro x y ⟨e, he⟩
    exact ⟨e.symm, fun i => by rw [← he, Relabel.symm_apply]⟩
  trans := by
    rintro x y z ⟨e, he⟩ ⟨f, hf⟩
    exact ⟨e.trans f, fun i => by rw [Relabel.trans_apply, he, hf]⟩

def orbitSetoid (A m t : ℕ) : Setoid (Raw A m t) :=
  ⟨fun x y => Orbit x.val y.val, ⟨fun x => orbit_equivalence.refl x.val,
    fun h => orbit_equivalence.symm h, fun h₁ h₂ => orbit_equivalence.trans h₁ h₂⟩⟩

/-- The literal finite orbit quotient from the source. -/
def Arrangements (A m t : ℕ) := Quotient (orbitSetoid A m t)


private theorem used_comp {t : ℕ} {α β : Type} [DecidableEq α] [DecidableEq β]
    (x : Fin t → α) (f : α → β) : used (f ∘ x) = (used x).image f := by
  simp [used, Finset.image_image, Function.comp_def]

/-- Numeric code of an address in the canonical labeling. -/
def code {A m : ℕ} (a : Address A m) : ℕ := m * a.1.val + a.2.val

private theorem code_div {A m : ℕ} (hm : 0 < m) (a : Address A m) : code a / m = a.1.val := by
  simp [code, Nat.mul_add_div hm, Nat.div_eq_of_lt a.2.isLt]

private theorem code_mod {A m : ℕ} (a : Address A m) : code a % m = a.2.val := by
  simp [code, Nat.mod_eq_of_lt a.2.isLt]

private theorem code_injective {A m : ℕ} (hm : 0 < m) :
    Function.Injective (code : Address A m → ℕ) := by
  intro a b h
  apply Prod.ext
  · apply Fin.ext
    rw [← code_div hm a, ← code_div hm b, h]
  · apply Fin.ext
    rw [← code_mod a, ← code_mod b, h]

def decode {A m : ℕ} (hm : 0 < m) (a : ℕ) (ha : a / m < A) : Address A m :=
  (⟨a / m, ha⟩, ⟨a % m, Nat.mod_lt _ hm⟩)

@[simp] private theorem code_decode {A m a : ℕ} (hm : 0 < m) (ha : a / m < A) :
    code (decode hm a ha) = a :=
  Nat.div_add_mod a m

/-- Replay uses quotient and remainder at every chronological position. -/
def replay {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (w : Word m t) :
    Fin t → Address A m :=
  fun i => decode hm (w.val i) (by
    have hi : w.val i < A := ((word_rank_le w.property i).trans_lt i.isLt).trans_le ht
    exact (Nat.div_le_self _ _).trans_lt hi)

@[simp] private theorem code_replay {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (w : Word m t)
    (i : Fin t) : code (replay hm ht w i) = w.val i :=
  code_decode _ _

private theorem replay_init {A m t : ℕ} (hm : 0 < m) (ht : t + 1 ≤ A)
    (w : Word m (t + 1)) :
    Fin.init (replay hm ht w) =
      replay hm (Nat.le_of_succ_le ht) ⟨Fin.init w.val, w.property.1⟩ :=
  rfl

private theorem replay_codes {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (w : Word m t) :
    (used (replay hm ht w)).image code = used w.val := by
  rw [← used_comp]
  congr 1
  funext i
  exact code_replay hm ht w i

private theorem mem_layout {A m p : ℕ} {s : Finset (Address A m)} (hm : 0 < m)
    (hs : s.image code = Finset.range p) (a : Address A m) :
    a ∈ s ↔ code a < p := by
  rw [← Finset.mem_range, ← hs, Finset.mem_image]
  exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, h⟩ => code_injective hm h ▸ hb⟩

private theorem full_layout {A m p : ℕ} {s : Finset (Address A m)} (hm : 0 < m)
    (hs : s.image code = Finset.range p) (u : Fin A) :
    Full s u ↔ u.val < p / m := by
  have hmul := Nat.mul_succ m u.val
  rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le hm, Nat.mul_comm (u.val + 1) m, hmul]
  constructor
  · intro hf
    have h := (mem_layout hm hs (u, ⟨m - 1, by omega⟩)).1 (hf ⟨m - 1, by omega⟩)
    change m * u.val + (m - 1) < p at h
    omega
  · intro h c
    apply (mem_layout hm hs (u,c)).2
    change m * u.val + c.val < p
    have hc := c.isLt
    omega

private theorem started_layout {A m p : ℕ} {s : Finset (Address A m)} (hm : 0 < m)
    (hs : s.image code = Finset.range p) (u : Fin A) :
    Started s u ↔ m * u.val < p := by
  constructor
  · intro ⟨c, hc⟩
    have h := (mem_layout hm hs (u,c)).1 hc
    exact (Nat.le_add_right _ _).trans_lt h
  · intro h
    exact ⟨⟨0, hm⟩, (mem_layout hm hs _).2 (by simpa [code] using h)⟩

private theorem rawMove_of_move {A m p : ℕ} {s : Finset (Address A m)} (hm : 0 < m)
    (hs : s.image code = Finset.range p) (a : Address A m) (ha : Move m p (code a)) :
    RawMove s a := by
  rcases ha with hnew | hold
  · constructor
    · intro hb
      have hh := (mem_layout hm hs a).1 hb
      omega
    · intro hn u hu
      have hbase : m * a.1.val ≤ p := by
        rw [← hnew]
        exact Nat.le_add_right _ _
      have heq : m * a.1.val = p :=
        hbase.antisymm (Nat.le_of_not_gt (fun hh => hn ((started_layout hm hs _).2 hh)))
      have hlt := (started_layout hm hs u).1 hu
      rw [← heq, Nat.mul_lt_mul_left hm] at hlt
      apply (full_layout hm hs u).2
      simpa [← code_div hm a, hnew] using hlt
  · have hh : a.1.val < p / m := by
      rw [← code_div hm a, Nat.div_lt_iff_lt_mul hm, Nat.mul_comm]
      exact hold
    have hf := (full_layout hm hs a.1).2 hh
    exact ⟨fun _ => hf, fun hn => False.elim (hn ⟨a.2, hf _⟩)⟩

theorem replay_legal {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (w : Word m t) :
    RawLegal (replay hm ht w) := by
  induction t with
  | zero => trivial
  | succ t ih =>
    refine ⟨?_, ?_⟩
    · rw [replay_init]
      exact ih _ _
    · have hr : (used (Fin.init (replay hm ht w))).image code =
          Finset.range (used (Fin.init w.val)).card := by
        rw [replay_init, replay_codes]
        exact used_range w.property.1
      apply rawMove_of_move hm hr
      rw [code_replay]
      exact w.property.2

/-- Relabeling an occupied set transports both raw move conditions. -/
private theorem rawMove_image {A m : ℕ} (e : Relabel A m) (s : Finset (Address A m))
    (a : Address A m) : RawMove (s.image e.apply) (e.apply a) ↔ RawMove s a := by
  have hmem (b : Address A m) : e.apply b ∈ s.image e.apply ↔ b ∈ s :=
    ⟨fun h => by
      obtain ⟨c,hc,hcb⟩ := Finset.mem_image.mp h
      exact e.injective hcb ▸ hc, Finset.mem_image_of_mem _⟩
  have hfull (u : Fin A) : Full (s.image e.apply) (e.urn u) ↔ Full s u := by
    constructor
    · intro h c
      exact (hmem (u,c)).1 (h (e.slot u c))
    · intro h c
      obtain ⟨d, rfl⟩ := (e.slot u).surjective c
      exact (hmem (u,d)).2 (h d)
  have hstarted (u : Fin A) : Started (s.image e.apply) (e.urn u) ↔ Started s u := by
    constructor
    · intro ⟨c,hc⟩
      obtain ⟨d, rfl⟩ := (e.slot u).surjective c
      exact ⟨d, (hmem (u,d)).1 hc⟩
    · intro ⟨d,hd⟩
      exact ⟨e.slot u d, (hmem (u,d)).2 hd⟩
  change (e.apply a ∈ _ → Full _ (e.urn a.1)) ∧
      (¬ Started _ (e.urn a.1) → _) ↔ _
  simp only [RawMove, hmem, hfull, hstarted]
  constructor
  · intro ⟨h, h'⟩
    exact ⟨h, fun hn u hu => (hfull u).1 (h' hn (e.urn u) ((hstarted u).2 hu))⟩
  · intro ⟨h, h'⟩
    refine ⟨h, fun hn u hu => ?_⟩
    obtain ⟨v, rfl⟩ := e.urn.surjective u
    exact (hfull v).2 (h' hn v ((hstarted v).1 hu))


/-- A fresh legal address can be aligned with the next canonical address by a
relabeling that fixes every occupied address. -/
private theorem align_fresh {A m p : ℕ} {s : Finset (Address A m)} (hm : 0 < m)
    (hs : s.image code = Finset.range p) (q a : Address A m)
    (hq : code q = p) (ha : a ∉ s) (hmv : RawMove s a) :
    ∃ e : Relabel A m, e.apply q = a ∧ ∀ b ∈ s, e.apply b = b := by
  classical
  have hq_out : q ∉ s := by
    rw [mem_layout hm hs, hq]
    exact Nat.lt_irrefl _
  by_cases hu : q.1 = a.1
  · let e : Relabel A m := ⟨Equiv.refl _, fun u =>
      if u = q.1 then Equiv.swap q.2 a.2 else Equiv.refl _⟩
    refine ⟨e, ?_, ?_⟩
    · exact Prod.ext hu (by simp [e, Relabel.apply])
    · intro b hb
      refine Prod.ext ?_ ?_
      · rfl
      · change (if b.1 = q.1 then Equiv.swap q.2 a.2 else Equiv.refl _) b.2 = b.2
        split
        next hbq =>
          apply Equiv.swap_apply_of_ne_of_ne
          · exact fun h => hq_out (Prod.ext hbq h ▸ hb)
          · exact fun h => ha (Prod.ext (hbq.trans hu) h ▸ hb)
        next => rfl
  · have hqdiv : q.1.val = p / m := by rw [← code_div hm q, hq]
    have h_anot : ¬ Started s a.1 := by
      intro ha_started
      have hale : a.1.val ≤ p / m := (Nat.le_div_iff_mul_le hm).2 (by
        simpa [Nat.mul_comm] using ((started_layout hm hs a.1).1 ha_started).le)
      have halt : a.1.val < p / m := lt_of_le_of_ne hale (by
        intro h
        exact hu (Fin.ext (hqdiv.trans h.symm)))
      exact ha ((full_layout hm hs a.1).2 halt a.2)
    have h_qnot : ¬ Started s q.1 := by
      intro h
      have hf := hmv.2 h_anot q.1 h
      exact hq_out (hf q.2)
    let e : Relabel A m := ⟨Equiv.swap q.1 a.1, fun u =>
      if u = q.1 then Equiv.swap q.2 a.2 else Equiv.refl _⟩
    refine ⟨e, ?_, ?_⟩
    · exact Prod.ext (Equiv.swap_apply_left _ _) (by simp [e, Relabel.apply])
    · intro b hb
      have h₁ : b.1 ≠ q.1 := fun h => h_qnot ⟨b.2, (show b = (_, b.2) from Prod.ext h rfl) ▸ hb⟩
      have h₂ : b.1 ≠ a.1 := fun h => h_anot ⟨b.2, (show b = (_, b.2) from Prod.ext h rfl) ▸ hb⟩
      exact Prod.ext (Equiv.swap_apply_of_ne_of_ne h₁ h₂)
        (by simp [e, Relabel.apply, h₁])

theorem legal_snoc {m t : ℕ} (w : Word m t) (a : ℕ)
    (h : Move m (used w.val).card a) : Legal m (Fin.snoc (α := fun _ => ℕ) w.val a) := by
  change Legal m (Fin.init (Fin.snoc (α := fun _ => ℕ) w.val a)) ∧
    Move m (used (Fin.init (Fin.snoc (α := fun _ => ℕ) w.val a))).card (Fin.snoc (α := fun _ => ℕ) w.val a (Fin.last t))
  rw [Fin.init_snoc, Fin.snoc_last]
  exact ⟨w.property, h⟩

/-- Every raw history admits a canonical first-use word in its orbit.
At each fresh placement the relabeling can be extended while fixing the prefix. -/
private theorem exists_word {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (x : Raw A m t) :
    ∃ w : Word m t, Orbit (replay hm ht w) x.val := by
  induction t with
  | zero =>
    exact ⟨⟨Fin.elim0, trivial⟩, Relabel.refl A m, fun i => Fin.elim0 i⟩
  | succ t ih =>
    let ht' : t ≤ A := Nat.le_of_succ_le ht
    obtain ⟨w, e, he⟩ := ih ht' ⟨Fin.init x.val, x.property.1⟩
    let s := used (replay hm ht' w)
    let p := (used w.val).card
    have hs : s.image code = Finset.range p := (replay_codes hm ht' w).trans (used_range w.property)
    let a := e.symm.apply (x.val (Fin.last t))
    have hae : e.apply a = x.val (Fin.last t) := e.apply_symm _
    have hprev : e.apply ∘ replay hm ht' w = Fin.init x.val := funext he
    have hmv : RawMove s a := (rawMove_image e s a).mp (by
      rw [← used_comp, hprev, hae]
      exact x.property.2)
    by_cases ha : a ∈ s
    · have hold : code a < threshold m p := by
        have hf := (full_layout hm hs a.1).1 (hmv.1 ha)
        rw [← code_div hm a, Nat.div_lt_iff_lt_mul hm, Nat.mul_comm] at hf
        exact hf
      let v : Word m (t + 1) := ⟨Fin.snoc (α := fun _ => ℕ) w.val (code a), legal_snoc w _ (.inr hold)⟩
      refine ⟨v, e, ?_⟩
      refine Fin.lastCases ?_ (fun j => ?_)
      · have hlast : replay hm ht v (Fin.last t) = a := code_injective hm (by
          rw [code_replay]
          exact Fin.snoc_last (α := fun _ => ℕ) _ _)
        rw [hlast, hae]
      · have hrep : replay hm ht v j.castSucc = replay hm ht' w j := code_injective hm (by
          rw [code_replay, code_replay]
          exact Fin.snoc_castSucc (α := fun _ => ℕ) _ _ _)
        rw [hrep]
        exact he j
    · have hp : p / m < A := (Nat.div_le_self _ _).trans_lt (by
        have hcard := used_card_le w.val
        dsimp [p]
        omega)
      let q := decode hm p hp
      obtain ⟨f, hf, hfix⟩ := align_fresh hm hs q a (code_decode hm hp) ha hmv
      let v : Word m (t + 1) := ⟨Fin.snoc (α := fun _ => ℕ) w.val p, legal_snoc w _ (.inl rfl)⟩
      refine ⟨v, f.trans e, ?_⟩
      refine Fin.lastCases ?_ (fun j => ?_)
      · have hlast : replay hm ht v (Fin.last t) = q := code_injective hm (by
          rw [code_replay, code_decode]
          exact Fin.snoc_last (α := fun _ => ℕ) _ _)
        rw [Relabel.trans_apply, hlast, hf, hae]
      · have hrep : replay hm ht v j.castSucc = replay hm ht' w j := code_injective hm (by
          rw [code_replay, code_replay]
          exact Fin.snoc_castSucc (α := fun _ => ℕ) _ _ _)
        rw [Relabel.trans_apply, hrep, hfix _ (mem_used.mpr ⟨j, rfl⟩)]
        exact he j


private theorem fresh_of_not_mem {m t : ℕ} (w : Word m (t + 1))
    (h : w.val (Fin.last t) ∉ used (Fin.init w.val)) :
    w.val (Fin.last t) = (used (Fin.init w.val)).card := by
  rcases w.property.2 with hf | ho
  · exact hf
  · exact (h (by
      rw [used_range w.property.1, Finset.mem_range]
      exact ho.trans_le (threshold_le _ _))).elim

/-- Legal first-use words are uniquely determined by their same-compartment relation. -/
private theorem word_unique {m t : ℕ} (u v : Word m t)
    (h : ∀ i j, u.val i = u.val j ↔ v.val i = v.val j) : u = v := by
  induction t with
  | zero => exact Subtype.ext (funext (fun i => Fin.elim0 i))
  | succ t ih =>
    let u' : Word m t := ⟨Fin.init u.val, u.property.1⟩
    let v' : Word m t := ⟨Fin.init v.val, v.property.1⟩
    have hh := ih u' v' (fun i j => h i.castSucc j.castSucc)
    have hp : Fin.init u.val = Fin.init v.val := congrArg Subtype.val hh
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => congrFun hp j) i
    by_cases hu : u.val (Fin.last t) ∈ used (Fin.init u.val)
    · obtain ⟨j,hj⟩ := mem_used.mp hu
      exact hj.symm.trans ((congrFun hp j).trans ((h _ _).1 hj))
    · have hv : v.val (Fin.last t) ∉ used (Fin.init v.val) := by
        intro hy
        obtain ⟨j,hj⟩ := mem_used.mp hy
        exact hu (mem_used.mpr ⟨j, (h _ _).2 hj⟩)
      rw [fresh_of_not_mem u hu, fresh_of_not_mem v hv, hp]

private theorem replay_orbit_injective {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A)
    (u v : Word m t) (h : Orbit (replay hm ht u) (replay hm ht v)) : u = v := by
  obtain ⟨e, he⟩ := h
  apply word_unique
  intro i j
  have hu : u.val i = u.val j ↔ replay hm ht u i = replay hm ht u j := by
    rw [← code_replay hm ht u i, ← code_replay hm ht u j]
    exact (code_injective hm).eq_iff
  have hv : v.val i = v.val j ↔ replay hm ht v i = replay hm ht v j := by
    rw [← code_replay hm ht v i, ← code_replay hm ht v j]
    exact (code_injective hm).eq_iff
  rw [hu, hv, ← he i, ← he j, e.injective.eq_iff]

/-- The unique legal word whose division/modulo replay is a relabeling of the raw history. -/
noncomputable def normalize {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (x : Raw A m t) :
    Word m t :=
  (exists_word hm ht x).choose

theorem replay_normalize_orbit {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (x : Raw A m t) :
    Orbit (replay hm ht (normalize hm ht x)) x.val :=
  (exists_word hm ht x).choose_spec

/-- The fibers of normalization are exactly the genuine raw relabeling orbits. -/
theorem normalize_eq_iff {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (x y : Raw A m t) :
    normalize hm ht x = normalize hm ht y ↔ Orbit x.val y.val := by
  have hx := replay_normalize_orbit hm ht x
  have hy := replay_normalize_orbit hm ht y
  constructor
  · intro h
    rw [h] at hx
    exact orbit_equivalence.trans (orbit_equivalence.symm hx) hy
  · intro h
    exact replay_orbit_injective hm ht _ _
      (orbit_equivalence.trans hx (orbit_equivalence.trans h (orbit_equivalence.symm hy)))

theorem normalize_replay {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (w : Word m t) :
    normalize hm ht ⟨replay hm ht w, replay_legal hm ht w⟩ = w :=
  replay_orbit_injective hm ht _ _ (replay_normalize_orbit hm ht _)

/-- The literal raw orbit quotient is equivalent to the legal first-use words.
The same construction works in every ambient with at least as many urns as marbles. -/
noncomputable def quotientEquivWord {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) :
    Arrangements A m t ≃ Word m t where
  toFun := Quotient.lift (normalize hm ht) (fun x y h => (normalize_eq_iff hm ht x y).2 h)
  invFun w := Quotient.mk _ ⟨replay hm ht w, replay_legal hm ht w⟩
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => exact Quotient.sound (replay_normalize_orbit hm ht x)
  right_inv := normalize_replay hm ht

/-- Canonical ranks at an actual raw prefix are the interval of length equal to the
number of distinct raw occupied addresses at that prefix. -/
theorem normalized_prefix_interval {A m t s : ℕ} (hm : 0 < m) (ht : t ≤ A)
    (x : Raw A m t) (hs : s ≤ t) :
    used (restrictPrefix (normalize hm ht x).val hs) =
      Finset.range (used (restrictPrefix x.val hs)).card := by
  let w := normalize hm ht x
  obtain ⟨e, he⟩ := replay_normalize_orbit hm ht x
  let g := restrictPrefix (replay hm ht w) hs
  have hx : restrictPrefix x.val hs = e.apply ∘ g := funext (fun i => (he _).symm)
  have hw : restrictPrefix w.val hs = code ∘ g := funext (fun i => (code_replay hm ht w _).symm)
  rw [actual_word_prefix_interval w.property hs]
  congr 1
  rw [hx, hw, used_comp, used_comp, Finset.card_image_of_injective _ e.injective,
    Finset.card_image_of_injective _ (code_injective hm)]


/-- The number of distinct occupied raw compartments is independent of the labels. -/
def occupied {A m t : ℕ} (q : Arrangements A m t) : ℕ :=
  Quotient.lift (fun x : Raw A m t => (used x.val).card) (by
    intro x y h
    obtain ⟨e, he⟩ := h
    have hy : y.val = e.apply ∘ x.val := funext (fun i => (he i).symm)
    rw [hy, used_comp, Finset.card_image_of_injective _ e.injective]) q

theorem occupied_normalize {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A)
    (q : Arrangements A m t) :
    occupied q = (used ((quotientEquivWord hm ht) q).val).card := by
  induction q using Quotient.inductionOn with
  | _ x =>
    change (used x.val).card = (used (normalize hm ht x).val).card
    have h := congrArg Finset.card (normalized_prefix_interval hm ht x (le_refl t))
    rw [Finset.card_range] at h
    exact h.symm

abbrev Fiber (A m t k : ℕ) := {q : Arrangements A m t // occupied q = k}
abbrev U (m t k : ℕ) := Fiber t m t k
abbrev WordFiber (m t k : ℕ) := {w : Word m t // (used w.val).card = k}

noncomputable def fiberEquivWord {A m t k : ℕ} (hm : 0 < m) (ht : t ≤ A) :
    Fiber A m t k ≃ WordFiber m t k :=
  (quotientEquivWord hm ht).subtypeEquiv (fun q => by rw [occupied_normalize hm ht q])

/-- Changing the ambient number of urn labels preserves each occupied-count fiber. -/
noncomputable def ambientEquiv {A B m t k : ℕ} (hm : 0 < m) (hA : t ≤ A) (hB : t ≤ B) :
    Fiber A m t k ≃ Fiber B m t k :=
  (fiberEquivWord hm hA).trans (fiberEquivWord hm hB).symm

/-! ## Prefix moves and first-use ranks -/


/-- Used compartments strictly before chronological position `i`. -/
def before {t : ℕ} (x : Fin t → ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun j : Fin t => j.val < i)).image x

theorem mem_before {t : ℕ} {x : Fin t → ℕ} {i a : ℕ} :
    a ∈ before x i ↔ ∃ j, j.val < i ∧ x j = a := by
  simp [before]

private theorem before_eq_used {t : ℕ} (x : Fin t → ℕ) {i : ℕ} (hi : i ≤ t) :
    before x i = used (restrictPrefix x hi) := by
  ext a
  simp only [mem_before, mem_used, restrictPrefix]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j.val, hj⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.castLE hi, j.isLt, rfl⟩

theorem before_end {t : ℕ} (x : Fin t → ℕ) : before x t = used x := by
  rw [before_eq_used x (le_refl t)]
  rfl

private theorem before_castSucc {t : ℕ} (x : Fin (t+1) → ℕ) (i : Fin t) :
    before x i.castSucc.val = before (Fin.init x) i.val := by
  rw [before_eq_used x (by omega), before_eq_used (Fin.init x) i.isLt.le]
  rfl

private theorem before_last {t : ℕ} (x : Fin (t+1) → ℕ) :
    before x (Fin.last t).val = used (Fin.init x) := by
  change before x t = _
  rw [before_eq_used x (Nat.le_succ t)]
  rfl

theorem legal_iff_moves {m t : ℕ} (x : Fin t → ℕ) :
    Legal m x ↔ ∀ i : Fin t, Move m (before x i.val).card (x i) := by
  induction t with
  | zero => exact ⟨fun _ i => Fin.elim0 i, fun _ => trivial⟩
  | succ t ih =>
    change (Legal m (Fin.init x) ∧ Move m (used (Fin.init x)).card (x (Fin.last t))) ↔ _
    rw [ih]
    constructor
    · intro ⟨hp, hl⟩
      refine Fin.lastCases ?_ (fun j => ?_)
      · simpa only [before_last] using hl
      · rw [before_castSucc]
        exact hp j
    · intro h
      exact ⟨fun j => by
        have hj := h j.castSucc
        rw [before_castSucc] at hj
        exact hj,
        by simpa only [before_last] using h (Fin.last t)⟩



/-- Two marble positions have the same canonical rank exactly when they use the same raw slot. -/
private theorem normalize_pair_eq_iff {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (x : Raw A m t)
    (i j : Fin t) :
    (normalize hm ht x).val i = (normalize hm ht x).val j ↔ x.val i = x.val j := by
  obtain ⟨e, he⟩ := replay_normalize_orbit hm ht x
  rw [← he i, ← he j, e.injective.eq_iff, ← (code_injective hm).eq_iff, code_replay, code_replay]

/-- Dividing ranks by the capacity detects raw urn equality. -/
theorem normalize_urn_eq_iff {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (x : Raw A m t)
    (i j : Fin t) :
    (normalize hm ht x).val i / m = (normalize hm ht x).val j / m ↔
      (x.val i).1 = (x.val j).1 := by
  obtain ⟨e, he⟩ := replay_normalize_orbit hm ht x
  rw [← he i, ← he j]
  change _ ↔ e.urn (replay hm ht (normalize hm ht x) i).1 =
    e.urn (replay hm ht (normalize hm ht x) j).1
  rw [e.urn.injective.eq_iff, Fin.ext_iff]
  rfl

/-- The numeric rank at the first use of a compartment is the actual prefix occupied count. -/
private theorem normalize_at_first_use {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (x : Raw A m t)
    (i : Fin t) (hn : ∀ j : Fin t, j < i → x.val j ≠ x.val i) :
    (normalize hm ht x).val i = (used (restrictPrefix x.val i.isLt.le)).card := by
  let w := normalize hm ht x
  have h := (legal_iff_moves w.val).1 w.property i
  have hbefore : before w.val i.val =
      Finset.range (used (restrictPrefix x.val i.isLt.le)).card :=
    (before_eq_used w.val i.isLt.le).trans (normalized_prefix_interval hm ht x i.isLt.le)
  have hmem : w.val i ∉ before w.val i.val := by
    intro h'
    obtain ⟨j, hj, he⟩ := mem_before.mp h'
    exact hn j hj ((normalize_pair_eq_iff hm ht x j i).1 he)
  rw [hbefore, Finset.card_range] at h
  rcases h with hf | ho
  · exact hf
  · exact (hmem (by rw [hbefore, Finset.mem_range]; exact ho.trans_le (threshold_le _ _))).elim

/-- Every normalized rank is determined by the first occurrence of its raw pair. -/
theorem normalize_first_occurrence {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A)
    (x : Raw A m t) (i : Fin t) :
    ∃ j : Fin t, j ≤ i ∧ x.val j = x.val i ∧
      (∀ h : Fin t, h < j → x.val h ≠ x.val i) ∧
      (normalize hm ht x).val i = (used (restrictPrefix x.val j.isLt.le)).card := by
  let s := Finset.univ.filter (fun j : Fin t => x.val j = x.val i)
  have hi : i ∈ s := by simp [s]
  let j := s.min' ⟨i, hi⟩
  have hj : x.val j = x.val i := by
    have hmemb := s.min'_mem ⟨i, hi⟩
    simpa [s, j] using hmemb
  have hjmin (h : Fin t) (hlt : h < j) (he : x.val h = x.val i) : False := by
    have hmem : h ∈ s := by simpa [s] using he
    exact (not_le_of_gt hlt) (s.min'_le h hmem)
  refine ⟨j, s.min'_le i hi, hj, hjmin, ?_⟩
  have hl := normalize_at_first_use hm ht x j (fun h hh he => hjmin h hh (he.trans hj))
  exact ((normalize_pair_eq_iff hm ht x j i).2 hj).symm.trans hl

/-- At the first use of an urn, the first-use slot is zero and earlier ranks
are exactly the complete earlier urns. -/
theorem normalize_at_first_urn {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (x : Raw A m t)
    (i : Fin t) (hn : ∀ j : Fin t, j < i → (x.val j).1 ≠ (x.val i).1) :
    (normalize hm ht x).val i % m = 0 := by
  let w := normalize hm ht x
  have hr := normalize_at_first_use hm ht x i (fun j hj h => hn j hj (congrArg Prod.fst h))
  have hbefore : before w.val i.val = Finset.range (w.val i) := by
    rw [before_eq_used w.val i.isLt.le, normalized_prefix_interval hm ht x i.isLt.le]
    exact congrArg Finset.range hr.symm
  have hbase := Nat.div_add_mod (w.val i) m
  by_contra hmod
  change w.val i % m ≠ 0 at hmod
  have hlt : m * (w.val i / m) < w.val i := by omega
  have hmem : m * (w.val i / m) ∈ before w.val i.val := by
    rw [hbefore, Finset.mem_range]
    exact hlt
  obtain ⟨j, hj, he⟩ := mem_before.mp hmem
  have hu : w.val j / m = w.val i / m := by rw [he, Nat.mul_div_cancel_left _ hm]
  exact hn j hj ((normalize_urn_eq_iff hm ht x j i).1 hu)


end PopovUrnShift
