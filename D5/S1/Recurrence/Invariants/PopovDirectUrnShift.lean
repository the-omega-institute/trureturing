import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fintype

/-!
# Popov's first-urn shift

Local probe for Problem 9.1 of Vencislav Popov, arXiv:2608.12011v1.
The marble domain is chronological and is fixed under every relabeling.
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

@[simp] theorem used_zero {α : Type} [DecidableEq α] (x : Fin 0 → α) :
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

theorem actual_word_prefix_interval {m t s : ℕ} {x : Fin t → ℕ}
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

@[simp] theorem refl_apply {A m : ℕ} (a : Address A m) : (refl A m).apply a = a := by
  cases a
  rfl

@[simp] theorem symm_apply {A m : ℕ} (e : Relabel A m) (a : Address A m) :
    e.symm.apply (e.apply a) = a := by
  rcases a with ⟨u, c⟩
  simp [symm, apply]

@[simp] theorem apply_symm {A m : ℕ} (e : Relabel A m) (a : Address A m) :
    e.apply (e.symm.apply a) = a := by
  rcases a with ⟨u, c⟩
  simp [symm, apply]

@[simp] theorem trans_apply {A m : ℕ} (e f : Relabel A m) (a : Address A m) :
    (e.trans f).apply a = f.apply (e.apply a) := rfl

theorem injective {A m : ℕ} (e : Relabel A m) : Function.Injective e.apply :=
  Function.LeftInverse.injective (symm_apply e)

end Relabel

/-- Orbit under the raw source relabelings, with every marble position fixed. -/
def Orbit {A m t : ℕ} (x y : Fin t → Address A m) : Prop :=
  ∃ e : Relabel A m, ∀ i, e.apply (x i) = y i

theorem orbit_equivalence {A m t : ℕ} :
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


theorem used_comp {t : ℕ} {α β : Type} [DecidableEq α] [DecidableEq β]
    (x : Fin t → α) (f : α → β) : used (f ∘ x) = (used x).image f := by
  simp [used, Finset.image_image, Function.comp_def]

/-- Numeric code of an address in the canonical labeling. -/
def code {A m : ℕ} (a : Address A m) : ℕ := m * a.1.val + a.2.val

theorem code_div {A m : ℕ} (hm : 0 < m) (a : Address A m) : code a / m = a.1.val := by
  simp [code, Nat.mul_add_div hm, Nat.div_eq_of_lt a.2.isLt]

theorem code_mod {A m : ℕ} (a : Address A m) : code a % m = a.2.val := by
  simp [code, Nat.mod_eq_of_lt a.2.isLt]

theorem code_injective {A m : ℕ} (hm : 0 < m) :
    Function.Injective (code : Address A m → ℕ) := by
  intro a b h
  apply Prod.ext
  · apply Fin.ext
    rw [← code_div hm a, ← code_div hm b, h]
  · apply Fin.ext
    rw [← code_mod a, ← code_mod b, h]

def decode {A m : ℕ} (hm : 0 < m) (a : ℕ) (ha : a / m < A) : Address A m :=
  (⟨a / m, ha⟩, ⟨a % m, Nat.mod_lt _ hm⟩)

@[simp] theorem code_decode {A m a : ℕ} (hm : 0 < m) (ha : a / m < A) :
    code (decode hm a ha) = a :=
  Nat.div_add_mod a m

/-- Replay uses quotient and remainder at every chronological position. -/
def replay {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (w : Word m t) :
    Fin t → Address A m :=
  fun i => decode hm (w.val i) (by
    have hi : w.val i < A := ((word_rank_le w.property i).trans_lt i.isLt).trans_le ht
    exact (Nat.div_le_self _ _).trans_lt hi)

@[simp] theorem code_replay {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (w : Word m t)
    (i : Fin t) : code (replay hm ht w i) = w.val i :=
  code_decode _ _

theorem replay_init {A m t : ℕ} (hm : 0 < m) (ht : t + 1 ≤ A)
    (w : Word m (t + 1)) :
    Fin.init (replay hm ht w) =
      replay hm (Nat.le_of_succ_le ht) ⟨Fin.init w.val, w.property.1⟩ :=
  rfl

theorem replay_codes {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (w : Word m t) :
    (used (replay hm ht w)).image code = used w.val := by
  rw [← used_comp]
  congr 1
  funext i
  exact code_replay hm ht w i

theorem replay_card {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (w : Word m t) :
    (used (replay hm ht w)).card = (used w.val).card := by
  rw [← replay_codes hm ht, Finset.card_image_of_injective _ (code_injective hm)]

theorem mem_layout {A m p : ℕ} {s : Finset (Address A m)} (hm : 0 < m)
    (hs : s.image code = Finset.range p) (a : Address A m) :
    a ∈ s ↔ code a < p := by
  rw [← Finset.mem_range, ← hs, Finset.mem_image]
  exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, h⟩ => code_injective hm h ▸ hb⟩

theorem full_layout {A m p : ℕ} {s : Finset (Address A m)} (hm : 0 < m)
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

theorem started_layout {A m p : ℕ} {s : Finset (Address A m)} (hm : 0 < m)
    (hs : s.image code = Finset.range p) (u : Fin A) :
    Started s u ↔ m * u.val < p := by
  constructor
  · intro ⟨c, hc⟩
    have h := (mem_layout hm hs (u,c)).1 hc
    exact (Nat.le_add_right _ _).trans_lt h
  · intro h
    exact ⟨⟨0, hm⟩, (mem_layout hm hs _).2 (by simpa [code] using h)⟩

theorem rawMove_of_move {A m p : ℕ} {s : Finset (Address A m)} (hm : 0 < m)
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
theorem rawMove_image {A m : ℕ} (e : Relabel A m) (s : Finset (Address A m))
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
theorem align_fresh {A m p : ℕ} {s : Finset (Address A m)} (hm : 0 < m)
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
theorem exists_word {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (x : Raw A m t) :
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


theorem fresh_of_not_mem {m t : ℕ} (w : Word m (t + 1))
    (h : w.val (Fin.last t) ∉ used (Fin.init w.val)) :
    w.val (Fin.last t) = (used (Fin.init w.val)).card := by
  rcases w.property.2 with hf | ho
  · exact hf
  · exact (h (by
      rw [used_range w.property.1, Finset.mem_range]
      exact ho.trans_le (threshold_le _ _))).elim

/-- Legal first-use words are uniquely determined by their same-compartment relation. -/
theorem word_unique {m t : ℕ} (u v : Word m t)
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

theorem replay_orbit_injective {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A)
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

/-! ## Chronological deletion and reinsertion -/

/-- Used compartments strictly before chronological position `i`. -/
def before {t : ℕ} (x : Fin t → ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun j : Fin t => j.val < i)).image x

theorem mem_before {t : ℕ} {x : Fin t → ℕ} {i a : ℕ} :
    a ∈ before x i ↔ ∃ j, j.val < i ∧ x j = a := by
  simp [before]

theorem before_eq_used {t : ℕ} (x : Fin t → ℕ) {i : ℕ} (hi : i ≤ t) :
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

theorem before_castSucc {t : ℕ} (x : Fin (t+1) → ℕ) (i : Fin t) :
    before x i.castSucc.val = before (Fin.init x) i.val := by
  rw [before_eq_used x (by omega), before_eq_used (Fin.init x) i.isLt.le]
  rfl

theorem before_last {t : ℕ} (x : Fin (t+1) → ℕ) :
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

theorem used_val (t : ℕ) : used (fun i : Fin t => i.val) = Finset.range t := by
  ext a
  simp only [mem_used, Finset.mem_range]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ i.isLt, fun h => ⟨⟨a,h⟩, rfl⟩⟩

/-- Before the first urn fills, the only legal ranks are the successive fresh ranks. -/
theorem forced_word {m t : ℕ} (ht : t ≤ m) {x : Fin t → ℕ} (hx : Legal m x) :
    x = fun i => i.val := by
  induction t with
  | zero => exact funext (fun i => Fin.elim0 i)
  | succ t ih =>
    have hp := ih (Nat.le_of_succ_le ht) hx.1
    have hcard : (used (Fin.init x)).card = t := by rw [hp, used_val, Finset.card_range]
    have hl := hx.2
    rw [hcard] at hl
    have he : x (Fin.last t) = t := by
      simpa [Move, threshold, Nat.div_eq_of_lt (show t < m by omega)] using hl
    exact funext (Fin.lastCases he (fun i => congrFun hp i))

theorem forced_prefix {m n : ℕ} {x : Fin (m+n) → ℕ} (hx : Legal m x) (i : Fin m) :
    x (i.castAdd n) = i.val :=
  congrFun (forced_word (le_refl m) (legal_prefix hx (Nat.le_add_right m n))) i

/-- The increasing enumeration of selected tail positions. -/
def selectedOrder {n : ℕ} (J : Finset (Fin n)) : Fin J.card ≃o J :=
  J.orderIsoOfFin rfl

abbrev Colors (m n : ℕ) (J : Finset (Fin n)) := {i : Fin n // i ∉ J} → Fin m

/-- The first-urn colors and the shifted-down ranks of the marbles outside the first urn. -/
abbrev TailData (m n : ℕ) :=
  Σ J : Finset (Fin n), Colors m n J × (Fin J.card → ℕ)

/-- Reinsert in chronological order, using the selected positions to read the residual word. -/
def assemble {m n : ℕ} (d : TailData m n) : Fin (m+n) → ℕ :=
  Fin.addCases (fun i : Fin m => i.val) (fun i : Fin n =>
    if hi : i ∈ d.1 then m + d.2.2 ((selectedOrder d.1).symm ⟨i,hi⟩)
    else (d.2.1 ⟨i,hi⟩).val)

@[simp] theorem assemble_prefix {m n : ℕ} (d : TailData m n) (i : Fin m) :
    assemble d (i.castAdd n) = i.val := by
  simp [assemble]

theorem assemble_color {m n : ℕ} (d : TailData m n) (i : Fin n) (hi : i ∉ d.1) :
    assemble d (Fin.natAdd m i) = (d.2.1 ⟨i,hi⟩).val := by
  simp [assemble, Fin.addCases_right, hi]

theorem assemble_selected {m n : ℕ} (d : TailData m n) (j : Fin d.1.card) :
    assemble d (Fin.natAdd m ((selectedOrder d.1) j).val) = m + d.2.2 j := by
  simp [assemble, Fin.addCases_right]

theorem assemble_ge {m n : ℕ} (d : TailData m n) (i : Fin n) :
    m ≤ assemble d (Fin.natAdd m i) ↔ i ∈ d.1 := by
  by_cases h : i ∈ d.1
  · let j := (selectedOrder d.1).symm ⟨i,h⟩
    have hj : ((selectedOrder d.1) j).val = i :=
      congrArg Subtype.val ((selectedOrder d.1).apply_symm_apply ⟨i,h⟩)
    rw [← hj, assemble_selected]
    exact iff_of_true (Nat.le_add_right _ _) ((selectedOrder d.1) j).property
  · rw [assemble_color d i h]
    exact iff_of_false (not_le_of_gt (d.2.1 ⟨i,h⟩).isLt) h

/-- Delete exactly the first-urn tail placements, retaining their colors at their original positions. -/
def splitTail {m n : ℕ} (x : Fin (m+n) → ℕ) : TailData m n :=
  let J := Finset.univ.filter (fun i : Fin n => m ≤ x (Fin.natAdd m i))
  ⟨J, (fun i => ⟨x (Fin.natAdd m i.val), by simpa [J] using i.property⟩),
    (fun j => x (Fin.natAdd m ((selectedOrder J) j).val) - m)⟩

theorem assemble_split {m n : ℕ} (x : Fin (m+n) → ℕ)
    (hp : ∀ i : Fin m, x (i.castAdd n) = i.val) :
    assemble (splitTail x) = x := by
  funext i
  refine Fin.addCases (motive := fun i => assemble (splitTail x) i = x i)
    (fun j => by rw [assemble_prefix, hp]) (fun j => ?_) i
  simp only [assemble, Fin.addCases_right]
  split
  next h =>
    have hj : ((selectedOrder (splitTail x).1) ((selectedOrder (splitTail x).1).symm
        ⟨j,h⟩)).val = j := congrArg Subtype.val ((selectedOrder _).apply_symm_apply ⟨j,h⟩)
    have hbound : m ≤ x (Fin.natAdd m j) := by simpa [splitTail] using h
    change m + (x (Fin.natAdd m (((selectedOrder (splitTail x).1)
      ((selectedOrder (splitTail x).1).symm ⟨j,h⟩)).val)) - m) = x (Fin.natAdd m j)
    rw [hj]
    omega
  next => rfl

theorem assemble_injective {m n : ℕ} :
    Function.Injective (assemble (m := m) (n := n)) := by
  rintro ⟨J, c, r⟩ ⟨K, b, s⟩ he
  have hJK : J = K := by
    ext i
    rw [← assemble_ge ⟨J,c,r⟩, ← assemble_ge ⟨K,b,s⟩, he]
  subst K
  have hc : c = b := by
    funext i
    apply Fin.ext
    have h := congrFun he (Fin.natAdd m i.val)
    rw [assemble_color ⟨J,c,r⟩ i.val i.property, assemble_color ⟨J,b,s⟩ i.val i.property] at h
    exact h
  have hr : r = s := by
    funext j
    have h := congrFun he (Fin.natAdd m ((selectedOrder J) j).val)
    rw [assemble_selected ⟨J,c,r⟩ j, assemble_selected ⟨J,b,s⟩ j] at h
    exact Nat.add_left_cancel h
  subst c
  subst r
  rfl

theorem split_assemble {m n : ℕ} (d : TailData m n) :
    splitTail (assemble d) = d :=
  assemble_injective (assemble_split _ (assemble_prefix d))


/-- Every tail prefix consists of the full first urn and the shifted residual prefix. -/
theorem mem_before_assemble {m n : ℕ} (d : TailData m n) (i a : ℕ) :
    a ∈ before (assemble d) (m+i) ↔
      a < m ∨ ∃ j : Fin d.1.card,
        ((selectedOrder d.1) j).val.val < i ∧ m + d.2.2 j = a := by
  rw [mem_before]
  constructor
  · rintro ⟨p, hp, rfl⟩
    revert hp
    refine Fin.addCases (motive := fun p => p.val < m+i →
      assemble d p < m ∨ ∃ j : Fin d.1.card, ((selectedOrder d.1) j).val.val < i ∧
        m + d.2.2 j = assemble d p) ?_ ?_ p
    · intro j _
      rw [assemble_prefix]
      exact .inl j.isLt
    · intro j hj
      by_cases h : j ∈ d.1
      · let k := (selectedOrder d.1).symm ⟨j,h⟩
        have hk : ((selectedOrder d.1) k).val = j :=
          congrArg Subtype.val ((selectedOrder d.1).apply_symm_apply ⟨j,h⟩)
        have hji : j.val < i := Nat.lt_of_add_lt_add_left hj
        refine .inr ⟨k, by rw [hk]; exact hji, ?_⟩
        exact (assemble_selected d k).symm.trans (congrArg (assemble d ∘ Fin.natAdd m) hk)
      · rw [assemble_color d j h]
        exact .inl (d.2.1 ⟨j,h⟩).isLt
  · rintro (h | ⟨j,hj,hr⟩)
    · let p : Fin m := ⟨a,h⟩
      exact ⟨p.castAdd n, h.trans_le (Nat.le_add_right _ _), assemble_prefix d p⟩
    · exact ⟨Fin.natAdd m ((selectedOrder d.1) j).val, Nat.add_lt_add_left hj m,
        (assemble_selected d j).trans hr⟩

theorem before_assemble_selected {m n : ℕ} (d : TailData m n) (j : Fin d.1.card) :
    before (assemble d) (m+((selectedOrder d.1) j).val.val) =
      Finset.range m ∪ (before d.2.2 j.val).image (m + ·) := by
  ext a
  rw [mem_before_assemble]
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image, mem_before]
  constructor
  · rintro (h | ⟨k,hk,rfl⟩)
    · exact .inl h
    · have hh : (selectedOrder d.1) k < (selectedOrder d.1) j := hk
      exact .inr ⟨d.2.2 k, ⟨k, (selectedOrder d.1).lt_iff_lt.mp hh, rfl⟩, rfl⟩
  · rintro (h | ⟨_,⟨k,hk,rfl⟩,rfl⟩)
    · exact .inl h
    · exact .inr ⟨k, (selectedOrder d.1).strictMono hk, rfl⟩

/-- The actual occupied set after assembly, with a disjoint full and shifted part. -/
theorem used_assemble {m n : ℕ} (d : TailData m n) :
    used (assemble d) = Finset.range m ∪ (used d.2.2).image (m + ·) := by
  rw [← before_end]
  ext a
  simp only [mem_before_assemble, Finset.mem_union, Finset.mem_range, Finset.mem_image, mem_used]
  constructor
  · rintro (h | ⟨k,_,rfl⟩)
    · exact .inl h
    · exact .inr ⟨d.2.2 k, ⟨k,rfl⟩, rfl⟩
  · rintro (h | ⟨_,⟨k,rfl⟩,rfl⟩)
    · exact .inl h
    · exact .inr ⟨k, ((selectedOrder d.1) k).val.isLt, rfl⟩

theorem card_range_union_shift (m : ℕ) (s : Finset ℕ) :
    (Finset.range m ∪ s.image (m + ·)).card = m + s.card := by
  rw [Finset.card_union_of_disjoint, Finset.card_range, Finset.card_image_of_injective]
  · exact fun _ _ => Nat.add_left_cancel
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_range, Finset.mem_image]
    rintro _ ha ⟨b,_,rfl⟩
    omega

theorem threshold_shift (m p : ℕ) (hm : 0 < m) :
    threshold m (m+p) = m + threshold m p := by
  unfold threshold
  rw [show m+p = m*1+p by simp, Nat.mul_add_div hm, Nat.mul_add, Nat.mul_one]

theorem move_shift {m p a : ℕ} (hm : 0 < m) :
    Move m (m+p) (m+a) ↔ Move m p a := by
  simp only [Move, threshold_shift _ _ hm, Nat.add_left_cancel_iff, Nat.add_lt_add_iff_left]

theorem before_assemble_prefix {m n : ℕ} (d : TailData m n) (i : Fin m) :
    before (assemble d) i.val = Finset.range i.val := by
  ext a
  rw [mem_before, Finset.mem_range]
  constructor
  · rintro ⟨p,hp,rfl⟩
    revert hp
    refine Fin.addCases (motive := fun p => p.val < i.val → assemble d p < i.val)
        (fun j hj => ?_) (fun j hj => ?_) p
    · rwa [assemble_prefix]
    · have hi := i.isLt
      change m + j.val < i.val at hj
      omega
  · intro h
    let j : Fin m := ⟨a,h.trans i.isLt⟩
    exact ⟨j.castAdd n,h,assemble_prefix d j⟩

/-- Inserting any first-urn color is legal throughout the tail. -/
theorem assemble_color_move {m n : ℕ} (hm : 0 < m) (d : TailData m n) (i : Fin n)
    (hi : i ∉ d.1) : Move m (before (assemble d) (m+i.val)).card (assemble d (Fin.natAdd m i)) := by
  have hsub : Finset.range m ⊆ before (assemble d) (m+i.val) :=
    fun _ ha => (mem_before_assemble _ _ _).2 (.inl (Finset.mem_range.mp ha))
  have hmle : m ≤ (before (assemble d) (m+i.val)).card := by
    simpa using Finset.card_le_card hsub
  have hdiv : 1 ≤ (before (assemble d) (m+i.val)).card / m :=
    (Nat.le_div_iff_mul_le hm).2 (by simpa using hmle)
  have hthr : m ≤ threshold m (before (assemble d) (m+i.val)).card := by
    simpa [threshold] using Nat.mul_le_mul_left m hdiv
  rw [assemble_color d i hi]
  exact .inr ((d.2.1 ⟨i,hi⟩).isLt.trans_le hthr)

theorem assemble_legal_iff {m n : ℕ} (hm : 0 < m) (d : TailData m n) :
    Legal m (assemble d) ↔ Legal m d.2.2 := by
  rw [legal_iff_moves, legal_iff_moves]
  have hsel (j : Fin d.1.card) :
      Move m (before (assemble d) (Fin.natAdd m ((selectedOrder d.1) j).val).val).card
          (assemble d (Fin.natAdd m ((selectedOrder d.1) j).val)) ↔
        Move m (before d.2.2 j.val).card (d.2.2 j) := by
    change Move m (before (assemble d) (m+((selectedOrder d.1) j).val.val)).card _ ↔ _
    rw [before_assemble_selected, card_range_union_shift, assemble_selected, move_shift hm]
  constructor
  · exact fun h j => (hsel j).1 (h _)
  · intro h i
    refine Fin.addCases (motive := fun i => Move m (before (assemble d) i.val).card (assemble d i))
      (fun j => ?_) (fun j => ?_) i
    · change Move m (before (assemble d) j.val).card (assemble d (j.castAdd n))
      rw [before_assemble_prefix, Finset.card_range, assemble_prefix]
      exact .inl rfl
    · by_cases hj : j ∈ d.1
      · let k := (selectedOrder d.1).symm ⟨j,hj⟩
        have hk : ((selectedOrder d.1) k).val = j :=
          congrArg Subtype.val ((selectedOrder d.1).apply_symm_apply ⟨j,hj⟩)
        rw [← hk]
        exact (hsel k).2 (h k)
      · exact assemble_color_move hm d j hj


abbrev WordPayload (m n r : ℕ) :=
  Σ J : Finset (Fin n), Colors m n J × WordFiber m J.card r

abbrev Payload (m n r : ℕ) :=
  Σ J : Finset (Fin n), Colors m n J × U m J.card r

def TailData.forget {m n r : ℕ} (d : WordPayload m n r) : TailData m n :=
  ⟨d.1, d.2.1, d.2.2.val.val⟩

theorem TailData.forget_injective {m n r : ℕ} :
    Function.Injective (TailData.forget (m := m) (n := n) (r := r)) := by
  rintro ⟨J,c,⟨⟨w,hw⟩,hk⟩⟩ ⟨K,b,⟨⟨v,hv⟩,hl⟩⟩ h
  change (⟨J,c,w⟩ : TailData m n) = ⟨K,b,v⟩ at h
  have hJK : J = K := congrArg Sigma.fst h
  subst K
  have hdata : (c,w) = (b,v) := eq_of_heq (Sigma.mk.inj h).2
  have hcb : c = b := congrArg Prod.fst hdata
  have hwv : w = v := congrArg Prod.snd hdata
  subst b
  subst v
  rfl

/-- Delete the first urn from the word and record the original positions and colors. -/
def deleteWord {m n r : ℕ} (hm : 0 < m) (w : WordFiber m (m+n) (m+r)) :
    WordPayload m n r := by
  let d := splitTail w.val.val
  have ha : assemble d = w.val.val := assemble_split _ (forced_prefix w.val.property)
  have hl : Legal m d.2.2 := (assemble_legal_iff hm d).1 (ha ▸ w.val.property)
  have hcnt := w.property
  rw [← ha, used_assemble, card_range_union_shift] at hcnt
  exact ⟨d.1, d.2.1, ⟨⟨d.2.2, hl⟩, Nat.add_left_cancel hcnt⟩⟩

/-- Prepend the full first urn and reinsert the two kinds of tail placements in order. -/
def reinsertWord {m n r : ℕ} (hm : 0 < m) (d : WordPayload m n r) :
    WordFiber m (m+n) (m+r) :=
  ⟨⟨assemble (TailData.forget d), (assemble_legal_iff hm _).2 d.2.2.val.property⟩, by
    rw [used_assemble, card_range_union_shift]
    exact congrArg (m + ·) d.2.2.property⟩

/-- Reinsertion after deletion recovers the forced prefix and each tail position. -/
theorem reinsert_delete_word {m n r : ℕ} (hm : 0 < m) (w : WordFiber m (m+n) (m+r)) :
    reinsertWord hm (deleteWord hm w) = w :=
  Subtype.ext (Subtype.ext (assemble_split _ (forced_prefix w.val.property)))

/-- Deletion after reinsertion recovers the selected positions, each color, and each residual rank. -/
theorem delete_reinsert_word {m n r : ℕ} (hm : 0 < m) (d : WordPayload m n r) :
    deleteWord hm (reinsertWord hm d) = d :=
  TailData.forget_injective (split_assemble (TailData.forget d))

def wordShift {m n r : ℕ} (hm : 0 < m) : WordFiber m (m+n) (m+r) ≃ WordPayload m n r :=
  ⟨deleteWord hm, reinsertWord hm, reinsert_delete_word hm, delete_reinsert_word hm⟩

noncomputable def payloadEquivWord {m n r : ℕ} (hm : 0 < m) :
    Payload m n r ≃ WordPayload m n r :=
  Equiv.sigmaCongrRight (fun J =>
    Equiv.prodCongr (Equiv.refl (Colors m n J)) (fiberEquivWord hm (le_refl J.card)))

/-- Popov's first-urn shift on the literal occupied-count orbit quotients. -/
noncomputable def firstUrnEquiv {m n r : ℕ} (hm : 0 < m) :
    U m (n+m) (m+r) ≃ Payload m n r :=
  (Equiv.cast (congrArg (fun length => U m length (m+r)) (Nat.add_comm n m))).trans
    ((fiberEquivWord hm (le_refl (m+n))).trans ((wordShift hm).trans (payloadEquivWord hm).symm))

/-- Chronological deletion on raw orbits, with the original complement colors. -/
noncomputable def deleteFirstUrn {m n r : ℕ} (hm : 0 < m) :
    U m (n+m) (m+r) → Payload m n r :=
  firstUrnEquiv hm

/-- Chronological reinsertion on raw orbits. -/
noncomputable def reinsertFirstUrn {m n r : ℕ} (hm : 0 < m) :
    Payload m n r → U m (n+m) (m+r) :=
  (firstUrnEquiv hm).symm

theorem reinsert_delete {m n r : ℕ} (hm : 0 < m) (q : U m (n+m) (m+r)) :
    reinsertFirstUrn hm (deleteFirstUrn hm q) = q :=
  (firstUrnEquiv hm).left_inv q

theorem delete_reinsert {m n r : ℕ} (hm : 0 < m) (d : Payload m n r) :
    deleteFirstUrn hm (reinsertFirstUrn hm d) = d :=
  (firstUrnEquiv hm).right_inv d

/-- The signed column is empty at every negative index. -/
def SignedU (m t : ℕ) (k : ℤ) := if k < 0 then Empty else U m t k.toNat

theorem signed_negative_empty {m t : ℕ} {k : ℤ} (hn : k < 0) : IsEmpty (SignedU m t k) := by
  rw [SignedU, ite_eq_left hn]
  infer_instance

theorem word_card_ge_m {m n : ℕ} (w : Word m (m+n)) : m ≤ (used w.val).card := by
  have ha := assemble_split _ (forced_prefix w.property)
  rw [← ha, used_assemble, card_range_union_shift]
  exact Nat.le_add_right _ _

theorem below_first_urn {m n k : ℕ} (hm : 0 < m) (hk : k < m) :
    IsEmpty (U m (n+m) k) := by
  refine ⟨fun q => ?_⟩
  let q' : U m (m+n) k :=
    (Equiv.cast (congrArg (fun length => U m length k) (Nat.add_comm n m))) q
  let w := fiberEquivWord hm (le_refl (m+n)) q'
  exact (not_le_of_gt hk) (w.property ▸ word_card_ge_m w.val)

theorem word_card_le_length {m t k : ℕ} (w : WordFiber m t k) : k ≤ t :=
  w.property ▸ used_card_le w.val.val

theorem beyond_length {m t k : ℕ} (hm : 0 < m) (hk : t < k) : IsEmpty (U m t k) :=
  ⟨fun q => (not_le_of_gt hk) (word_card_le_length (fiberEquivWord hm (le_refl t) q))⟩


/-! ## Finite counting -/

/-- Recurrence (7.1), with the zero column separated from the positive columns. -/
def stirling (m : ℕ) : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | _+1, 0 => 0
  | t+1, k+1 => threshold m (k+1) * stirling m t (k+1) + stirling m t k

/-- Definition 7.1 with the paper's negative-column convention. -/
def S (m t : ℕ) (k : ℤ) : ℕ :=
  if k < 0 then 0 else stirling m t k.toNat

@[simp] theorem S_nat (m t k : ℕ) : S m t k = stirling m t k := by simp [S]

instance wordFinite (m t : ℕ) : Finite (Word m t) :=
  Finite.of_injective (fun w : Word m t => fun i : Fin t =>
    (⟨w.val i, (word_rank_le w.property i).trans_lt i.isLt⟩ : Fin t))
    (fun _ _ h => Subtype.ext (funext (fun i => congrArg Fin.val (congrFun h i))))

noncomputable instance wordFiberFintype (m t k : ℕ) : Fintype (WordFiber m t k) :=
  Fintype.ofFinite _

instance arrangementsFinite (A m t : ℕ) : Finite (Arrangements A m t) :=
  Finite.of_surjective (Quotient.mk (orbitSetoid A m t)) (by
    intro q
    exact Quotient.inductionOn q (fun x => ⟨x,rfl⟩))

noncomputable instance rawFiberFintype (A m t k : ℕ) : Fintype (Fiber A m t k) :=
  Fintype.ofFinite _

theorem used_snoc {t : ℕ} {α : Type} [DecidableEq α] (x : Fin t → α) (a : α) :
    used (Fin.snoc (α := fun _ => α) x a) = insert a (used x) := by
  rw [used_init, Fin.init_snoc, Fin.snoc_last]

private def appendOld {m t k : ℕ} (a : Fin (threshold m k)) (w : WordFiber m t k) :
    WordFiber m (t+1) k :=
  ⟨⟨Fin.snoc (α := fun _ => ℕ) w.val.val a.val, legal_snoc w.val a.val
    (.inr (w.property.symm ▸ a.isLt))⟩, by
    have ha : a.val ∈ used w.val.val := by
      rw [used_range w.val.property, Finset.mem_range, w.property]
      exact a.isLt.trans_le (threshold_le _ _)
    rw [used_snoc, Finset.insert_eq_of_mem ha]
    exact w.property⟩

private def appendFresh {m t k : ℕ} (w : WordFiber m t k) :
    WordFiber m (t+1) (k+1) :=
  ⟨⟨Fin.snoc (α := fun _ => ℕ) w.val.val k, legal_snoc w.val k (.inl w.property.symm)⟩, by
    have hk : k ∉ used w.val.val := by
      rw [used_range w.val.property, Finset.mem_range, w.property]
      exact Nat.lt_irrefl _
    rw [used_snoc, Finset.card_insert_of_notMem hk, w.property]⟩

private theorem old_prefix_count {m t k : ℕ} (a : Fin (threshold m k)) (w : WordFiber m t k) :
    (used (Fin.init (appendOld a w).val.val)).card = k := by
  change (used (Fin.init (Fin.snoc (α := fun _ => ℕ) w.val.val a.val))).card = k
  rw [Fin.init_snoc]
  exact w.property

private theorem fresh_prefix_count {m t k : ℕ} (w : WordFiber m t k) :
    (used (Fin.init (appendFresh w).val.val)).card = k := by
  change (used (Fin.init (Fin.snoc (α := fun _ => ℕ) w.val.val k))).card = k
  rw [Fin.init_snoc]
  exact w.property

/-- The last move is one of the available old compartments, or the unique fresh compartment. -/
noncomputable def lastMoveEquiv (m t k : ℕ) :
    (Fin (threshold m (k+1)) × WordFiber m t (k+1) ⊕ WordFiber m t k) ≃
      WordFiber m (t+1) (k+1) := by
  let go : (Fin (threshold m (k+1)) × WordFiber m t (k+1) ⊕ WordFiber m t k) →
      WordFiber m (t+1) (k+1) :=
    Sum.elim (fun d => appendOld d.1 d.2) appendFresh
  refine Equiv.ofBijective go ⟨?_, ?_⟩
  · rintro (⟨a,u⟩ | u) (⟨b,v⟩ | v) h
    · have hh := congrArg (fun w : WordFiber m (t+1) (k+1) => w.val.val) h
      change Fin.snoc (α := fun _ => ℕ) u.val.val a.val =
        Fin.snoc (α := fun _ => ℕ) v.val.val b.val at hh
      have huv := congrArg Fin.init hh
      rw [Fin.init_snoc, Fin.init_snoc] at huv
      have hab := congrFun hh (Fin.last t)
      rw [Fin.snoc_last, Fin.snoc_last] at hab
      exact congrArg Sum.inl (Prod.ext (Fin.ext hab) (Subtype.ext (Subtype.ext huv)))
    · change appendOld a u = appendFresh v at h
      have he := congrArg (fun w : WordFiber m (t+1) (k+1) => (used (Fin.init w.val.val)).card) h
      change (used (Fin.init (appendOld a u).val.val)).card =
        (used (Fin.init (appendFresh v).val.val)).card at he
      rw [old_prefix_count, fresh_prefix_count] at he
      omega
    · change appendFresh u = appendOld b v at h
      have he := congrArg (fun w : WordFiber m (t+1) (k+1) => (used (Fin.init w.val.val)).card) h
      change (used (Fin.init (appendFresh u).val.val)).card =
        (used (Fin.init (appendOld b v).val.val)).card at he
      rw [fresh_prefix_count, old_prefix_count] at he
      omega
    · have hh := congrArg (fun w : WordFiber m (t+1) (k+1) => Fin.init w.val.val) h
      change Fin.init (Fin.snoc (α := fun _ => ℕ) u.val.val k) =
        Fin.init (Fin.snoc (α := fun _ => ℕ) v.val.val k) at hh
      rw [Fin.init_snoc, Fin.init_snoc] at hh
      exact congrArg Sum.inr (Subtype.ext (Subtype.ext hh))
  · intro w
    let v := Fin.init w.val.val
    let a := w.val.val (Fin.last t)
    have hl : Legal m v := w.val.property.1
    have ha : Move m (used v).card a := w.val.property.2
    have hw : (insert a (used v)).card = k+1 := by
      change (insert (w.val.val (Fin.last t)) (used (Fin.init w.val.val))).card = _
      rw [← used_init]
      exact w.property
    rcases ha with hf | ho
    · have hn : a ∉ used v := by
        rw [used_range hl, Finset.mem_range, hf]
        exact Nat.lt_irrefl _
      rw [Finset.card_insert_of_notMem hn] at hw
      have hp : (used v).card = k := Nat.succ.inj hw
      refine ⟨Sum.inr ⟨⟨v,hl⟩,hp⟩, Subtype.ext (Subtype.ext ?_)⟩
      change Fin.snoc (α := fun _ => ℕ) v k = w.val.val
      have he : k = a := hp.symm.trans hf.symm
      calc
        Fin.snoc (α := fun _ => ℕ) v k = Fin.snoc (α := fun _ => ℕ) v a :=
          congrArg (Fin.snoc (α := fun _ => ℕ) v) he
        _ = w.val.val := Fin.snoc_init_self _
    · have hn : a ∈ used v := by
        rw [used_range hl, Finset.mem_range]
        exact ho.trans_le (threshold_le _ _)
      rw [Finset.insert_eq_of_mem hn] at hw
      refine ⟨Sum.inl (⟨a, hw ▸ ho⟩, ⟨⟨v,hl⟩,hw⟩), Subtype.ext (Subtype.ext ?_)⟩
      exact Fin.snoc_init_self w.val.val

theorem word_nonempty_count {m t k : ℕ} (w : WordFiber m (t+1) k) : 0 < k :=
  w.property ▸ Finset.card_pos.mpr ⟨_, mem_used.mpr ⟨Fin.last t,rfl⟩⟩

def emptyWord (m : ℕ) : WordFiber m 0 0 :=
  ⟨⟨Fin.elim0, trivial⟩, by simp⟩

theorem word_zero_unique (m : ℕ) (w : WordFiber m 0 0) : w = emptyWord m :=
  Subtype.ext (Subtype.ext (funext (fun i => Fin.elim0 i)))

theorem word_zero_length_empty {m k : ℕ} (hk : 0 < k) : IsEmpty (WordFiber m 0 k) :=
  ⟨fun w => (Nat.lt_irrefl 0) (hk.trans_le (word_card_le_length w))⟩

/-- Counting canonical words by the actual last move gives the printed Stirling recurrence. -/
theorem card_word_eq_stirling (m t k : ℕ) :
    Fintype.card (WordFiber m t k) = stirling m t k := by
  induction t generalizing k with
  | zero =>
    cases k with
    | zero =>
      let : Unique (WordFiber m 0 0) := ⟨⟨emptyWord m⟩, word_zero_unique m⟩
      rw [Fintype.card_unique]
      rfl
    | succ k =>
      let := word_zero_length_empty (m := m) (Nat.zero_lt_succ k)
      rw [Fintype.card_of_isEmpty]
      rfl
  | succ t ih =>
    cases k with
    | zero =>
      let : IsEmpty (WordFiber m (t+1) 0) := ⟨fun w => (Nat.lt_irrefl 0) (word_nonempty_count w)⟩
      rw [Fintype.card_of_isEmpty]
      rfl
    | succ k =>
      rw [← Fintype.card_congr (lastMoveEquiv m t k), Fintype.card_sum, Fintype.card_prod,
        Fintype.card_fin, ih, ih]
      rfl

theorem card_urn_eq_stirling {m : ℕ} (hm : 0 < m) (t k : ℕ) :
    Fintype.card (U m t k) = stirling m t k :=
  (Fintype.card_congr (fiberEquivWord hm (le_refl t))).trans (card_word_eq_stirling m t k)


open scoped BigOperators

theorem card_colors (m n : ℕ) (J : Finset (Fin n)) :
    Fintype.card (Colors m n J) = m^(n-J.card) := by
  rw [Fintype.card_fun, Fintype.card_subtype_compl (fun i => i ∈ J),
    Fintype.card_fin, Fintype.card_fin, Fintype.card_coe J]

theorem group_subsets_by_card (n : ℕ) (f : ℕ → ℕ) :
    (∑ J : Finset (Fin n), f J.card) =
      ∑ j ∈ Finset.range (n+1), n.choose j * f j := by
  classical
  have hmaps (J : Finset (Fin n)) (_ : J ∈ Finset.univ) :
      J.card ∈ Finset.range (n+1) := by
    apply Finset.mem_range.mpr
    have h := Finset.card_le_card (Finset.subset_univ J)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun J => f J.card)]
  apply Finset.sum_congr rfl
  intro j _
  have hfilter : (Finset.univ.filter (fun J : Finset (Fin n) => J.card = j)) =
      (Finset.univ : Finset (Fin n)).powersetCard j := by
    ext J
    simp [Finset.mem_powersetCard]
  calc
    ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))) with J.card = j, f J.card =
        ∑ _J ∈ (Finset.univ : Finset (Fin n)).powersetCard j, f j := by
      apply Finset.sum_congr hfilter
      intro J hJ
      rw [(Finset.mem_powersetCard.mp hJ).2]
    _ = n.choose j * f j := by
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rfl

/-- Taking cardinalities of the exhibited first-urn equivalence and grouping its payload. -/
theorem shift_nat {m : ℕ} (hm : 0 < m) (n r : ℕ) :
    stirling m (n+m) (m+r) =
      ∑ j ∈ Finset.range (n+1), n.choose j * m^(n-j) * stirling m j r := by
  classical
  have h := Fintype.card_congr (firstUrnEquiv (m := m) (n := n) (r := r) hm)
  change Fintype.card (U m (n+m) (m+r)) =
    Fintype.card (Σ J : Finset (Fin n), Colors m n J × U m J.card r) at h
  rw [card_urn_eq_stirling hm, Fintype.card_sigma] at h
  calc
    stirling m (n+m) (m+r) =
        ∑ J : Finset (Fin n), m^(n-J.card) * stirling m J.card r := by
      simpa only [Fintype.card_prod, card_colors, card_urn_eq_stirling hm] using h
    _ = _ := by
      simpa only [mul_assoc] using group_subsets_by_card n (fun j => m^(n-j) * stirling m j r)

/-- Equation (7.2), including the negative residual columns of Definition 7.1. -/
theorem shift_7_2 {m : ℕ} (hm : 0 < m) (n k : ℕ) :
    S m (n+m) k =
      ∑ j ∈ Finset.range (n+1), n.choose j * m^(n-j) * S m j ((k : ℤ) - m) := by
  by_cases h : k < m
  · let : IsEmpty (U m (n+m) k) := below_first_urn hm h
    have hzero := card_urn_eq_stirling hm (n+m) k
    rw [Fintype.card_of_isEmpty] at hzero
    rw [S_nat, ← hzero]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hneg : (k : ℤ) - m < 0 := by omega
    simp [S, hneg]
  · let r := k - m
    have hk : k = m+r := by dsimp [r]; omega
    have hr : (k : ℤ) - m = (r : ℤ) := by omega
    rw [hr, S_nat, hk]
    simp only [S_nat]
    exact shift_nat hm n r


/-! ## Boundary cases -/

/-- At capacity one, the legal move is exactly the ordinary zero-based restricted-growth rule. -/
theorem capacity_one_legal {t : ℕ} (x : Fin t → ℕ) :
    Legal 1 x ↔ ∀ i : Fin t, x i ≤ (before x i.val).card := by
  rw [legal_iff_moves]
  simp only [Move, threshold, Nat.div_one, Nat.one_mul, le_iff_eq_or_lt]

/-- At capacity one, the first urn is the block containing the initial marble. -/
theorem capacity_one_first_block {n : ℕ} (w : Word 1 (1+n)) (i : Fin (1+n)) :
    w.val i / 1 = w.val ((0 : Fin 1).castAdd n) / 1 ↔ w.val i = 0 := by
  rw [forced_prefix w.property (0 : Fin 1)]
  simp

theorem capacity_one_color_unique {n : ℕ} (J : Finset (Fin n)) :
    Subsingleton (Colors 1 n J) :=
  inferInstance

theorem capacity_one_stirling (t k : ℕ) : stirling 1 t k = Nat.stirlingSecond t k := by
  induction t generalizing k with
  | zero =>
    cases k <;> rfl
  | succ t ih =>
    cases k with
    | zero => rw [stirling, Nat.stirlingSecond_succ_zero]
    | succ k =>
      rw [stirling, Nat.stirlingSecond_succ_succ, ih, ih]
      simp [threshold, Nat.add_comm]

/-- With no tail positions, the payload index and the color function have empty domains. -/
theorem zero_tail_selected (J : Finset (Fin 0)) : J = ∅ := by
  ext i
  exact Fin.elim0 i

@[instance_reducible] def zero_tail_colors (m : ℕ) (J : Finset (Fin 0)) :
    Unique (Colors m 0 J) :=
  ⟨⟨fun i => Fin.elim0 i.val⟩, fun _ => funext (fun i => Fin.elim0 i.val)⟩

@[instance_reducible] noncomputable def zero_length_quotient_unique {m : ℕ} (hm : 0 < m) : Unique (U m 0 0) := by
  letI : Unique (WordFiber m 0 0) := ⟨⟨emptyWord m⟩, word_zero_unique m⟩
  exact (fiberEquivWord hm (le_refl 0)).unique

@[instance_reducible] noncomputable def zero_tail_source_unique {m : ℕ} (hm : 0 < m) : Unique (U m (0+m) m) := by
  letI : Unique (Payload m 0 0) := by
    let c := zero_tail_colors m (∅ : Finset (Fin 0))
    let u : Unique (U m (∅ : Finset (Fin 0)).card 0) := by
      rw [Finset.card_empty]
      exact zero_length_quotient_unique hm
    refine ⟨⟨⟨∅, c.default, u.default⟩⟩, ?_⟩
    rintro ⟨J, d⟩
    have hJ := zero_tail_selected J
    subst J
    exact congrArg (Sigma.mk ∅) (Prod.ext (c.uniq _) (u.uniq _))
  have e := firstUrnEquiv (n := 0) (r := 0) hm
  exact e.unique

theorem zero_tail_source_empty {m k : ℕ} (hm : 0 < m) (hk : k ≠ m) :
    IsEmpty (U m (0+m) k) := by
  rcases lt_or_gt_of_ne hk with h | h
  · exact below_first_urn hm h
  · exact beyond_length hm (by simpa using h)

theorem zero_tail_residual_empty {m r : ℕ} (hm : 0 < m) (hr : 0 < r) :
    IsEmpty (Payload m 0 r) := by
  refine ⟨fun d => ?_⟩
  have hc : d.1.card = 0 := by rw [zero_tail_selected d.1, Finset.card_empty]
  exact (beyond_length (k := r) hm (by rwa [hc])).false d.2.2

theorem beyond_length_payload_empty {m n r : ℕ} (hm : 0 < m) (hr : n < r) :
    IsEmpty (Payload m n r) := by
  refine ⟨fun d => ?_⟩
  have hJ : d.1.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ d.1)
  exact (beyond_length hm (hJ.trans_lt hr)).false d.2.2

theorem below_first_urn_payload_empty {m n k : ℕ} (hk : k < m) :
    IsEmpty (Σ J : Finset (Fin n), Colors m n J × SignedU m J.card ((k : ℤ) - m)) :=
  ⟨fun d => (signed_negative_empty (by omega)).false d.2.2⟩

/-- Old slots of any full urn remain legal, even if another urn has only started. -/
theorem full_urn_reuse {A m : ℕ} (s : Finset (Address A m)) (a : Address A m)
    (hf : Full s a.1) : RawMove s a :=
  ⟨fun _ => hf, fun h => (h ⟨a.2, hf a.2⟩).elim⟩

private def decideLegal (m : ℕ) : {t : ℕ} → (x : Fin t → ℕ) → Decidable (Legal m x)
  | 0, _ => isTrue trivial
  | t+1, x => by
    change Decidable (Legal m (Fin.init x) ∧
      Move m (used (Fin.init x)).card (x (Fin.last t)))
    letI := decideLegal m (Fin.init x)
    unfold Move
    infer_instance

/-- At capacity two, the fourth move can revisit urn zero while urn one is incomplete. -/
theorem partial_example :
    Legal 2 (![0,1,2,0,3] : Fin 5 → ℕ) ∧
      before (![0,1,2,0,3] : Fin 5 → ℕ) 3 = Finset.range 3 := by
  constructor
  · exact @of_decide_eq_true _ (decideLegal 2 (![0,1,2,0,3] : Fin 5 → ℕ)) rfl
  · decide


/-! ## First-use ranks and the raw addresses retained by deletion -/

/-- Two marble positions have the same canonical rank exactly when they use the same raw slot. -/
theorem normalize_pair_eq_iff {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (x : Raw A m t)
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
theorem normalize_at_first_use {A m t : ℕ} (hm : 0 < m) (ht : t ≤ A) (x : Raw A m t)
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


/-- In column `m`, every tail marble goes back to the first urn. -/
theorem zero_residual_selected {m n : ℕ} (hm : 0 < m) (d : Payload m n 0) :
    d.1 = ∅ := by
  apply Finset.card_eq_zero.mp
  by_contra h
  let w := fiberEquivWord hm (le_refl d.1.card) d.2.2
  let i : Fin d.1.card := ⟨0, Nat.pos_of_ne_zero h⟩
  have hp : 0 < (used w.val.val).card := Finset.card_pos.mpr ⟨_, mem_used.mpr ⟨i,rfl⟩⟩
  have h0 : (used w.val.val).card = 0 := w.property
  rw [h0] at hp
  exact (Nat.lt_irrefl 0) hp

/-- Selection for deletion is exactly avoidance of the raw urn containing marble one. -/
theorem selected_iff_avoids_first_urn {A m n : ℕ} (hm : 0 < m) (ht : m+n ≤ A)
    (x : Raw A m (m+n)) (i : Fin n) :
    i ∈ (splitTail (normalize hm ht x).val).1 ↔
      (x.val (Fin.natAdd m i)).1 ≠ (x.val ((⟨0,hm⟩ : Fin m).castAdd n)).1 := by
  let w := normalize hm ht x
  have he := normalize_urn_eq_iff hm ht x (Fin.natAdd m i) ((⟨0,hm⟩ : Fin m).castAdd n)
  have hn : (¬ w.val (Fin.natAdd m i) / m = w.val ((⟨0, hm⟩ : Fin m).castAdd n) / m) ↔
      _ := not_congr he
  refine Iff.trans ?_ hn
  rw [forced_prefix w.property]
  simp [splitTail, Nat.div_eq_zero_iff_lt hm]
  rfl


/-- The first `m` raw marbles use exactly all the slots of their common urn. -/
theorem raw_forced_used {A m n : ℕ} (hm : 0 < m) (ht : m+n ≤ A)
    (x : Raw A m (m+n)) :
    used (fun i : Fin m => x.val (i.castAdd n)) =
      Finset.univ.image (fun c : Fin m => ((x.val ((⟨0,hm⟩ : Fin m).castAdd n)).1, c)) := by
  let w := normalize hm ht x
  let i₀ : Fin m := ⟨0,hm⟩
  obtain ⟨e, he⟩ := replay_normalize_orbit hm ht x
  have hrep (i : Fin m) :
      replay hm ht w (i.castAdd n) = ((replay hm ht w (i₀.castAdd n)).1, i) := by
    apply Prod.ext
    · apply Fin.ext
      change w.val (i.castAdd n) / m = w.val (i₀.castAdd n) / m
      rw [forced_prefix w.property, forced_prefix w.property]
      exact (Nat.div_eq_of_lt i.isLt).trans (Nat.div_eq_of_lt i₀.isLt).symm
    · apply Fin.ext
      change w.val (i.castAdd n) % m = i.val
      rw [forced_prefix w.property, Nat.mod_eq_of_lt i.isLt]
  ext a
  rw [mem_used, Finset.mem_image]
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨(x.val (i.castAdd n)).2, Finset.mem_univ _, Prod.ext ?_ rfl⟩
    rw [← he (i.castAdd n), ← he (i₀.castAdd n)]
    exact (congrArg (fun b => (e.apply b).1) (hrep i)).symm
  · rintro ⟨c,_,rfl⟩
    let u := (replay hm ht w (i₀.castAdd n)).1
    obtain ⟨d, hd⟩ := (e.slot u).surjective c
    refine ⟨d, ?_⟩
    rw [← he (d.castAdd n), hrep d, ← he (i₀.castAdd n)]
    exact Prod.ext rfl hd

/-- The retained tail has exactly the distinct raw addresses outside the first urn. -/
theorem retained_raw_used {A m n : ℕ} (hm : 0 < m) (ht : m+n ≤ A)
    (x : Raw A m (m+n)) :
    let J := (splitTail (normalize hm ht x).val).1
    let first := (x.val ((⟨0,hm⟩ : Fin m).castAdd n)).1
    used (fun j : Fin J.card => x.val (Fin.natAdd m ((selectedOrder J) j).val)) =
      (used x.val).filter (fun a => a.1 ≠ first) := by
  dsimp only
  let J := (splitTail (normalize hm ht x).val).1
  let i₀ : Fin m := ⟨0,hm⟩
  let first := (x.val (i₀.castAdd n)).1
  have hfirst (i : Fin m) : (x.val (i.castAdd n)).1 = first := by
    apply (normalize_urn_eq_iff hm ht x _ _).1
    rw [forced_prefix (normalize hm ht x).property, forced_prefix (normalize hm ht x).property]
    exact (Nat.div_eq_of_lt i.isLt).trans (Nat.div_eq_of_lt i₀.isLt).symm
  ext a
  rw [Finset.mem_filter, mem_used, mem_used]
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨⟨_, rfl⟩, (selected_iff_avoids_first_urn hm ht x _).1 ((selectedOrder J) j).property⟩
  · rintro ⟨⟨i,hi⟩,hna⟩
    revert hi
    refine Fin.addCases
      (motive := fun i => x.val i = a →
        ∃ j : Fin J.card, x.val (Fin.natAdd m ((selectedOrder J) j).val) = a) ?_ ?_ i
    · intro j hj
      exact (hna ((congrArg Prod.fst hj).symm.trans (hfirst j))).elim
    · intro j hj
      have hJ : j ∈ J := (selected_iff_avoids_first_urn hm ht x j).2
        (fun he => hna ((congrArg Prod.fst hj).symm.trans he))
      let k := (selectedOrder J).symm ⟨j,hJ⟩
      have hk : ((selectedOrder J) k).val = j :=
        congrArg Subtype.val ((selectedOrder J).apply_symm_apply ⟨j,hJ⟩)
      exact ⟨k, (congrArg (x.val ∘ Fin.natAdd m) hk).trans hj⟩

/-- Removing the first urn removes exactly `m` distinct raw addresses. -/
theorem retained_raw_count {A m n : ℕ} (hm : 0 < m) (ht : m+n ≤ A)
    (x : Raw A m (m+n)) :
    let J := (splitTail (normalize hm ht x).val).1
    m + (used (fun j : Fin J.card => x.val (Fin.natAdd m ((selectedOrder J) j).val))).card =
      (used x.val).card := by
  dsimp only
  rw [retained_raw_used hm ht x]
  let first := (x.val ((⟨0,hm⟩ : Fin m).castAdd n)).1
  let f := fun c : Fin m => (first,c)
  have hf : Function.Injective f := fun _ _ h => congrArg Prod.snd h
  have hfull : (used x.val).filter (fun a => a.1 = first) = Finset.univ.image f := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨a.2, Prod.ext h.2.symm rfl⟩
    · rintro ⟨c,rfl⟩
      refine ⟨?_,rfl⟩
      have hc : f c ∈ Finset.univ.image f := Finset.mem_image_of_mem _ (Finset.mem_univ c)
      have hpre := raw_forced_used hm ht x
      change used (fun i : Fin m => x.val (i.castAdd n)) = Finset.univ.image f at hpre
      rw [← hpre, mem_used] at hc
      obtain ⟨i,hi⟩ := hc
      exact mem_used.mpr ⟨i.castAdd n, hi⟩
  let s := (used x.val).filter (fun a => a.1 = first)
  let t := (used x.val).filter (fun a => a.1 ≠ first)
  have hd : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2
  have hu : s ∪ t = used x.val := by
    ext a
    by_cases ha : a.1 = first <;> simp [s, t, ha]
  have hc : s.card = m := by
    change ((used x.val).filter (fun a => a.1 = first)).card = m
    rw [hfull, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  calc
    m + t.card = s.card + t.card := congrArg (· + t.card) hc.symm
    _ = (s ∪ t).card := (Finset.card_union_of_disjoint hd).symm
    _ = (used x.val).card := congrArg Finset.card hu

end PopovUrnShift
