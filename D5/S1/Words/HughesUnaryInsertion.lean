/- GID: D5/S1/Words/HughesUnaryInsertion
   generality: G
   mirror-B: D5/B/S1/Words/HughesUnaryInsertion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native unary insertion minima from occurrence-indexed gap masses. -/

import D5.S1.Words.UnaryGapWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.HughesUnaryInsertion

open D5.S1.Words.HughesBlockExchange
open D5.S1.Words.UnaryGapWords
open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder

variable {α : Type*}

/-- Positive extra mass, including the two outer gaps in the inserted orientation. -/
def occupied (e : List Nat) : Nat := e.countP (0 < ·)

/-- Actual shuffle membership, in the original ordered native mask semantics. -/
def Sh (u v : List α) : Set (List α) := {w | ∃ M, ValidMask u v w M}

/-- Natural attained minimum degrees; invalid outputs contribute no value. -/
def spectrum (u v : List α) : Set Nat :=
  {r | ∃ w, w ∈ Sh u v ∧ degree u v w = (r : WithTop Nat)}

/-- The unary inserted source does not change the occurrence-indexed spine. -/
theorem inserted_gap_iff (a : α) (m : Nat) (cs : List α)
    (h : List Nat) (w : List α) (ha : ∀ c ∈ cs, c ≠ a)
    (hh : h.length = cs.length + 1) :
    w ∈ Sh (List.replicate m a) (gap a cs h) ↔
    ∃! e : List Nat, e.length = h.length ∧ e.sum = m ∧
      w = gap a cs (List.zipWith (· + ·) h e) := by
  rw [← native_gap_iff a .second m cs h w ha hh]
  simp only [Sh, Set.mem_setOf_eq, mask_projections]
  constructor <;> rintro ⟨M, hl, h1, h2⟩ <;> exact ⟨M, hl, h2, h1⟩

/-- In the reverse orientation it is the base mass that enlarges the gaps. -/
theorem reverse_gap_iff (a : α) (n : Nat) (cs : List α)
    (h : List Nat) (w : List α) (ha : ∀ c ∈ cs, c ≠ a)
    (hh : h.length = cs.length + 1) :
    w ∈ Sh (gap a cs h) (List.replicate n a) ↔
    ∃! e : List Nat, e.length = h.length ∧ e.sum = n ∧
      w = gap a cs (List.zipWith (· + ·) h e) := by
  rw [← native_gap_iff a .first n cs h w ha hh]
  simp only [Sh, Set.mem_setOf_eq, mask_projections, ↓reduceIte]

private theorem rho_positive (b : List Side) (hb : 0 < b.count .first) : 0 < rho b := by
  induction b with
  | nil => simp at hb
  | cons t b ih =>
    cases t with
    | first => simp only [rho_starts, starts, step]; simp; omega
    | second =>
      simpa [rho_starts, starts, step] using ih (by simpa using hb)

private theorem rho_separated (b M : List Side) :
    rho (b ++ .second :: M) = rho b + rho M := by
  rw [rho_starts, starts_append]
  cases h : lastSide .second b <;> simp [rho_starts, starts, step]

/-- Each occupied gap needs its own inserted run in every positional mask. -/
theorem inserted_trace_lower (a : α) {cs : List α} {h e : List Nat}
    {w : List α} {M : List Side} (ht : Trace a .second cs h e w M) :
    occupied e ≤ rho M := by
  have local_lower (b : List Side) :
      (if 0 < b.count .first then 1 else 0) ≤ rho b := by
    by_cases hb : 0 < b.count .first
    · have hp := rho_positive b hb
      simp only [hb, ite_true]
      omega
    · simp [hb]
  induction ht with
  | last b =>
    simpa [occupied] using local_lower b
  | @next b c hc cs h e w M tail ih =>
    rw [rho_separated]
    simpa [occupied, List.countP_cons, Nat.add_comm] using
      Nat.add_le_add (local_lower b) ih


private theorem starts_bracket (p : Side) (b M : List Side) :
    starts p (b ++ .first :: M) =
      starts p (b ++ [.first]) + starts .first M := by
  simp [starts_append, starts, Nat.add_assoc]

private theorem bracket_positive (b : List Side) :
    0 < starts .second (b ++ [.first]) := by
  have hp := rho_positive (b ++ [Side.first]) (by simp)
  rwa [rho_starts] at hp

private theorem bracket_internal_lower (b : List Side) :
    (if 0 < b.count .second then 1 else 0) ≤ starts .first (b ++ [.first]) := by
  induction b with
  | nil => simp [starts, step]
  | cons t b ih =>
    cases t with
    | first => simpa [starts, step] using ih
    | second =>
      have hp := bracket_positive b
      simp [starts, step]
      omega

/-- Only extra masses strictly between two non-unary occurrences count here. -/
def internalOccupied (e : List Nat) : Nat := occupied e.tail.dropLast

private theorem reverse_tail_lower (a : α) {cs : List α} {h e : List Nat}
    {w : List α} {M : List Side} (ht : Trace a .first cs h e w M) :
    occupied e.dropLast ≤ starts .first M := by
  induction ht with
  | last b => simp [occupied]
  | @next b c hc cs h e w M tail ih =>
    have hn : e ≠ [] := by
      have he := (trace_projections a .first tail).2.2.1
      have hh := (trace_projections a .first tail).2.1
      intro hz
      simp [hz] at he
      omega
    rw [starts_bracket, List.dropLast_cons_of_ne_nil hn]
    have hb := bracket_internal_lower b
    simp only [occupied, List.countP_cons] at *
    split_ifs at hb ⊢ <;> simp_all <;> omega

/-- All positive internal gaps already separate forced inserted-source groups. -/
theorem reverse_trace_lower (a : α) {cs : List α} {h e : List Nat}
    {w : List α} {M : List Side} (ht : Trace a .first cs h e w M)
    (hc : cs ≠ []) : 1 + internalOccupied e ≤ rho M := by
  cases ht with
  | last b => exact (hc rfl).elim
  | next b c hca tail =>
    have htail := reverse_tail_lower a tail
    have hb := bracket_positive b
    rw [rho_starts, starts_bracket]
    simpa [internalOccupied] using Nat.add_le_add hb htail


private theorem starts_rep (p q : Side) (n : Nat) :
    starts p (List.replicate n q) = if n = 0 then 0 else step p q := by
  by_cases hn : n = 0
  · simp [hn, starts]
  · simpa [hn] using starts_pure p q n (by omega)

private theorem last_rep (p q : Side) (n : Nat) :
    lastSide p (List.replicate n q) = if n = 0 then p else q := by
  cases n <;> simp [lastSide, List.getLast?_replicate]

private theorem grouped_gap_runs (n k : Nat) :
    rho (List.replicate n .second ++ List.replicate k .first) =
      if 0 < k then 1 else 0 := by
  by_cases hn : n = 0 <;> by_cases hk : k = 0 <;>
    simp [rho_starts, starts_append, starts_rep, last_rep, starts, step, hn, hk] <;> omega

private theorem reverse_gap_starts (p : Side) (n k : Nat) :
    starts p (List.replicate k .second ++ List.replicate n .first ++ [.first]) =
      if p = .second then 1 else if 0 < k then 1 else 0 := by
  by_cases hn : n = 0 <;> by_cases hk : k = 0 <;> cases p <;>
    simp [List.append_assoc, starts_append, starts_rep, last_rep, starts, step, hn, hk] <;>
    omega

private theorem reverse_last_starts (n k : Nat) :
    starts .first (List.replicate n .first ++ List.replicate k .second) = 0 := by
  by_cases hn : n = 0 <;> by_cases hk : k = 0 <;>
    simp [starts_append, starts_rep, last_rep, starts, step, hn, hk]

private theorem grouped_inserted_runs (cs : List α) (h e : List Nat)
    (hh : h.length = cs.length + 1) (he : e.length = h.length) :
    rho (grouped .second cs h e) = occupied e := by
  induction cs generalizing h e with
  | nil =>
    obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hh
    obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp (by simpa using he)
    simpa [grouped, occupied] using grouped_gap_runs n k
  | cons c cs ih =>
    cases h with
    | nil => simp at hh
    | cons n hs =>
      cases e with
      | nil => simp at he
      | cons k es =>
        have hi := ih hs es (by simpa using hh) (by simpa using he)
        simp only [grouped, List.headD_cons, List.tail_cons, reduceCtorEq, ↓reduceIte]
        rw [rho_separated, grouped_gap_runs, hi]
        simp [occupied, List.countP_cons, Nat.add_comm]

private theorem grouped_reverse_tail (cs : List α) (h e : List Nat)
    (hh : h.length = cs.length + 1) (he : e.length = h.length) :
    starts .first (grouped .first cs h e) = occupied e.dropLast := by
  induction cs generalizing h e with
  | nil =>
    obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hh
    obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp (by simpa using he)
    simp [grouped, reverse_last_starts, occupied]
  | cons c cs ih =>
    cases h with
    | nil => simp at hh
    | cons n hs =>
      cases e with
      | nil => simp at he
      | cons k es =>
        have hhs : hs.length = cs.length + 1 := by simpa using hh
        have hes : es.length = hs.length := by simpa using he
        have hn : es ≠ [] := by intro hz; simp [hz] at hes; omega
        have hi := ih hs es hhs hes
        simp only [grouped, List.headD_cons, List.tail_cons, ↓reduceIte]
        rw [starts_bracket, reverse_gap_starts, hi, List.dropLast_cons_of_ne_nil hn]
        simp [occupied, List.countP_cons, Nat.add_comm]

private theorem grouped_reverse_runs (cs : List α) (h e : List Nat)
    (hh : h.length = cs.length + 1) (he : e.length = h.length) (hc : cs ≠ []) :
    rho (grouped .first cs h e) = 1 + internalOccupied e := by
  cases cs with
  | nil => exact (hc rfl).elim
  | cons c cs =>
    cases h with
    | nil => simp at hh
    | cons n hs =>
      cases e with
      | nil => simp at he
      | cons k es =>
        have hi := grouped_reverse_tail cs hs es (by simpa using hh) (by simpa using he)
        simp only [grouped, List.headD_cons, List.tail_cons, ↓reduceIte]
        rw [rho_starts, starts_bracket, reverse_gap_starts, hi]
        simp [internalOccupied]

private theorem trace_native (a : α) (q : Side) {cs : List α} {h e : List Nat}
    {w : List α} {M : List Side} (ht : Trace a q cs h e w M) :
    (q = .second → ValidMask (List.replicate e.sum a) (gap a cs h) w M) ∧
    (q = .first → ValidMask (gap a cs h) (List.replicate e.sum a) w M) := by
  obtain ⟨hl, _, _, _, hp, hu, _⟩ := trace_projections a q ht
  constructor
  · intro hq
    subst q
    apply (mask_projections _ _ _ _).mpr
    exact ⟨hl, hu, hp⟩
  · intro hq
    subst q
    apply (mask_projections _ _ _ _).mpr
    exact ⟨hl, hp, hu⟩

private theorem native_trace_inserted (a : α) (m : Nat) (cs : List α) (h e : List Nat)
    (w : List α) (M : List Side) (ha : ∀ c ∈ cs, c ≠ a)
    (hh : h.length = cs.length + 1) (he : e.length = h.length)
    (hw : w = gap a cs (List.zipWith (· + ·) h e))
    (hM : ValidMask (List.replicate m a) (gap a cs h) w M) :
    Trace a .second cs h e w M := by
  obtain ⟨hl, hu, hv⟩ := (mask_projections _ _ _ _).mp hM
  apply trace_of_projections a .second cs h e w M ha hh he hw hl hv
  simp only [reduceCtorEq, ↓reduceIte, hu]
  intro x hx
  exact (List.mem_replicate.mp hx).2

private theorem native_trace_reverse (a : α) (n : Nat) (cs : List α) (h e : List Nat)
    (w : List α) (M : List Side) (ha : ∀ c ∈ cs, c ≠ a)
    (hh : h.length = cs.length + 1) (he : e.length = h.length)
    (hw : w = gap a cs (List.zipWith (· + ·) h e))
    (hM : ValidMask (gap a cs h) (List.replicate n a) w M) :
    Trace a .first cs h e w M := by
  obtain ⟨hl, hu, hv⟩ := (mask_projections _ _ _ _).mp hM
  apply trace_of_projections a .first cs h e w M ha hh he hw hl hu
  simp only [↓reduceIte, hv]
  intro x hx
  exact (List.mem_replicate.mp hx).2

/-- The lower bound and this actual attaining mask identify the native minimum. -/
theorem inserted_degree (a : α) (m : Nat) (cs : List α) (h e : List Nat)
    (ha : ∀ c ∈ cs, c ≠ a) (hh : h.length = cs.length + 1)
    (he : e.length = h.length) (hm : e.sum = m) :
    let w := gap a cs (List.zipWith (· + ·) h e)
    IsMinimumMask (List.replicate m a) (gap a cs h) w (grouped .second cs h e)
      (occupied e) ∧ degree (List.replicate m a) (gap a cs h) w =
        (occupied e : WithTop Nat) := by
  dsimp only
  have ht := trace_construct a .second cs h e ha hh he
  have hv := (trace_native a .second ht).1 rfl
  rw [hm] at hv
  have hr := grouped_inserted_runs cs h e hh he
  have hlo : ∀ N, ValidMask (List.replicate m a) (gap a cs h)
      (gap a cs (List.zipWith (· + ·) h e)) N → occupied e ≤ rho N := by
    intro N hN
    exact inserted_trace_lower a
      (native_trace_inserted a m cs h e _ N ha hh he rfl hN)
  refine ⟨⟨hv, hr, hlo⟩, le_antisymm ?_ ?_⟩
  · simpa [degree, hr] using minRuns_le _ _ hv
  · apply (le_minRuns _ _).mpr
    intro N hN
    exact_mod_cast hlo N hN

/-- Outer base masses are retained in the word and excluded only from the count. -/
theorem reverse_degree (a : α) (n : Nat) (cs : List α) (h e : List Nat)
    (ha : ∀ c ∈ cs, c ≠ a) (hh : h.length = cs.length + 1)
    (he : e.length = h.length) (hn : e.sum = n) (hc : cs ≠ []) :
    let w := gap a cs (List.zipWith (· + ·) h e)
    IsMinimumMask (gap a cs h) (List.replicate n a) w (grouped .first cs h e)
      (1 + internalOccupied e) ∧ degree (gap a cs h) (List.replicate n a) w =
        ((1 + internalOccupied e : Nat) : WithTop Nat) := by
  dsimp only
  have ht := trace_construct a .first cs h e ha hh he
  have hv := (trace_native a .first ht).2 rfl
  rw [hn] at hv
  have hr := grouped_reverse_runs cs h e hh he hc
  have hlo : ∀ N, ValidMask (gap a cs h) (List.replicate n a)
      (gap a cs (List.zipWith (· + ·) h e)) N → 1 + internalOccupied e ≤ rho N := by
    intro N hN
    exact reverse_trace_lower a
      (native_trace_reverse a n cs h e _ N ha hh he rfl hN) hc
  refine ⟨⟨hv, hr, hlo⟩, le_antisymm ?_ ?_⟩
  · simpa [degree, hr] using minRuns_le _ _ hv
  · apply (le_minRuns _ _).mpr
    intro N hN
    exact_mod_cast hlo N hN


private theorem both_unary (a : α) (h n : Nat) (hh : 0 < h) :
    degree (List.replicate h a) (List.replicate n a) (List.replicate (h + n) a) =
      ((1 : Nat) : WithTop Nat) := by
  have ht := trace_construct a .first [] [h] [n] (by simp) rfl rfl
  have hv := (trace_native a .first ht).2 rfl
  have hv' : ValidMask (List.replicate h a) (List.replicate n a)
      (List.replicate (h + n) a)
      (List.replicate h .first ++ List.replicate n .second) := by
    simpa [gap, grouped] using hv
  have hr : rho (List.replicate h .first ++ List.replicate n .second) = 1 := by
    by_cases hn : n = 0 <;>
      simp [rho_starts, starts_append, starts_rep, last_rep, starts, step, hn,
        Nat.ne_of_gt hh]
  apply le_antisymm
  · simpa [degree, hr] using minRuns_le _ _ hv'
  · apply (le_minRuns _ _).mpr
    intro N hN
    have hc := hN.1.1
    change N.count .first = (List.replicate h a).length at hc
    have hp : 0 < N.count .first := by simpa [hc] using hh
    have hpos := rho_positive N hp
    exact_mod_cast (show 1 ≤ rho N by omega)

/-- This includes no separators and a single separator, with both outer masses. -/
theorem reverse_degree_all (a : α) (n : Nat) (cs : List α) (h e : List Nat)
    (ha : ∀ c ∈ cs, c ≠ a) (hh : h.length = cs.length + 1)
    (he : e.length = h.length) (hn : e.sum = n) (hu : gap a cs h ≠ []) :
    degree (gap a cs h) (List.replicate n a)
      (gap a cs (List.zipWith (· + ·) h e)) =
      ((if cs = [] then 1 else 1 + internalOccupied e : Nat) : WithTop Nat) := by
  by_cases hc : cs = []
  · subst cs
    obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hh
    obtain ⟨m, rfl⟩ := List.length_eq_one_iff.mp (by simpa using he)
    have hk : 0 < k := by
      by_contra hle
      have hk0 : k = 0 := by omega
      simp [gap, hk0] at hu
    have hmn : m = n := by simpa using hn
    subst n
    simpa [gap] using both_unary a k m hk
  · simpa [hc] using (reverse_degree a n cs h e ha hh he hn hc).2


private theorem occupied_le_sum (e : List Nat) : occupied e ≤ e.sum := by
  induction e with
  | nil => simp [occupied]
  | cons x e ih =>
    simp only [occupied, List.countP_cons, List.sum_cons] at *
    by_cases hx : 0 < x <;> simp [hx] <;> omega

private theorem occupied_pos (e : List Nat) : 0 < occupied e ↔ 0 < e.sum := by
  simp [occupied, List.countP_pos_iff, List.sum_pos_iff_exists_pos_nat]

private theorem inserted_masses (L m r : Nat) (hr : 1 ≤ r) (hm : r ≤ m)
    (hL : r ≤ L) : ∃ e : List Nat, e.length = L ∧ e.sum = m ∧ occupied e = r := by
  let e := List.replicate (r - 1) 1 ++ [m - (r - 1)] ++ List.replicate (L - r) 0
  have hp : 0 < m - (r - 1) := by omega
  refine ⟨e, ?_, ?_, ?_⟩
  · simp only [e, List.length_append, List.length_replicate, List.length_singleton]
    omega
  · simp [e]
    omega
  · simp [e, occupied, List.countP_append, List.countP_replicate, hp]
    omega

/-- Every positive number up to the two independent bounds is attained. -/
theorem inserted_spectrum (a : α) (m : Nat) (cs : List α) (h : List Nat)
    (ha : ∀ c ∈ cs, c ≠ a) (hh : h.length = cs.length + 1) (hm : 0 < m) :
    spectrum (List.replicate m a) (gap a cs h) =
      {r | 1 ≤ r ∧ r ≤ min m (cs.length + 1)} := by
  ext r
  constructor
  · rintro ⟨w, hsw, hd⟩
    obtain ⟨e, ⟨he, hs, hw⟩, _⟩ := (inserted_gap_iff a m cs h w ha hh).mp hsw
    have hg := (inserted_degree a m cs h e ha hh he hs).2
    rw [← hw] at hg
    have hr : r = occupied e := by exact_mod_cast hd.symm.trans hg
    subst r
    have hp : 0 < occupied e := (occupied_pos e).mpr (by omega)
    have hsum := occupied_le_sum e
    have hlen : occupied e ≤ e.length := List.countP_le_length
    constructor
    · omega
    · exact le_min (by omega) (by omega)
  · rintro ⟨hr, hbound⟩
    obtain ⟨e, he, hs, hc⟩ := inserted_masses (cs.length + 1) m r hr
      ((Nat.le_min.mp hbound).1) ((Nat.le_min.mp hbound).2)
    have hel : e.length = h.length := he.trans hh.symm
    have hg := inserted_degree a m cs h e ha hh hel hs
    refine ⟨gap a cs (List.zipWith (· + ·) h e), ⟨grouped .second cs h e, hg.1.1⟩, ?_⟩
    simpa [hc] using hg.2

private theorem internal_le_occupied (e : List Nat) : internalOccupied e ≤ occupied e := by
  exact (List.dropLast_sublist (l := e.tail)).countP_le.trans (List.countP_tail_le e)

private theorem reverse_masses (s n t : Nat) (htn : t ≤ n) (hts : t ≤ s - 1) :
    ∃ e : List Nat, e.length = s + 1 ∧ e.sum = n ∧ internalOccupied e = t := by
  cases s with
  | zero =>
    have ht : t = 0 := by omega
    subst t
    exact ⟨[n], by simp, by simp, by simp [internalOccupied, occupied]⟩
  | succ s =>
    let e := (n - t) :: (List.replicate t 1 ++ List.replicate (s + 1 - t) 0)
    have hpos : 0 < s + 1 - t := by omega
    have hne : List.replicate (s + 1 - t) 0 ≠ [] := by simpa using hpos.ne'
    refine ⟨e, ?_, ?_, ?_⟩
    · simp only [e, List.length_cons, List.length_append, List.length_replicate]
      omega
    · simp [e]
      omega
    · simp [e, internalOccupied, List.dropLast_append_of_ne_nil hne, occupied,
        List.countP_append, List.countP_replicate]

/-- Base mass may be placed at either exterior end without adding an internal separator. -/
theorem reverse_spectrum (a : α) (n : Nat) (cs : List α) (h : List Nat)
    (ha : ∀ c ∈ cs, c ≠ a) (hh : h.length = cs.length + 1)
    (hu : gap a cs h ≠ []) :
    spectrum (gap a cs h) (List.replicate n a) =
      {r | 1 ≤ r ∧ r ≤ 1 + min n (cs.length - 1)} := by
  ext r
  constructor
  · rintro ⟨w, hsw, hd⟩
    obtain ⟨e, ⟨he, hs, hw⟩, _⟩ := (reverse_gap_iff a n cs h w ha hh).mp hsw
    have hg := reverse_degree_all a n cs h e ha hh he hs hu
    rw [← hw] at hg
    have hr : r = if cs = [] then 1 else 1 + internalOccupied e := by
      exact_mod_cast hd.symm.trans hg
    have hsum := (internal_le_occupied e).trans (occupied_le_sum e)
    have hlen : internalOccupied e ≤ e.length - 2 := by
      simpa [internalOccupied, occupied, Nat.sub_sub] using
        (List.countP_le_length (l := e.tail.dropLast) (p := fun x : Nat => decide (0 < x)))
    by_cases hc : cs = [] <;> simp only [hc, ite_true, ite_false] at hr
    · simp [hc, hr]
    · constructor
      · omega
      · have heq : e.length = cs.length + 1 := he.trans hh
        have hp : 0 < cs.length := List.length_pos_iff.mpr hc
        have hbound : internalOccupied e ≤ min n (cs.length - 1) :=
          le_min (by omega) (by omega)
        omega
  · rintro ⟨hr, hbound⟩
    have htn : r - 1 ≤ n := by have := (Nat.le_min.mp (show r - 1 ≤ min n (cs.length - 1) by omega)).1; omega
    have hts : r - 1 ≤ cs.length - 1 := by
      have := (Nat.le_min.mp (show r - 1 ≤ min n (cs.length - 1) by omega)).2
      omega
    obtain ⟨e, he, hs, hc⟩ := reverse_masses cs.length n (r - 1) htn hts
    have hel : e.length = h.length := he.trans hh.symm
    have ht := trace_construct a .first cs h e ha hh hel
    have hv := (trace_native a .first ht).2 rfl
    rw [hs] at hv
    refine ⟨gap a cs (List.zipWith (· + ·) h e), ⟨grouped .first cs h e, hv⟩, ?_⟩
    rw [reverse_degree_all a n cs h e ha hh hel hs hu]
    by_cases hcs : cs = []
    · have hrs : r = 1 := by simp [hcs] at hbound; omega
      simp [hcs, hrs]
    · simp only [hcs, ite_false, hc]
      congr 1
      omega

/-- Each actual gap of the trace has precisely its necessary inserted run. -/
inductive InsertedTight (a : α) : List α → List Nat → List Nat →
    List α → List Side → Prop
  | last (b : List Side) (hb : rho b = if 0 < b.count .first then 1 else 0) :
      InsertedTight a [] [b.count .second] [b.count .first]
        (List.replicate b.length a) b
  | next (b : List Side) (c : α) (hc : c ≠ a)
      {cs : List α} {h e : List Nat} {w : List α} {M : List Side}
      (hb : rho b = if 0 < b.count .first then 1 else 0)
      (tail : InsertedTight a cs h e w M) :
      InsertedTight a (c :: cs) (b.count .second :: h) (b.count .first :: e)
        (List.replicate b.length a ++ c :: w) (b ++ .second :: M)

private theorem inserted_tight_of_eq (a : α) {cs : List α} {h e : List Nat}
    {w : List α} {M : List Side} (ht : Trace a .second cs h e w M)
    (heq : rho M = occupied e) : InsertedTight a cs h e w M := by
  induction ht with
  | last b => exact .last b (by simpa [occupied] using heq)
  | @next b c hc cs h e w M tail ih =>
    have htail := inserted_trace_lower a tail
    have hb : (if 0 < b.count .first then 1 else 0) ≤ rho b := by
      split_ifs with h
      · exact rho_positive b h
      · omega
    rw [rho_separated] at heq
    have heq' : rho M + rho b = occupied e + if 0 < b.count .first then 1 else 0 := by
      simpa [occupied,List.countP_cons,Nat.add_comm] using heq
    apply InsertedTight.next b c hc (by omega)
    exact ih (by omega)

/-- Equality in the lower bound holds in every indexed gap of every minimum mask. -/
theorem inserted_minimum_shape (a : α) (m : Nat) (cs : List α) (h e : List Nat)
    (w : List α) (M : List Side) (r : Nat) (ha : ∀ c ∈ cs, c ≠ a)
    (hh : h.length = cs.length + 1) (he : e.length = h.length) (hm : e.sum = m)
    (hw : w = gap a cs (List.zipWith (· + ·) h e))
    (hmin : IsMinimumMask (List.replicate m a) (gap a cs h) w M r) :
    InsertedTight a cs h e w M := by
  have ht := native_trace_inserted a m cs h e w M ha hh he hw hmin.1
  have hlo := inserted_trace_lower a ht
  have hg := (inserted_degree a m cs h e ha hh he hm).1
  rw [← hw] at hg
  have hhi := hmin.2.2 _ hg.1
  have hgr := hg.2.1
  have hmr := hmin.2.1
  apply inserted_tight_of_eq a ht
  rw [hmin.2.1]
  omega

private theorem second_zero (b : List Side) (hz : starts .second b = 0) :
    b = List.replicate b.length .second := by
  induction b with
  | nil => rfl
  | cons p b ih =>
    cases p with
    | first => simp [starts,step] at hz
    | second => simpa [List.replicate_succ] using
        congrArg (Side.second :: ·) (ih (by simpa [starts,step] using hz))

private theorem zero_bracket (b : List Side) (hz : starts .first (b++[.first]) = 0) :
    b = List.replicate b.length .first := by
  induction b with
  | nil => rfl
  | cons p b ih =>
    cases p with
    | first => simpa [List.replicate_succ] using
        congrArg (Side.first :: ·) (ih (by simpa [starts,step] using hz))
    | second => have hp := bracket_positive b; simp [starts,step] at hz; omega

private theorem initial_one (b : List Side) (hz : starts .second (b++[.first]) = 1) :
    ∃ x y : Nat, b = List.replicate x .second ++ List.replicate y .first := by
  induction b with
  | nil => exact ⟨0,0,rfl⟩
  | cons p b ih =>
    cases p with
    | first =>
      have hb : starts .first (b++[.first]) = 0 := by simp [starts,step] at hz; omega
      exact ⟨0,b.length+1,by
        simpa only [List.replicate_zero,List.nil_append,List.replicate_succ] using
          congrArg (Side.first :: ·) (zero_bracket b hb)⟩
    | second =>
      obtain ⟨x,y,he⟩ := ih (by simpa [starts,step] using hz)
      exact ⟨x+1,y,by simp [List.replicate_succ,← he]⟩

private theorem internal_one (b : List Side) (hz : starts .first (b++[.first]) = 1) :
    ∃ x y z : Nat, b = List.replicate x .first ++ List.replicate y .second ++
      List.replicate z .first := by
  induction b with
  | nil => simp [starts,step] at hz
  | cons p b ih =>
    cases p with
    | first =>
      obtain ⟨x,y,z,he⟩ := ih (by simpa [starts,step] using hz)
      exact ⟨x+1,y,z,by simp [List.replicate_succ,← he]⟩
    | second =>
      obtain ⟨y,z,he⟩ := initial_one b (by simpa [starts,step] using hz)
      exact ⟨0,y+1,z,by simp [List.replicate_succ,← he]⟩

private theorem internal_shape (b : List Side)
    (hz : starts .first (b++[.first]) = if 0 < b.count .second then 1 else 0) :
    ∃ x z : Nat, b = List.replicate x .first ++
      List.replicate (b.count .second) .second ++ List.replicate z .first := by
  by_cases hp : 0 < b.count .second
  · obtain ⟨x,y,z,he⟩ := internal_one b (by simpa [hp] using hz)
    have hc : b.count .second = y := by simp [he,List.count_replicate]
    exact ⟨x,z,by simpa [hc] using he⟩
  · have hc : b.count .second = 0 := by omega
    have he := zero_bracket b (by simpa [hp] using hz)
    exact ⟨b.length,0,by simpa [hc] using he⟩

private theorem terminal_zero (b : List Side) (hz : starts .first b = 0) :
    ∃ x y : Nat, b = List.replicate x .first ++ List.replicate y .second := by
  induction b with
  | nil => exact ⟨0,0,rfl⟩
  | cons p b ih =>
    cases p with
    | first =>
      obtain ⟨x,y,he⟩ := ih (by simpa [starts,step] using hz)
      exact ⟨x+1,y,by simp [List.replicate_succ,← he]⟩
    | second =>
      have hb := second_zero b (by simpa [starts,step] using hz)
      exact ⟨0,b.length+1,by
        simpa only [List.replicate_zero,List.nil_append,List.replicate_succ] using
          congrArg (Side.second :: ·) hb⟩

/-- The exact internal and terminal costs retain every label in every gap. -/
inductive ReverseTailTight (a : α) : List α → List Nat → List Nat →
    List α → List Side → Prop
  | last (b : List Side) (hb : starts .first b = 0)
      (shape : ∃ x y : Nat, b = List.replicate x .first ++ List.replicate y .second) :
      ReverseTailTight a [] [b.count .first] [b.count .second]
        (List.replicate b.length a) b
  | next (b : List Side) (c : α) (hc : c ≠ a)
      {cs : List α} {h e : List Nat} {w : List α} {M : List Side}
      (hb : starts .first (b ++ [.first]) = if 0 < b.count .second then 1 else 0)
      (shape : ∃ x z : Nat, b = List.replicate x .first ++
        List.replicate (b.count .second) .second ++ List.replicate z .first)
      (tail : ReverseTailTight a cs h e w M) :
      ReverseTailTight a (c :: cs) (b.count .first :: h) (b.count .second :: e)
        (List.replicate b.length a ++ c :: w) (b ++ .first :: M)

/-- The initial forced group contributes one run; the rest is internally tight. -/
inductive ReverseTight (a : α) : List α → List Nat → List Nat →
    List α → List Side → Prop
  | next (b : List Side) (c : α) (hc : c ≠ a)
      {cs : List α} {h e : List Nat} {w : List α} {M : List Side}
      (hb : starts .second (b ++ [.first]) = 1)
      (shape : ∃ x y : Nat, b = List.replicate x .second ++ List.replicate y .first)
      (tail : ReverseTailTight a cs h e w M) :
      ReverseTight a (c :: cs) (b.count .first :: h) (b.count .second :: e)
        (List.replicate b.length a ++ c :: w) (b ++ .first :: M)

private theorem reverse_tail_tight_of_eq (a : α) {cs : List α} {h e : List Nat}
    {w : List α} {M : List Side} (ht : Trace a .first cs h e w M)
    (heq : starts .first M = occupied e.dropLast) : ReverseTailTight a cs h e w M := by
  induction ht with
  | last b =>
    have hb : starts .first b = 0 := by simpa [occupied] using heq
    exact .last b hb (terminal_zero b hb)
  | @next b c hc cs h e w M tail ih =>
    have hn : e ≠ [] := by
      obtain ⟨_,hh,he,_⟩ := trace_projections a .first tail
      intro hz
      simp [hz] at he
      omega
    have htail := reverse_tail_lower a tail
    have hb := bracket_internal_lower b
    rw [starts_bracket,List.dropLast_cons_of_ne_nil hn] at heq
    have heq' : starts .first (b++[.first]) + starts .first M =
        occupied e.dropLast + if 0 < b.count .second then 1 else 0 := by
      simpa [occupied,List.countP_cons] using heq
    have heqb : starts .first (b++[.first]) =
        if 0 < b.count .second then 1 else 0 := by omega
    exact .next b c hc heqb (internal_shape b heqb) (ih (by omega))

/-- Every reverse-unary minimum has exactly the forced initial, internal,
and terminal gap costs, including all outer base material. -/
theorem reverse_minimum_shape (a : α) (n : Nat) (cs : List α) (h e : List Nat)
    (w : List α) (M : List Side) (r : Nat) (ha : ∀ c ∈ cs, c ≠ a)
    (hh : h.length = cs.length + 1) (he : e.length = h.length) (hn : e.sum = n)
    (hc : cs ≠ []) (hw : w = gap a cs (List.zipWith (· + ·) h e))
    (hmin : IsMinimumMask (gap a cs h) (List.replicate n a) w M r) :
    ReverseTight a cs h e w M := by
  have ht := native_trace_reverse a n cs h e w M ha hh he hw hmin.1
  have hlo := reverse_trace_lower a ht hc
  have hg := (reverse_degree a n cs h e ha hh he hn hc).1
  rw [← hw] at hg
  have hhi := hmin.2.2 _ hg.1
  have hgr := hg.2.1
  have hmr := hmin.2.1
  have heq : rho M = 1 + internalOccupied e := by omega
  cases ht with
  | last b => exact (hc rfl).elim
  | next b c hca tail =>
    have htail := reverse_tail_lower a tail
    have hb := bracket_positive b
    rw [rho_starts,starts_bracket] at heq
    simp only [internalOccupied,List.tail_cons] at heq
    have heqb : starts .second (b++[.first]) = 1 := by omega
    exact .next b c hca heqb (initial_one b heqb)
      (reverse_tail_tight_of_eq a tail (by omega))

/-- Both complete spectra, counted on the actual source words. -/
theorem spectra (a : α) (m n : Nat) (u v : List α) (hu : u ≠ []) (hv : v ≠ [])
    (hm : 0 < m) (hn : 0 < n) :
    spectrum (List.replicate m a) v =
      {r | 1 ≤ r ∧ r ≤ min m ((spine a v).length + 1)} ∧
    spectrum u (List.replicate n a) =
      {r | 1 ≤ r ∧ r ≤ 1 + min n ((spine a u).length - 1)} := by
  constructor
  · obtain ⟨cs,h,ha,hh,rfl⟩ := gap_exists a v
    rw [(profile_gap a cs h ha hh).1]
    exact inserted_spectrum a m cs h ha hh hm
  · obtain ⟨cs,h,ha,hh,he⟩ := gap_exists a u
    subst u
    rw [(profile_gap a cs h ha hh).1]
    exact reverse_spectrum a n cs h ha hh hu

end D5.S1.Words.HughesUnaryInsertion
