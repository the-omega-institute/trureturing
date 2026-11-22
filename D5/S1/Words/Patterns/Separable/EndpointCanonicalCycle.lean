/- GID: D5/S1/Words/Patterns/Separable/EndpointCanonicalCycle
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/EndpointCanonicalCycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The canonical endpoint parser identifies actual emitted-coordinate hits on sufficiently long successful bounded tuple fibers. -/

import D5.S1.Words.Patterns.Separable.EndpointCycleHazardSeries

namespace D5.S1.Words.Patterns.Separable.EndpointCanonicalCycle

open ActualCycles ActualCycleLaw CutFactorization MinimumCutKernel EndpointHistoryKernel
open CappedExploration StableEndpointCodes
open EndpointCycleHazard (hit)

/-- Actual low-value-origin advance minus actual position-origin advance.
This is the cycle increment of the existing endpoint-hazard construction. -/
def discrepancyDelta : {sign : Bool} → UnboundedCycle sign → ℤ
  | sign, .terminal n _ => if sign then -((n : ℤ) + 1) else 0
  | sign, .discard n _ tail =>
      (if sign then (n : ℤ) + 1 else 0) + discrepancyDelta tail

/-- Literal recursive classifier of an actual unbounded tuple. -/
def tupleHits : {k : ℕ} → UnboundedTuple k → ℤ → Prop
  | 0, _, _ => False
  | _ + 1, p, e =>
      hit p.1.2 e ∨ tupleHits p.2 (e + discrepancyDelta p.1.2)

abbrev Residual := Σ n : ℕ, Avoider n
abbrev CycleResult := MarkedCycle × Residual

/-- Continue from the actual left factor and record the actual discarded right factor.
A sign mismatch is a failure, not an erased successful cycle. -/
private def pushDiscard (sign : Bool) (n : ℕ) (shape : Avoider n)
    (result : CycleResult) : Option CycleResult :=
  if hsize : 0 < n then
    if hs : result.1.1 = !sign then
      some (⟨sign, .discard (n - 1) (by simpa only [Nat.sub_add_cancel hsize] using shape)
        (hs ▸ result.1.2)⟩, result.2)
    else none
  else none

/-- A cap-independent parser on the actual avoider, using the real minimum-cut
factorization and recursing only through the smaller discarded endpoint's complement.
There is no arbitrary outcome on equal splits: that case is tagged undecided. -/
noncomputable def canonicalCycle : (n : ℕ) → Avoider n → Option CycleResult
  | n, π =>
    if hn : 2 ≤ n then
      let cut := recover (state := none) ⟨π, trivial⟩ hn
      if cut.left < cut.right then
        some (⟨cut.sign, .terminal (cut.left - 1)
          (by simpa only [Nat.sub_add_cancel cut.left_pos] using cut.first)⟩,
          ⟨cut.right, cut.last⟩)
      else if cut.right < cut.left then
        (canonicalCycle cut.left cut.first.val).bind (pushDiscard cut.sign cut.right cut.last)
      else none
    else none
termination_by n _ => n
decreasing_by
  change cut.left < n
  have hh := cut.sum_eq
  have hp := cut.right_pos
  omega

/-- At the concrete minimum cut of the actual permutation, a shorter left endpoint
finishes a cycle and exposes the actual right residual. -/
private theorem canonicalCycle_emits_recovered {n : ℕ} (π : Avoider n) (hn : 2 ≤ n)
    (lt : (recover (state := none) ⟨π,trivial⟩ hn).left <
      (recover (state := none) ⟨π,trivial⟩ hn).right) :
    let cut := recover (state := none) ⟨π,trivial⟩ hn
    canonicalCycle n π = some (⟨cut.sign, .terminal (cut.left - 1)
      (by simpa only [Nat.sub_add_cancel cut.left_pos] using cut.first)⟩,
      ⟨cut.right, cut.last⟩) := by
  rw [canonicalCycle]
  simp only [hn, dite_true, lt, ite_true]

/-- A shorter right endpoint recurses on the actual left residual, preserving
the discarded shape and the final residual without resampling. -/
private theorem canonicalCycle_discards_recovered {n : ℕ} (π : Avoider n) (hn : 2 ≤ n)
    (lt : (recover (state := none) ⟨π,trivial⟩ hn).right <
      (recover (state := none) ⟨π,trivial⟩ hn).left) :
    let cut := recover (state := none) ⟨π,trivial⟩ hn
    canonicalCycle n π =
      (canonicalCycle cut.left cut.first.val).bind (pushDiscard cut.sign cut.right cut.last) := by
  dsimp
  rw [canonicalCycle]
  simp only [hn, dite_true, lt, (not_lt_of_gt lt), ite_false, ite_true]

private def actualBlock {left right : ℕ} (sign : Bool)
    (first : Indecomposable sign left) (last : Avoider right) : Avoider (left + right) :=
  ⟨blockSum sign first.val.val last.val,
    (avoids_block_sum_iff sign _ _).mpr ⟨first.val.property, last.property⟩⟩

private def actualBlockRecovery {left right : ℕ} (sign : Bool)
    (first : Indecomposable sign left) (last : Avoider right)
    (hl : 0 < left) (hr : 0 < right)
    (hm : MinimumCut sign (actualBlock sign first last).val left) :
    Recovered (state := none) ⟨actualBlock sign first last, trivial⟩ where
  sign := sign
  left := left
  right := right
  left_pos := hl
  right_pos := hr
  sum_eq := rfl
  compatible := Or.inl rfl
  first := first
  last := last
  reconstruct := rfl
  minimum := hm
  unique other cut hp hb hcut := by
    let r := recover (state := none) ⟨actualBlock sign first last, trivial⟩ (by omega)
    have a := r.unique other cut hp hb hcut
    have b := r.unique sign left hl (by omega) hm
    exact ⟨a.1.trans b.1.symm, a.2.trans b.2.symm⟩
  factor_unique a b eq := by
    have same : (a.val,b) = (first.val,last) :=
      ((fixed_cut_factorization hl hr sign (actualBlock sign first last)).mp hm.1).unique eq rfl
    exact ⟨Subtype.ext (congrArg Prod.fst same), congrArg Prod.snd same⟩

/-- Actual recovery reuses the very same factors of a certified block sum,
not merely a count-equivalent residual. -/
private theorem recover_actualBlock {left right : ℕ} (sign : Bool)
    (first : Indecomposable sign left) (last : Avoider right)
    (hl : 0 < left) (hr : 0 < right)
    (hm : MinimumCut sign (actualBlock sign first last).val left) :
    recover (state := none) ⟨actualBlock sign first last, trivial⟩ (by omega) =
      actualBlockRecovery sign first last hl hr hm := by
  generalize recover (state := none)
    ⟨actualBlock sign first last, trivial⟩ (by omega) = c
  rcases c with ⟨s,a,b,ha,hb,hab,ok,fa,fb,eq,hcut,uniq,factors⟩
  obtain ⟨rfl,rfl⟩ := uniq sign left hl (by omega) hm
  have hright : b = right := by omega
  subst b
  change actualBlock sign fa fb = actualBlock sign first last at eq
  obtain ⟨ef,eb⟩ := factors first last
    (congrArg Subtype.val eq.symm)
  subst first
  subst last
  rfl

private theorem canonicalCycle_emit_block {left right : ℕ} (sign : Bool)
    (first : Indecomposable sign left) (last : Avoider right)
    (hl : 0 < left) (hr : 0 < right)
    (hm : MinimumCut sign (actualBlock sign first last).val left)
    (hshort : left < right) :
    canonicalCycle (left+right) (actualBlock sign first last) =
      some (⟨sign, .terminal (left-1)
        (by simpa only [Nat.sub_add_cancel hl] using first)⟩, ⟨right,last⟩) := by
  have hn : 2 ≤ left + right := by omega
  have ht : (recover (state := none) ⟨actualBlock sign first last,trivial⟩ hn).left <
      (recover (state := none) ⟨actualBlock sign first last,trivial⟩ hn).right := by
    rw [recover_actualBlock sign first last hl hr hm]
    exact hshort
  have he := canonicalCycle_emits_recovered (actualBlock sign first last) hn ht
  dsimp only at he
  rw [recover_actualBlock sign first last hl hr hm] at he
  exact he

private theorem canonicalCycle_discard_block {left right : ℕ} (sign : Bool)
    (first : Indecomposable sign left) (last : Avoider right)
    (hl : 0 < left) (hr : 0 < right)
    (hm : MinimumCut sign (actualBlock sign first last).val left)
    (hshort : right < left) :
    canonicalCycle (left+right) (actualBlock sign first last) =
      (canonicalCycle left first.val).bind (pushDiscard sign right last) := by
  have hn : 2 ≤ left + right := by omega
  have ht : (recover (state := none) ⟨actualBlock sign first last,trivial⟩ hn).right <
      (recover (state := none) ⟨actualBlock sign first last,trivial⟩ hn).left := by
    rw [recover_actualBlock sign first last hl hr hm]
    exact hshort
  have he := canonicalCycle_discards_recovered (actualBlock sign first last) hn ht
  dsimp only at he
  rw [recover_actualBlock sign first last hl hr hm] at he
  exact he

/-- The exact side guard needed for an actual single-cycle history. A terminal
emit is followed by a stop; right discards may precede it. -/
def canonicalSingleHistory {state n} : EndpointHistory state n → Prop
  | .stop _ _ => False
  | .emit (left := l) (right := r) _ _ _ _ _ t => l < r ∧ t.steps = 0
  | .discard (left := l) (right := r) _ _ _ _ _ t =>
    r < l ∧ canonicalSingleHistory t

private theorem eq_stop_of_steps_zero {state n} (p : EndpointHistory state n)
    (h : p.steps = 0) : p = .stop state n := by
  cases p <;> simp_all [EndpointHistory.steps]

/-- Reading the erased marked cycle from the actual history, preserving its
witness residual. This is defined on any path; the theorem limits it to one cycle. -/
def readSingleHistory {state n} (p : EndpointHistory state n)
    (sample : p.Leaf) : Option CycleResult :=
  match p with
  | .stop _ _ => none
  | .emit (left := l) sign hl _ _ shape _ =>
      some (⟨sign, .terminal (l-1)
        (by simpa only [Nat.sub_add_cancel hl] using shape)⟩, ⟨_,sample.val⟩)
  | .discard (right := r) sign _ _ _ shape t =>
      (readSingleHistory t sample).bind (pushDiscard sign r shape)

/-- The actual endpoint history Event agrees recursively with the bound-independent
parser, including every erased shape and the same residual permutation. -/
private theorem canonicalCycle_agrees_actual_history {state n} (p : EndpointHistory state n)
    (π : Avoider n) (sample : p.Leaf) (ev : p.assemble sample = π)
    (guard : canonicalSingleHistory p) :
    canonicalCycle n π = readSingleHistory p sample := by
  rw [← ev]
  induction p with
  | stop => exact False.elim guard
  | @emit state left right sign hl hr ok shape tail ih =>
      have ht : tail = .stop none right := eq_stop_of_steps_zero tail guard.2
      have short : left < right := guard.1
      subst tail
      have htrace := ((endpoint_history_count_kernel
        (.emit sign hl hr ok shape (.stop none right))).1 sample).2
      exact canonicalCycle_emit_block sign shape sample.val hl hr htrace.1 short
  | @discard state left right sign hl hr ok shape tail ih =>
      have htail := ((endpoint_history_count_kernel tail).1 sample).1
      let first : Indecomposable sign left := ⟨tail.assemble sample, htail⟩
      have htrace := ((endpoint_history_count_kernel
        (.discard sign hl hr ok shape tail)).1 sample).2
      change canonicalCycle (left+right) (actualBlock sign first shape) =
        (readSingleHistory tail sample).bind (pushDiscard sign right shape)
      rw [canonicalCycle_discard_block sign first shape hl hr htrace.1 guard.1]
      rw [ih (tail.assemble sample) sample rfl guard.2]

private theorem canonicalSingleHistory_cast {state n m} (eq : n = m)
    (p : EndpointHistory state n) :
    canonicalSingleHistory (eq ▸ p : EndpointHistory state m) ↔
      canonicalSingleHistory p := by
  cases eq
  rfl

/-- The genuine decoded single-cycle history meets the cap-independent guard
on every recursive step, uniformly under the source's linear buffer. -/
private theorem stable_cycle_is_canonical {K H : ℕ} {sign : Bool} {state : Option Bool}
    (c : Cycle K sign H) (ok : state = none ∨ state = some (!sign))
    (n : ℕ) (large : H * K + 2 * K < n) :
    canonicalSingleHistory (history (c.stable ok) n (by omega)) := by
  induction H generalizing sign state n with
  | zero => exact nomatch c
  | succ H ih =>
    cases c with
    | inl x =>
      have hb := x.1.isLt
      simp only [history, Cycle.stable, Cycle.code, decode, canonicalSingleHistory_cast,
        canonicalSingleHistory, EndpointHistory.steps]
      constructor
      · rw [Nat.succ_mul] at large
        omega
      · trivial
    | inr x =>
      have hb := x.1.1.isLt
      have large' : H * K + 2*K < n - (x.1.1.val + 1) := by
        rw [Nat.succ_mul] at large
        omega
      have hchild := ih x.2 (state := some sign) (by simp) _ large'
      simp only [history, Cycle.stable, Cycle.code, decode, canonicalSingleHistory_cast,
        canonicalSingleHistory]
      constructor
      · rw [Nat.succ_mul] at large
        omega
      · exact hchild

private def readsActualMark {state n} (p : EndpointHistory state n)
    (mark : MarkedCycle) : Prop :=
  ∀ sample : p.Leaf, readSingleHistory p sample =
    some (mark, ⟨p.remaining, sample.val⟩)

private theorem readsActualMark_cast {state n m} (eq : n = m)
    (p : EndpointHistory state n) (mark : MarkedCycle) :
    readsActualMark (eq ▸ p : EndpointHistory state m) mark ↔ readsActualMark p mark := by
  cases eq
  rfl

private theorem stable_cycle_readsActualMark {K H : ℕ} {sign : Bool} {state : Option Bool}
    (c : Cycle K sign H) (ok : state = none ∨ state = some (!sign))
    (n : ℕ) (large : H * K < n) :
    readsActualMark (history (c.stable ok) n large) ⟨sign,c.erase⟩ := by
  induction H generalizing sign state n with
  | zero => exact nomatch c
  | succ H ih =>
    cases c with
    | inl x =>
      simp only [history, Cycle.stable, Cycle.code, decode, readsActualMark_cast, Cycle.erase]
      intro sample
      rfl
    | inr x =>
      have hb := x.1.1.isLt
      have large' : H * K < n - (x.1.1.val + 1) := by
        rw [Nat.succ_mul] at large
        omega
      have hchild := ih x.2 (state := some sign) (by simp) _ large'
      simp only [history, Cycle.stable, Cycle.code, decode, readsActualMark_cast, Cycle.erase]
      intro sample
      simp only [readSingleHistory, EndpointHistory.remaining]
      have heq := hchild sample
      dsimp only [history, Cycle.stable] at heq
      rw [heq]
      simp [pushDiscard]

/-- Exact agreement with the actual emitted cycle mark and the literal sample
as its residual, for a stable finite permutation history. -/
private theorem canonicalCycle_agrees_stable {K H : ℕ} {sign : Bool} {state : Option Bool}
    (c : Cycle K sign H) (ok : state = none ∨ state = some (!sign))
    (n : ℕ) (large : H * K + 2*K < n)
    (sample : (history (c.stable ok) n (by omega)).Leaf)
    (π : Avoider n) (ev : (history (c.stable ok) n (by omega)).assemble sample = π) :
    canonicalCycle n π =
      some (⟨sign,c.erase⟩, ⟨(history (c.stable ok) n (by omega)).remaining,sample.val⟩) :=
  (canonicalCycle_agrees_actual_history _ π sample ev
    (stable_cycle_is_canonical c ok n large)).trans
      (stable_cycle_readsActualMark c ok n (by omega) sample)

/-- Fixed-k canonical readout of actual successive residuals. A failure remains
visible as none, not an empty hit trace. -/
noncomputable def canonicalTuple : (k n : ℕ) → Avoider n →
    Option (UnboundedTuple k × Residual)
  | 0, n, π => some ((), ⟨n, π⟩)
  | k+1, n, π => do
      let (c, r) ← canonicalCycle n π
      let (cs, rest) ← canonicalTuple k r.1 r.2
      pure ((c, cs), rest)

private def reindexLeaf {state n m} (hn : n = m) (hs : state = none) :
    Carrier state n ≃ Avoider m := by
  rw [hn, hs]
  exact Equiv.subtypeUnivEquiv (fun _ => trivial)

private theorem reindexLeaf_sigma {state n m} (hn : n = m) (hs : state = none)
    (sample : Carrier state n) :
    (⟨m, reindexLeaf hn hs sample⟩ : Residual) = ⟨n,sample.val⟩ := by
  cases hn
  cases hs
  rfl

private theorem canonicalCycle_agrees_family {K H : ℕ} (c : Family K H)
    (n : ℕ) (large : H*K + 2*K < n)
    (sample : (history c.stable n (by omega)).Leaf) (π : Avoider n)
    (ev : (history c.stable n (by omega)).assemble sample = π) :
    canonicalCycle n π = some (⟨c.1,c.2.erase⟩, ⟨n-c.size,c.leaf n (by omega) sample⟩) := by
  have h := canonicalCycle_agrees_stable c.2 (Or.inl rfl) n large sample π ev
  let rem := c.2.remaining (Or.inl rfl) n (by omega)
  have heq : c.leaf n (by omega) = reindexLeaf rem.1 rem.2 := rfl
  rw [heq]
  exact h.trans (congrArg (fun r : Residual => some ((⟨c.1,c.2.erase⟩ : MarkedCycle),r))
    (reindexLeaf_sigma rem.1 rem.2 sample).symm)

/-- At every actual successful finite tuple cylinder, the cap-independent
parser returns the identical erased prefix. The last residual is also retained,
rather than declaring a missing parse to be a miss. -/
private theorem canonicalTuple_agrees_event {K H k n} (p : Tuple K H k)
    (large : Tuple.threshold K H k < n) (π : Avoider n) (occurs : p.Event n large π) :
    ∃ r : Residual, canonicalTuple k n π = some (p.erase,r) := by
  induction k generalizing n with
  | zero => exact ⟨⟨n,π⟩, rfl⟩
  | succ k ih =>
      have hfirst : H*K + 2*K < n := by
        have hb := Tuple.first_bound large
        omega
      have htail := p.child_bound large
      let head := history p.1.stable n (by omega)
      change ∃ s : head.Leaf,
        p.2.Event (n-p.1.size) htail (p.1.leaf n (by omega) s) ∧
          head.assemble s = π at occurs
      obtain ⟨sample, ht, he⟩ := occurs
      obtain ⟨r, rr⟩ := ih p.2 htail _ ht
      have hc := canonicalCycle_agrees_family p.1 n hfirst sample π he
      refine ⟨r, ?_⟩
      rw [canonicalTuple, hc]
      change (do
        let (cs, rest) ← canonicalTuple k (n-p.1.size) (p.1.leaf n (by omega) sample)
        pure ((⟨p.1.1,p.1.2.erase⟩,cs),rest)) = some (p.erase,r)
      rw [rr]
      rfl

open OccupiedComparison (hitsDiagonal)
open EndpointCycleHazard (hit)

/-- A hit in the literal initial block, without testing any index in the remaining
block or any index removed by the endpoint history. -/
def initialHits {n : ℕ} (π : Equiv.Perm (Fin n)) (positions : ℕ) (e : ℤ) : Prop :=
  ∃ j : Fin n, j.val < positions ∧ (j.val : ℤ) - ((π j).val : ℤ) = e

private theorem blockSum_left_value {left right : ℕ} (sign : Bool)
    (α : Equiv.Perm (Fin left)) (β : Equiv.Perm (Fin right)) (i : Fin left) :
    (blockSum sign α β (Fin.castAdd right i)).val =
      (if sign then right else 0) + (α i).val := by
  cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm, Nat.add_comm]

private theorem initialHits_blockSum_left {m k : ℕ} (sign : Bool)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin k)) (positions : ℕ)
    (hpos : positions ≤ m) (e : ℤ) :
    initialHits (blockSum sign α β) positions e ↔
      initialHits α positions (e + if sign then (k : ℤ) else 0) := by
  constructor
  · rintro ⟨j, hj, he⟩
    let i : Fin m := ⟨j.val, lt_of_lt_of_le hj hpos⟩
    have jj : j = Fin.castAdd k i := Fin.ext rfl
    refine ⟨i, hj, ?_⟩
    rw [jj, blockSum_left_value] at he
    cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte, Fin.val_castAdd,
      Nat.cast_add, zero_add] at he ⊢ <;> omega
  · rintro ⟨i, hi, he⟩
    refine ⟨Fin.castAdd k i, hi, ?_⟩
    rw [blockSum_left_value]
    cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte, Fin.val_castAdd,
      Nat.cast_add, zero_add] at he ⊢ <;> omega

private theorem initialHits_all {n : ℕ} (π : Equiv.Perm (Fin n)) (e : ℤ) :
    initialHits π n e ↔ hitsDiagonal π e :=
  ⟨fun ⟨j, _, hj⟩ => ⟨j, hj⟩, fun ⟨j, hj⟩ => ⟨j, j.isLt, hj⟩⟩

private theorem not_hitsDiagonal_large {n : ℕ} (π : Equiv.Perm (Fin n))
    (e : ℤ) (guard : (n : ℤ) ≤ e) : ¬hitsDiagonal π e := by
  rintro ⟨i, hi⟩
  have h := i.isLt
  omega

/-- A direct terminal emits the unshifted local hit; a skew terminal emits
none when even its least lifted value is above all emitted positions.
The guard is only required on the skew branch. -/
private theorem literal_terminal_hit {left right : ℕ} (sign : Bool)
    (α : Equiv.Perm (Fin left)) (β : Equiv.Perm (Fin right)) (e : ℤ)
    (guard : sign = true → (left : ℤ) ≤ e + (right : ℤ)) :
    initialHits (blockSum sign α β) left e ↔ sign = false ∧ hitsDiagonal α e := by
  rw [initialHits_blockSum_left sign α β left le_rfl, initialHits_all]
  cases sign with
  | false => simp
  | true => simpa only [↓reduceIte, Bool.true_eq_false, false_and] using
      (iff_false_intro (not_hitsDiagonal_large α (e + right) (guard rfl)))

/-- Discarding a right block preserves the literal tested positions and shifts
the local diagonal exactly by the discarded right length on a skew cut. -/
private theorem literal_discard_hit {state : Option Bool} {left right : ℕ} (sign : Bool)
    (hl : 0 < left) (hr : 0 < right) (ok : state = none ∨ state = some (!sign))
    (shape : Avoider right) (tail : EndpointHistory (some sign) left)
    (sample : tail.Leaf) (e : ℤ) :
    initialHits ((EndpointHistory.discard sign hl hr ok shape tail).assemble sample).val
      tail.emitted e ↔
        initialHits (tail.assemble sample).val tail.emitted
          (e + if sign then (right : ℤ) else 0) := by
  exact initialHits_blockSum_left sign (tail.assemble sample).val shape.val
    tail.emitted (by have h := (endpoint_history_count_kernel tail).2.2.2.2.1; omega) e


/-- A complete mark records the length of its sole emitted left factor. -/
def markEmitted : {sign : Bool} → UnboundedCycle sign → ℕ
  | _, .terminal n _ => n+1
  | _, .discard _ _ t => markEmitted t

/-- Exact original emitted-coordinate hit test for a history's readout. The additive
guard excludes only skew terminal hits, not direct or recursive discard hits. -/
private theorem actual_literal_hit_of_read {state n K} (p : EndpointHistory state n)
    (sample : p.Leaf) (e : ℤ) (one : canonicalSingleHistory p)
    (capped : p.Capped K) (far : (K : ℤ) ≤ e + p.remaining)
    (mark : MarkedCycle) (residual : Residual)
    (read : readSingleHistory p sample = some (mark,residual)) :
    p.emitted = markEmitted mark.2 ∧
      (initialHits (p.assemble sample).val p.emitted e ↔ hit mark.2 e) := by
  induction p generalizing e mark residual with
  | stop => exact False.elim one
  | @emit root left right sign hl hr ok shape tail ih =>
      have hstop := eq_stop_of_steps_zero tail one.2
      subst tail
      cases left with
      | zero => omega
      | succ l =>
        simp only [readSingleHistory] at read
        cases read
        refine ⟨rfl, ?_⟩
        exact literal_terminal_hit (left := l+1) (right := right) sign shape.val.val sample.val.val e (fun _ => by
          have cap := capped.1
          change l + 1 ≤ K at cap
          change (K : ℤ) ≤ e + right at far
          omega)
  | @discard root left right sign hl hr ok shape tail ih =>
      cases right with
      | zero => omega
      | succ r =>
        cases htail : readSingleHistory tail sample with
        | none =>
          simp [readSingleHistory, htail] at read
        | some data =>
          rcases data with ⟨⟨tailSign,tailMark⟩,tailResidual⟩
          by_cases signs : tailSign = !sign
          · subst tailSign
            simp only [readSingleHistory, htail, Option.bind, pushDiscard,
              Nat.zero_lt_succ, dite_true] at read
            cases read
            let eNext := e + if sign then ((r+1 : ℕ) : ℤ) else 0
            have hfar : (K : ℤ) ≤ eNext + tail.remaining := by
              change (K : ℤ) ≤ e + tail.remaining at far
              cases sign <;> simp [eNext] <;> omega
            obtain ⟨hcount, hhit⟩ :=
              ih sample eNext one.2 capped.2 hfar _ _ htail
            refine ⟨hcount, ?_⟩
            refine (literal_discard_hit sign hl hr ok shape tail sample e).trans ?_
            simpa only [eNext, Nat.add_sub_cancel, Nat.cast_succ, add_assoc, hit] using hhit
          · simp [readSingleHistory, htail, pushDiscard, signs] at read

/-- Low-value advance of the remaining finite block. The corresponding
position advance is the already-defined `EndpointHistory.emitted`. -/
def historyLowAdvance {state n} : EndpointHistory state n → ℕ
  | .stop _ _ => 0
  | .emit (left := left) sign _ _ _ _ tail =>
      (if sign then 0 else left) + historyLowAdvance tail
  | .discard (right := right) sign _ _ _ _ tail =>
      (if sign then right else 0) + historyLowAdvance tail

/-- Net change of low-value origin minus position origin in the decoded history. -/
def historyDelta {state n} (p : EndpointHistory state n) : ℤ :=
  (historyLowAdvance p : ℤ) - p.emitted

/-- Residual position inside the actual initial permutation. A left emission
moves the residual positions right by its length. A right discard does not. -/
def residualPosition {state n} (p : EndpointHistory state n) :
    Fin p.remaining → Fin n :=
  match p with
  | .stop _ _ => id
  | .emit (left := left) _ _ _ _ _ tail =>
      fun j => Fin.natAdd left (residualPosition tail j)
  | .discard (right := right) _ _ _ _ _ tail =>
      fun j => Fin.castAdd right (residualPosition tail j)

private theorem residualPosition_val {state n} (p : EndpointHistory state n)
    (j : Fin p.remaining) :
    (residualPosition p j).val = p.emitted + j.val := by
  induction p with
  | stop => simp [residualPosition, EndpointHistory.emitted]
  | @emit root left right sign hl hr ok shape tail ih =>
      change left + (residualPosition tail j).val =
        left + tail.emitted + j.val
      rw [ih j, Nat.add_assoc]
  | @discard root left right sign hl hr ok shape tail ih =>
      exact ih j

private theorem blockSum_right_value {left right : ℕ} (sign : Bool)
    (α : Equiv.Perm (Fin left)) (β : Equiv.Perm (Fin right)) (i : Fin right) :
    (blockSum sign α β (Fin.natAdd left i)).val =
      (if sign then 0 else left) + (β i).val := by
  cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm]

/-- The value in the assembled permutation at the embedded residual position
is the residual leaf's actual value plus the cumulative low-value advance. -/
private theorem assemble_residual_value {state n} (p : EndpointHistory state n)
    (sample : p.Leaf) (j : Fin p.remaining) :
    ((p.assemble sample).val (residualPosition p j)).val =
      historyLowAdvance p + (sample.val.val j).val := by
  induction p with
  | stop =>
      simp [EndpointHistory.assemble, residualPosition, historyLowAdvance]
      rfl
  | @emit root left right sign hl hr ok shape tail ih =>
      change (blockSum sign shape.val.val (tail.assemble sample).val
        (Fin.natAdd left (residualPosition tail j))).val =
          ((if sign then 0 else left) + historyLowAdvance tail) + (sample.val.val j).val
      rw [blockSum_right_value, ih sample j, Nat.add_assoc]
      rfl
  | @discard root left right sign hl hr ok shape tail ih =>
      change (blockSum sign (tail.assemble sample).val shape.val
        (Fin.castAdd right (residualPosition tail j))).val =
          ((if sign then right else 0) + historyLowAdvance tail) + (sample.val.val j).val
      rw [blockSum_left_value, ih sample j, Nat.add_assoc]
      rfl

/-- For any tested residual position the original diagonal equation becomes
the residual equation with precisely the history-origin discrepancy added. -/
private theorem assemble_residual_diagonal {state n} (p : EndpointHistory state n)
    (sample : p.Leaf) (j : Fin p.remaining) (e : ℤ) :
    ((residualPosition p j).val : ℤ) -
      (((p.assemble sample).val (residualPosition p j)).val : ℤ) = e ↔
    (j.val : ℤ) - ((sample.val.val j).val : ℤ) = e + historyDelta p := by
  rw [residualPosition_val, assemble_residual_value]
  simp only [historyDelta, Nat.cast_add]
  omega

private theorem historyDelta_cast {state n m} (eq : n = m) (p : EndpointHistory state n) :
    historyDelta (eq ▸ p : EndpointHistory state m) = historyDelta p := by cases eq; rfl

private theorem historyDelta_stop (state : Option Bool) (n : ℕ) :
    historyDelta (.stop state n) = 0 := rfl

private theorem historyDelta_emit {state left right} (sign : Bool) (hl : 0 < left) (hr : 0 < right)
    (ok : state = none ∨ state = some (!sign)) (shape : Indecomposable sign left)
    (tail : EndpointHistory none right) :
    historyDelta (.emit sign hl hr ok shape tail) =
      (if sign then -(left : ℤ) else 0) + historyDelta tail := by
  cases sign <;> simp [historyDelta, historyLowAdvance, EndpointHistory.emitted]
  omega

private theorem historyDelta_discard {state left right} (sign : Bool) (hl : 0 < left) (hr : 0 < right)
    (ok : state = none ∨ state = some (!sign)) (shape : Avoider right)
    (tail : EndpointHistory (some sign) left) :
    historyDelta (.discard sign hl hr ok shape tail) =
      (if sign then (right : ℤ) else 0) + historyDelta tail := by
  cases sign <;> simp [historyDelta, historyLowAdvance, EndpointHistory.emitted]
  omega

private theorem cycle_historyDelta {K H sign state} (c : Cycle K sign H)
    (ok : state = none ∨ state = some (!sign)) (n : ℕ) (large : H*K < n) :
    historyDelta (history (c.stable ok) n large) = discrepancyDelta c.erase := by
  induction H generalizing sign state n with
  | zero => exact nomatch c
  | succ H ih =>
    cases c with
    | inl x =>
      simp only [history, Cycle.stable, Cycle.code, decode, historyDelta_cast,
        historyDelta_emit, historyDelta_stop, add_zero, Cycle.erase, discrepancyDelta, Nat.cast_add, Nat.cast_one]
    | inr x =>
      have hl : H*K < n - (x.1.1.val + 1) := by
        have := x.1.1.isLt
        rw [Nat.succ_mul] at large
        omega
      have hh := ih x.2 (state := some sign) (by simp) _ hl
      simp only [history, Cycle.stable, Cycle.code, decode, historyDelta_cast,
        historyDelta_discard, Cycle.erase, discrepancyDelta, Nat.cast_add, Nat.cast_one]
      rw [show historyDelta (decode x.2.code _ _ _) = discrepancyDelta x.2.erase from hh]

/-- The geometry is in the uncast coordinates of the original avoider; only the
residual input index is cast to the length recorded by the history. -/
private theorem family_residual_geometry {K H} (c : Family K H) (n : ℕ) (large : H*K < n)
    (sample : (history c.stable n large).Leaf) (e : ℤ) :
    ∃ embed : Fin (n-c.size) → Fin n,
      (∀ j, (embed j).val = (history c.stable n large).emitted + j.val) ∧
      ∀ j, ((embed j).val : ℤ) -
        ((((history c.stable n large).assemble sample).val (embed j)).val : ℤ) = e ↔
        (j.val : ℤ) - (((c.leaf n large sample).val j).val : ℤ) =
          e + discrepancyDelta c.2.erase := by
  let p := history c.stable n large
  let rem := c.2.remaining (Or.inl rfl) n large
  let embed (j : Fin (n-c.size)) := residualPosition p (Fin.cast rem.1.symm j)
  refine ⟨embed, fun j => residualPosition_val p _, ?_⟩
  intro j
  have hd := assemble_residual_diagonal p sample (Fin.cast rem.1.symm j) e
  have heq : c.leaf n large = reindexLeaf rem.1 rem.2 := rfl
  have hval_cast {state l m} (hn : l = m) (hs : state = none)
      (s : Carrier state l) (j : Fin m) :
      ((reindexLeaf hn hs s).val j).val = (s.val.val (Fin.cast hn.symm j)).val := by
    cases hn
    cases hs
    rfl
  have hval := hval_cast rem.1 rem.2 sample j
  rw [heq]
  exact hd.trans (iff_of_eq (congrArg₂ (fun x y : ℤ => x = y)
    (congrArg (fun x : ℕ => (j.val : ℤ) - (x : ℤ)) hval.symm)
    (congrArg (fun x : ℤ => e + x) (cycle_historyDelta c.2 (Or.inl rfl) n large))))

private theorem split_initialHits {n m : ℕ} (π : Equiv.Perm (Fin n))
    (τ : Equiv.Perm (Fin m)) (embed : Fin m → Fin n) (a b : ℕ)
    (hb : b ≤ m) (e d : ℤ)
    (pos : ∀ i, (embed i).val = a + i.val)
    (diag : ∀ i, ((embed i).val : ℤ) - ((π (embed i)).val : ℤ) = e ↔
      (i.val : ℤ) - ((τ i).val : ℤ) = e + d) :
    initialHits π (a + b) e ↔ initialHits π a e ∨ initialHits τ b (e + d) := by
  constructor
  · rintro ⟨j, hj, he⟩
    by_cases h : j.val < a
    · exact Or.inl ⟨j, h, he⟩
    · let i : Fin m := ⟨j.val - a, by omega⟩
      have hi : i.val < b := by dsimp [i]; omega
      have hji : embed i = j := Fin.ext (by rw [pos]; dsimp [i]; omega)
      exact Or.inr ⟨i, hi, (diag i).mp (by simpa only [hji] using he)⟩
  · rintro (⟨j, hj, he⟩ | ⟨i, hi, he⟩)
    · exact ⟨j, by omega, he⟩
    · exact ⟨embed i, by rw [pos]; omega, (diag i).mpr he⟩


private theorem literal_family_emit {K H} (c : Family K H) (n : ℕ)
    (large : H*K + 2*K < n) (sample : (history c.stable n (by omega)).Leaf)
    (e : ℤ) (far : (K : ℤ) ≤ e + (n - c.size : ℕ)) :
    (history c.stable n (by omega)).emitted = markEmitted c.2.erase ∧
      (initialHits ((history c.stable n (by omega)).assemble sample).val
        (history c.stable n (by omega)).emitted e ↔ hit c.2.erase e) := by
  let path := history c.stable n (by omega)
  have hc : path.Capped K :=
    ((stable_code_transport K H).1 none 1 n (by omega) c.stable).2.1
  have hr := (c.2.remaining (Or.inl rfl) n (by omega)).1
  have hf : (K : ℤ) ≤ e + path.remaining :=
    (congrArg (fun v : ℕ => (K : ℤ) ≤ e + v) hr).mpr far
  exact actual_literal_hit_of_read path sample e
    (stable_cycle_is_canonical c.2 (Or.inl rfl) n large) hc hf
    ⟨c.1,c.2.erase⟩ ⟨path.remaining,sample.val⟩
    (stable_cycle_readsActualMark c.2 (Or.inl rfl) n (by omega) sample)

/-- Number of original positions emitted by these complete marks, not
the total removed length (which would include the right discards). -/
def emittedLength : {k : ℕ} → UnboundedTuple k → ℕ
  | 0, _ => 0
  | _+1, p => markEmitted p.1.2 + emittedLength p.2

private theorem cycle_markEmitted_le_size {K H sign} (c : Cycle K sign H) :
    markEmitted c.erase ≤ c.size := by
  induction H generalizing sign with
  | zero => exact nomatch c
  | succ H ih =>
    cases c with
    | inl x => rfl
    | inr x =>
      have h := ih x.2
      simp only [Cycle.size, Cycle.erase, markEmitted]
      omega

private theorem emittedLength_le_size {K H k} (p : Tuple K H k) :
    emittedLength p.erase ≤ p.size := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact Nat.add_le_add (cycle_markEmitted_le_size p.1.2) (ih p.2)

private theorem emittedLength_fits {K H k n} (p : Tuple K H k)
    (large : Tuple.threshold K H k < n) :
    emittedLength p.erase ≤ n := by
  have h := (emittedLength_le_size p).trans (p.size_bound)
  simp only [Tuple.threshold] at large
  omega

def literalGuard {K H : ℕ} : {k : ℕ} → Tuple K H k → ℕ → ℤ → Prop
  | 0, _, _, _ => True
  | _+1, p, n, e =>
    (K : ℤ) ≤ e + (n - p.1.size : ℕ) ∧
      literalGuard p.2 (n-p.1.size) (e + discrepancyDelta p.1.2.erase)

/-- Exact geometry on an actual bounded tuple fiber. At the same original
index (j), the test is (j-π(j)=e), not a surrogate on the recovered shape. -/
private theorem tuple_event_literal_hit {K H k n} (p : Tuple K H k)
    (large : Tuple.threshold K H k < n) (π : Avoider n) (ev : p.Event n large π)
    (e : ℤ) (guard : literalGuard p n e) :
    initialHits π.val (emittedLength p.erase) e ↔ tupleHits p.erase e := by
  induction k generalizing n e with
  | zero => simp [initialHits, emittedLength, tupleHits]
  | succ k ih =>
      let c := p.1
      have big : H*K + 2*K < n := by
        have hb := Tuple.first_bound large
        omega
      have tailBig := p.child_bound large
      let path := history c.stable n (by omega)
      change ∃ s : path.Leaf, p.2.Event (n-c.size) tailBig
        (c.leaf n (by omega) s) ∧ path.assemble s = π at ev
      obtain ⟨sample, htail, hp⟩ := ev
      obtain ⟨hlen, hh⟩ := literal_family_emit c n big sample e guard.1
      obtain ⟨embed, hpos, hdiag⟩ := family_residual_geometry c n (by omega) sample e
      let tailπ := c.leaf n (by omega) sample
      have split := split_initialHits (path.assemble sample).val tailπ.val embed
        path.emitted (emittedLength p.2.erase) (emittedLength_fits p.2 tailBig)
        e (discrepancyDelta c.2.erase) hpos hdiag
      have hrest := ih p.2 tailBig tailπ htail _ guard.2
      have both := split.trans (or_congr hh hrest)
      rw [hp, hlen] at both
      exact both


open Filter Topology MeasureTheory

/-- An explicit sufficient bound from the successive skew exclusions. -/
def literalThreshold {K H : ℕ} : {k : ℕ} → Tuple K H k → ℤ → ℕ
  | 0, _, _ => 0
  | _+1, p, e =>
      p.1.size + max ((K : ℤ) - e).toNat
        (literalThreshold p.2 (e + discrepancyDelta p.1.2.erase))

private theorem literalGuard_of_threshold {K H k} (p : Tuple K H k)
    (n : ℕ) (e : ℤ) (hn : literalThreshold p e ≤ n) :
    literalGuard p n e := by
  induction k generalizing n e with
  | zero => trivial
  | succ k ih =>
      change p.1.size + max ((K : ℤ) - e).toNat
        (literalThreshold p.2 (e + discrepancyDelta p.1.2.erase)) ≤ n at hn
      change (K : ℤ) ≤ e + (n-p.1.size : ℕ) ∧
        literalGuard p.2 (n-p.1.size) (e + discrepancyDelta p.1.2.erase)
      have hm : max ((K : ℤ) - e).toNat
        (literalThreshold p.2 (e + discrepancyDelta p.1.2.erase)) ≤ n-p.1.size := by omega
      have hhead := le_trans (le_max_left _ _) hm
      exact ⟨by omega, ih p.2 _ _ (le_trans (le_max_right _ _) hm)⟩

private theorem eventually_literalGuard (K H k : ℕ) (e : ℤ) :
    ∀ᶠ n : ℕ in atTop, ∀ p : Tuple K H k, literalGuard p n e := by
  classical
  let bound := (Finset.univ : Finset (Tuple K H k)).sup (fun p => literalThreshold p e)
  filter_upwards [eventually_ge_atTop bound] with n hn p
  exact literalGuard_of_threshold p n e ((Finset.le_sup (Finset.mem_univ p)).trans hn)

/-- The successful canonical parse supplies only the emitted segment length.
The hit itself is tested on the original finite permutation, not on the marks. -/
def actualCanonicalFirstKLiteralHit (k : ℕ) (e : ℤ) (n : ℕ) (π : Avoider n) : Prop :=
  ∃ p r, canonicalTuple k n π = some (p,r) ∧ initialHits π.val (emittedLength p) e

private theorem actualCanonicalFirstKLiteralHit_agrees {K H k n} (e : ℤ)
    (big : Tuple.threshold K H k < n) (p : Tuple K H k)
    (π : Avoider n) (ev : p.Event n big π) (guard : literalGuard p n e) :
    actualCanonicalFirstKLiteralHit k e n π ↔ tupleHits p.erase e := by
  obtain ⟨r, rr⟩ := canonicalTuple_agrees_event p big π ev
  have h := tuple_event_literal_hit p big π ev e guard
  constructor
  · rintro ⟨q, s, hs, hit⟩
    rw [rr] at hs
    have hq : p.erase = q := congrArg Prod.fst (Option.some.inj hs)
    exact h.mp (hq.symm ▸ hit)
  · exact fun hh => ⟨p.erase,r,rr,h.mpr hh⟩


/-- On every sufficiently long successful bounded tuple, the literal finite
diagonal test agrees with the erased marked cycles. Both cutoff parameters
are fixed before the length grows; all tests use the original permutation. -/
theorem actualCanonicalFirstKLiteralHit_eventually_agrees (k : ℕ) (e : ℤ) (K H : ℕ) :
    ∀ᶠ n in atTop, ∀ (big : Tuple.threshold K H k < n) (p : Tuple K H k)
      (π : Avoider n), p.Event n big π →
        (actualCanonicalFirstKLiteralHit k e n π ↔ tupleHits p.erase e) := by
  filter_upwards [eventually_literalGuard K H k e] with n hg
  intro big p π ev
  exact actualCanonicalFirstKLiteralHit_agrees e big p π ev (hg p)

end D5.S1.Words.Patterns.Separable.EndpointCanonicalCycle
