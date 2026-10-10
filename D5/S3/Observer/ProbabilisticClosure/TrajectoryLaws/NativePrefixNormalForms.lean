/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePrefixNormalForms
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePrefixNormalForms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered paid retries and all payload cuts have unique concatenated witnesses. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixState

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixState

open FourthSegmentStoppedLaw (Letter ActivePhase loopWord pWord)

/-- Decoder of concatenated witnesses, separate from native execution. -/
def parsePayload (n : ℕ) (last : Letter) (phase : ActivePhase) (j : ℕ) :
    List Operation → Option (PayloadForm n last)
  | [] => match n with | 0 => some .pending | _ + 1 => some (.active j phase)
  | op :: ops => match n with
    | 0 => match op, ops with
        | .stop b, [] => if b = last then some .delivered else none
        | _, _ => none
    | n + 1 => match op with
        | .stop _ => none
        | .read x => match phase with
          | .p => if x = 0 then (parsePayload n 0 .p 0 ops).map (.segment j 0)
              else parsePayload (n + 1) last .beta j ops
          | .beta => if x = 0 then parsePayload (n + 1) last .p (j + 1) ops
              else (parsePayload n 1 .p 0 ops).map (.segment j 1)

def parseSeed (u : List Letter) (first : Option Letter) : List Operation → Option PrefixForm
  | [] => some ⟨u, match first with | none => .ready | some x => .first x⟩
  | .stop _ :: _ => none
  | .read x :: ops => match first with
      | none => parseSeed u (some x) ops
      | some y => if x = y then parseSeed (u ++ [y]) none ops
          else (parsePayload 4 0 .p 0 ops).map (fun p => ⟨u, .acquired y p⟩)

def addLoops {n : ℕ} {last : Letter} (k : ℕ) : PayloadForm n last → PayloadForm n last
  | .active j phase => .active (k + j) phase
  | .segment j b rest => .segment (k + j) b rest
  | .pending => .pending
  | .delivered => .delivered

private theorem loop_snoc (j : ℕ) : loopWord (j + 1) = loopWord j ++ [1, 0] := by
  simp [loopWord, List.replicate_succ', List.flatten_append]

private theorem parse_render_payload {n : ℕ} {last : Letter} (p : PayloadForm n last) :
    ∀ k, parsePayload n last .p k (renderPayload p) = some (addLoops k p) := by
  induction p with
  | active j phase =>
      induction j with
      | zero =>
          intro k; cases phase <;>
            simp [renderPayload, phaseWord, loopWord, reads, parsePayload, addLoops]
      | succ j ih =>
          intro k
          simpa [renderPayload, phaseWord, FourthSegmentStoppedLaw.loop_succ,
            reads, parsePayload, addLoops,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)
  | @segment n last j b rest ih =>
      induction j with
      | zero =>
          intro k
          have hz : addLoops 0 rest = rest := by cases rest <;> simp [addLoops]
          have hs := (ih 0).trans (congrArg some hz)
          have hm := congrArg (fun z : Option (PayloadForm n b) =>
            z.map (PayloadForm.segment (last := last) k b)) hs
          fin_cases b <;> exact hm
      | succ j hj =>
          intro k
          simpa [renderPayload, phaseWord, FourthSegmentStoppedLaw.p_word_succ,
            reads, parsePayload, addLoops,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj (k + 1)
  | pending => intro k; rfl
  | delivered => intro k; simp [renderPayload, parsePayload, addLoops]

private theorem parse_render_seed (nf : PrefixForm) (u : List Letter) :
    parseSeed u none (render nf) = some ⟨u ++ nf.retries, nf.tail⟩ := by
  rcases nf with ⟨v, tail⟩
  induction v generalizing u with
  | nil =>
      cases tail with
      | ready => simp [render, retryWord, reads, parseSeed]
      | first x => simp [render, retryWord, reads, parseSeed]
      | acquired rho p =>
          have hp := parse_render_payload p 0
          have ha : addLoops 0 p = p := by cases p <;> simp [addLoops]
          fin_cases rho <;>
            simpa [render, retryWord, reads, seedWord, parseSeed, ha] using hp
  | cons x v ih =>
      simpa [render, retryWord, reads, parseSeed, List.append_assoc] using ih (u ++ [x])

/-- The independent grammar has an exact inverse, including ordered retry blocks. -/
theorem prefix_form_unique : Function.Injective render := by
  intro nf ng h
  have he := congrArg (parseSeed [] none) h
  cases nf
  cases ng
  simpa [parse_render_seed] using he

def freshPayload (n : ℕ) (last : Letter) : PayloadForm n last :=
  match n with | 0 => .pending | _ + 1 => .active 0 .p

/-- Appending one actual operation updates a proof witness, not runtime state. -/
def appendPayload {n : ℕ} {last : Letter} :
    PayloadForm n last → Operation → Option (PayloadForm n last)
  | .active (n := n) j .p, .read x =>
      if x = 0 then some (.segment j 0 (freshPayload n 0)) else some (.active j .beta)
  | .active (n := n) j .beta, .read x =>
      if x = 0 then some (.active (j + 1) .p) else some (.segment j 1 (freshPayload n 1))
  | .active _ _, .stop _ => none
  | .segment j b rest, op => (appendPayload rest op).map (.segment j b)
  | .pending, .stop b => if b = last then some .delivered else none
  | .pending, .read _ => none
  | .delivered, _ => none

def appendForm (nf : PrefixForm) (op : Operation) : Option PrefixForm :=
  match nf.tail, op with
  | .ready, .read x => some ⟨nf.retries, .first x⟩
  | .first y, .read x => some (if x = y then ⟨nf.retries ++ [y], .ready⟩
      else ⟨nf.retries, .acquired y (freshPayload 4 0)⟩)
  | .acquired rho p, op => (appendPayload p op).map (fun q => ⟨nf.retries, .acquired rho q⟩)
  | _, .stop _ => none

private theorem render_fresh (n : ℕ) (last : Letter) :
    renderPayload (freshPayload n last) = [] := by
  cases n <;> rfl

private theorem render_append_payload {n : ℕ} {last : Letter}
    (p q : PayloadForm n last) (op : Operation) (h : appendPayload p op = some q) :
    renderPayload q = renderPayload p ++ [op] := by
  induction p with
  | active j phase =>
      cases op with
      | stop b => simp [appendPayload] at h
      | read x =>
          cases phase <;> fin_cases x <;>
            simp [appendPayload] at h <;> subst q
          · simp [renderPayload, phaseWord, pWord, render_fresh, reads, List.map_append]
          · simp [renderPayload, phaseWord, reads, List.map_append]
          · simp [renderPayload, phaseWord, loop_snoc, reads, List.map_append, List.append_assoc]
          · simp [renderPayload, phaseWord, pWord, render_fresh, reads,
              List.map_append, List.append_assoc]
  | segment j b rest ih =>
      simp only [appendPayload, Option.map_eq_some_iff] at h
      obtain ⟨q', hq', rfl⟩ := h
      simp only [renderPayload, ih q' hq', List.append_assoc]
  | pending =>
      cases op with
      | read x => simp [appendPayload] at h
      | stop b =>
          simp only [appendPayload] at h
          split_ifs at h with hb
          · cases h; subst b; rfl
  | delivered => cases op <;> simp [appendPayload] at h

/-- Concatenation commutes with the independent right extension of witnesses. -/
theorem render_append_form (nf ng : PrefixForm) (op : Operation)
    (h : appendForm nf op = some ng) : render ng = render nf ++ [op] := by
  rcases nf with ⟨u, tail⟩
  cases tail with
  | ready =>
      cases op <;> simp only [appendForm, Option.some.injEq, reduceCtorEq] at h
      cases h
      simp [render]
  | first y =>
      cases op with
      | stop b => simp [appendForm] at h
      | read x =>
          fin_cases y <;> fin_cases x <;> simp [appendForm] at h <;> subst ng <;>
            simp [render, retryWord, seedWord, render_fresh, reads, List.map_append,
              List.flatten_append, List.append_assoc]
  | acquired rho p =>
      simp only [appendForm, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, rfl⟩ := h
      simp [render, render_append_payload p q op hq, List.append_assoc]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixState
