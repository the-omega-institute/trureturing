module
import all Init.Data.String.Lemmas.Pattern.Basic
import all Init.Data.String.Lemmas.Pattern.String.Basic
import all Init.Data.String.Lemmas.Pattern.String.ForwardPattern
import all Init.Data.String.Lemmas.Pattern.String.ForwardSearcher
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.Lemmas.Pattern.Char
import all Init.Data.String.Lemmas.Pattern.Pred
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.Lemmas.Pattern.Find.String
import all Init.Data.Iterators.Consumers.Loop
import all Init.Data.Iterators.Consumers.Monadic.Loop
import all OmegaChecks.InitPort.Alternatives.Array
import all OmegaChecks.InitPort.Alternatives.FiniteLoop
public import OmegaChecks.InitPort.Alternatives.StringPattern.Encoding
public import OmegaChecks.InitPort.Alternatives.StringPattern.Searchers
import all OmegaChecks.InitPort.Alternatives.StringPattern.Searchers

/-! Search traces, invariants and matching character positions. -/

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher

public theorem prefixFunction.go._proof_1 :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.go._proof_1) := by
  intro pat stack bound k miss atZero
  subst k
  exact miss ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_zero) bound)

public theorem prefixFunction.go._proof_3 :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.go._proof_3) :=
  private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.go._proof_1

public theorem prefixFunction.go._proof_4 :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.go._proof_4) :=
  @prefixFunction.go._proof_1

open _root_.String.Slice.Pattern.Model.ForwardSliceSearcher

public theorem prefixFunction.le_go_iff :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.le_go_iff) := by
  intro pat stack bound k limit
  delta prefixFunction.go
  let P (n largest : Nat) := k ≤ largest ↔ ∃ i, k ≤ i ∧ i ≤ n ∧ PartialMatch pat pat i (stack + 1)
  apply (private_decl% OmegaChecks.InitPort.Alternatives.fixInvariant) (P := P)
  intro n cont ih
  dsimp only [P]
  by_cases hit : PartialMatch pat pat n (stack + 1)
  · rw [dite_eq_left hit]
    exact ⟨fun h => ⟨_, h, Nat.le_refl _, hit⟩, fun ⟨a, lo, hi, _⟩ => Nat.le_trans lo hi⟩
  · rw [dite_eq_right hit]
    cases n with
    | zero => exact (hit (partialMatch_zero bound)).elim
    | succ n =>
      have prev := ih n (Nat.lt_succ_self n)
      constructor
      · intro h
        obtain ⟨a, lo, hi, yes⟩ := prev.mp h
        exact ⟨a, lo, Nat.le_succ_of_le hi, yes⟩
      · rintro ⟨a, lo, hi, yes⟩
        refine prev.mpr ⟨a, lo, ?_, yes⟩
        exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hi (fun eq => by
          subst a
          exact hit yes))

public theorem prefixFunction.go.eq_def :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.go.eq_def) := by
  intro pat stack bound k
  let go := prefixFunction.go pat stack bound
  have spec (a n) : a ≤ go n ↔ ∃ i, a ≤ i ∧ i ≤ n ∧ PartialMatch pat pat i (stack + 1) :=
    prefixFunction.le_go_iff
  by_cases hit : PartialMatch pat pat k (stack + 1)
  · rw [dite_eq_left hit]
    obtain ⟨i, hi, hk, _⟩ := (spec (go k) k).mp (Nat.le_refl _)
    exact Nat.le_antisymm (Nat.le_trans hi hk) ((spec k k).mpr ⟨k, Nat.le_refl _, Nat.le_refl _, hit⟩)
  · rw [dite_eq_right hit]
    obtain ⟨i, hi, hk, yes⟩ := (spec (go k) k).mp (Nat.le_refl _)
    have before : i < k := Nat.lt_of_le_of_ne hk (fun e => hit (e ▸ yes))
    obtain ⟨j, hj, prev, yes'⟩ := (spec (go (k - 1)) (k - 1)).mp (Nat.le_refl _)
    exact Nat.le_antisymm ((spec (go k) (k - 1)).mpr ⟨i, hi, by omega, yes⟩)
      ((spec (go (k - 1)) k).mpr ⟨j, hj, Nat.le_trans prev (Nat.sub_le ..), yes'⟩)

public theorem le_prefixFunction_iff :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff) := by
  intro k pat stack bound
  exact (private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.le_go_iff)

public theorem prefixFunction_le_iff :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_iff) := by
  intro k pat stack bound
  constructor
  · intro le j hj hst hit
    exact Nat.not_lt_of_ge le (Nat.lt_of_lt_of_le hj ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff).mpr ⟨_, Nat.le_refl _, hst, hit⟩))
  · intro maximal
    apply Nat.le_of_not_lt
    intro gt
    obtain ⟨j, lo, hi, hit⟩ := (private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff).mp (Nat.le_refl (prefixFunction pat stack bound))
    exact maximal _ (Nat.lt_of_lt_of_le gt lo) hi hit

public theorem prefixFunction_eq_iff :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_eq_iff) := by
  intro k pat stack bound
  constructor
  · intro eq
    subst k
    have limit := Nat.le_refl (prefixFunction pat stack bound)
    have maximal := (private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_iff).mp limit
    obtain ⟨j, lo, hi, hit⟩ := (private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff).mp limit
    obtain eq | lt := Nat.eq_or_lt_of_le lo
    · subst j
      exact ⟨hi, hit, maximal⟩
    · exact (maximal _ lt hi hit).elim
  · rintro ⟨hi, hit, maximal⟩
    exact Nat.le_antisymm ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_iff).mpr maximal) ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff).mpr ⟨_, Nat.le_refl _, hi, hit⟩)

public theorem prefixFunctionRecurrence_eq_prefixFunction :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence_eq_prefixFunction) := by
  intro pat pos limit start hs
  delta prefixFunctionRecurrence prefixFunctionRecurrence._unary
  let best := prefixFunction pat pos limit
  let P (q : (g : Nat) ×' g < pos) (v : Nat) :=
    best ≤ q.1 + 1 → PartialMatch pat pat q.1 pos → v = best
  apply (private_decl% OmegaChecks.InitPort.Alternatives.fixInvariant) (P := P) (x := ⟨start, hs⟩)
  rintro ⟨g, hg⟩ cont ih upper hp
  dsimp only
  by_cases same : pat[g] = pat[pos]
  · rw [dite_eq_left same]
    exact Nat.le_antisymm ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff).mpr ⟨_, Nat.le_refl _, hg,
      partialMatch_add_one_add_one_iff.mpr ⟨hp, ⟨_, _, same⟩⟩⟩) upper
  · rw [dite_eq_right same]
    by_cases zero : g = 0
    · rw [dite_eq_left zero]
      subst g
      cases bestEq : best with
      | zero => rfl
      | succ n =>
        have nonzero : best = 1 := (Nat.le_antisymm upper (bestEq ▸ Nat.zero_lt_succ n))
        have hit := ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_eq_iff).mp nonzero).2.1
        have byte := hit.getElem_eq 0 (Nat.zero_lt_succ 0)
        simp only [Nat.add_one_sub_one, Nat.add_zero] at byte
        exact (same byte).elim
    · rw [dite_eq_right zero]
      apply ih
      · apply (private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_iff).mpr
        intro k more small part
        have bound := ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff).mpr ⟨k, Nat.le_refl _, small, part⟩ :
          k ≤ prefixFunction pat pos limit)
        have kbound := Nat.le_trans bound upper
        cases k with
        | zero => exact (Nat.not_lt_zero _ more).elim
        | succ j =>
          obtain ⟨partialPrev, ⟨h₁, h₂, eq⟩⟩ := partialMatch_add_one_add_one_iff.mp part
          have jle : j ≤ g := Nat.le_of_succ_le_succ kbound
          have lt : j < g := Nat.lt_of_le_of_ne jle (fun h => by
            subst j
            exact same eq)
          have inner := hp.partialMatch_iff.mpr ⟨jle, partialPrev⟩
          exact Nat.not_lt_of_ge
            (inner.le_prefixFunction (Nat.pos_of_ne_zero zero) (Nat.le_pred_of_lt lt))
            (Nat.lt_of_succ_lt_succ more)
      · exact (hp.partialMatch_iff.mp (partialMatch_prefixFunction_sub_one (Nat.pos_of_ne_zero zero))).2

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher
open _root_.String _root_.String.Slice _root_.String.Slice.Pattern.Model _root_.String.Slice.Pattern.Model.ForwardSliceSearcher

public theorem Invariants.not_matchesAt_of_prefixFunction_eq :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq) := by
  intro pat s stack needle h k hki hk pos lower upper hs hp different found
  have full := (matchesAt_iff_partialMatch h.isEmpty_eq_false).mp found
  change stack.byteIdx - needle.byteIdx ≤ pos.offset.byteIdx at lower
  change pos.offset.byteIdx < stack.byteIdx - k at upper
  by_cases inside : stack.byteIdx - pos.offset.byteIdx ≤ needle.byteIdx - 1
  · have truncated := full.partialMatch_of_le stack.byteIdx (by omega) (by omega)
    have inner := h.partialMatch.partialMatch_iff.mpr ⟨by omega, truncated⟩
    have bounded := inner.le_prefixFunction (by omega) (by omega)
    rw [hk] at bounded
    omega
  · have eq : stack = needle.offsetBy pos.offset := String.Pos.Raw.ext (by
      change stack.byteIdx = pos.offset.byteIdx + needle.byteIdx
      omega)
    subst stack
    have eqByte := full.getElem_eq needle.byteIdx (by simpa only [String.Pos.Raw.lt_iff,
      _root_.String.Slice.byteIdx_rawEndPos, _root_.String.Slice.utf8ByteSize_eq_size_toByteArray_copy] using hp)
    apply different
    simp only [getUTF8Byte_eq_getUTF8Byte_copy, String.getUTF8Byte]
    simpa only [Nat.add_sub_cancel, String.Pos.Raw.byteIdx_offsetBy, Nat.add_comm] using eqByte.symm

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher
open _root_.String.Slice.Pattern _root_.String.Slice.Pattern.Model _root_.String.Slice.Pattern.Model.ForwardSliceSearcher
open _root_.String.Slice.Pattern.ForwardSliceSearcher _root_.String.Slice
open _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants

public theorem Invariants.isValidSearchFrom_toList :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList) := by
  intro pat s stackPos needlePos it h table ht hn heq p hp
  induction it using Std.Iter.inductSteps generalizing p stackPos needlePos with | step it ihy ihs
  cases heq
  cases hp
  rw [Std.Iter.toList_eq_match_step]
  generalize hit' : (Std.Iter.mk (α := ForwardSliceSearcher s)
    (.proper pat table ht stackPos needlePos hn)).step = it'

  have hit'' := congrArg Subtype.val hit'
  have plausible := it'.property
  simp only [Std.Iter.step_eq, ne_eq, Std.Iter.toIterM] at hit''
  split at hit'' <;> rename_i h₁
  · split at hit'' <;> rename_i h₂
    · split at hit'' <;> rename_i h₃
      · -- Case 1: matched the full pattern
        simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
          Std.PlausibleIterStep.yield, Std.IterM.toIter_mk] at hit''
        have hinc := h.inc _ _ h₂.symm
        have hzero := hinc.zero_of_eq h₃
        rw [s.pos!_eq_pos hinc.isValidForSlice, s.pos!_eq_pos (hzero.isValidForSlice' rfl)] at hit''
        simp only [← hit'', _root_.String.Pos.Raw.inc_unoffsetBy_inc] at ⊢ plausible
        apply IsValidSearchFrom.matched_of_eq (ihy plausible hzero rfl rfl) _ rfl
        simpa [base] using hinc.isLongestMatchAt h₃

      · -- Case 2: matched the next character, but not yet the full pattern
        simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_skip,
          Std.PlausibleIterStep.skip, Std.IterM.toIter_mk] at hit''
        simp only [← hit''] at ⊢ plausible
        exact ihs plausible (h.inc _ _ h₂.symm) rfl (by simp [base])

    · split at hit'' <;> rename_i h₃
      · -- Case 3: mismatch at the start of the pattern -> jump to next position
        simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
          Std.PlausibleIterStep.yield, Std.IterM.toIter_mk] at hit''
        cases h₃
        rw [s.pos!_eq_pos (h.isValidForSlice' rfl)] at hit''
        simp only [← hit''] at ⊢ plausible
        apply IsValidSearchFrom.mismatched_of_eq _ (by simp [base]) _ (by simp [base])
        · exact ihy plausible (.offset h.isEmpty_eq_false) rfl rfl
        · simp only [base, _root_.String.Pos.Raw.unoffsetBy_zero, Pos.le_iff, offset_pos, lt_posGT_iff]
          intro pos hp₁ hp₂
          obtain rfl : stackPos = pos.offset := Std.le_antisymm hp₁ hp₂
          intro found
          obtain ⟨_, same⟩ := (matchesAt_iff_getElem h.isEmpty_eq_false).mp found
          have nonempty : 0 < pat.utf8ByteSize := Nat.pos_of_ne_zero (fun z =>
            Bool.noConfusion (h.isEmpty_eq_false.symm.trans (isEmpty_iff.mpr z)))
          have inBounds := pat.utf8ByteSize_eq_size_toByteArray_copy ▸ nonempty
          have atZero := same 0 inBounds
          apply h₂
          simpa only [getUTF8Byte_eq_getUTF8Byte_copy, String.getUTF8Byte, _root_.String.Pos.Raw.byteIdx_zero, Nat.add_zero] using atZero.symm

      · cases ht
        simp only [getElem_buildTable] at hit''

        split at hit'' <;> rename_i h₄
        · -- Case 4: mismatch in the middle of the pattern, and no common prefix ->
          -- jump to next position if not at the start of the character
          simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
            Std.PlausibleIterStep.yield, Std.IterM.toIter_mk] at hit''
          rw [s.pos!_eq_pos h.isValidForSlice] at hit''
          simp only [← hit''] at ⊢ plausible
          apply IsValidSearchFrom.mismatched_of_eq _ _ _ (by simp [base])
          · exact ihy plausible (.offset h.isEmpty_eq_false) rfl rfl
          · have := h.partialMatch.needlePos_le_stackPos
            simp only [_root_.String.Pos.Raw.ext_iff, _root_.String.Pos.Raw.byteIdx_zero, base, lt_posGE_iff, offset_pos,
              _root_.String.Pos.Raw.lt_iff, _root_.String.Pos.Raw.byteIdx_unoffsetBy, gt_iff_lt] at ⊢ h₃
            omega
          · simp only [base, lt_posGE_iff]
            exact fun p hp₁ hp₂ => (private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq) h h₄ _ hp₁ hp₂ h₂

        · -- Case 5: mismatch in the middle of the pattern with a common prefix
          simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
            Std.PlausibleIterStep.yield, Std.IterM.toIter_mk] at hit''
          rw [s.pos!_eq_pos h.isValidForSlice,
            s.pos!_eq_pos (h.of_prefixFunction_eq h₃ rfl (by omega)).isValidForSlice] at hit''
          simp only [← hit''] at ⊢ plausible
          apply IsValidSearchFrom.mismatched_of_eq _ _ _ (by simp [base])
          · exact ihy plausible (h.of_prefixFunction_eq h₃ rfl (by omega)) rfl rfl
          · have h₅ := h.partialMatch.needlePos_le_stackPos
            simp [base, Pos.lt_iff, _root_.String.Pos.Raw.ext_iff] at ⊢ h₃ h₅
            apply _root_.String.Pos.Raw.unoffsetBy_lt_unoffsetBy_of_le_of_lt
            all_goals exact Std.lt_of_le_of_lt prefixFunction_le (by simp [_root_.String.Pos.Raw.lt_iff]; omega)
          · exact fun p hp₁ hp₂ => (private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq) h rfl _ hp₁ hp₂ h₂

  · split at hit'' <;> rename_i h₂
    · -- Case 6: so close to the end that we cannot match anymore -> reject, then done
      simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
        Std.PlausibleIterStep.yield, Std.IterM.toIter_mk] at hit''
      rw [s.pos!_eq_pos h.isValidForSlice] at hit''
      simp only [← hit''] at ⊢ plausible
      apply IsValidSearchFrom.mismatched_of_eq _ _ _ (by simp [base])
      · rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
        simpa [Std.Iter.toIterM] using IsValidSearchFrom.endPos
      · simp only [_root_.String.Pos.Raw.lt_iff, _root_.String.Pos.Raw.byteIdx_unoffsetBy, byteIdx_rawEndPos, base, Pos.lt_iff,
          offset_pos, offset_endPos] at ⊢ h₂
        omega
      · refine fun p hp₁ hp₂ hm => ?_
        have := le_of_matchesAt h.isEmpty_eq_false hm
        simp only [base, Pos.le_iff, offset_pos, _root_.String.Pos.Raw.le_iff, _root_.String.Pos.Raw.byteIdx_unoffsetBy,
          Nat.sub_le_iff_le_add, _root_.String.Pos.Raw.byteIdx_increaseBy, byteIdx_rawEndPos,
          Nat.not_le] at hp₁ this h₁
        omega

    · --  Case 7: reached the end with empty partial match -> done
      simp only [base, ← hit'', Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_done,
        Std.PlausibleIterStep.done, Std.IterM.toIter_mk]
      apply IsValidSearchFrom.endPos_of_eq (Std.le_antisymm (Pos.le_endPos _) _) rfl
      simpa [_root_.String.Pos.Raw.le_iff, Pos.le_iff, _root_.String.Pos.Raw.lt_iff] using h₂

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardStringSearcher

public theorem lawfulToForwardSearcherModel :
    type_of% @_root_.String.Slice.Pattern.Model.ForwardStringSearcher.lawfulToForwardSearcherModel := by
  intro pat nonempty
  refine ⟨fun s => ?_⟩
  exact (_root_.String.Slice.Pattern.Model.ForwardStringSearcher.isValidSearchFrom_iff_isValidSearchFrom_toSlice).mpr
    ((_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.lawfulToForwardSearcherModel
      (toSliceNonempty nonempty)).isValidSearchFrom_toList s)

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardStringSearcher

namespace OmegaChecks.InitPort.Alternatives
open _root_.Std _root_.Std.Iterators
private theorem anyFiniteAux {α β : Type u} [Iterator α Id β] [Finite α Id]
    (p : β → Bool) (it : IterM (α := α) Id β) (P : β → Prop)
    (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b) :
    it.toIter.toList.any p =
      finiteForIn (n := Id) (fun _ _ f c => f c.run) Bool (fun _ _ _ => True)
        it false P hP (fun out _ _ => ⟨if p out then .done true else .yield false, trivial⟩) := by
  induction it using (Finite.wf (α := α) (m := Id) (β := β)).induction with
  | h it ih =>
    rw [_root_.Std.Iter.toList_eq_match_step]
    unfold finiteForIn
    rw [WellFounded.fix_eq]
    unfold Iter.step
    dsimp only [Id.run, IterM.toIter, Iter.toIterM]
    cases it.step.inflate using PlausibleIterStep.casesOn with
    | yield next out h =>
      dsimp only [IterM.Step.toPure, IterStep.mapIterator, List.any_cons, bind, pure]
      cases p out
      · apply ih next (IterM.isPlausibleSuccessorOf_of_yield h)
      · rfl
    | skip next h => exact ih next (IterM.isPlausibleSuccessorOf_of_skip h) _
    | done _ => rfl

private theorem finiteAnyToList {α β : Type u} [Iterator α Id β] [Finite α Id]
    (p : β → Bool) (it : Iter (α := α) β) :
    it.toList.any p = @Iter.any α β _ finiteIteratorLoop p it :=
  anyFiniteAux p it.toIterM _ (fun _ => id)

open _root_.String.Slice _root_.String.Slice.Pattern _root_.String.Slice.Pattern.Model

private theorem firstMatch {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    {s : String.Slice} {p : s.Pos} {steps : List (SearchStep s)}
    (valid : IsValidSearchFrom pat p steps) (q : s.Pos) :
    steps.findSome? (fun | .matched pos _ => some pos | .rejected .. => none) = some q ↔
      p ≤ q ∧ MatchesAt pat q ∧ ∀ r, p ≤ r → r < q → ¬ MatchesAt pat r := by
  induction valid with
  | endPos =>
    refine ⟨(fun h => nomatch h), fun ⟨hle, hm, _⟩ => ?_⟩
    exact (not_matchesAt_endPos ((Std.le_antisymm (Pos.le_endPos q) hle) ▸ hm)).elim
  | @matched _ start stop hit tail ih =>
    constructor
    · intro eq
      obtain rfl := Option.some.inj eq
      exact ⟨Nat.le_refl _, hit.matchesAt, fun _ bound before =>
        (Nat.not_lt_of_ge bound before).elim⟩
    · rintro ⟨bound, _, first⟩
      by_cases same : start = q
      · cases same; rfl
      · have lt : start < q := Std.lt_of_le_of_ne bound same
        exact (first start (Nat.le_refl _) lt hit.matchesAt).elim
  | @mismatched _ start stop lt miss tail ih =>
    refine ih.trans ⟨?_, ?_⟩
    · rintro ⟨bound, yes, first⟩
      refine ⟨Nat.le_trans (Nat.le_of_lt lt) bound, yes, fun r lo hi => ?_⟩
      by_cases below : stop ≤ r
      · exact first r below hi
      · exact miss r lo (Nat.lt_of_not_ge below)
    · rintro ⟨bound, yes, first⟩
      have after : stop ≤ q := Nat.le_of_not_gt fun before => miss q bound before yes
      exact ⟨after, yes, fun r lo => first r (Nat.le_trans (Nat.le_of_lt lt) lo)⟩

public theorem String.Slice.Pattern.Model.find?_eq_some_iff :
    type_of% @_root_.String.Slice.Pattern.Model.find?_eq_some_iff := by
  intro ρ pat model strict σ iter finite loop lawful search valid s pos
  unfold _root_.String.Slice.find?
  rw [← _root_.Std.Iter.findSome?_toList]
  refine (firstMatch (LawfulToForwardSearcherModel.isValidSearchFrom_toList (pat := pat) s) pos).trans ?_
  exact ⟨fun ⟨_, yes, first⟩ => ⟨yes, fun r => first r (Pos.startPos_le _)⟩,
    fun ⟨yes, first⟩ => ⟨Pos.startPos_le _, yes, fun r _ => first r⟩⟩

public theorem String.Slice.Pattern.Model.find?_eq_none_iff :
    type_of% @_root_.String.Slice.Pattern.Model.find?_eq_none_iff := by
  intro ρ pat model strict σ iter finite loop lawful search valid s
  constructor
  · intro no q
    induction q using WellFounded.induction Pos.wellFounded_lt with
    | h q ih =>
      intro yes
      have someMatch := (_root_.String.Slice.Pattern.Model.find?_eq_some_iff pat).mpr ⟨yes, ih⟩
      exact nomatch (no.symm.trans someMatch)
  · intro absent
    cases eq : s.find? pat with
    | none => rfl
    | some q => exact (absent q ((_root_.String.Slice.Pattern.Model.find?_eq_some_iff pat).mp eq).1).elim

public theorem String.Slice.isSome_find? : type_of% @_root_.String.Slice.isSome_find? := by
  intro ρ pat σ iter finite loop lawful search s
  unfold _root_.String.Slice.find? _root_.String.Slice.contains
  rw [← _root_.Std.Iter.findSome?_toList, ← _root_.Std.Iter.any_toList]
  induction (ToForwardSearcher.toSearcher pat s).toList with
  | nil => rfl
  | cons step steps ih => cases step <;> first | rfl | exact ih

public theorem String.Slice.Pattern.Model.contains_eq_true_iff :
    type_of% @_root_.String.Slice.Pattern.Model.contains_eq_true_iff := by
  intro ρ pat model strict σ iter finite loop lawful search valid s
  rw [← _root_.String.Slice.isSome_find? pat]
  cases eq : s.find? pat with
  | none =>
    exact ⟨(fun h => nomatch h), fun ⟨q, yes⟩ =>
      ((_root_.String.Slice.Pattern.Model.find?_eq_none_iff pat).mp eq q yes).elim⟩
  | some q =>
    exact ⟨fun _ => ⟨q, ((_root_.String.Slice.Pattern.Model.find?_eq_some_iff pat).mp eq).1⟩,
      fun _ => rfl⟩

public theorem String.Slice.Pattern.Model.posFind?_eq_some_iff :
    type_of% @_root_.String.Slice.Pattern.Model.posFind?_eq_some_iff := by
  intro ρ pat model strict σ iter finite loop lawful search valid s p q
  rw [_root_.String.Slice.Pos.find?_eq_find?_sliceFrom, Option.map_eq_some_iff]
  constructor
  · rintro ⟨r, found, rfl⟩
    obtain ⟨matched, first⟩ := (_root_.String.Slice.Pattern.Model.find?_eq_some_iff pat).mp found
    refine ⟨Pos.le_ofSliceFrom, matchesAt_iff_matchesAt_ofSliceFrom.mp matched, ?_⟩
    intro x lo hi yes
    apply first (Pos.sliceFrom p x lo) (Pos.sliceFrom_lt_iff.mpr hi)
    apply matchesAt_iff_matchesAt_ofSliceFrom.mpr
    exact Pos.ofSliceFrom_sliceFrom.symm ▸ yes
  · rintro ⟨lo, matched, first⟩
    refine ⟨Pos.sliceFrom p q lo, (_root_.String.Slice.Pattern.Model.find?_eq_some_iff pat).mpr ?_,
      Pos.ofSliceFrom_sliceFrom⟩
    refine ⟨matchesAt_iff_matchesAt_ofSliceFrom.mpr (Pos.ofSliceFrom_sliceFrom.symm ▸ matched), ?_⟩
    intro x before yes
    exact first _ Pos.le_ofSliceFrom (Pos.lt_sliceFrom_iff.mp before) (matchesAt_iff_matchesAt_ofSliceFrom.mp yes)

public theorem String.Slice.Pattern.Model.posFind?_eq_none_iff :
    type_of% @_root_.String.Slice.Pattern.Model.posFind?_eq_none_iff := by
  intro ρ pat model strict σ iter finite loop lawful search valid s p
  rw [_root_.String.Slice.Pos.find?_eq_find?_sliceFrom, Option.map_eq_none_iff,
    _root_.String.Slice.Pattern.Model.find?_eq_none_iff]
  constructor
  · intro absent q lo yes
    apply absent (Pos.sliceFrom p q lo)
    exact matchesAt_iff_matchesAt_ofSliceFrom.mpr (Pos.ofSliceFrom_sliceFrom.symm ▸ yes)
  · intro absent q yes
    exact absent _ Pos.le_ofSliceFrom (matchesAt_iff_matchesAt_ofSliceFrom.mp yes)

private theorem anyMatched {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    {s : String.Slice} {pos : s.Pos} {steps : List (SearchStep s)}
    (h : IsValidSearchFrom pat pos steps) :
    steps.any (· matches .matched ..) = true ↔ ∃ q : s.Pos, pos ≤ q ∧ MatchesAt pat q := by
  induction h with
  | endPos =>
    refine ⟨fun h => False.elim (Bool.noConfusion h), ?_⟩
    rintro ⟨q, bound, m⟩
    exact False.elim (not_matchesAt_endPos ((Std.le_antisymm (Pos.le_endPos q) bound) ▸ m))
  | matched h _ _ =>
    exact ⟨fun _ => ⟨_, Std.le_refl _, h.matchesAt⟩, fun _ => rfl⟩
  | mismatched lt miss tail ih =>
    rename_i start stop
    refine ⟨fun a => ?_, fun ⟨q, bound, m⟩ => ?_⟩
    · obtain ⟨q, b, m⟩ := ih.mp a
      exact ⟨q, Std.le_trans (Std.le_of_lt lt) b, m⟩
    · apply ih.mpr
      by_cases hb : stop ≤ q
      · exact ⟨q, hb, m⟩
      · change ¬ stop.offset.byteIdx ≤ q.offset.byteIdx at hb
        exact False.elim (miss q bound (Nat.lt_of_not_ge hb) m)

public theorem String.Slice.contains_slice_iff {t s : String.Slice} :
    @_root_.String.Slice.contains _ _ _
      (fun _ => OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.ForwardSliceSearcher.instIteratorLoopIdSearchStep) s t _ ↔ t.copy.toList <:+: s.copy.toList := by
  unfold _root_.String.Slice.contains
  change @Iter.any _ _ _ finiteIteratorLoop (fun (x : SearchStep s) => x matches .matched ..) (ToForwardSearcher.toSearcher t s) = true ↔ _
  rw [← finiteAnyToList (it := ToForwardSearcher.toSearcher t s)]
  cases ht : t.isEmpty with
  | true =>
    rw [_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.toSearcher_of_isEmpty ht,
      _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.toList_emptyBefore_eq,
      _root_.String.Slice.copy_eq_empty_iff.mpr ht]
    split <;> exact ⟨fun _ => List.nil_infix, fun _ => rfl⟩
  | false =>
    letI := _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.strictPatternModel ht
    have valid := (_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.lawfulToForwardSearcherModel ht).isValidSearchFrom_toList s
    refine (anyMatched valid).trans (Iff.trans ?_ ((_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.exists_matchesAt_iff_eq_append).trans
      _root_.String.Slice.isInfix_toList_iff.symm))
    exact ⟨fun ⟨q, _, m⟩ => ⟨q, m⟩, fun ⟨q, m⟩ => ⟨q, Pos.startPos_le _, m⟩⟩
end OmegaChecks.InitPort.Alternatives

namespace OmegaChecks.InitPort.Alternatives

public theorem String.Slice.contains_string_iff :
    type_of% @_root_.String.Slice.contains_string_iff := by
  intro t s
  rw [_root_.String.Slice.contains_string_eq_contains_toSlice]
  have h := _root_.String.Slice.contains_slice_iff (t := t.toSlice) (s := s)
  rw [_root_.String.copy_toSlice] at h
  exact h

public theorem String.contains_slice_iff :
    type_of% @_root_.String.contains_slice_iff := by
  intro t s
  rw [_root_.String.contains_eq_contains_toSlice]
  have h := _root_.String.Slice.contains_slice_iff (t := t) (s := s.toSlice)
  rw [_root_.String.copy_toSlice] at h
  exact h

public theorem String.contains_string_iff :
    type_of% @_root_.String.contains_string_iff := by
  intro t s
  rw [_root_.String.contains_eq_contains_toSlice]
  have h := _root_.String.Slice.contains_string_iff (t := t) (s := s.toSlice)
  rw [_root_.String.copy_toSlice] at h
  exact h

end OmegaChecks.InitPort.Alternatives

namespace OmegaChecks.InitPort.Alternatives

public theorem List.isPrefixOf_iff_prefix :
    type_of% @_root_.List.isPrefixOf_iff_prefix := by
  intro α _ _ needle haystack
  induction needle generalizing haystack with
  | nil => exact ⟨fun _ => List.nil_prefix, fun _ => rfl⟩
  | cons a as ih =>
    cases haystack with
    | nil =>
      exact ⟨fun h => False.elim (Bool.noConfusion h), fun h => nomatch List.eq_nil_of_prefix_nil h⟩
    | cons b bs =>
      change (_ && _) = true ↔ _
      exact Bool.and_eq_true_iff.trans ((and_congr beq_iff_eq (ih (haystack := bs))).trans List.cons_prefix_cons.symm)

public theorem List.isInfixOf_internal_iff_isInfix :
    type_of% @_root_.List.isInfixOf_internal_iff_isInfix := by
  intro α _ _ needle haystack
  induction haystack with
  | nil =>
    cases needle with
    | nil => exact ⟨fun _ => List.infix_rfl, fun _ => rfl⟩
    | cons a as =>
      exact ⟨fun h => False.elim (Bool.noConfusion h),
        fun h => nomatch List.eq_nil_of_infix_nil h⟩
  | cons a as ih =>
    change (_ || _) = true ↔ _
    exact Bool.or_eq_true_iff.trans ((or_congr _root_.List.isPrefixOf_iff_prefix ih).trans
      List.infix_cons_iff.symm)

end OmegaChecks.InitPort.Alternatives
