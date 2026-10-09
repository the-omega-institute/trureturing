/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every legal initialized prefix earns its unique full native state and paid counts. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePrefixNormalForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixState

open FourthSegmentStoppedLaw (Letter ActivePhase FourthControl loopWord pWord)

private theorem execute_append (c : AcquiredNativeState) (u v : List Operation) :
    execute c (u ++ v) = (execute c u).bind (fun d => execute d v) := by
  induction u generalizing c with
  | nil => rfl
  | cons op u ih => simp [execute, ih, Option.bind_assoc]

private theorem reconstruct_append_payload {n : ℕ} {last : Letter}
    (p : PayloadForm n last) (op : Operation) (t : ℕ) (r : Registers) (s : ℕ) (c : Counts)
    (ht : t + n = 4) :
    nativeStep (reconstructPayload t r s c p) op =
      (appendPayload p op).map (reconstructPayload t r s c) := by
  induction p generalizing t r s c with
  | @active n last j phase =>
      have ht' : t ≤ 3 := by omega
      have hn' : n ≤ 3 := by omega
      cases op with
      | stop b =>
          interval_cases t <;> cases phase <;>
            simp [reconstructPayload, nativeStep, nativeStop, finiteStop,
              payloadControl, appendPayload]
      | read x =>
          interval_cases t <;> interval_cases n <;> try omega
          all_goals cases phase <;> fin_cases x <;>
            simp [reconstructPayload, nativeStep, nativeRead, finiteRead, payloadRead,
              isReturn, countRead, payloadControl, completionControl, appendPayload,
              freshPayload, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | @segment n last j b rest ih =>
      simpa [reconstructPayload, appendPayload, Option.map_map, Function.comp_def] using
        ih (t + 1) (writeMarker r t b) (s + j)
          ⟨c.alpha + j + (1 - b.val), c.beta + j + 2 * b.val⟩ (by omega)
  | pending =>
      cases op <;> simp [reconstructPayload, nativeStep, nativeRead, finiteRead,
        nativeStop, finiteStop, appendPayload]
  | delivered =>
      cases op <;> rfl

/-- The literal transaction table agrees with independent witness extension. -/
theorem reconstruct_append_form (nf : PrefixForm) (op : Operation) :
    nativeStep (reconstruct nf) op = (appendForm nf op).map reconstruct := by
  rcases nf with ⟨u, tail⟩
  cases tail with
  | ready =>
      cases op <;> simp [reconstruct, appendForm, nativeStep, nativeRead, finiteRead,
        nativeStop, finiteStop, isReturn]
  | first y =>
      cases op with
      | stop b => rfl
      | read x =>
          fin_cases y <;> fin_cases x <;>
            simp [reconstruct, appendForm, nativeStep, nativeRead, finiteRead,
              acquiredRegisters, emptyRegisters, isReturn,
              countRead, retryCounts, List.count_append, freshPayload, reconstructPayload,
              Nat.mul_add, Nat.add_assoc]
  | acquired rho p =>
      simpa [reconstruct, appendForm, Option.map_map, Function.comp_def] using
        reconstruct_append_payload p op 0 (acquiredRegisters rho) 0
          ⟨(retryCounts u).alpha + 1, (retryCounts u).beta + 1⟩ (by omega)

private theorem execute_payload {n : ℕ} {last : Letter} (p : PayloadForm n last)
    (t : ℕ) (r : Registers) (s : ℕ) (c : Counts) (ht : t + n = 4) :
    execute (reconstructPayload t r s c (freshPayload n last)) (renderPayload p) =
      some (reconstructPayload t r s c p) := by
  induction p generalizing t r s c with
  | @active n last j phase =>
      have ht' : t ≤ 3 := by omega
      have he := execute_payload_loops t ht' r s c j (reads (phaseWord phase))
      have hz : execute (atPhase t r (s + j) ⟨c.alpha + j, c.beta + j⟩ .p)
          (reads (phaseWord phase)) =
            some (reconstructPayload t r s c (.active (n := n) (last := last) j phase)) := by
        cases phase
        · rfl
        · interval_cases t <;>
            simp [phaseWord, reconstructPayload, reads, atPhase, execute, nativeStep,
              nativeRead, finiteRead, payloadRead, payloadControl, isReturn, countRead]
      simpa [freshPayload, reconstructPayload, renderPayload, reads, List.map_append,
        atPhase] using he.trans hz
  | @segment n last j b rest ih =>
      have ht' : t ≤ 3 := by omega
      have hn' : n ≤ 3 := by omega
      have he := execute_payload_loops t ht' r s c j
        (reads (if b = 0 then [0] else [1, 1]) ++ renderPayload rest)
      have hi := ih (t + 1) (writeMarker r t b) (s + j)
        ⟨c.alpha + j + (1 - b.val), c.beta + j + 2 * b.val⟩ (by omega)
      have hz : execute (atPhase t r (s + j) ⟨c.alpha + j, c.beta + j⟩ .p)
          (reads (if b = 0 then [0] else [1, 1]) ++ renderPayload rest) =
            some (reconstructPayload t r s c (.segment (last := last) j b rest)) := by
        interval_cases t <;> interval_cases n <;> try omega
        all_goals fin_cases b <;>
          simpa [freshPayload, reconstructPayload, reads, execute, atPhase, nativeStep, nativeRead,
            finiteRead, payloadRead, payloadControl, completionControl, isReturn,
            countRead, Nat.add_assoc] using hi
      simpa [freshPayload, reconstructPayload, renderPayload, pWord, reads,
        List.map_append, List.append_assoc, atPhase] using he.trans hz
  | pending => rfl
  | delivered => simp [freshPayload, renderPayload, reconstructPayload, execute,
      nativeStep, nativeStop, finiteStop]

private theorem execute_seed (nf : PrefixForm) (c : Counts) :
    execute ⟨⟨⟨.seed none, emptyRegisters⟩, 0⟩, c⟩ (render nf) =
      some (match nf.tail with
        | .ready => ⟨⟨⟨.seed none, emptyRegisters⟩, 0⟩,
            ⟨c.alpha + (retryCounts nf.retries).alpha, c.beta + (retryCounts nf.retries).beta⟩⟩
        | .first x => ⟨⟨⟨.seed (some x), emptyRegisters⟩, 0⟩,
            countRead ⟨c.alpha + (retryCounts nf.retries).alpha,
              c.beta + (retryCounts nf.retries).beta⟩ x⟩
        | .acquired rho p => reconstructPayload 0 (acquiredRegisters rho) 0
            ⟨c.alpha + (retryCounts nf.retries).alpha + 1,
              c.beta + (retryCounts nf.retries).beta + 1⟩ p) := by
  rcases nf with ⟨u, tail⟩
  induction u generalizing c with
  | nil =>
      cases tail with
      | ready => simp [render, retryWord, reads, retryCounts, execute]
      | first x => fin_cases x <;> simp [render, retryWord, reads, retryCounts,
          execute, nativeStep, nativeRead, finiteRead, emptyRegisters, isReturn, countRead]
      | acquired rho p =>
          have he := execute_payload p 0 (acquiredRegisters rho) 0
            ⟨c.alpha + 1, c.beta + 1⟩ (by omega)
          fin_cases rho <;>
            simpa [render, retryWord, retryCounts, seedWord, reads, execute,
              nativeStep, nativeRead, finiteRead, acquiredRegisters, emptyRegisters,
              isReturn, countRead,
              freshPayload, reconstructPayload] using he
  | cons x u ih =>
      fin_cases x
      · simpa [render, retryWord, reads, execute, nativeStep, nativeRead, finiteRead,
          isReturn, countRead, retryCounts, Nat.mul_add, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using ih ⟨c.alpha + 2, c.beta⟩
      · simpa [render, retryWord, reads, execute, nativeStep, nativeRead, finiteRead,
          isReturn, countRead, retryCounts, Nat.mul_add, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using ih ⟨c.alpha, c.beta + 2⟩

/-- Every independently concatenated form executes legally from the one initialization. -/
theorem run_render (nf : PrefixForm) : run (render nf) = some (reconstruct nf) := by
  have h := execute_seed nf ⟨0, 0⟩
  cases he : nf.tail <;> simpa [run, initial, reconstruct, he, retryCounts] using h

private theorem legal_has_form (ops : List Operation) (h : Legal ops) :
    ∃ nf, render nf = ops ∧ run ops = some (reconstruct nf) := by
  induction ops using List.reverseRecOn with
  | nil => exact ⟨⟨[], .ready⟩, rfl, rfl⟩
  | append_singleton ops op ih =>
      obtain ⟨c, hc⟩ := h
      have hr : run (ops ++ [op]) = (run ops).bind (fun d => nativeStep d op) := by
        simp [run, execute_append, execute]
      rw [hr] at hc
      obtain ⟨d, hd, hs⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨nf, hf, hn⟩ := ih ⟨d, hd⟩
      have hd' : d = reconstruct nf := Option.some.inj (hd.symm.trans hn)
      subst d
      rw [reconstruct_append_form] at hs
      obtain ⟨ng, hg, hrec⟩ := Option.map_eq_some_iff.mp hs
      exact ⟨ng, (render_append_form nf ng op hg).trans (by rw [hf]),
        (hr.trans (by rw [hn]; simp [reconstruct_append_form, hg]))⟩

/-- Each completed native block refines the already frozen local first-completion parser. -/
def SegmentRefinements {n : ℕ} {last : Letter} : PayloadForm n last → Prop
  | .segment j b rest =>
      FourthSegmentStoppedLaw.Parses (.active .p) (pWord j b) b ∧ SegmentRefinements rest
  | _ => True

private theorem segment_refinements {n : ℕ} {last : Letter} (p : PayloadForm n last) :
    SegmentRefinements p := by
  induction p with
  | active => trivial
  | segment j b rest ih =>
      exact ⟨(FourthSegmentStoppedLaw.parses_normal_form .p (pWord j b) b).mpr ⟨j, rfl⟩, ih⟩
  | pending => trivial
  | delivered => trivial

private theorem bits_bound {n : ℕ} {last : Letter} (p : PayloadForm n last) :
    (completedBits p).length ≤ n := by
  induction p <;> simp_all [completedBits]

private theorem weight_bound (bs : List Letter) : markerWeight bs ≤ bs.length := by
  simpa [markerWeight] using
    List.sum_le_card_nsmul (bs.map Fin.val) 1 (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      simpa using b.isLt)

private theorem payload_values {n : ℕ} {last : Letter} (p : PayloadForm n last)
    (t : ℕ) (r : Registers) (s : ℕ) (c : Counts) :
    let d := reconstructPayload t r s c p
    d.source.payloadReturns = s + returns p ∧
    d.counts.alpha + markerWeight (completedBits p) =
      c.alpha + (completedBits p).length + returns p ∧
    d.counts.beta = c.beta + 2 * markerWeight (completedBits p) + returns p + pendingExponent p ∧
    d.source.finiteFields.registers = foldMarkers t r (completedBits p) := by
  induction p generalizing t r s c with
  | active j phase => cases phase <;> simp [reconstructPayload, returns, completedBits,
      markerWeight, pendingExponent, foldMarkers]
  | segment j b rest ih =>
      obtain ⟨hs, ha, hb, hr⟩ := ih (t + 1) (writeMarker r t b) (s + j)
        ⟨c.alpha + j + (1 - b.val), c.beta + j + 2 * b.val⟩
      refine ⟨?_, ?_, ?_, hr⟩
      · simpa [reconstructPayload, returns, Nat.add_assoc] using hs
      · fin_cases b <;>
          simp [reconstructPayload, completedBits, markerWeight, returns] at ha ⊢ <;> omega
      · simp [reconstructPayload, completedBits, markerWeight, returns, pendingExponent] at hb ⊢
        omega
  | pending => simp [reconstructPayload, returns, completedBits, markerWeight,
      pendingExponent, foldMarkers]
  | delivered => simp [reconstructPayload, returns, completedBits, markerWeight,
      pendingExponent, foldMarkers]

private theorem payload_completed {n : ℕ} {last : Letter} (p : PayloadForm n last)
    (t : ℕ) (r : Registers) (s : ℕ) (c : Counts) (ht : t + n = 4) :
    completedCount (reconstructPayload t r s c p).source.finiteFields.control =
      t + (completedBits p).length := by
  induction p generalizing t r s c with
  | active j phase =>
      have ht' : t ≤ 3 := by omega
      interval_cases t <;> rfl
  | segment j b rest ih =>
      simpa [reconstructPayload, completedBits, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih (t + 1) (writeMarker r t b) (s + j)
          ⟨c.alpha + j + (1 - b.val), c.beta + j + 2 * b.val⟩ (by omega)
  | pending => simp [reconstructPayload, completedBits, completedCount]; omega
  | delivered => simp [reconstructPayload, completedBits, completedCount]; omega

private theorem marker_control_count (bs : List Letter) (h : bs.length ≤ 4) :
    completedCount (if bs.length < 4 then payloadControl bs.length .p
      else .fourth (.pending (bs.getLastD 0))) = bs.length := by
  split_ifs with hb
  · have he : bs.length ≤ 3 := by omega
    generalize bs.length = t at *
    interval_cases t <;> rfl
  · simp [completedCount]; omega

/-- Exact paid acquisition and original written-field obligations for a proof witness. -/
def PrefixFacts (nf : PrefixForm) (c : AcquiredNativeState) : Prop :=
  match nf.tail with
  | .ready => c.source.finiteFields = ⟨.seed none, emptyRegisters⟩ ∧
      c.source.payloadReturns = 0 ∧ c.counts = retryCounts nf.retries
  | .first x => c.source.finiteFields = ⟨.seed (some x), emptyRegisters⟩ ∧
      c.source.payloadReturns = 0 ∧ c.counts = countRead (retryCounts nf.retries) x
  | .acquired rho p =>
      let bs := completedBits p
      let t := bs.length
      let w := markerWeight bs
      let j := returns p
      c.source.payloadReturns = j ∧
      c.counts.alpha = 1 + t - w + 2 * nf.retries.count 0 + j ∧
      c.counts.beta = 1 + 2 * w + 2 * nf.retries.count 1 + j + pendingExponent p ∧
      completedCount c.source.finiteFields.control = t ∧
      c.source.finiteFields.registers = markerRegisters rho bs ∧
      WrittenFields rho bs c.source.finiteFields.registers ∧
      recoverMarkers c.source.finiteFields = bs.take 3 ∧ SegmentRefinements p

/-- The independently calculated state earns all fields and from-zero count formulas. -/
theorem reconstruction_invariants (nf : PrefixForm) : PrefixFacts nf (reconstruct nf) := by
  rcases nf with ⟨u, tail⟩
  cases tail with
  | ready => simp [PrefixFacts, reconstruct]
  | first x => simp [PrefixFacts, reconstruct]
  | acquired rho p =>
      obtain ⟨hs, ha, hb, hr⟩ := payload_values p 0 (acquiredRegisters rho) 0
        ⟨(retryCounts u).alpha + 1, (retryCounts u).beta + 1⟩
      have hc := payload_completed p 0 (acquiredRegisters rho) 0
        ⟨(retryCounts u).alpha + 1, (retryCounts u).beta + 1⟩ (by omega)
      have hbound := bits_bound p
      have hw := weight_bound (completedBits p)
      have he := marker_fields_recover rho (completedBits p)
      have hfields := marker_fields_exact rho (completedBits p)
      dsimp only [retryCounts] at hs ha hb hr hc
      dsimp only [PrefixFacts, reconstruct, retryCounts]
      refine ⟨by simpa using hs, ?_, ?_, by simpa using hc, hr, ?_, ?_, segment_refinements p⟩
      · omega
      · omega
      · obtain ⟨hseed, hweight, hsyn, hz, hqone, hqtwo, hsnapshot⟩ := hfields
        have hlt : markerWeight (completedBits p) < 5 := by omega
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals rw [hr]
        · exact hseed
        · simpa only [markerRegisters, Nat.mod_eq_of_lt hlt] using hweight
        · exact hsyn
        · exact hz
        · exact hqone
        · exact hqtwo
        · exact hsnapshot
      · have hh : recoverMarkers (reconstructPayload 0 (acquiredRegisters rho) 0
            ⟨2 * u.count 0 + 1, 2 * u.count 1 + 1⟩ p).source.finiteFields =
            recoverMarkers ⟨if (completedBits p).length < 4 then
              payloadControl (completedBits p).length .p else
              .fourth (.pending ((completedBits p).getLastD 0)),
              markerRegisters rho (completedBits p)⟩ := by
          unfold recoverMarkers
          rw [hc, hr, marker_control_count _ hbound]
          simp only [Nat.zero_add, markerRegisters]
        exact hh.trans he

/-- Independent folding of the finite operation table. -/
def executeFinite (f : FiniteFields) : List Operation → Option FiniteFields
  | [] => some f
  | op :: ops => (finiteStep f op).bind (fun g => executeFinite g ops)

def finiteRun (ops : List Operation) : Option FiniteFields :=
  executeFinite initial.source.finiteFields ops

private theorem execute_finite_projection (c : AcquiredNativeState) (ops : List Operation) :
    (execute c ops).map (fun d => d.source.finiteFields) =
      executeFinite c.source.finiteFields ops := by
  induction ops generalizing c with
  | nil => rfl
  | cons op ops ih =>
      have hf := finite_projection_commutes c op
      cases hs : nativeStep c op with
      | none =>
          simp only [hs, Option.map_none] at hf
          simp [execute, executeFinite, hs, ← hf]
      | some d =>
          simp only [hs, Option.map_some] at hf
          simp [execute, executeFinite, hs, ← hf, ih]

/-- Every legal from-zero operation word has a unique independently concatenated witness.
    That witness executes with its full native fields, S, paid counts and finite projection. -/
theorem native_acquired_prefix_reconstruction (ops : List Operation) :
    (Legal ops ↔ ∃! nf : PrefixForm, render nf = ops) ∧
    ∀ nf : PrefixForm, render nf = ops →
      run ops = some (reconstruct nf) ∧ PrefixFacts nf (reconstruct nf) ∧
      finiteRun ops = some (reconstruct nf).source.finiteFields := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      obtain ⟨nf, hf, _⟩ := legal_has_form ops h
      exact ⟨nf, hf, fun ng hg => prefix_form_unique (hg.trans hf.symm)⟩
    · rintro ⟨nf, hf, _⟩
      exact ⟨reconstruct nf, by rw [← hf]; exact run_render nf⟩
  · intro nf hf
    have hr : run ops = some (reconstruct nf) := by rw [← hf]; exact run_render nf
    refine ⟨hr, reconstruction_invariants nf, ?_⟩
    have hp := execute_finite_projection initial ops
    change (run ops).map (fun d => d.source.finiteFields) = finiteRun ops at hp
    simpa only [hr, Option.map_some] using hp.symm

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixState
