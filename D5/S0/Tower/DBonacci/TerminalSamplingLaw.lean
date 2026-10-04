/- GID: D5/S0/Tower/DBonacci/TerminalSamplingLaw
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacci/TerminalSamplingLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Adaptive first-hit fair-bit sampling is uniform on native legal terminal words. -/

import D5.S0.Tower.DBonacci.TerminalSampling
set_option autoImplicit false
noncomputable section
namespace D5.S0.Tower.DBonacci.TerminalSampling
open D5.S0.Tower.DBonacci.Names D5.S0.Tower.DBonacci.Values
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The same literal first-hit fair-tape sampler has the uniform native completion law.
Its continuation factors at every actual accepted-draw cursor, and its output equals
the finite fair-word law conditioned on native legality. The full-budget cardinality
is the d-bonacci term with the length-plus-two shift. -/
theorem terminal_sampling_uniform_law (maxTrue : ℕ) :
    (∀ (fuel h cursor : ℕ) (word : Fin h → Bool),
      fairTape {source | ∃ stop, sample maxTrue source fuel h cursor = some (word, stop)} =
        if runAdmissible maxTrue fuel h word then (completionCount maxTrue fuel h : ℝ≥0∞)⁻¹ else 0) ∧
    (∀ (fuel h cursor : ℕ) (word : Fin h → Bool),
      fairTape {source | ∃ stop, sample maxTrue source fuel h cursor = some (word, stop)} =
        ProbabilityTheory.cond (Measure.infinitePi (fun _ : Fin h => fairBit))
          {w | runAdmissible maxTrue fuel h w = true} {word}) ∧
    (∀ (fuel q cursor t : ℕ) (x : Fin (2 ^ (q + 1))) (word : Fin q → Bool),
      fairTape {source | draw (q + 1) (completionCount maxTrue fuel (q + 1)) cursor source =
        some (t, x) ∧ ∃ stop, sample maxTrue source
          (if decide (completionCount maxTrue maxTrue q ≤ x.val) then fuel - 1 else maxTrue)
          q (cursor + (t + 1) * (q + 1)) = some (word, stop)} =
      fairTape {source | draw (q + 1) (completionCount maxTrue fuel (q + 1)) cursor source =
        some (t, x)} *
      fairTape {source | ∃ stop, sample maxTrue source
        (if decide (completionCount maxTrue maxTrue q ≤ x.val) then fuel - 1 else maxTrue)
        q (cursor + (t + 1) * (q + 1)) = some (word, stop)}) ∧
    (∀ (N cursor : ℕ) (word : Fin N → Bool),
      fairTape {source | ∃ stop, sample maxTrue source maxTrue N cursor = some (word, stop)} =
        if runAdmissible maxTrue maxTrue N word then (dbonacci (maxTrue + 1) (N + 2) : ℝ≥0∞)⁻¹ else 0) := by
  classical
  have sourceFactor (fuel q cursor t : ℕ)
      (x : Fin (2 ^ (q + 1))) (word : Fin q → Bool) :
      fairTape {source | draw (q + 1) (completionCount maxTrue fuel (q + 1)) cursor source =
        some (t, x) ∧ ∃ stop, sample maxTrue source
          (if decide (completionCount maxTrue maxTrue q ≤ x.val) then fuel - 1 else maxTrue)
          q (cursor + (t + 1) * (q + 1)) = some (word, stop)} =
      fairTape {source | draw (q + 1) (completionCount maxTrue fuel (q + 1)) cursor source =
        some (t, x)} *
      fairTape {source | ∃ stop, sample maxTrue source
        (if decide (completionCount maxTrue maxTrue q ≤ x.val) then fuel - 1 else maxTrue)
        q (cursor + (t + 1) * (q + 1)) = some (word, stop)} := by
    classical
    have prefixTail (e : ℕ) :
        IndepFun (fun (tape : Tape) (i : Fin e) => tape i.val)
          (fun (tape : Tape) (i : ℕ) => tape (e + i)) fairTape := by
      have ind : iIndepFun (fun (i : ℕ) (tape : Tape) => tape i) fairTape :=
        iIndepFun_infinitePi (X := fun _ bit => bit) (by fun_prop)
      have separated := indep_iSup_of_disjoint
        (m := fun i : ℕ => MeasurableSpace.comap (fun tape : Tape => tape i) inferInstance)
        (fun _ => measurable_pi_apply _ |>.comap_le) ind.iIndep
        (S := {i | i < e}) (T := {i | e ≤ i})
        (Set.disjoint_left.mpr (by intro i hi hj; change i < e at hi; change e ≤ i at hj; omega))
      apply (IndepFun_iff_Indep _ _ _).mpr
      apply indep_of_indep_of_le separated
      · rw [MeasurableSpace.comap_process_pi]
        apply iSup_le
        intro i
        exact le_iSup_of_le i.val (le_iSup_of_le i.isLt le_rfl)
      · rw [MeasurableSpace.comap_process_pi]
        apply iSup_le
        intro i
        exact le_iSup_of_le (e + i) (le_iSup_of_le (by omega : e ≤ e + i) le_rfl)
    have causal (source other : Tape) (f g c final : ℕ) (w : Fin g → Bool)
        (he : sample maxTrue source f g c = some (w, final))
        (agree : ∀ i, c ≤ i → other i = source i) :
        sample maxTrue other f g c = some (w, final) := by
      have hh := terminal_sampling_execution_cylinders maxTrue source f g c final w
      exact (hh.2.1 he).2.2.1 other (fun i hi _ => agree i hi)
    have returnMeas (f g c : ℕ) (w : Fin g → Bool) :
        MeasurableSet {source | ∃ stop, sample maxTrue source f g c = some (w, stop)} := by
      have hh := terminal_sampling_execution_cylinders maxTrue (fun _ => false) f g c c w
      exact hh.2.2.2.2.2.2.2.1.2
    have drawCorr (source : Tape) (r : ℕ) (y : Fin (2 ^ (q + 1))) :
        draw (q + 1) (completionCount maxTrue fuel (q + 1)) cursor source = some (r, y) ↔
        AcceptedAt (q + 1) (completionCount maxTrue fuel (q + 1)) cursor source r ∧
          readBlock (q + 1) (cursor + r * (q + 1)) source = y := by
      have hh := terminal_sampling_execution_cylinders maxTrue source fuel (q + 1) cursor cursor
        (fun _ => false)
      exact hh.2.2.1 r y
    let e := cursor + (t + 1) * (q + 1)
    let f := if decide (completionCount maxTrue maxTrue q ≤ x.val) then fuel - 1 else maxTrue
    let representative (bits : Fin e → Bool) : Tape :=
      fun i => if hi : i < e then bits ⟨i, hi⟩ else false
    let P : Set (Fin e → Bool) := {bits | draw (q + 1)
      (completionCount maxTrue fuel (q + 1)) cursor (representative bits) = some (t, x)}
    have prefixEvent : {source | draw (q + 1) (completionCount maxTrue fuel (q + 1)) cursor source =
        some (t, x)} = (fun (source : Tape) (i : Fin e) => source i.val) ⁻¹' P := by
      ext source
      let rep := representative (fun i : Fin e => source i.val)
      have blocks (j : ℕ) (hj : j ≤ t) :
          readBlock (q + 1) (cursor + j * (q + 1)) rep =
            readBlock (q + 1) (cursor + j * (q + 1)) source := by
        unfold readBlock
        apply congrArg (blockEquiv (q + 1))
        funext i
        have hi : cursor + j * (q + 1) + i.val < e := by
          have hm := Nat.mul_le_mul_right (q + 1) hj
          have hb := i.isLt
          dsimp [e]
          rw [Nat.succ_mul]
          omega
        simp [rep, representative, hi]
      change draw (q + 1) (completionCount maxTrue fuel (q + 1)) cursor source = some (t, x) ↔
        draw (q + 1) (completionCount maxTrue fuel (q + 1)) cursor rep = some (t, x)
      rw [drawCorr source t x, drawCorr rep t x]
      constructor
      · rintro ⟨⟨prior, accept⟩, last⟩
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro j hj
          rw [blocks j (by omega)]
          exact prior j hj
        · rw [blocks t le_rfl]
          exact accept
        · rw [blocks t le_rfl]
          exact last
      · rintro ⟨⟨prior, accept⟩, last⟩
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro j hj
          rw [← blocks j (by omega)]
          exact prior j hj
        · rw [← blocks t le_rfl]
          exact accept
        · rw [← blocks t le_rfl]
          exact last
    let rebuild (tail : Tape) : Tape := fun i => if i < e then false else tail (i - e)
    let B : Set Tape := {tail | ∃ stop, sample maxTrue (rebuild tail) f q e = some (word, stop)}
    have rebuildMeas : Measurable rebuild := by
      apply measurable_pi_lambda
      intro i
      by_cases hi : i < e
      · simpa [rebuild, hi] using (measurable_const : Measurable (fun _ : Tape => false))
      · simpa [rebuild, hi] using (measurable_pi_apply (i - e) : Measurable (fun z : Tape => z (i-e)))
    have Bmeas : MeasurableSet B := (returnMeas f q e word).preimage rebuildMeas
    have suffixEvent : {source | ∃ stop, sample maxTrue source f q e = some (word, stop)} =
        (fun (source : Tape) i => source (e + i)) ⁻¹' B := by
      ext source
      have agree : ∀ i, e ≤ i → rebuild (fun j => source (e + j)) i = source i := by
        intro i hi
        simp [rebuild, Nat.not_lt.mpr hi, Nat.add_sub_of_le hi]
      constructor
      · rintro ⟨stop, he⟩
        exact ⟨stop, causal source _ f q e stop word he agree⟩
      · rintro ⟨stop, he⟩
        exact ⟨stop, causal _ source f q e stop word he (fun i hi => (agree i hi).symm)⟩
    have factored := (prefixTail e).measure_inter_preimage_eq_mul P B
      (Set.toFinite P).measurableSet Bmeas
    rw [← prefixEvent, ← suffixEvent] at factored
    exact factored
  have returnMeas (f g c : ℕ) (w : Fin g → Bool) :
      MeasurableSet {source | ∃ stop, sample maxTrue source f g c = some (w, stop)} := by
    have hh := terminal_sampling_execution_cylinders maxTrue (fun _ => false) f g c c w
    exact hh.2.2.2.2.2.2.2.1.2
  have uniform : ∀ (h fuel cursor : ℕ) (word : Fin h → Bool),
      runAdmissible maxTrue fuel h word = true →
      fairTape {source | ∃ stop, sample maxTrue source fuel h cursor = some (word, stop)} =
        (completionCount maxTrue fuel h : ℝ≥0∞)⁻¹ := by
    intro h
    induction h with
    | zero =>
      intro fuel cursor word legal
      have hw : word = fun i => Fin.elim0 i := Subsingleton.elim _ _
      subst word
      have event : {source | ∃ stop, sample maxTrue source fuel 0 cursor =
          some ((fun i => Fin.elim0 i), stop)} = Set.univ := by
        ext source
        simp [sample]
      rw [event, measure_univ]
      let : Unique (BoundedRunName maxTrue fuel 0) :=
        { default := ⟨fun i => Fin.elim0 i, rfl⟩
          uniq := fun w => Subtype.ext (Subsingleton.elim _ _) }
      simp [completionCount]
    | succ q ih =>
      intro fuel cursor word legal
      let D := completionCount maxTrue fuel (q + 1)
      let A := completionCount maxTrue maxTrue q
      let bit := word 0
      let next := if bit then fuel - 1 else maxTrue
      let tail := Fin.tail word
      have legalTail : runAdmissible maxTrue next q tail = true := by
        cases hf : fuel <;> cases hb : word 0 <;>
          simp_all [runAdmissible, next, bit, tail]
      have countBound : D ≤ 2 ^ (q + 1) := by
        unfold D completionCount
        simpa [BoundedRunName] using Fintype.card_subtype_le
          (fun w : Fin (q + 1) → Bool => runAdmissible maxTrue fuel (q + 1) w = true)
      have Ale : A ≤ D := by
        dsimp [A, D, completionCount]
        cases fuel with
        | zero => rw [bounded_run_name_card_zero]
        | succ f => rw [bounded_run_name_card_succ]; omega
      have trueCount (hb : bit = true) : D = A + completionCount maxTrue next q := by
        cases fuel with
        | zero => simp [runAdmissible, bit, hb] at legal
        | succ f =>
          simpa [D, A, next, hb, completionCount] using bounded_run_name_card_succ maxTrue f q
      let choices : Set (Fin D) := {x | decide (A ≤ x.val) = bit}
      have choiceCount : Fintype.card choices = completionCount maxTrue next q := by
        by_cases hb : bit = false
        ·
          let e : choices ≃ Fin A :=
            { toFun := fun x => ⟨x.val.val, by
                have hx := x.property
                change decide (A ≤ x.val.val) = bit at hx
                have hn : ¬ A ≤ x.val.val := by simpa [hb] using hx
                omega⟩
              invFun := fun y => ⟨⟨y.val, y.isLt.trans_le Ale⟩, by
                change decide (A ≤ y.val) = bit
                simp [hb, Nat.not_le.mpr y.isLt]⟩
              left_inv := fun x => by apply Subtype.ext; apply Fin.ext; rfl
              right_inv := fun y => by apply Fin.ext; rfl }
          rw [Fintype.card_congr e, Fintype.card_fin]
          simp [next, hb, A]
        · have hb : bit = true := by cases he : bit <;> simp_all
          have hd := trueCount hb
          let e : choices ≃ Fin (completionCount maxTrue next q) :=
            { toFun := fun x => ⟨x.val.val - A, by
                have hx := x.property
                change decide (A ≤ x.val.val) = bit at hx
                have ha : A ≤ x.val.val := by simpa [hb] using hx
                have hxlt := x.val.isLt
                omega⟩
              invFun := fun y => ⟨⟨A + y.val, by have hy := y.isLt; omega⟩, by
                change decide (A ≤ A + y.val) = bit
                simp [hb]⟩
              left_inv := fun x => by
                apply Subtype.ext
                apply Fin.ext
                have hx := x.property
                change decide (A ≤ x.val.val) = bit at hx
                have ha : A ≤ x.val.val := by simpa [hb] using hx
                change A + (x.val.val - A) = x.val.val
                omega
              right_inv := fun y => by apply Fin.ext; simp }
          rw [Fintype.card_congr e, Fintype.card_fin]
      let embed : Fin D → Fin (2 ^ (q + 1)) := Fin.castLE countBound
      let E (x : choices) (t : ℕ) : Set Tape :=
        {source | draw (q + 1) D cursor source = some (t, embed x.val) ∧
          ∃ stop, sample maxTrue source next q (cursor + (t + 1) * (q + 1)) = some (tail, stop)}
      have firstLaw (x : choices) (t : ℕ) :
          MeasurableSet {source | draw (q + 1) D cursor source = some (t, embed x.val)} ∧
          fairTape {source | draw (q + 1) D cursor source = some (t, embed x.val)} =
            ((((2 ^ (q + 1) - D : ℕ) : ℝ≥0∞) / (2 ^ (q + 1) : ℝ≥0∞)) ^ t) /
              (2 ^ (q + 1) : ℝ≥0∞) := by
        have hh := terminal_sampling_execution_cylinders maxTrue (fun _ => false) fuel
          (q + 1) cursor cursor word
        exact hh.2.2.2.1 t (embed x.val) x.val.isLt
      have measurableE (x : choices) (t : ℕ) : MeasurableSet (E x t) :=
        (firstLaw x t).1.inter (returnMeas next q (cursor + (t + 1) * (q + 1)) tail)
      have massE (x : choices) (t : ℕ) : fairTape (E x t) =
          fairTape {source | draw (q + 1) D cursor source = some (t, embed x.val)} *
            (completionCount maxTrue next q : ℝ≥0∞)⁻¹ := by
        have hx : decide (completionCount maxTrue maxTrue q ≤ (embed x.val).val) = bit := x.property
        have hf : (if decide (completionCount maxTrue maxTrue q ≤ (embed x.val).val)
          then fuel - 1 else maxTrue) = next := by rw [hx]
        have hh := sourceFactor fuel q cursor t (embed x.val) tail
        rw [hf] at hh
        change fairTape (E x t) = _ at hh
        rw [hh, ih next (cursor + (t + 1) * (q + 1)) tail legalTail]
      have disjointE (x : choices) : Pairwise (fun t r => Disjoint (E x t) (E x r)) := by
        intro t r htr
        apply Set.disjoint_left.mpr
        intro source ht hr
        exact htr (congrArg Prod.fst (Option.some.inj (ht.1.symm.trans hr.1)))
      have massRetry (x : choices) : fairTape (⋃ t, E x t) =
          (D : ℝ≥0∞)⁻¹ * (completionCount maxTrue next q : ℝ≥0∞)⁻¹ := by
        rw [measure_iUnion (disjointE x) (measurableE x)]
        simp_rw [massE]
        rw [ENNReal.tsum_mul_right]
        have drawDisjoint : Pairwise (fun t r => Disjoint
            {source | draw (q + 1) D cursor source = some (t, embed x.val)}
            {source | draw (q + 1) D cursor source = some (r, embed x.val)}) := by
          intro t r htr
          apply Set.disjoint_left.mpr
          intro source ht hr
          exact htr (congrArg Prod.fst (Option.some.inj (ht.symm.trans hr)))
        have drawEvent : {source | ∃ t, draw (q + 1) D cursor source = some (t, embed x.val)} =
            ⋃ t, {source | draw (q + 1) D cursor source = some (t, embed x.val)} := by
          ext source
          simp
        have hh := terminal_sampling_execution_cylinders maxTrue (fun _ => false) fuel
          (q + 1) cursor cursor word
        have hv := (hh.2.2.2.2.1 (embed x.val) x.val.isLt).2
        rw [drawEvent, measure_iUnion drawDisjoint (fun t => (firstLaw x t).1)] at hv
        rw [hv]
      have disjointChoices : Pairwise (fun x y : choices => Disjoint (⋃ t, E x t) (⋃ t, E y t)) := by
        intro x y hxy
        apply Set.disjoint_left.mpr
        intro source hx hy
        rcases Set.mem_iUnion.mp hx with ⟨t, ht⟩
        rcases Set.mem_iUnion.mp hy with ⟨r, hr⟩
        have he := congrArg Prod.snd (Option.some.inj (ht.1.symm.trans hr.1))
        apply hxy
        apply Subtype.ext
        apply Fin.ext
        exact congrArg (fun z : Fin (2 ^ (q + 1)) => z.val) he
      have event : {source | ∃ stop, sample maxTrue source fuel (q + 1) cursor = some (word, stop)} =
          ⋃ x : choices, ⋃ t, E x t := by
        ext source
        constructor
        · rintro ⟨stop, hs⟩
          cases hd : draw (q + 1) D cursor source with
          | none => simp [sample, show completionCount maxTrue fuel (q + 1) = D from rfl, hd] at hs
          | some result =>
            rcases result with ⟨t, y⟩
            have hh := terminal_sampling_execution_cylinders maxTrue source fuel (q + 1) cursor cursor word
            have hc := (hh.2.2.1 t y).mp hd
            have hy : y.val < D := by simpa [hc.2] using hc.1.2
            simp only [sample, show completionCount maxTrue fuel (q + 1) = D from rfl, hd] at hs
            change (match sample maxTrue source
              (if decide (completionCount maxTrue maxTrue q ≤ y.val) then fuel - 1 else maxTrue)
              q (cursor + (t + 1) * (q + 1)) with
                | none => none
                | some (w, final) => some (Fin.cons
                    (decide (completionCount maxTrue maxTrue q ≤ y.val)) w, final)) = some (word, stop) at hs
            cases hr : sample maxTrue source
                (if completionCount maxTrue maxTrue q ≤ y.val then fuel - 1 else maxTrue)
                q (cursor + (t + 1) * (q + 1)) with
            | none => simp [hr] at hs
            | some result =>
              rcases result with ⟨w, final⟩
              have hp : (Fin.cons (decide (completionCount maxTrue maxTrue q ≤ y.val)) w, final) =
                  (word, stop) := by simpa only [decide_eq_true_eq, hr, Option.some.injEq] using hs
              have hb : decide (A ≤ y.val) = bit := by
                simpa [A, bit] using congrArg (fun z => z.1 0) hp
              have hw : w = tail := by simpa [tail] using congrArg (fun z => Fin.tail z.1) hp
              have hf : final = stop := congrArg Prod.snd hp
              let x : choices := ⟨⟨y.val, hy⟩, hb⟩
              refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨t, ?_⟩⟩
              have he : embed x.val = y := Fin.ext rfl
              refine ⟨by simpa [E, he] using hd, stop, ?_⟩
              simpa [next, bit, ← hb, A, hw, hf] using hr
        · intro hu
          rcases Set.mem_iUnion.mp hu with ⟨x, hx⟩
          rcases Set.mem_iUnion.mp hx with ⟨t, hd, stop, hr⟩
          refine ⟨stop, ?_⟩
          have hb : decide (completionCount maxTrue maxTrue q ≤ (embed x.val).val) = bit := x.property
          simp only [sample, show completionCount maxTrue fuel (q + 1) = D from rfl, hd, hb]
          change (match sample maxTrue source next q (cursor + (t + 1) * (q + 1)) with
            | none => none
            | some (w, final) => some (Fin.cons bit w, final)) = some (word, stop)
          rw [hr]
          change some (Fin.cons bit tail, stop) = some (word, stop)
          rw [show Fin.cons bit tail = word from Fin.cons_self_tail word]
      rw [event, measure_iUnion disjointChoices (fun x => MeasurableSet.iUnion (measurableE x))]
      simp_rw [massRetry]
      rw [tsum_fintype]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, choiceCount]
      have pos : (completionCount maxTrue next q : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (bounded_run_level_pos maxTrue next q).ne'
      rw [mul_left_comm, ENNReal.mul_inv_cancel pos (by simp), mul_one]
  have nativeLaw : ∀ (fuel h cursor : ℕ) (word : Fin h → Bool),
      fairTape {source | ∃ stop, sample maxTrue source fuel h cursor = some (word, stop)} =
        if runAdmissible maxTrue fuel h word then (completionCount maxTrue fuel h : ℝ≥0∞)⁻¹ else 0 := by
    intro fuel h cursor word
    cases hl : runAdmissible maxTrue fuel h word with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hh := terminal_sampling_execution_cylinders maxTrue (fun _ => false) fuel h cursor cursor word
      exact hh.2.2.2.2.2.2.2.2.2.1 hl
    | true =>
      simp only [↓reduceIte]
      exact uniform h fuel cursor word hl
  have conditionedLaw (fuel h : ℕ) (word : Fin h → Bool) :
      ProbabilityTheory.cond (Measure.infinitePi (fun _ : Fin h => fairBit))
        {w | runAdmissible maxTrue fuel h w = true} {word} =
          if runAdmissible maxTrue fuel h word then (completionCount maxTrue fuel h : ℝ≥0∞)⁻¹ else 0 := by
    classical
    have finiteFair : Measure.infinitePi (fun _ : Fin h => fairBit) =
        (PMF.uniformOfFintype (Fin h → Bool)).toMeasure := by
      apply Measure.ext_of_singleton
      intro w
      rw [Measure.infinitePi_singleton_of_fintype]
      simp [fairBit, Nat.cast_pow, ← ENNReal.inv_pow]
    have layerMass : (Measure.infinitePi (fun _ : Fin h => fairBit))
        {w | runAdmissible maxTrue fuel h w = true} =
          (completionCount maxTrue fuel h : ℝ≥0∞) / (2 ^ h : ℝ≥0∞) := by
      rw [finiteFair, PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet]
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      rfl
    rw [ProbabilityTheory.cond_apply (Set.toFinite _).measurableSet, layerMass]
    cases hl : runAdmissible maxTrue fuel h word with
    | false =>
      have inter : {w | runAdmissible maxTrue fuel h w = true} ∩ {word} = ∅ := by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false]
        constructor
        · rintro ⟨hw, rfl⟩
          rw [hl] at hw
          contradiction
        · exact False.elim
      simp [inter]
    | true =>
      have inter : {w | runAdmissible maxTrue fuel h w = true} ∩ {word} = {word} := by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · exact And.right
        · intro hw; subst w; exact ⟨hl, rfl⟩
      have atom : (PMF.uniformOfFintype (Fin h → Bool)).toMeasure {word} = (2 ^ h : ℝ≥0∞)⁻¹ := by simp
      rw [inter, finiteFair, atom]
      simp only [↓reduceIte]
      have Qne : (2 ^ h : ℝ≥0∞) ≠ 0 := by simp
      have Qtop : (2 ^ h : ℝ≥0∞) ≠ ∞ := by simp
      rw [ENNReal.inv_div (Or.inl Qtop) (Or.inl Qne), div_eq_mul_inv, mul_right_comm,
        ENNReal.mul_inv_cancel Qne Qtop, one_mul]
  refine ⟨nativeLaw, ?_, sourceFactor, ?_⟩
  · intro fuel h cursor word
    rw [nativeLaw, conditionedLaw]
  · intro N cursor word
    have counts : completionCount maxTrue maxTrue N = dbonacci (maxTrue + 1) (N + 2) := by
      unfold completionCount
      rw [← dbonacci_name_card_eq_bounded, dbonacci_name_card]
    rw [nativeLaw, counts]

end D5.S0.Tower.DBonacci.TerminalSampling
#print axioms D5.S0.Tower.DBonacci.TerminalSampling.terminal_sampling_uniform_law
