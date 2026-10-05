/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidance
   mirror-E: none(waiver:external-open-question-resolution)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Complement and reversal are exactly the Wilf symmetries for four-letter rotations. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceSymmetry
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceGroups
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceGaps
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceFibonacciGap
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAlternatingContraction
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAlternating
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLayeredCount
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLayeredEmpty
import Mathlib.Data.List.Sort
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidance
open D5.S3.Combinatorics Nonnesting.NonnestingDefs
open RotationAvoidanceDefs RotationAvoidanceCircular
open Lean Meta Elab Tactic in private meta def countBlocks : TacticM Unit := do
  let goal ← getMainGoal; goal.withContext do
    let certify := fun (type proof : Expr) => withOptions (Elab.async.set · false) do
      withDeclNameForAuxNaming (mkPrivateName (← getEnv) (← mkAuxDeclName)) do
        mkAuxLemma [] type proof
    let type ← zetaReduce (← instantiateMVars (← goal.getType))
    let args := type.getAppArgs[1]!.headBeta.getAppArgs
    let elemType := args[0]!; let originalPred := args[1]!; let pred := originalPred
    let sizeExpr := args[2]!.getAppArgs[1]!.getAppArgs[1]!
    let testArgs := pred.bindingBody!.getAppArgs
    let some size ← getNatValue? (← whnf sizeExpr) | throwError "non-numeral size"
    let some cuts ← getNatValue? (← whnf testArgs[1]!.getAppArgs[0]!) | throwError "non-numeral cut"
    let some patternExpr := pred.find? (·.isAppOfArity ``List.cons 3)
      | throwError "missing pattern"
    let mut tail ← reduce patternExpr; let mut pattern := []
    while tail.isAppOfArity ``List.cons 3 do
      let some n ← getNatValue? tail.getAppArgs[1]! | throwError "non-numeral rank"
      pattern := pattern ++ [n]; tail := tail.getAppArgs[2]!
    -- Expand only list structure; certify equality for all lists before counting.
    let nat := mkConst ``Nat; let bool := mkConst ``Bool
    let compare ← elabTerm (← `(fun a b : Nat => decide (a < b))) none
    let nil ← mkListLit nat []; let prepend := fun xs tail => xs.foldr (fun x tail =>
      mkApp3 (mkConst ``List.cons [0]) nat x tail) tail
    let compact := fun (xs : Array Expr) => Id.run do
      let mut full := mkConst ``Bool.true
      for cut in (List.range cuts).reverse do
        let indices := ((List.range size).rotate cut).sublistsLen 4
        let mut found := mkConst ``Bool.false
        for positions in indices.reverse do
          let valueAt := fun r => xs[positions[pattern.idxOf r]!]!
          let comp := fun a b => mkApp2 compare (valueAt a) (valueAt b)
          let chain := mkApp2 (mkConst ``Bool.and)
            (mkApp2 (mkConst ``Bool.and) (comp 1 2) (comp 2 3)) (comp 3 4)
          found := mkApp2 (mkConst ``Bool.or) chain found
        full := mkApp2 (mkConst ``Bool.and) (mkApp (mkConst ``Bool.not) found) full
      return full
    let boolMotive ← withLocalDeclD `p elemType fun p => mkLambdaFVars #[p] bool
    let rec expand (depth : Nat) (xs : Array Expr) (p : Expr) : MetaM (Expr × Expr) := do
      let old := fun tail => mkApp originalPred (prepend xs tail)
      let nilBody := if depth == 0 then compact xs else old nil; let nilProof ← mkEqRefl (old nil)
      let (consBody, consProof) ← withLocalDeclD `a nat fun a =>
        withLocalDeclD `tail elemType fun tail => do
          let (body, proof) ← match depth with
            | 0 => do
              let body := old (mkApp3 (mkConst ``List.cons [0]) nat a tail)
              pure (body, ← mkEqRefl body)
            | d + 1 => expand d (xs.push a) tail
          pure (← mkLambdaFVars #[a, tail] body, ← mkLambdaFVars #[a, tail] proof)
      let newBody ← mkAppOptM ``List.casesOn
        #[some nat, some boolMotive, some p, some nilBody, some consBody]
      let motive ← withLocalDeclD `p elemType fun p => do
        let newBody ← mkAppOptM ``List.casesOn
          #[some nat, some boolMotive, some p, some nilBody, some consBody]
        mkLambdaFVars #[p] (← mkEq (old p) newBody)
      let proof ← mkAppOptM ``List.casesOn
        #[some nat, some motive, some p, some nilProof, some consProof]
      pure (newBody, proof)
    let (pred, predProof) ← withLocalDeclD `p elemType fun p => do
      let (body, proof) ← expand size #[] p
      pure (← mkLambdaFVars #[p] body, ← mkAppM ``funext #[← mkLambdaFVars #[p] proof])
    let predType ← mkEq originalPred pred; let predName ← certify predType predProof
    -- Every block count and the complete permutation enumeration are kernel checked.
    let words := (List.range' 1 size).permutations'.toArray
    let atRank := fun (ys : List Nat) rank => ys.getD (pattern.idxOf rank) 0
    let accept := fun p => (List.range cuts).all fun cut =>
      !((p.rotate cut).sublistsLen 4).any fun ys =>
        decide (atRank ys 1 < atRank ys 2) && decide (atRank ys 2 < atRank ys 3) &&
          decide (atRank ys 3 < atRank ys 4)
    let mut nodes : Array (Expr × Expr) := #[]
    for i in [0:(words.size + 127) / 128] do
      let node ← withFreshCache do
        let chunk := (words.extract (i * 128) ((i + 1) * 128)).toList
        let items ← chunk.mapM fun word => mkListLit (mkConst ``Nat) (word.map mkNatLit)
        let list ← mkListLit elemType items
        let value := mkApp3 (mkConst ``List.countP [0]) elemType pred list
        let type ← mkEq value (mkNatLit (chunk.countP accept))
        let proof ← mkEqRefl value; let name ← certify type proof
        pure (list, mkConst name)
      nodes := nodes.push node
    while nodes.size > 1 do
      let mut next := #[]
      for i in [0:(nodes.size + 1) / 2] do
        if 2 * i + 1 < nodes.size then
          let (left, hl) := nodes[2 * i]!; let (right, hr) := nodes[2 * i + 1]!
          let step ← mkAppOptM ``List.countP_append
            #[some elemType, some pred, some left, some right]
          let stepType ← inferType step; let append := stepType.getAppArgs[1]!.getAppArgs[2]!
          let add := stepType.getAppArgs[2]!.appFn!.appFn!
          let sum ← mkAppM ``congrArg₂ #[add, hl, hr]
          next := next.push (append, ← mkAppM ``Eq.trans #[step, sum])
        else next := next.push nodes[2 * i]!
      nodes := next
    let (list, proof) := nodes[0]!; let eqType ← mkEq args[2]! list
    let name ← certify eqType (← mkEqRefl args[2]!)
    let countFn := mkApp2 (mkConst ``List.countP [0]) elemType pred
    let congr ← mkAppM ``congrArg #[countFn, mkConst name]
    let predDomain ← mkArrow elemType (mkConst ``Bool)
    let varyPred := mkLambda `p .default predDomain
      (mkApp3 (mkConst ``List.countP [0]) elemType (mkBVar 0) args[2]!)
    let predStep ← mkAppM ``congrArg #[varyPred, mkConst predName]
    let proof ← mkAppM ``Eq.trans #[predStep, ← mkAppM ``Eq.trans #[congr, proof]]
    let name ← certify type proof
    goal.assign (mkConst name)
  replaceMainGoal []
set_option maxHeartbeats 10000000 in set_option maxRecDepth 100000 in
theorem result : RotationAvoidanceDefs.claim := by
  classical
  have layered_single_bad_count (size : ℕ) (hsize : 5 ≤ size) :
      (singleBadCircles size [1, 4, 2, 3]).ncard =
        ∑ first ∈ Finset.range size, ∑ last ∈ Finset.range size,
          if 1 ≤ first ∧ first + 1 < last then
            if first = 1 then (last - 2) * Nat.fib (2 * (size - last) - 1)
            else Nat.fib (2 * (first - 1) - 1) * Nat.fib (2 * (size - last) - 1)
          else 0 := by
    let q : List ℕ := [1, 4, 2, 3]; let words := {p : List ℕ | p.Perm (List.range' 1 size) ∧
      ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0}
    have lengthEq (p : List ℕ) (hp : p.Perm (List.range' 1 size)) : p.length = size := by
      simpa using hp.length_eq
    have rotateSum (p : List ℕ) (hp : p.Perm (List.range' 1 size)) (a b : ℕ) :
        (p.rotate a).rotate b = p.rotate ((a + b) % size) := by
      rw [List.rotate_rotate, ← List.rotate_mod, lengthEq p hp]
    have shiftZero (a b : ℕ) (ha : a < size) (hb : b < size) :
        (a + b) % size = a ↔ b = 0 := by
      by_cases hs : a + b < size
      · rw [Nat.mod_eq_of_lt hs]; omega
      · have hh : size ≤ a + b := by omega
        rw [Nat.mod_eq_sub_mod hh, Nat.mod_eq_of_lt (by omega : a + b - size < size)]; omega
    let bad := fun (p : List ℕ) (hp : p ∈ singleBadCircles size q) =>
      Classical.choose hp.2.2
    have badSpec (p : List ℕ) (hp : p ∈ singleBadCircles size q) :
        bad p hp < size ∧ ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = bad p hp :=
      Classical.choose_spec hp.2.2
    let emit := fun (p : List ℕ) (hp : p ∈ singleBadCircles size q) => p.rotate (bad p hp)
    have emitMember (p : List ℕ) (hp : p ∈ singleBadCircles size q) :
      emit p hp ∈ words := by
      have hs := badSpec p hp
      refine ⟨(List.rotate_perm _ _).trans hp.1, ?_⟩
      intro cut hc; change Occurs q ((p.rotate (bad p hp)).rotate cut) ↔ cut = 0
      rw [rotateSum p hp.1, hs.2 _ (Nat.mod_lt _ (by omega))]; exact shiftZero _ _ hs.1 hc
    have rootUnique (u v : List ℕ) (hu : u.Perm (List.range' 1 size))
        (headU : u.head? = some 1) (headV : v.head? = some 1)
        (hr : List.IsRotated u v) : u = v := by
      obtain ⟨cut, he⟩ := hr; have hb : cut % u.length < u.length  := by
        rw [lengthEq u hu]; exact Nat.mod_lt _ (by omega)
      have hz : 0 < u.length := by rw [lengthEq u hu]; omega
      have hg : u[cut % u.length]? = u[0]? := by
        rw [← List.head?_rotate hb, List.rotate_mod, he, ← List.head?_eq_getElem?,
          headU, headV]
      rw [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hz, Option.some.injEq] at hg
      have hzero := (hu.nodup_iff.mpr List.nodup_range').getElem_inj_iff.mp hg
      rw [← List.rotate_mod u cut, hzero, List.rotate_zero] at he; exact he
    have emitInjective (u v : List ℕ) (hu : u ∈ singleBadCircles size q)
        (hv : v ∈ singleBadCircles size q) (he : emit u hu = emit v hv) : u = v := by
      apply rootUnique u v hu.1 hu.2.1 hv.2.1
      have hrU : List.IsRotated u (emit u hu) := (List.IsRotated.forall u (bad u hu)).symm
      have hrV : List.IsRotated (emit v hv) v := List.IsRotated.forall v (bad v hv)
      exact hrU.trans (he.symm ▸ hrV)
    have emitSurjective (p : List ℕ) (hp : p ∈ words) :
        ∃ (circle : List ℕ) (hc : circle ∈ singleBadCircles size q),
          emit circle hc = p := by
      have hm : 1 ∈ p := hp.1.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      have hi : p.idxOf 1 < size := by
        have hh := List.idxOf_lt_length_iff.mpr hm; rw [lengthEq p hp.1] at hh; exact hh
      let root := p.rotate (p.idxOf 1); let back := (size - p.idxOf 1) % size
      have reverseRoot : root.rotate back = p := by
        rw [rotateSum p hp.1]; have he : (p.idxOf 1 + back) % size = 0 := by
          dsimp [back]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show p.idxOf 1 + (size - p.idxOf 1) = size by omega, Nat.mod_self]
        rw [he, List.rotate_zero]
      have rootMember : root ∈ singleBadCircles size q := by
        refine ⟨(List.rotate_perm _ _).trans hp.1, ?_, back, Nat.mod_lt _ (by omega), ?_⟩
        · rw [List.head?_rotate (by rwa [lengthEq p hp.1])]
          exact List.getElem?_idxOf hm
        · intro cut hc
          rw [rotateSum p hp.1, hp.2 _ (Nat.mod_lt _ (by omega))]
          change (p.idxOf 1 + cut) % size = 0 ↔ cut = (size - p.idxOf 1) % size
          by_cases hz : p.idxOf 1 = 0
          · simp [hz, Nat.mod_eq_of_lt hc]
          · have hb : size - p.idxOf 1 < size := by omega
            rw [Nat.mod_eq_of_lt hb]
            by_cases hs : p.idxOf 1 + cut < size
            · rw [Nat.mod_eq_of_lt hs]; omega
            · rw [Nat.mod_eq_sub_mod (by omega : size ≤ p.idxOf 1 + cut),
                Nat.mod_eq_of_lt (by omega : p.idxOf 1 + cut - size < size)]; omega
      have badEq : bad root rootMember = back := by
        have ho : Occurs q (root.rotate back) := by
          rw [reverseRoot]
          simpa using (hp.2 0 (by omega)).mpr rfl
        exact ((badSpec root rootMember).2 _ (Nat.mod_lt _ (by omega))).mp ho |>.symm
      exact ⟨root, rootMember, by simp only [emit, badEq, reverseRoot]⟩
    have rootCard := Set.ncard_congr (s := singleBadCircles size q) (t := words)
      emit emitMember emitInjective emitSurjective
    have endpoints (p : List ℕ) (hp : p ∈ words) :
        ∃ first last interior, p = first :: interior ++ [last] ∧
          1 ≤ first ∧ first + 1 < last ∧ last < size := by
      have hl := lengthEq p hp.1
      obtain ⟨first, tail, split⟩ : ∃ first tail, p = first :: tail := by
        cases p with
        | nil => simp at hl; omega
        | cons first tail => exact ⟨first, tail, rfl⟩
      obtain ⟨last, interior, splitP⟩ : ∃ last interior,
        p = first :: interior ++ [last] := by
        have ht : tail.length = size - 1 := by rw [split] at hl; simp at hl; omega
        cases hr : tail.reverse with
        | nil => have hh := congrArg List.length hr; simp [ht] at hh; omega
        | cons last rest =>
          have hh := congrArg List.reverse hr
          simp only [List.reverse_reverse, List.reverse_cons] at hh
          exact ⟨last, rest.reverse, by rw [split, hh]; rfl⟩
      have criterion := (unique_bad_cut_iff size (by omega) q p (by decide) hp.1).mp hp.2
      obtain ⟨chosen, hi, hm, selected, _⟩ := criterion.1
      have h12 : chosen 1 < chosen 2 := by simpa [q] using hi 1 (by omega) (by decide)
      have h23 : chosen 2 < chosen 3 := by simpa [q] using hi 2 (by omega) (by decide)
      have h34 : chosen 3 < chosen 4 := by simpa [q] using hi 3 (by omega) (by decide)
      have firstUsed : chosen 1 = first := by
        by_contra hn
        apply criterion.2.2.1; have ht : (q.map chosen).Sublist p.tail := by
          rw [splitP] at selected ⊢; exact List.Sublist.of_cons_of_ne hn selected
        refine ⟨chosen, hi, ?_, ht, by simp⟩
        intro rank hlo hhi; apply ht.subset
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4  := by
          change rank ≤ 4 at hhi; omega
        rcases hh with rfl | rfl | rfl | rfl <;> simp [q]
      have lastUsed : chosen 3 = last := by
        by_contra hn
        apply criterion.2.2.2; have selected' : [chosen 3, chosen 2, chosen 4, chosen 1].Sublist
            (last :: (first :: interior).reverse) := by
          simpa [q, splitP, List.reverse_append] using selected.reverse
        have ht := List.Sublist.of_cons_of_ne hn selected'
        have dropP : p.dropLast = first :: interior := by
          rw [splitP]; change ((first :: interior) ++ [last]).dropLast = _
          rw [List.dropLast_append_cons]; simp
        have ht : (q.map chosen).Sublist p.dropLast := by simpa [q, dropP] using ht.reverse
        refine ⟨chosen, hi, ?_, ht, by simp⟩
        intro rank hlo hhi; apply ht.subset
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4  := by
          change rank ≤ 4 at hhi; omega
        rcases hh with rfl | rfl | rfl | rfl <;> simp [q]
      have lowBound := List.mem_range'_1.mp (hp.1.mem_iff.mp (hm 1 (by omega) (by decide)))
      have highBound := List.mem_range'_1.mp (hp.1.mem_iff.mp (hm 4 (by omega) (by decide)))
      exact ⟨first, last, interior, splitP, by omega, by omega, by omega⟩
    let slice := fun first last : Fin size => {p : List ℕ | p ∈ words ∧
      p.head? = some first.val ∧ p.getLast? = some last.val}
    have finiteSlice (a b : Fin size) : (slice a b).Finite := by
      apply (List.finite_toSet (List.range' 1 size).permutations).subset
      intro p hp; exact List.mem_permutations.mpr hp.1.1
    letI (a b : Fin size) : Finite (slice a b) := (finiteSlice a b).to_subtype
    let family := Σ a : Fin size, Σ b : Fin size, slice a b
    let forget := fun element : family => element.2.2.val
    have forgetMember (element : family) : forget element ∈ words := element.2.2.property.1
    have forgetInjective : Function.Injective forget := by
      rintro ⟨a, b, p, hp⟩ ⟨c, d, r, hr⟩ he
      change p = r at he; subst r
      have hab : a = c := Fin.ext (Option.some.inj (hp.2.1.symm.trans hr.2.1))
      have hbd : b = d := Fin.ext (Option.some.inj (hp.2.2.symm.trans hr.2.2))
      subst c; subst d; rfl
    have forgetSurjective (p : List ℕ) (hp : p ∈ words) : ∃ element : family,
      forget element = p := by
      obtain ⟨a, b, interior, he, ha, hab, hb⟩ := endpoints p hp
      have ah : p.head? = some a := by simp [he]
      have bh : p.getLast? = some b := by
        rw [he]; change ((a :: interior) ++ [b]).getLast? = some b
        rw [List.getLast?_append_cons]; rfl
      exact ⟨⟨⟨a, by omega⟩, ⟨b, hb⟩, ⟨p, hp, ah, bh⟩⟩, rfl⟩
    let f : family → words := fun element => ⟨forget element, forgetMember element⟩
    have fBijective : Function.Bijective f := by
      constructor
      · intro a b he; exact forgetInjective (congrArg Subtype.val he)
      · rintro ⟨p, hp⟩
        obtain ⟨element, he⟩ := forgetSurjective p hp; exact ⟨element, Subtype.ext he⟩
    have familyCard := Nat.card_congr (Equiv.ofBijective f fBijective)
    have sliceCounts (a b : Fin size) : (slice a b).ncard =
        if 1 ≤ a.val ∧ a.val + 1 < b.val then
          if a.val = 1 then (b.val - 2) * Nat.fib (2 * (size - b.val) - 1)
          else Nat.fib (2 * (a.val - 1) - 1) * Nat.fib (2 * (size - b.val) - 1)
        else 0 := by
      by_cases hh : 1 ≤ a.val ∧ a.val + 1 < b.val
      · rw [if_pos hh]
        have he : slice a b = {p : List ℕ | p.Perm (List.range' 1 size) ∧
            p.head? = some a.val ∧ p.getLast? = some b.val ∧
            ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0} := by
          ext p; simp only [slice, words, Set.mem_setOf_eq]; tauto
        rw [he]
        by_cases hc : a.val = 1
        · rw [if_pos hc]
          have count := RotationAvoidanceLayeredEmpty.layered_empty_lower_endpoint_count
            size b.val (by omega) b.isLt
          simpa only [hc, q] using count
        · rw [if_neg hc]
          have count := RotationAvoidanceLayeredCount.layered_nonempty_lower_endpoint_count
            size a.val b.val (by omega) hh.2 b.isLt
          simpa only [q, Nat.mul_comm] using count
      · rw [if_neg hh]
        have he : slice a b = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr; intro p hp
          obtain ⟨first, last, interior, split, ha, hab, hb⟩ := endpoints p hp.1
          have head : first = a.val := by simpa [split] using hp.2.1
          have tail : last = b.val := by
            have he : p.getLast? = some last := by
              rw [split]; change ((first :: interior) ++ [last]).getLast? = some last
              rw [List.getLast?_append_cons]; rfl
            exact Option.some.inj (he.symm.trans hp.2.2)
          exact hh (by omega)
        rw [he, Set.ncard_empty]
    change (singleBadCircles size q).ncard = _; rw [rootCard, ← Nat.card_coe_set_eq, ← familyCard]
    change Nat.card (Σ a : Fin size, Σ b : Fin size, slice a b) = _
    rw [Nat.card_sigma]; simp only [Nat.card_sigma, Nat.card_coe_set_eq, sliceCounts]
    let term := fun first last : ℕ =>
      if 1 ≤ first ∧ first + 1 < last then
        if first = 1 then (last - 2) * Nat.fib (2 * (size - last) - 1)
        else Nat.fib (2 * (first - 1) - 1) * Nat.fib (2 * (size - last) - 1)
      else 0
    change (∑ a : Fin size, ∑ b : Fin size, term a.val b.val) =
      ∑ a ∈ Finset.range size, ∑ b ∈ Finset.range size, term a b
    calc
      _ = ∑ a : Fin size, ∑ b ∈ Finset.range size, term a.val b := by
        apply Finset.sum_congr rfl; intro a ha; exact Fin.sum_univ_eq_sum_range (term a.val) size
      _ = _ := Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range size, term a b) size
  have alternating_single_bad_count (size : ℕ) (hsize : 5 ≤ size) :
      (singleBadCircles size [2, 4, 1, 3]).ncard =
        ∑ first ∈ Finset.range size, ∑ last ∈ Finset.range size,
          if 2 ≤ first ∧ first < last then
            if last = first + 1 then Nat.fib (2 * (size - 2) - 1) -
              Nat.fib (2 * (first - 1) - 1) * Nat.fib (2 * (size - last) - 1)
            else Nat.fib (2 * (first - 1) - 1) * Nat.fib (2 * (size - last) - 1)
          else 0 := by
    let q : List ℕ := [2, 4, 1, 3]; let words := {p : List ℕ | p.Perm (List.range' 1 size) ∧
      ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0}
    have lengthEq (p : List ℕ) (hp : p.Perm (List.range' 1 size)) : p.length = size := by
      simpa using hp.length_eq
    have rotateSum (p : List ℕ) (hp : p.Perm (List.range' 1 size)) (a b : ℕ) :
        (p.rotate a).rotate b = p.rotate ((a + b) % size) := by
      rw [List.rotate_rotate, ← List.rotate_mod, lengthEq p hp]
    have shiftZero (a b : ℕ) (ha : a < size) (hb : b < size) :
        (a + b) % size = a ↔ b = 0 := by
      by_cases hs : a + b < size
      · rw [Nat.mod_eq_of_lt hs]; omega
      · have hh : size ≤ a + b := by omega
        rw [Nat.mod_eq_sub_mod hh, Nat.mod_eq_of_lt (by omega : a + b - size < size)]; omega
    let bad := fun (p : List ℕ) (hp : p ∈ singleBadCircles size q) =>
      Classical.choose hp.2.2
    have badSpec (p : List ℕ) (hp : p ∈ singleBadCircles size q) :
        bad p hp < size ∧ ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = bad p hp :=
      Classical.choose_spec hp.2.2
    let emit := fun (p : List ℕ) (hp : p ∈ singleBadCircles size q) => p.rotate (bad p hp)
    have emitMember (p : List ℕ) (hp : p ∈ singleBadCircles size q) :
      emit p hp ∈ words := by
      have hs := badSpec p hp
      refine ⟨(List.rotate_perm _ _).trans hp.1, ?_⟩
      intro cut hc; change Occurs q ((p.rotate (bad p hp)).rotate cut) ↔ cut = 0
      rw [rotateSum p hp.1, hs.2 _ (Nat.mod_lt _ (by omega))]; exact shiftZero _ _ hs.1 hc
    have rootUnique (u v : List ℕ) (hu : u.Perm (List.range' 1 size))
        (headU : u.head? = some 1) (headV : v.head? = some 1)
        (hr : List.IsRotated u v) : u = v := by
      obtain ⟨cut, he⟩ := hr; have hb : cut % u.length < u.length  := by
        rw [lengthEq u hu]; exact Nat.mod_lt _ (by omega)
      have hz : 0 < u.length := by rw [lengthEq u hu]; omega
      have hg : u[cut % u.length]? = u[0]? := by
        rw [← List.head?_rotate hb, List.rotate_mod, he, ← List.head?_eq_getElem?,
          headU, headV]
      rw [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hz, Option.some.injEq] at hg
      have hzero := (hu.nodup_iff.mpr List.nodup_range').getElem_inj_iff.mp hg
      rw [← List.rotate_mod u cut, hzero, List.rotate_zero] at he; exact he
    have emitInjective (u v : List ℕ) (hu : u ∈ singleBadCircles size q)
        (hv : v ∈ singleBadCircles size q) (he : emit u hu = emit v hv) : u = v := by
      apply rootUnique u v hu.1 hu.2.1 hv.2.1
      have hrU : List.IsRotated u (emit u hu) := (List.IsRotated.forall u (bad u hu)).symm
      have hrV : List.IsRotated (emit v hv) v := List.IsRotated.forall v (bad v hv)
      exact hrU.trans (he.symm ▸ hrV)
    have emitSurjective (p : List ℕ) (hp : p ∈ words) :
        ∃ (circle : List ℕ) (hc : circle ∈ singleBadCircles size q),
          emit circle hc = p := by
      have hm : 1 ∈ p := hp.1.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      have hi : p.idxOf 1 < size := by
        have hh := List.idxOf_lt_length_iff.mpr hm; rw [lengthEq p hp.1] at hh; exact hh
      let root := p.rotate (p.idxOf 1); let back := (size - p.idxOf 1) % size
      have reverseRoot : root.rotate back = p := by
        rw [rotateSum p hp.1]; have he : (p.idxOf 1 + back) % size = 0 := by
          dsimp [back]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show p.idxOf 1 + (size - p.idxOf 1) = size by omega, Nat.mod_self]
        rw [he, List.rotate_zero]
      have rootMember : root ∈ singleBadCircles size q := by
        refine ⟨(List.rotate_perm _ _).trans hp.1, ?_, back, Nat.mod_lt _ (by omega), ?_⟩
        · rw [List.head?_rotate (by rwa [lengthEq p hp.1])]
          exact List.getElem?_idxOf hm
        · intro cut hc
          rw [rotateSum p hp.1, hp.2 _ (Nat.mod_lt _ (by omega))]
          change (p.idxOf 1 + cut) % size = 0 ↔ cut = (size - p.idxOf 1) % size
          by_cases hz : p.idxOf 1 = 0
          · simp [hz, Nat.mod_eq_of_lt hc]
          · have hb : size - p.idxOf 1 < size := by omega
            rw [Nat.mod_eq_of_lt hb]
            by_cases hs : p.idxOf 1 + cut < size
            · rw [Nat.mod_eq_of_lt hs]; omega
            · rw [Nat.mod_eq_sub_mod (by omega : size ≤ p.idxOf 1 + cut),
                Nat.mod_eq_of_lt (by omega : p.idxOf 1 + cut - size < size)]; omega
      have badEq : bad root rootMember = back := by
        have ho : Occurs q (root.rotate back) := by
          rw [reverseRoot]
          simpa using (hp.2 0 (by omega)).mpr rfl
        exact ((badSpec root rootMember).2 _ (Nat.mod_lt _ (by omega))).mp ho |>.symm
      exact ⟨root, rootMember, by simp only [emit, badEq, reverseRoot]⟩
    have rootCard := Set.ncard_congr (s := singleBadCircles size q) (t := words)
      emit emitMember emitInjective emitSurjective
    have endpoints (p : List ℕ) (hp : p ∈ words) :
        ∃ first last interior, p = first :: interior ++ [last] ∧
          2 ≤ first ∧ first < last ∧ last < size := by
      have hl := lengthEq p hp.1
      obtain ⟨first, tail, split⟩ : ∃ first tail, p = first :: tail := by
        cases p with
        | nil => simp at hl; omega
        | cons first tail => exact ⟨first, tail, rfl⟩
      obtain ⟨last, interior, splitP⟩ : ∃ last interior,
        p = first :: interior ++ [last] := by
        have ht : tail.length = size - 1 := by rw [split] at hl; simp at hl; omega
        cases hr : tail.reverse with
        | nil => have hh := congrArg List.length hr; simp [ht] at hh; omega
        | cons last rest =>
          have hh := congrArg List.reverse hr
          simp only [List.reverse_reverse, List.reverse_cons] at hh
          exact ⟨last, rest.reverse, by rw [split, hh]; rfl⟩
      have criterion := (unique_bad_cut_iff size (by omega) q p (by decide) hp.1).mp hp.2
      obtain ⟨chosen, hi, hm, selected, _⟩ := criterion.1
      have h12 : chosen 1 < chosen 2 := by simpa [q] using hi 1 (by omega) (by decide)
      have h23 : chosen 2 < chosen 3 := by simpa [q] using hi 2 (by omega) (by decide)
      have h34 : chosen 3 < chosen 4 := by simpa [q] using hi 3 (by omega) (by decide)
      have firstUsed : chosen 2 = first := by
        by_contra hn
        apply criterion.2.2.1; have ht : (q.map chosen).Sublist p.tail := by
          rw [splitP] at selected ⊢; exact List.Sublist.of_cons_of_ne hn selected
        refine ⟨chosen, hi, ?_, ht, by simp⟩
        intro rank hlo hhi; apply ht.subset
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4  := by
          change rank ≤ 4 at hhi; omega
        rcases hh with rfl | rfl | rfl | rfl <;> simp [q]
      have lastUsed : chosen 3 = last := by
        by_contra hn
        apply criterion.2.2.2; have selected' : [chosen 3, chosen 1, chosen 4, chosen 2].Sublist
            (last :: (first :: interior).reverse) := by
          simpa [q, splitP, List.reverse_append] using selected.reverse
        have ht := List.Sublist.of_cons_of_ne hn selected'
        have dropP : p.dropLast = first :: interior := by
          rw [splitP]; change ((first :: interior) ++ [last]).dropLast = _
          rw [List.dropLast_append_cons]; simp
        have ht : (q.map chosen).Sublist p.dropLast := by simpa [q, dropP] using ht.reverse
        refine ⟨chosen, hi, ?_, ht, by simp⟩
        intro rank hlo hhi; apply ht.subset
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4  := by
          change rank ≤ 4 at hhi; omega
        rcases hh with rfl | rfl | rfl | rfl <;> simp [q]
      have lowBound := List.mem_range'_1.mp (hp.1.mem_iff.mp (hm 1 (by omega) (by decide)))
      have highBound := List.mem_range'_1.mp (hp.1.mem_iff.mp (hm 4 (by omega) (by decide)))
      exact ⟨first, last, interior, splitP, by omega, by omega, by omega⟩
    let slice := fun first last : Fin size => {p : List ℕ | p ∈ words ∧
      p.head? = some first.val ∧ p.getLast? = some last.val}
    have finiteSlice (a b : Fin size) : (slice a b).Finite := by
      apply (List.finite_toSet (List.range' 1 size).permutations).subset
      intro p hp; exact List.mem_permutations.mpr hp.1.1
    letI (a b : Fin size) : Finite (slice a b) := (finiteSlice a b).to_subtype
    let family := Σ a : Fin size, Σ b : Fin size, slice a b
    let forget := fun element : family => element.2.2.val
    have forgetMember (element : family) : forget element ∈ words := element.2.2.property.1
    have forgetInjective : Function.Injective forget := by
      rintro ⟨a, b, p, hp⟩ ⟨c, d, r, hr⟩ he
      change p = r at he; subst r
      have hab : a = c := Fin.ext (Option.some.inj (hp.2.1.symm.trans hr.2.1))
      have hbd : b = d := Fin.ext (Option.some.inj (hp.2.2.symm.trans hr.2.2))
      subst c; subst d; rfl
    have forgetSurjective (p : List ℕ) (hp : p ∈ words) : ∃ element : family,
      forget element = p := by
      obtain ⟨a, b, interior, he, ha, hab, hb⟩ := endpoints p hp
      have ah : p.head? = some a := by simp [he]
      have bh : p.getLast? = some b := by
        rw [he]; change ((a :: interior) ++ [b]).getLast? = some b
        rw [List.getLast?_append_cons]; rfl
      exact ⟨⟨⟨a, by omega⟩, ⟨b, hb⟩, ⟨p, hp, ah, bh⟩⟩, rfl⟩
    let f : family → words := fun element => ⟨forget element, forgetMember element⟩
    have fBijective : Function.Bijective f := by
      constructor
      · intro a b he; exact forgetInjective (congrArg Subtype.val he)
      · rintro ⟨p, hp⟩
        obtain ⟨element, he⟩ := forgetSurjective p hp; exact ⟨element, Subtype.ext he⟩
    have familyCard := Nat.card_congr (Equiv.ofBijective f fBijective)
    have sliceCounts (a b : Fin size) : (slice a b).ncard =
        if 2 ≤ a.val ∧ a.val < b.val then
          if b.val = a.val + 1 then Nat.fib (2 * (size - 2) - 1) -
            Nat.fib (2 * (a.val - 1) - 1) * Nat.fib (2 * (size - b.val) - 1)
          else Nat.fib (2 * (a.val - 1) - 1) * Nat.fib (2 * (size - b.val) - 1)
        else 0 := by
      by_cases hh : 2 ≤ a.val ∧ a.val < b.val
      · rw [if_pos hh]
        have he : slice a b = {p : List ℕ | p.Perm (List.range' 1 size) ∧
            p.head? = some a.val ∧ p.getLast? = some b.val ∧
            ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0} := by
          ext p; simp only [slice, words, Set.mem_setOf_eq]; tauto
        rw [he]
        by_cases hc : b.val = a.val + 1
        · rw [if_pos hc]
          have count :=
            RotationAvoidanceAlternatingContraction.alternating_consecutive_endpoint_count
            (size - 2) a.val (by omega) hh.1 (by omega)
          have hs : size - 2 + 2 = size := by omega
          have hb : size - 2 + 1 - a.val = size - b.val := by omega
          simpa only [hs, hb, hc, q] using count
        · rw [if_neg hc]
          have count :=
            RotationAvoidanceAlternating.alternating_positive_middle_endpoint_count
            size a.val b.val hh.1 (by omega) b.isLt
          simpa only [q, Nat.mul_comm] using count
      · rw [if_neg hh]
        have he : slice a b = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr; intro p hp
          obtain ⟨first, last, interior, split, ha, hab, hb⟩ := endpoints p hp.1
          have head : first = a.val := by simpa [split] using hp.2.1
          have tail : last = b.val := by
            have he : p.getLast? = some last := by
              rw [split]; change ((first :: interior) ++ [last]).getLast? = some last
              rw [List.getLast?_append_cons]; rfl
            exact Option.some.inj (he.symm.trans hp.2.2)
          exact hh (by omega)
        rw [he, Set.ncard_empty]
    change (singleBadCircles size q).ncard = _; rw [rootCard, ← Nat.card_coe_set_eq, ← familyCard]
    change Nat.card (Σ a : Fin size, Σ b : Fin size, slice a b) = _
    rw [Nat.card_sigma]; simp only [Nat.card_sigma, Nat.card_coe_set_eq, sliceCounts]
    let term := fun first last : ℕ =>
      if 2 ≤ first ∧ first < last then
        if last = first + 1 then Nat.fib (2 * (size - 2) - 1) -
          Nat.fib (2 * (first - 1) - 1) * Nat.fib (2 * (size - last) - 1)
        else Nat.fib (2 * (first - 1) - 1) * Nat.fib (2 * (size - last) - 1)
      else 0
    change (∑ a : Fin size, ∑ b : Fin size, term a.val b.val) =
      ∑ a ∈ Finset.range size, ∑ b ∈ Finset.range size, term a b
    calc
      _ = ∑ a : Fin size, ∑ b ∈ Finset.range size, term a.val b := by
        apply Finset.sum_congr rfl; intro a ha; exact Fin.sum_univ_eq_sum_range (term a.val) size
      _ = _ := Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range size, term a b) size
  let reps : List (List ℕ) :=
    [[1, 2, 3, 4], [1, 2, 4, 3], [1, 3, 2, 4], [1, 3, 4, 2],
      [1, 4, 2, 3], [1, 4, 3, 2], [2, 1, 4, 3], [2, 4, 1, 3]]
  have repsPerm : ∀ r ∈ reps, r.Perm [1, 2, 3, 4] := by decide
  have representatives : ∀ q ∈ ([1, 2, 3, 4] : List ℕ).permutations',
      ∃ r ∈ reps, q ∈ orbit r := by
    simp only [orbit, Set.mem_insert_iff, Set.mem_singleton_iff]
    decide
  have orbitTransfer (r q s : List ℕ) (hr : r.Perm [1, 2, 3, 4])
      (hq : q ∈ orbit r) (hs : s ∈ orbit r) : s ∈ orbit q := by
    have bound (v : ℕ) (hv : v ∈ r) : 1 ≤ v ∧ v ≤ 4 := by
      have hh := hr.mem_iff.mp hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl <;> omega
    have involution : complement (complement r) = r := by
      unfold complement
      rw [List.map_map]
      conv_rhs => rw [← List.map_id r]
      apply List.map_congr_left; intro v hv; have hh := bound v hv; dsimp; omega
    have reverseComplement (t : List ℕ) : (complement t).reverse = complement t.reverse := by
      simp only [complement, List.map_reverse]
    have involutionRev : complement (complement r.reverse) = r.reverse := by
      rw [← reverseComplement, ← reverseComplement, involution]
    simp only [orbit, Set.mem_insert_iff, Set.mem_singleton_iff] at hq hs ⊢
    rcases hq with rfl | rfl | rfl | rfl <;>
      rcases hs with rfl | rfl | rfl | rfl <;>
      simp only [reverseComplement, List.reverse_reverse, involution, involutionRev] <;> tauto
  let matchesPattern := fun q ys : List ℕ => match q, ys with
    | [qa, qb, qc, _], [a, b, c, d] =>
      let atRank := fun rank => if qa = rank then a else if qb = rank then b
        else if qc = rank then c else d
      decide (atRank 1 < atRank 2) && decide (atRank 2 < atRank 3) &&
        decide (atRank 3 < atRank 4)
    | _, _ => false
  let tests := fun k : ℕ => fun q p : List ℕ =>
    (List.range k).all fun i => !((p.rotate i).sublistsLen 4).any (matchesPattern q)
  let count := fun n k : ℕ => fun q : List ℕ =>
    (List.range' 1 n).permutations'.countP (tests k q)
  have boundedOccurs (n : ℕ) (hn : n ≤ 7) (q p : List ℕ) (hq : q.Perm [1, 2, 3, 4])
      (hp : p.Perm (List.range' 1 n)) :
      Occurs q p ↔ ∃ xs ∈ (List.range' 1 7).sublistsLen 4,
        (q.map (fun rank => xs.getD (rank - 1) 0)).Sublist p := by
    have lettersEq : letters q = 4 := by simpa [letters] using hq.foldr_eq (f := max) 0
    have ranks (rank : ℕ) (hm : rank ∈ q) :
        rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hq.mem_iff.mp hm
    unfold Occurs ArrowWilfDefs.Contains
    rw [lettersEq]
    constructor
    · rintro ⟨x, hi, hm, selected, _⟩
      let xs := [x 1, x 2, x 3, x 4]; have h12 := hi 1 (by omega) (by omega)
      have h23 := hi 2 (by omega) (by omega); have h34 := hi 3 (by omega) (by omega)
      change x 1 < x 2 at h12; change x 2 < x 3 at h23
      change x 3 < x 4 at h34; have ordered : xs.Pairwise (· < ·) := by
        simp [xs, List.pairwise_cons]
        omega
      have intoRange (i : ℕ) (hlo : 1 ≤ i) (hhi : i ≤ 4) :
          x i ∈ List.range' 1 7 := by
        obtain ⟨j, hj, he⟩ := List.mem_range'.mp (hp.mem_iff.mp (hm i hlo hhi))
        exact List.mem_range'.mpr ⟨j, by omega, he⟩
      have subset : xs ⊆ List.range' 1 7 := by
        intro v hv; simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl <;>
          exact intoRange _ (by omega) (by omega)
      have sub := List.sublist_of_subperm_of_pairwise
        (ordered.nodup.subperm subset) ordered List.pairwise_lt_range'
      refine ⟨xs, List.mem_sublistsLen.mpr ⟨sub, by simp [xs]⟩, ?_⟩
      have he : q.map (fun rank => xs.getD (rank - 1) 0) = q.map x := by
        apply List.map_congr_left; intro rank hrank
        rcases ranks rank hrank with rfl | rfl | rfl | rfl <;> rfl
      rwa [he]
    · rintro ⟨xs, hxs, selected⟩
      obtain ⟨sub, len⟩ := List.mem_sublistsLen.mp hxs
      obtain ⟨a, b, c, e, he⟩ : ∃ a b c e, xs = [a, b, c, e] := by
        cases xs with
        | nil => simp at len
        | cons a rest =>
          cases rest with
          | nil => simp at len
          | cons b rest =>
            cases rest with
            | nil => simp at len
            | cons c rest =>
              cases rest with
              | nil => simp at len
              | cons e rest =>
                have hz : rest = [] := by simpa using len
                subst rest; exact ⟨a, b, c, e, rfl⟩
      subst xs; have ordered := (List.pairwise_lt_range' (s := 1) (n := 7)).sublist sub
      have order : a < b ∧ b < c ∧ c < e := by
        simp [List.pairwise_cons] at ordered; exact ⟨ordered.1.1, ordered.2.1.1, ordered.2.2⟩
      refine ⟨fun rank => [a, b, c, e].getD (rank - 1) 0, ?_, ?_, selected, by simp⟩
      · intro i hlo hhi
        have casesI : i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases casesI with rfl | rfl | rfl
        · exact order.1
        · exact order.2.1
        · exact order.2.2
      · intro i hlo hhi
        have casesI : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
        have mappedPerm : (q.map (fun rank => [a, b, c, e].getD (rank - 1) 0)).Perm
            [a, b, c, e] := by
          simpa using hq.map (fun rank => [a, b, c, e].getD (rank - 1) 0)
        apply selected.subset; apply mappedPerm.mem_iff.mpr
        rcases casesI with rfl | rfl | rfl | rfl <;> simp
  have signatureMap : ∀ xs ∈ (List.range' 1 7).sublistsLen 4,
      ∀ q ∈ ([1, 2, 3, 4] : List ℕ).permutations',
      matchesPattern q (q.map (fun r => xs.getD (r - 1) 0)) = true := by
    intro xs hxs
    fin_cases hxs <;> decide +kernel
  have recoverSignature : ∀ xs ∈ (List.range' 1 7).sublistsLen 4,
      ∀ ys ∈ xs.permutations', ∀ q ∈ ([1, 2, 3, 4] : List ℕ).permutations',
      matchesPattern q ys = true → q.map (fun r => xs.getD (r - 1) 0) = ys := by
    intro xs hxs
    fin_cases hxs <;> decide +kernel
  have positionalOccurs (n : ℕ) (hn : n ≤ 7) (q p : List ℕ) (hq : q.Perm [1, 2, 3, 4])
      (hp : p.Perm (List.range' 1 n)) :
      Occurs q p ↔ ∃ ys ∈ p.sublistsLen 4, matchesPattern q ys = true := by
    constructor
    · intro ho
      obtain ⟨xs, hxs, sub⟩ := (boundedOccurs n hn q p hq hp).mp ho
      refine ⟨q.map (fun r => xs.getD (r - 1) 0),
        List.mem_sublistsLen.mpr ⟨sub, ?_⟩, ?_⟩
      · simpa using hq.length_eq
      · exact signatureMap xs hxs q (List.mem_permutations'.mpr hq)
    · rintro ⟨ys, hy, hpattern⟩
      obtain ⟨sub, len⟩ := List.mem_sublistsLen.mp hy
      let xs := ys.mergeSort (fun a b => decide (a ≤ b))
      have perm : xs.Perm ys := List.mergeSort_perm ys _
      have nd : xs.Nodup := perm.nodup_iff.mpr
        ((hp.nodup_iff.mpr List.nodup_range').sublist sub)
      have sorted : xs.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) ys
      have strict : xs.Pairwise (· < ·) := (sorted.and nd).imp fun {a b} h => by omega
      have subset : xs ⊆ List.range' 1 7 := by
        intro v hv; obtain ⟨i, hi, he⟩ := List.mem_range'.mp
          (hp.mem_iff.mp (sub.subset (perm.mem_iff.mp hv)))
        exact List.mem_range'.mpr ⟨i, by omega, he⟩
      have rangeSub := List.sublist_of_subperm_of_pairwise
        (nd.subperm subset) strict List.pairwise_lt_range'
      have hxs : xs ∈ (List.range' 1 7).sublistsLen 4 :=
        List.mem_sublistsLen.mpr ⟨rangeSub, perm.length_eq.trans len⟩
      have recover := recoverSignature xs hxs ys (List.mem_permutations'.mpr perm.symm)
        q (List.mem_permutations'.mpr hq) hpattern
      apply (boundedOccurs n hn q p hq hp).mpr
      refine ⟨xs, hxs, ?_⟩
      rw [recover]; exact sub
  have finiteCount (n : ℕ) (hn : n ≤ 7) (k : ℕ) (q : List ℕ) (hq : q.Perm [1, 2, 3, 4]) :
      (rotationAvoiders n k q).ncard = count n k q := by
    let accepted := (List.range' 1 n).permutations'.filter (tests k q)
    have testsEq (p : List ℕ) (hp : p.Perm (List.range' 1 n)) :
        tests k q p = true ↔ ∀ i < k, ¬ Occurs q (p.rotate i) := by
      simp only [tests, List.all_eq_true, List.mem_range, Bool.not_eq_true',
        List.any_eq_false]
      constructor
      · intro hh i hi ho
        obtain ⟨xs, hxs, hx⟩ := (positionalOccurs n hn q (p.rotate i) hq
          ((List.rotate_perm _ _).trans hp)).mp ho
        exact hh i hi xs hxs hx
      · intro hh i hi xs hxs hx
        exact hh i hi ((positionalOccurs n hn q (p.rotate i) hq
          ((List.rotate_perm _ _).trans hp)).mpr ⟨xs, hxs, hx⟩)
    have setEq : rotationAvoiders n k q = (accepted.toFinset : Set (List ℕ)) := by
      ext p
      simp only [Finset.mem_coe, List.mem_toFinset, accepted, List.mem_filter,
        List.mem_permutations', rotationAvoiders, Set.mem_setOf_eq]
      constructor
      · intro hp; exact ⟨hp.1, (testsEq p hp.1).mpr hp.2⟩
      · intro hp; exact ⟨hp.1, (testsEq p hp.1).mp hp.2⟩
    rw [setEq, Set.ncard_coe_finset]; dsimp only [count]
    rw [List.countP_eq_length_filter]; have nd : (List.range' 1 n).permutations'.Nodup :=
      (List.permutations_perm_permutations' _).nodup_iff.mp
        (List.nodup_permutations _ List.nodup_range')
    exact List.toFinset_card_of_nodup (nd.filter _)
  have table64 : reps.map (count 6 4) = [264, 233, 262, 239, 260, 268, 262, 286] := by
    simp only [reps, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    repeat' apply And.intro
    all_goals run_tac countBlocks
  have table65 : reps.map (count 6 5) = [221, 182, 221, 187, 221, 221, 214, 234] := by
    simp only [reps, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    repeat' apply And.intro
    all_goals run_tac countBlocks
  have table74 : [[1, 3, 2, 4], [2, 1, 4, 3]].map (count 7 4) = [1058, 1070] := by
    simp only [reps, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    repeat' apply And.intro
    all_goals run_tac countBlocks
  have table75 : [[1, 2, 3, 4], [1, 3, 2, 4], [1, 4, 2, 3], [1, 4, 3, 2]].map
      (count 7 5) = [782, 807, 798, 794] := by
    simp only [reps, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    repeat' apply And.intro
    all_goals run_tac countBlocks
  have representativeSymmetries (size : ℕ) (hsize : 1 ≤ size) :
      (circularAvoiders (size + 1) [1, 4, 3, 2]).ncard =
          (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard ∧
      (circularAvoiders (size + 1) [2, 1, 4, 3]).ncard =
          (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard ∧
      (circularAvoiders (size + 1) [1, 2, 4, 3]).ncard =
          (circularAvoiders (size + 1) [1, 3, 4, 2]).ncard ∧
      (circularAvoiders (size + 1) [1, 4, 2, 3]).ncard =
          (circularAvoiders (size + 1) [1, 3, 2, 4]).ncard ∧
      (circularAvoiders (size + 1) [2, 4, 1, 3]).ncard =
          (circularAvoiders (size + 1) [1, 3, 2, 4]).ncard := by
    have symmetry (q s : List ℕ) (hq : q.Perm [1, 2, 3, 4]) (hs : s ∈ orbit q) :
        (circularAvoiders (size + 1) s).ncard =
          (circularAvoiders (size + 1) q).ncard := by
      have heq := RotationAvoidanceSymmetry.orbit_wilfEquivalent
        (size + 1) (by omega) q s hq hs (size + 1) (by omega)
      rw [(counting_cuts (size + 1) (by omega) q).1,
        (counting_cuts (size + 1) (by omega) s).1] at heq
      exact (Nat.eq_of_mul_eq_mul_left (by omega : 0 < size + 1) heq).symm
    have cycle (q : List ℕ) (hq : q.Perm [1, 2, 3, 4]) (shift : ℕ)
        (hshift : shift < 4) :
        (circularAvoiders (size + 1) (q.rotate shift)).ncard =
          (circularAvoiders (size + 1) q).ncard := by
      have qlength : q.length = 4 := by simpa using hq.length_eq
      have forward (pattern : List ℕ) (hlen : pattern.length = 4) (offset : ℕ)
          (word : List ℕ) (havoid : ∀ cut < 4, ¬ Occurs (pattern.rotate cut) word) :
          ∀ cut < 4, ¬ Occurs ((pattern.rotate offset).rotate cut) word := by
        intro cut hcut
        rw [List.rotate_rotate, ← List.rotate_mod, hlen]; exact havoid _ (Nat.mod_lt _ (by omega))
      have restore : (q.rotate shift).rotate (4 - shift) = q := by
        rw [List.rotate_rotate, show shift + (4 - shift) = 4 by omega,
          ← qlength, List.rotate_length]
      have setEq : circularAvoiders (size + 1) (q.rotate shift) =
          circularAvoiders (size + 1) q := by
        ext word
        constructor <;> intro hword
        · have havoid := (all_cuts_iff_cycle_avoidance (size + 1) (by omega)
            (q.rotate shift) word ((List.rotate_perm q shift).trans hq) hword.1.1).mp hword.1
          refine ⟨(all_cuts_iff_cycle_avoidance (size + 1) (by omega) q word hq
            hword.1.1).mpr ?_, hword.2⟩
          simpa only [restore] using forward (q.rotate shift)
            (by simpa using qlength) (4 - shift) word havoid
        · have havoid := (all_cuts_iff_cycle_avoidance (size + 1) (by omega) q word hq
            hword.1.1).mp hword.1
          exact ⟨(all_cuts_iff_cycle_avoidance (size + 1) (by omega) (q.rotate shift)
            word ((List.rotate_perm q shift).trans hq) hword.1.1).mpr
              (forward q qlength shift word havoid), hword.2⟩
      rw [setEq]
    have ascendingReverse : (circularAvoiders (size + 1) [1, 4, 3, 2]).ncard =
        (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard := by
      calc
        _ = (circularAvoiders (size + 1) [4, 3, 2, 1]).ncard :=
          (by simpa only [show ([1, 4, 3, 2] : List ℕ).rotate 1 = [4, 3, 2, 1] by decide]
            using (cycle [1, 4, 3, 2] (by decide) 1 (by omega)).symm)
        _ = _ := symmetry [1, 2, 3, 4] [4, 3, 2, 1] (by decide) (by simp [orbit, complement])
    have ascendingOther : (circularAvoiders (size + 1) [2, 1, 4, 3]).ncard =
        (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard := by
      calc
        _ = (circularAvoiders (size + 1) [1, 4, 3, 2]).ncard := by
          simpa only [show ([1, 4, 3, 2] : List ℕ).rotate 3 = [2, 1, 4, 3] by decide]
            using cycle [1, 4, 3, 2] (by decide) 3 (by omega)
        _ = _ := ascendingReverse
    have binaryOther : (circularAvoiders (size + 1) [1, 2, 4, 3]).ncard =
        (circularAvoiders (size + 1) [1, 3, 4, 2]).ncard := by
      calc
        _ = (circularAvoiders (size + 1) [2, 4, 3, 1]).ncard :=
          (by simpa only [show ([1, 2, 4, 3] : List ℕ).rotate 1 = [2, 4, 3, 1] by decide]
            using (cycle [1, 2, 4, 3] (by decide) 1 (by omega)).symm)
        _ = _ := symmetry [1, 3, 4, 2] [2, 4, 3, 1] (by decide) (by simp [orbit, complement])
    have fibonacciOther : (circularAvoiders (size + 1) [1, 4, 2, 3]).ncard =
        (circularAvoiders (size + 1) [1, 3, 2, 4]).ncard := by
      calc
        _ = (circularAvoiders (size + 1) [3, 2, 4, 1]).ncard :=
          symmetry [3, 2, 4, 1] [1, 4, 2, 3] (by decide) (by simp [orbit, complement])
        _ = _ := by simpa only
          [show ([1, 3, 2, 4] : List ℕ).rotate 1 = [3, 2, 4, 1] by decide]
            using cycle [1, 3, 2, 4] (by decide) 1 (by omega)
    have fibonacciLast : (circularAvoiders (size + 1) [2, 4, 1, 3]).ncard =
        (circularAvoiders (size + 1) [1, 3, 2, 4]).ncard := by
      simpa only [show ([1, 3, 2, 4] : List ℕ).rotate 2 = [2, 4, 1, 3] by decide]
        using cycle [1, 3, 2, 4] (by decide) 2 (by omega)
    exact ⟨ascendingReverse, ascendingOther, binaryOther, fibonacciOther, fibonacciLast⟩
  intro k hk q s hq hs
  constructor
  · intro equivalence
    obtain ⟨r, hr, hqr⟩ := representatives q (List.mem_permutations'.mpr hq)
    obtain ⟨t, ht, hst⟩ := representatives s (List.mem_permutations'.mpr hs)
    have erq := RotationAvoidanceSymmetry.orbit_wilfEquivalent k (by omega) r q
      (repsPerm r hr) hqr
    have ets := RotationAvoidanceSymmetry.orbit_wilfEquivalent k (by omega) t s
      (repsPerm t ht) hst
    have ert : WilfEquivalent k r t := by
      intro n hn; exact (erq n hn).trans ((equivalence n hn).trans (ets n hn).symm)
    have representativeEq : r = t := by
      by_cases big : 6 ≤ k
      · have full := ert k le_rfl
        have near := ert (k + 1) (by omega)
        have fullCounts (pattern : List ℕ) : (rotationAvoiders k k pattern).ncard =
            k * (circularAvoiders k pattern).ncard := (counting_cuts k (by omega) pattern).1
        have nearCounts (pattern : List ℕ) : (rotationAvoiders (k + 1) k pattern).ncard =
            (k + 1) * (circularAvoiders (k + 1) pattern).ncard +
              (singleBadCircles (k + 1) pattern).ncard := by
          simpa only [Nat.add_sub_cancel] using (counting_cuts (k + 1) (by omega) pattern).2
        rw [fullCounts r, fullCounts t] at full
        have circleEq := Nat.eq_of_mul_eq_mul_left (by omega : 0 < k) full
        rw [nearCounts r, nearCounts t] at near
        have groups := representativeSymmetries (k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega] at groups
        obtain ⟨cA1, cA2, cB1, cC1, cC2⟩ := groups; have separation :=
          RotationAvoidanceGroups.circular_representative_separations (k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega] at separation
        obtain ⟨nA1, nA2, nB1, nC1, nC2⟩ := representativeSymmetries k (by omega)
        obtain ⟨gapA1, gapA2, gapB⟩ :=
          RotationAvoidanceGaps.three_strict_count_gaps (k + 1) (by omega)
        have gapC1 := RotationAvoidanceFibonacciGap.fibonacci_lt_layered (k + 1) (by omega)
        have gapC2 : (singleBadCircles (k + 1) [1, 4, 2, 3]).ncard <
            (singleBadCircles (k + 1) [2, 4, 1, 3]).ncard := by
          let size := k + 1; have hsize : 5 ≤ size := by dsimp [size]; omega
          have evenGrowth (l : ℕ) : l ≤ Nat.fib (2 * l) := by
            have supplied := Nat.le_fib_add_one (2 * l)
            omega
          have gap (l h : ℕ) (hl : 1 ≤ l) (hh : 1 ≤ h) :
              l * Nat.fib (2 * h - 1) ≤
                Nat.fib (2 * (l + h) - 1) - Nat.fib (2 * l - 1) * Nat.fib (2 * h - 1) ∧
              (l = 2 → l * Nat.fib (2 * h - 1) <
                Nat.fib (2 * (l + h) - 1) - Nat.fib (2 * l - 1) * Nat.fib (2 * h - 1)) := by
            have addition := Nat.fib_add (2 * l) (2 * h - 2)
            have index : 2 * l + (2 * h - 2) + 1 = 2 * (l + h) - 1 := by omega
            have odd : 2 * h - 2 + 1 = 2 * h - 1 := by omega
            rw [index, odd] at addition; have recur := Nat.fib_add_two (n := 2 * l - 1)
            rw [show 2 * l - 1 + 2 = 2 * l + 1 by omega,
              show 2 * l - 1 + 1 = 2 * l by omega] at recur
            have bound : (Nat.fib (2 * l - 1) + l) * Nat.fib (2 * h - 1) ≤
                Nat.fib (2 * (l + h) - 1) := by
              have hg := evenGrowth l; have hm := Nat.mul_le_mul_right (Nat.fib (2 * h - 1))
                (Nat.add_le_add_left hg (Nat.fib (2 * l - 1)))
              rw [← recur] at hm; rw [addition]; exact hm.trans (Nat.le_add_left _ _)
            rw [Nat.add_mul] at bound
            constructor
            · omega
            · intro he
              subst l; have pos : 0 < Nat.fib (2 * h - 1) := Nat.fib_pos.mpr (by omega)
              norm_num at addition ⊢
              omega
          let C := fun t : ℕ => Nat.fib (2 * t - 1)
          let asc := fun a b : ℕ => if 2 ≤ a ∧ a < b then
            if b = a + 1 then C (size - 2) - C (a - 1) * C (size - b)
            else C (a - 1) * C (size - b) else 0
          let lay := fun a b : ℕ => if 1 ≤ a ∧ a + 1 < b then
            if a = 1 then (b - 2) * C (size - b)
            else C (a - 1) * C (size - b) else 0
          have row (b : ℕ) (hb : b < size) :
              (∑ a ∈ Finset.range size, lay a b) ≤ (∑ a ∈ Finset.range size, asc a b) ∧
              (b = 4 → (∑ a ∈ Finset.range size, lay a b) <
                (∑ a ∈ Finset.range size, asc a b)) := by
            by_cases small : b < 3
            · have zeros (a : ℕ) : lay a b = 0 ∧ asc a b = 0 := by
                have hl : ¬ (1 ≤ a ∧ a + 1 < b) := by omega
                have ha : ¬ (2 ≤ a ∧ a < b) := by omega
                simp [lay, asc, hl, ha]
              simp only [zeros, Finset.sum_const_zero]; exact ⟨le_rfl, by intro he; omega⟩
            · have big : 3 ≤ b := by omega
              have oneMem : 1 ∈ Finset.range size := Finset.mem_range.mpr (by omega)
              have edgeMem : b - 1 ∈ (Finset.range size).erase 1 := by
                simp only [Finset.mem_erase, ne_eq, Finset.mem_range]; omega
              let rest := ((Finset.range size).erase 1).erase (b - 1)
              have common (a : ℕ) (ha : a ∈ rest) : lay a b = asc a b := by
                have ha' : a ≠ 1 ∧ a ≠ b - 1 := by
                  have he := Finset.mem_erase.mp ha; exact ⟨(Finset.mem_erase.mp he.2).1, he.1⟩
                have ia : (1 ≤ a ∧ a + 1 < b) ↔ (2 ≤ a ∧ a < b) := by omega
                have notConsecutive : b ≠ a + 1 := by omega
                simp only [lay, asc, ia, ha'.1, if_false, notConsecutive]
              have split (term : ℕ → ℕ) :
                  (∑ a ∈ rest, term a) + term (b - 1) + term 1 =
                    ∑ a ∈ Finset.range size, term a := by
                rw [show rest = ((Finset.range size).erase 1).erase (b - 1) by rfl,
                  Finset.sum_erase_add _ _ edgeMem, Finset.sum_erase_add _ _ oneMem]
              have commonSum : (∑ a ∈ rest, lay a b) = ∑ a ∈ rest, asc a b :=
                Finset.sum_congr rfl common
              have layEdge : lay (b - 1) b = 0 := by
                have hi : ¬ (1 ≤ b - 1 ∧ b - 1 + 1 < b) := by omega
                simp [lay, hi]
              have ascOne : asc 1 b = 0 := by simp [asc]
              have layOne : lay 1 b = (b - 2) * C (size - b) := by
                simp [lay, show 1 + 1 < b by omega]
              have ascEdge : asc (b - 1) b = C (size - 2) - C (b - 2) * C (size - b) := by
                change (if 2 ≤ b - 1 ∧ b - 1 < b then
                  if b = b - 1 + 1 then C (size - 2) - C (b - 1 - 1) * C (size - b)
                  else C (b - 1 - 1) * C (size - b) else 0) = _
                rw [if_pos (by omega : 2 ≤ b - 1 ∧ b - 1 < b),
                  if_pos (by omega : b = b - 1 + 1), show b - 1 - 1 = b - 2 by omega]
              have growth := gap (b - 2) (size - b) (by omega) (by omega)
              rw [show b - 2 + (size - b) = size - 2 by omega] at growth
              change (b - 2) * C (size - b) ≤ C (size - 2) - C (b - 2) * C (size - b) ∧
                (b - 2 = 2 → (b - 2) * C (size - b) <
                  C (size - 2) - C (b - 2) * C (size - b)) at growth
              have ls := split (fun a => lay a b); have as := split (fun a => asc a b)
              rw [commonSum, layEdge, layOne] at ls; rw [ascOne, ascEdge] at as
              constructor
              · omega
              · intro he
                have strict := growth.2 (by omega)
                omega
          have strictSum : (∑ b ∈ Finset.range size, ∑ a ∈ Finset.range size, lay a b) <
              ∑ b ∈ Finset.range size, ∑ a ∈ Finset.range size, asc a b := by
            apply Finset.sum_lt_sum
            · intro b hb; exact (row b (Finset.mem_range.mp hb)).1
            · exact ⟨4, Finset.mem_range.mpr (by omega), (row 4 (by omega)).2 rfl⟩
          rw [layered_single_bad_count size hsize,
            alternating_single_bad_count size hsize]
          change (∑ a ∈ Finset.range size, ∑ b ∈ Finset.range size, lay a b) <
            ∑ a ∈ Finset.range size, ∑ b ∈ Finset.range size, asc a b
          rw [Finset.sum_comm, Finset.sum_comm (f := asc)]; exact strictSum
        simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at hr ht
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | rfl | {
          exfalso; try simp only [cA1, cA2, cB1, cC1, cC2] at circleEq
          try simp only [nA1, nA2, nB1, nC1, nC2] at near
          omega }
      · have small : k = 4 ∨ k = 5 := by omega
        have equal6 := ert 6 (by omega); have equal7 := ert 7 (by omega)
        rw [finiteCount 6 (by omega) k r (repsPerm r hr),
          finiteCount 6 (by omega) k t (repsPerm t ht)] at equal6
        rw [finiteCount 7 (by omega) k r (repsPerm r hr),
          finiteCount 7 (by omega) k t (repsPerm t ht)] at equal7
        simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at hr ht
        rcases small with rfl | rfl
        · have values6 := table64; have values7 := table74
          generalize hf6 : count 6 4 = f6 at values6 equal6
          generalize hf7 : count 7 4 = f7 at values7 equal7
          simp only [reps, List.map_cons, List.map_nil, List.cons.injEq, and_true]
            at values6 values7
          obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := values6; obtain ⟨w0, w1⟩ := values7
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals first | rfl | {
            exfalso
            omega }
        · have values6 := table65; have values7 := table75
          generalize hf6 : count 6 5 = f6 at values6 equal6
          generalize hf7 : count 7 5 = f7 at values7 equal7
          simp only [reps, List.map_cons, List.map_nil, List.cons.injEq, and_true]
            at values6 values7
          obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := values6; obtain ⟨w0, w1, w2, w3⟩ := values7
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals first | rfl | {
            exfalso
            omega }
    subst t; exact orbitTransfer r q s (repsPerm r hr) hqr hst
  · exact RotationAvoidanceSymmetry.orbit_wilfEquivalent k (by omega) q s hq
end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidance
