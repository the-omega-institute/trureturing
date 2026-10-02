/- GID: D5/S3/Combinatorics/VincularStack/VincularStackSort
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VincularStack/VincularStackSort
   mirror-E: none(waiver:finite-kernel-cancellation)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Schroder, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Finite weighted tree sums and kernel cancellation give the Schroeder enumeration. -/

import D5.S3.Combinatorics.VincularStack.VincularStackTree
import Mathlib.RingTheory.PowerSeries.Schroder
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VincularStack.VincularStackCounting

open VincularStackDefs VincularStackBasic VincularStackParents VincularStackTree

def labelledLevel : ℕ → Σ carrier : Type, carrier → ℕ
  | 0 => ⟨PUnit, fun _ => 2⟩
  | depth + 1 =>
    let previous := labelledLevel depth
    ⟨Σ parent : previous.1, Fin (previous.2 parent), fun pair =>
      if pair.2.val = 0 then previous.2 pair.1 + 1 else pair.2.val + 2⟩


end D5.S3.Combinatorics.VincularStack.VincularStackCounting

namespace D5.S3.Combinatorics.VincularStack.VincularStackSort

open VincularStackDefs VincularStackCounting Finset PowerSeries
open VincularStackBasic VincularStackParents VincularStackTree

theorem result : VincularStackDefs.claim := by
  classical
  have level_equivalence (depth : ℕ) :
      ∃ equivalence : sortable (depth + 1) ≃ (labelledLevel depth).1,
        Finite (sortable (depth + 1)) ∧
        ∀ word : sortable (depth + 1),
          2 ≤ (activeSites word.val (depth + 2)).card ∧
            (activeSites word.val (depth + 2)).card =
              (labelledLevel depth).2 (equivalence word) := by
    classical
    have hnil : ¬ ContainsV [] := by
      rintro ⟨position, hposition, _⟩
      simp at hposition
    have hshort (word : List ℕ) (hsize : word.length ≤ 2) : ¬ Contains231 word := by
      rintro ⟨first, middle, last, hfirst, hmiddle, hlast, _⟩
      omega
    have hlabels (depth : ℕ) : ∀ node : (labelledLevel depth).1,
        2 ≤ (labelledLevel depth).2 node := by
      induction depth with
      | zero => intro node; exact le_refl 2
      | succ depth inductionHypothesis =>
        intro node
        change 2 ≤ if node.2.val = 0 then
          (labelledLevel depth).2 node.1 + 1 else node.2.val + 2
        split_ifs
        · have := inductionHypothesis node.1
          omega
        · omega
    induction depth with
    | zero =>
      have hroot : [1] ∈ sortable 1 := by
        refine ⟨by simp, ?_⟩
        have hperm := (process_preserves [1] [] hnil).1
        apply hshort
        simp [SC, hperm.length_eq]
      have hrootCard : (activeSites [1] 2).card = 2 := by
        have havoidNil : ¬ Contains231 (SC []) := by simpa [SC, Process] using hshort [] (by simp)
        obtain ⟨_, hrootRule, _⟩ := succession_rule [] 1 2
          (by simp) (by simp) (by omega) havoidNil
        have hsingle : ¬ Contains231 (SC [1]) := hroot.2
        have hbase : (activeSites [] 1).card = 1 := by simp [activeSites, hsingle]
        simpa [hbase] using hrootRule
      let equivalence : sortable 1 ≃ PUnit :=
        { toFun := fun _ => PUnit.unit
          invFun := fun _ => ⟨[1], hroot⟩
          left_inv := by
            intro word
            apply Subtype.ext
            have hperm : word.val.Perm [1] := by simpa using word.property.1
            exact (List.perm_singleton.mp hperm).symm
          right_inv := by intro value; cases value; rfl }
      refine ⟨equivalence, Finite.of_equiv PUnit equivalence.symm, ?_⟩
      intro word
      have hword : word.val = [1] := List.perm_singleton.mp (by simpa using word.property.1)
      refine ⟨by rw [hword, hrootCard], ?_⟩
      simpa only [labelledLevel, hword] using hrootCard
    | succ depth inductionHypothesis =>
      obtain ⟨previous, hfinitePrevious, hprevious⟩ := inductionHypothesis
      let _ : Finite (sortable (depth + 1)) := hfinitePrevious
      let _ : Finite (labelledLevel depth).1 :=
        Finite.of_equiv (sortable (depth + 1)) previous
      let _ : Fintype (labelledLevel depth).1 := Fintype.ofFinite _
      let _ : Finite (labelledLevel (depth + 1)).1 := by
        change Finite (Σ parent : (labelledLevel depth).1, Fin ((labelledLevel depth).2 parent))
        infer_instance
      have hpreviousEqual (parent : sortable (depth + 1)) := (hprevious parent).2
      let Eligible (parent : sortable (depth + 1)) :=
        {site : Fin (depth + 2) //
          parent.val.take site.val ++ (depth + 2) :: parent.val.drop site.val ∈
            sortable (depth + 2)}
      have hparentLength (parent : sortable (depth + 1)) : parent.val.length = depth + 1 := by
        simpa only [List.length_range'] using parent.property.1.length_eq
      have hparentBound (parent : sortable (depth + 1)) :
          ∀ value ∈ parent.val, value < depth + 2 := by
        intro value hvalue
        obtain ⟨index, hindex, hvalue⟩ :=
          List.mem_range'.mp (parent.property.1.mem_iff.mp hvalue)
        omega
      have hparentNodup (parent : sortable (depth + 1)) : parent.val.Nodup :=
        parent.property.1.nodup_iff.mpr (List.nodup_range')
      have hpermInsert (parent : sortable (depth + 1)) (site : ℕ) :
          (parent.val.take site ++ (depth + 2) :: parent.val.drop site).Perm
            (List.range' 1 (depth + 2)) := by
        have hmove : (parent.val.take site ++ (depth + 2) :: parent.val.drop site).Perm
            ((depth + 2) :: parent.val) := by
          simpa using (List.perm_middle :
            (parent.val.take site ++ (depth + 2) :: parent.val.drop site).Perm
              ((depth + 2) :: (parent.val.take site ++ parent.val.drop site)))
        have hcons := parent.property.1.cons (depth + 2)
        have hrotate : ((depth + 2) :: List.range' 1 (depth + 1)).Perm
            (List.range' 1 (depth + 2)) := by
          have hrange : List.range' 1 (depth + 2) =
              List.range' 1 (depth + 1) ++ [depth + 2] := by
            simpa only [Nat.one_mul, show 1 + (depth + 1) = depth + 2 by omega] using
              (List.range'_concat (s := 1) (n := depth + 1) (step := 1))
          rw [hrange]
          simpa using
            (List.perm_append_comm : ([depth + 2] ++ List.range' 1 (depth + 1)).Perm
              (List.range' 1 (depth + 1) ++ [depth + 2]))
        exact hmove.trans (hcons.trans hrotate)
      let eligibility (parent : sortable (depth + 1)) :
          Eligible parent ≃ activeSites parent.val (depth + 2) :=
        { toFun := fun site => ⟨site.val.val, by
            simp only [activeSites, Finset.mem_filter, Finset.mem_range]
            exact ⟨by rw [hparentLength]; exact site.val.isLt, site.property.2⟩⟩
          invFun := fun site => ⟨⟨site.val, by
            have hmem := (Finset.mem_filter.mp site.property).1
            simpa only [Finset.mem_range, hparentLength] using hmem⟩,
            hpermInsert parent site.val, (Finset.mem_filter.mp site.property).2⟩
          left_inv := by intro site; apply Subtype.ext; apply Fin.ext; rfl
          right_inv := by intro site; apply Subtype.ext; rfl }
      have edge_data (parent : sortable (depth + 1)) :
          ∃ edge : activeSites parent.val (depth + 2) ≃
              Fin ((activeSites parent.val (depth + 2)).card),
            ∀ site : activeSites parent.val (depth + 2),
              (activeSites (parent.val.take site.val ++ (depth + 2) :: parent.val.drop site.val)
                (depth + 3)).card =
                  if (edge site).val = 0 then (activeSites parent.val (depth + 2)).card + 1
                  else (edge site).val + 2 := by
        obtain ⟨rank, hzeroCount, hrankCount⟩ := succession_rule parent.val (depth + 2)
          (depth + 3) (hparentNodup parent) (hparentBound parent) (by omega) parent.property.2
        let sites := activeSites parent.val (depth + 2)
        have hzero : 0 ∈ sites := by
          have hlength : 0 < parent.val.length := by rw [hparentLength]; omega
          have hlast : parent.val.take 0 ++ (depth + 2) :: parent.val.drop 0 ∈
              sortable (depth + 2) := by
            refine ⟨hpermInsert parent 0, ?_⟩
            have hinsert := (VincularStackMarkers.maximum_insertion [] parent.val (depth + 2)
              (by simpa using hparentBound parent)).1
            have hperm : (SC parent.val).Perm parent.val := by
              simpa [SC] using (process_preserves parent.val [] hnil).1
            have houtBound : ∀ value ∈ SC parent.val, value < depth + 2 := by
              intro value hvalue
              exact hparentBound parent value (hperm.mem_iff.mp hvalue)
            have houtNodup : (SC parent.val).Nodup := by
              exact hperm.nodup_iff.mpr (hparentNodup parent)
            have htest := VincularStackCuts.maximum_cut (SC parent.val) [] (depth + 2)
              (by simpa using houtNodup) (by simpa using houtBound)
            have hgap : VincularStackMarkers.outputGap [] parent.val = (SC parent.val).length := by
              simp [VincularStackMarkers.outputGap, hperm.length_eq]
            simp only [List.take_zero, List.drop_zero, List.nil_append]
            change ¬ Contains231 (SC ([] ++ (depth + 2) :: parent.val))
            rw [hinsert]
            simpa [hgap] using htest.mpr
              ⟨by simpa using parent.property.2, by simp [VincularStackCuts.separatingCut]⟩
          exact (eligibility parent ⟨⟨0, by omega⟩, hlast⟩).property
        have hpositive : 0 < sites.card := Finset.card_pos.mpr ⟨0, hzero⟩
        have hsitesCard : sites.card = (activeSites parent.val (depth + 2)).card := rfl
        let forward : sites → Fin sites.card := fun site =>
          if hsite : site.val = 0 then ⟨0, hpositive⟩ else
            ⟨(rank ⟨site.val, Finset.mem_erase.mpr ⟨hsite, site.property⟩⟩).val + 1, by
              have hbound := (rank ⟨site.val,
                Finset.mem_erase.mpr ⟨hsite, site.property⟩⟩).isLt
              omega⟩
        let backward : Fin sites.card → sites := fun position =>
          if hposition : position.val = 0 then ⟨0, hzero⟩ else
            ⟨(rank.symm ⟨position.val - 1, by have hbound := position.isLt; omega⟩).val,
              (Finset.mem_erase.mp (rank.symm _).property).2⟩
        let edge : sites ≃ Fin sites.card :=
          { toFun := forward
            invFun := backward
            left_inv := by
              intro site
              apply Subtype.ext
              by_cases hsite : site.val = 0
              · simp [forward, backward, hsite]
              · simp only [forward, dif_neg hsite]
                simp only [backward, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
                  Nat.add_sub_cancel]
                rw [dif_neg (by simp : ¬ False)]
                exact congrArg (fun point : sites.erase 0 => point.val)
                  (rank.symm_apply_apply
                    ⟨site.val, Finset.mem_erase.mpr ⟨hsite, site.property⟩⟩)
            right_inv := by
              intro position
              apply Fin.ext
              by_cases hposition : position.val = 0
              · simp [backward, forward, hposition]
              · have hnonzero := (Finset.mem_erase.mp (rank.symm
                  ⟨position.val - 1, by have hbound := position.isLt; omega⟩).property).1
                simp only [backward, dif_neg hposition, forward, dif_neg hnonzero]
                let recovered : Fin (sites.card - 1) :=
                  ⟨position.val - 1, by have hbound := position.isLt; omega⟩
                change (rank (rank.symm recovered)).val + 1 = position.val
                rw [Equiv.apply_symm_apply]
                simp only [recovered]
                omega }
        refine ⟨edge, ?_⟩
        intro site
        change (activeSites (parent.val.take site.val ++ (depth + 2) :: parent.val.drop site.val)
          (depth + 3)).card =
            if (forward site).val = 0 then sites.card + 1 else (forward site).val + 2
        by_cases hsite : site.val = 0
        · simp only [forward, dif_pos hsite]
          simpa [sites, hsite] using hzeroCount
        · have hcount := hrankCount ⟨site.val, Finset.mem_erase.mpr ⟨hsite, site.property⟩⟩
          simp only [forward, dif_neg hsite]
          simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
          omega
      let edge (parent : sortable (depth + 1)) := Classical.choose (edge_data parent)
      have hedge (parent : sortable (depth + 1)) := Classical.choose_spec (edge_data parent)
      let edges (parent : sortable (depth + 1)) :
          Eligible parent ≃ Fin ((labelledLevel depth).2 (previous parent)) :=
        ((eligibility parent).trans (edge parent)).trans (finCongr (hpreviousEqual parent))
      let equivalence : sortable (depth + 2) ≃ (labelledLevel (depth + 1)).1 :=
        (((parentSiteEquiv (depth + 1)).symm.trans (Equiv.sigmaCongrRight edges)).trans
          (Equiv.sigmaCongrLeft
            (β := fun node : (labelledLevel depth).1 => Fin ((labelledLevel depth).2 node))
            previous))
      refine ⟨equivalence, Finite.of_equiv (labelledLevel (depth + 1)).1 equivalence.symm, ?_⟩
      intro child
      let pair := (parentSiteEquiv (depth + 1)).symm child
      have hchild : child.val = pair.1.val.take pair.2.val.val ++ (depth + 2) ::
          pair.1.val.drop pair.2.val.val := by
        exact (congrArg Subtype.val ((parentSiteEquiv (depth + 1)).apply_symm_apply child)).symm
      have hcount := hedge pair.1 (eligibility pair.1 pair.2)
      have hequality : (activeSites child.val (depth + 3)).card =
          (labelledLevel (depth + 1)).2 (equivalence child) := by
        change (activeSites child.val (depth + 3)).card =
          if (edge pair.1 (eligibility pair.1 pair.2)).val = 0
          then (labelledLevel depth).2 (previous pair.1) + 1
          else (edge pair.1 (eligibility pair.1 pair.2)).val + 2
        rw [hchild, ← hpreviousEqual pair.1]
        exact hcount
      exact ⟨by rw [hequality]; exact hlabels _ _, hequality⟩
  have hfinite (depth : ℕ) : Finite (labelledLevel depth).1 := by
    obtain ⟨equivalence, hfinite, _⟩ := level_equivalence depth
    let _ := hfinite
    exact Finite.of_equiv (sortable (depth + 1)) equivalence
  let _ (depth : ℕ) : Finite (labelledLevel depth).1 := hfinite depth
  let _ (depth : ℕ) : Fintype (labelledLevel depth).1 := Fintype.ofFinite _
  have hlabels (depth : ℕ) (node : (labelledLevel depth).1) :
      2 ≤ (labelledLevel depth).2 node := by
    obtain ⟨equivalence, _, hlabel⟩ := level_equivalence depth
    have hbound := (hlabel (equivalence.symm node)).1
    have hequal := (hlabel (equivalence.symm node)).2
    rw [equivalence.apply_symm_apply] at hequal
    omega
  let schroder : PowerSeries ℚ := largeSchroderSeries.map (Nat.castRingHom ℚ)
  let kernelRoot : PowerSeries ℚ := (schroder + 1) * C (1 / 2 : ℚ)
  let kernelFactor : PowerSeries ℚ := kernelRoot - 2 * kernelRoot ^ 2
  have hschroder : schroder = 1 + X * schroder + X * schroder ^ 2 := by
    have hequation := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
    simpa only [map_add, map_one, map_mul, map_X, map_pow, schroder] using hequation
  have hhalf : (2 : PowerSeries ℚ) * C (1 / 2 : ℚ) = 1 := by
    rw [show (2 : PowerSeries ℚ) = C 2 by rfl, ← map_mul]
    norm_num
  have hroot : 2 * kernelRoot = schroder + 1 := by
    dsimp only [kernelRoot]
    calc
      2 * ((schroder + 1) * C (1 / 2 : ℚ)) =
          (schroder + 1) * (2 * C (1 / 2 : ℚ)) := by ring
      _ = schroder + 1 := by rw [hhalf, mul_one]
  have hkernel : 1 - kernelRoot = X * kernelFactor := by
    dsimp only [kernelFactor]
    have hscaled : 2 * (1 - kernelRoot - X * (kernelRoot - 2 * kernelRoot ^ 2)) = 0 := by
      linear_combination -hschroder + (-1 + X * (2 * kernelRoot + schroder)) * hroot
    have hzero : 1 - kernelRoot - X * (kernelRoot - 2 * kernelRoot ^ 2) = 0 := by
      calc
        _ = (2 * C (1 / 2 : ℚ)) *
            (1 - kernelRoot - X * (kernelRoot - 2 * kernelRoot ^ 2)) := by rw [hhalf, one_mul]
        _ = C (1 / 2 : ℚ) *
            (2 * (1 - kernelRoot - X * (kernelRoot - 2 * kernelRoot ^ 2))) := by ring
        _ = 0 := by rw [hscaled, mul_zero]
    exact sub_eq_zero.mp hzero
  have hrootZero : coeff 0 kernelRoot = 1 := by
    dsimp only [kernelRoot]
    rw [coeff_mul]
    norm_num [schroder, coeff_map]
  have hmodel : kernelRoot * schroder = -kernelFactor := by
    dsimp only [kernelFactor]
    linear_combination -kernelRoot * hroot
  let population (depth : ℕ) : ℕ := Fintype.card (labelledLevel depth).1
  let weighted (depth : ℕ) : PowerSeries ℚ :=
    ∑ node : (labelledLevel depth).1, kernelRoot ^ ((labelledLevel depth).2 node - 2)
  have hweightedZero : weighted 0 = 1 := by
    have hcard : Fintype.card (labelledLevel 0).1 = 1 := by
      calc
        _ = Fintype.card PUnit := Fintype.card_congr
          (show (labelledLevel 0).1 ≃ PUnit from Equiv.refl _)
        _ = 1 := by simp
    change (∑ _ : (labelledLevel 0).1, (1 : PowerSeries ℚ)) = 1
    simp only [sum_const, card_univ, nsmul_eq_mul, hcard, Nat.cast_one, mul_one]
  have hchildren (label : ℕ) (hlabel : 2 ≤ label) :
      (1 - kernelRoot) *
        (∑ edge : Fin label,
          kernelRoot ^ ((if edge.val = 0 then label + 1 else edge.val + 2) - 2)) =
        kernelRoot + kernelFactor * kernelRoot ^ (label - 2) := by
    have hlabelSplit : label = (label - 1) + 1 := by omega
    have hsum :
        (∑ edge : Fin label,
          kernelRoot ^ ((if edge.val = 0 then label + 1 else edge.val + 2) - 2)) =
          kernelRoot ^ (label - 1) +
            ∑ index ∈ range (label - 1), kernelRoot ^ (index + 1) := by
      conv_lhs => rw [hlabelSplit, Fin.sum_univ_succ]
      simp only [Fin.val_zero, if_true, Fin.val_succ, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, if_false]
      simp only [show label - 1 + 1 + 1 - 2 = label - 1 by omega,
        show ∀ index : ℕ, index + 1 + 2 - 2 = index + 1 by omega]
      congr 1
      exact Fin.sum_univ_eq_sum_range (fun index => kernelRoot ^ (index + 1)) (label - 1)
    have hgeometric (length : ℕ) :
        (1 - kernelRoot) * (∑ index ∈ range length, kernelRoot ^ (index + 1)) =
          kernelRoot - kernelRoot ^ (length + 1) := by
      induction length with
      | zero => simp
      | succ length inductionHypothesis =>
        rw [sum_range_succ, mul_add, inductionHypothesis, pow_succ kernelRoot (length + 1)]
        ring
    rw [hsum, mul_add, hgeometric]
    have hpowers : kernelRoot ^ (label - 1) = kernelRoot * kernelRoot ^ (label - 2) := by
      rw [show label - 1 = (label - 2) + 1 by omega, pow_succ']
    have hlastPower : kernelRoot ^ (label - 1 + 1) =
        kernelRoot ^ 2 * kernelRoot ^ (label - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hlastPower, hpowers]
    dsimp only [kernelFactor]
    ring
  have hstep (depth : ℕ) :
      (1 - kernelRoot) * weighted (depth + 1) =
        kernelRoot * C (population depth : ℚ) + kernelFactor * weighted depth := by
    have hsum : weighted (depth + 1) =
        ∑ parent : (labelledLevel depth).1,
          ∑ edge : Fin ((labelledLevel depth).2 parent),
            kernelRoot ^
              ((if edge.val = 0 then (labelledLevel depth).2 parent + 1
                else edge.val + 2) - 2) := by
      let equivalence : (labelledLevel (depth + 1)).1 ≃
          (Σ parent : (labelledLevel depth).1, Fin ((labelledLevel depth).2 parent)) :=
        Equiv.refl _
      have htransport := Fintype.sum_equiv equivalence
        (fun node => kernelRoot ^ ((labelledLevel (depth + 1)).2 node - 2))
        (fun node => kernelRoot ^
          ((if node.2.val = 0 then (labelledLevel depth).2 node.1 + 1
            else node.2.val + 2) - 2)) (fun _ => rfl)
      exact htransport.trans (Fintype.sum_sigma _)
    rw [hsum, mul_sum]
    simp_rw [hchildren _ (hlabels depth _)]
    rw [sum_add_distrib]
    simp only [sum_const, card_univ, nsmul_eq_mul]
    rw [← mul_sum]
    simp only [weighted, population, map_natCast]
    ring
  have htelescope (length : ℕ) :
      kernelRoot *
          (∑ depth ∈ range length, X ^ depth * C (population depth : ℚ)) =
        kernelFactor * (X ^ length * weighted length - 1) := by
    induction length with
    | zero => simp [hweightedZero]
    | succ length inductionHypothesis =>
      have htransition : kernelRoot * C (population length : ℚ) =
          kernelFactor * (X * weighted (length + 1) - weighted length) := by
        rw [hkernel] at hstep
        have hlocal := hstep length
        linear_combination -hlocal
      rw [sum_range_succ, mul_add, inductionHypothesis, pow_succ]
      calc
        kernelFactor * (X ^ length * weighted length - 1) +
            kernelRoot * (X ^ length * C (population length : ℚ)) =
          kernelFactor * (X ^ length * weighted length - 1) +
            X ^ length * (kernelRoot * C (population length : ℚ)) := by ring
        _ = kernelFactor * (X ^ length * X * weighted (length + 1) - 1) := by
          rw [htransition]
          ring
  have hcoefficient (depth : ℕ) :
      coeff depth
          (kernelRoot *
            (∑ index ∈ range (depth + 1), X ^ index * C (population index : ℚ))) =
        coeff depth (kernelRoot * schroder) := by
    rw [htelescope]
    have hboundary : coeff depth
        (kernelFactor * (X ^ (depth + 1) * weighted (depth + 1))) = 0 := by
      rw [show kernelFactor * (X ^ (depth + 1) * weighted (depth + 1)) =
        X ^ (depth + 1) * (kernelFactor * weighted (depth + 1)) by ring,
        coeff_X_pow_mul']
      simp
    rw [mul_sub, map_sub, hboundary, mul_one, zero_sub, ← map_neg, ← hmodel]
  have hpopulation (depth : ℕ) : population depth = Nat.largeSchroder depth := by
    induction depth using Nat.strong_induction_on with
    | h depth inductionHypothesis =>
      have hmember : (0, depth) ∈ antidiagonal depth :=
        mem_antidiagonal.mpr (zero_add depth)
      have htruncate (index : ℕ) (hindex : index ≤ depth) :
          coeff index
              (∑ position ∈ range (depth + 1), X ^ position * C (population position : ℚ)) =
            (population index : ℚ) := by
        rw [map_sum, sum_eq_single index]
        · rw [mul_comm, coeff_C_mul_X_pow, if_pos rfl]
        · intro position hposition hne
          rw [mul_comm, coeff_C_mul_X_pow, if_neg (Ne.symm hne)]
        · intro hnot
          exact (hnot (mem_range.mpr (by omega))).elim
      have hequation := hcoefficient depth
      rw [coeff_mul, coeff_mul] at hequation
      simp only [schroder, coeff_map, coeff_largeSchroderSeries] at hequation
      have hcancel :
          ∑ pair ∈ antidiagonal depth,
              coeff pair.1 kernelRoot *
                coeff pair.2
                  (∑ position ∈ range (depth + 1),
                    X ^ position * C (population position : ℚ)) =
            (population depth : ℚ) +
              ∑ pair ∈ (antidiagonal depth).erase (0, depth),
                coeff pair.1 kernelRoot * (Nat.largeSchroder pair.2 : ℚ) := by
        rw [← sum_erase_add _ _ hmember]
        rw [htruncate depth (le_refl depth), hrootZero, one_mul, add_comm]
        congr 1
        apply sum_congr rfl
        intro pair hpair
        obtain ⟨hne, hpair⟩ := mem_erase.mp hpair
        have htotal := mem_antidiagonal.mp hpair
        rw [htruncate pair.2 (by omega), inductionHypothesis pair.2 (by
          by_contra hnot
          have hsecond : pair.2 = depth := by omega
          have hfirst : pair.1 = 0 := by omega
          exact hne (Prod.ext hfirst hsecond))]
      rw [hcancel, ← sum_erase_add _ _ hmember] at hequation
      simp only [hrootZero, one_mul] at hequation
      have hcast : (population depth : ℚ) = (Nat.largeSchroder depth : ℚ) := by
        linear_combination hequation
      exact_mod_cast hcast
  intro size hsize
  have hsizeEq : size = (size - 1) + 1 := by omega
  rw [hsizeEq, Nat.add_sub_cancel]
  obtain ⟨equivalence, hfinite, _⟩ := level_equivalence (size - 1)
  let _ := hfinite
  let _ : Fintype (sortable ((size - 1) + 1)) := Fintype.ofFinite _
  rw [← Set.fintypeCard_eq_ncard, Fintype.card_congr equivalence]
  exact hpopulation (size - 1)

end D5.S3.Combinatorics.VincularStack.VincularStackSort
