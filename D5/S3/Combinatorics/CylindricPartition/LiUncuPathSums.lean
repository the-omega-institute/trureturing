/- GID: D5/S3/Combinatorics/CylindricPartition/LiUncuPathSums
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CylindricPartition/LiUncuPathSums
   mirror-E: none(waiver:weighted-insertion-slots)
   anchors: []
   utility: none
   digest: Mandatory insertion slots have a Gaussian polynomial weight enumerator. -/

import D5.S3.Combinatorics.CylindricPartition.LiUncuDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CylindricPartition.LiUncu

open Polynomial LiUncuDefs

/-- The mandatory inserted pair at an internal up-down vertex, and zero elsewhere. -/
def peakRequirement : List Step → ℕ → ℕ
  | [], _ => 0
  | Step.up :: Step.down :: _, 1 => 1
  | _ :: w, j + 1 => peakRequirement w j
  | _ :: _, 0 => 0

open Classical in
/-- The finite image of all admissible insertion vectors with a specified total. -/
noncomputable def insertionWords (q : List Step) (N : ℕ) (boundary : Bool) :
    Finset (List Step) :=
  (Finset.univ : Finset {v : Fin (q.length + 1) → Fin (N + 1) //
    Insertible q (v 0).val (List.ofFn (fun j : Fin q.length => (v j.succ).val)) ∧
      ∑ j, (v j).val = N }).image (fun v =>
        let w := insertPeaks q (v.val 0).val
          (List.ofFn (fun j : Fin q.length => (v.val j.succ).val))
        if boundary then Step.down :: (w ++ [Step.up]) else w)

open Classical in
/-- Deletion separates finite insertion fibers and transports their exact polynomial weights. -/
theorem peak_deletion_weighted_sum (S : Finset (List Step)) (N offset : ℕ)
    (boundary : Bool) :
    (∑ w ∈ S.biUnion (fun q => insertionWords q N boundary),
      (X : ℤ[X]) ^ peakWeight offset w) =
      X ^ (N ^ 2 + (offset + boundary.toNat) * N) * ∑ q ∈ S,
        if (peakData q).2.1 + (peakData q).2.2.sum ≤ N then
          X ^ peakWeight 0 q *
            gauss (q.length + (N - ((peakData q).2.1 + (peakData q).2.2.sum)))
              (N - ((peakData q).2.1 + (peakData q).2.2.sum))
        else 0 := by
  classical
  have fiber (q : List Step) (N offset : ℕ) :
      (∑ v : {v : Fin (q.length + 1) → Fin (N + 1) //
          Insertible q (v 0).val (List.ofFn (fun j : Fin q.length => (v j.succ).val)) ∧
            ∑ j, (v j).val = N},
        (X : ℤ[X]) ^ peakWeight offset
          (insertPeaks q (v.val 0).val
            (List.ofFn (fun j : Fin q.length => (v.val j.succ).val)))) =
        if (peakData q).2.1 + (peakData q).2.2.sum ≤ N then
          X ^ (N ^ 2 + offset * N + peakWeight 0 q) *
            gauss (q.length + (N - ((peakData q).2.1 + (peakData q).2.2.sum)))
              (N - ((peakData q).2.1 + (peakData q).2.2.sum))
        else 0 := by
    classical
    have forced (M N : ℕ) (b : Fin (M + 1) → ℕ) :
      (∑ u : {u : Fin (M + 1) → Fin (N + 1) //
          (∀ j, b j ≤ (u j).val) ∧ ∑ j, (u j).val = N},
        (X : ℤ[X]) ^ (∑ j, j.val * (u.val j).val)) =
        if (∑ j, b j) ≤ N then
          X ^ (∑ j, j.val * b j) * gauss (M + (N - ∑ j, b j)) (N - ∑ j, b j)
        else 0 := by
      let C (M m : ℕ) := {u : Fin (M + 1) → Fin (m + 1) // ∑ j, (u j).val = m}
      have free (M m : ℕ) :
          (∑ u : C M m, (X : ℤ[X]) ^ (∑ j, j.val * (u.val j).val)) =
            gauss (M + m) m := by
        induction M generalizing m with
        | zero =>
            let u : C 0 m := ⟨fun _ => ⟨m, by omega⟩, by simp⟩
            have unique (v : C 0 m) : v = u := by
              apply Subtype.ext
              funext j
              have hj : j = 0 := Fin.eq_zero j
              subst j
              apply Fin.ext
              simpa using v.property
            have diagonal (m : ℕ) : gauss m m = 1 := by
              induction m with
              | zero => rfl
              | succ m ih =>
                  rw [gauss, gauss_zero_of_lt m (m + 1) (by omega), Nat.sub_self]
                  simpa using ih
            conv_rhs => rw [zero_add, diagonal]
            rw [Finset.sum_eq_single u]
            · simp
            · intro v _ hv
              exact (hv (unique v)).elim
            · simp
        | succ M ihM =>
            induction m with
            | zero =>
                let u : C (M + 1) 0 := ⟨fun _ => 0, by simp⟩
                rw [Finset.sum_eq_single u]
                · simp [u, gauss]
                · intro v _ hv
                  exact (hv (Subtype.ext (_root_.funext fun _ => Fin.eq_zero _))).elim
                · simp
            | succ m ihm =>
                have bound (v : C (M + 1) (m + 1)) (j : Fin (M + 1)) :
                    (v.val j.castSucc).val + (v.val (Fin.last (M + 1))).val ≤ m + 1 := by
                  have hj := Finset.single_le_sum
                    (fun (i : Fin (M + 1)) _ => Nat.zero_le (v.val i.castSucc).val)
                    (Finset.mem_univ j)
                  have hs := v.property
                  rw [Fin.sum_univ_castSucc] at hs
                  omega
                let Small := C M (m + 1)
                let Tail := C (M + 1) m
                let Big := C (M + 1) (m + 1)
                let shorten (v : Big) (h : (v.val (Fin.last (M + 1))).val = 0) : Small :=
                  ⟨fun j => v.val j.castSucc, by
                    have hs := v.property
                    rw [Fin.sum_univ_castSucc, h] at hs
                    simpa using hs⟩
                let adjoin (v : Small) : Big :=
                  ⟨Fin.snoc v.val 0, by
                    rw [Fin.sum_univ_castSucc]
                    simp only [Fin.snoc_castSucc, Fin.snoc_last]
                    simpa using v.property⟩
                let lower (v : Big) (h : (v.val (Fin.last (M + 1))).val ≠ 0) : Tail :=
                  ⟨Fin.snoc (fun j => ⟨(v.val j.castSucc).val, by
                      have := bound v j
                      omega⟩)
                    ⟨(v.val (Fin.last (M + 1))).val - 1, by
                      have := (v.val (Fin.last (M + 1))).isLt
                      omega⟩, by
                    rw [Fin.sum_univ_castSucc]
                    simp only [Fin.snoc_castSucc, Fin.snoc_last]
                    have hs := v.property
                    rw [Fin.sum_univ_castSucc] at hs
                    omega⟩
                let raise (v : Tail) : Big :=
                  ⟨Fin.snoc (fun j => (v.val j.castSucc).castSucc)
                    ⟨(v.val (Fin.last (M + 1))).val + 1, by
                      have := (v.val (Fin.last (M + 1))).isLt
                      omega⟩, by
                    rw [Fin.sum_univ_castSucc]
                    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc]
                    have hs := v.property
                    rw [Fin.sum_univ_castSucc] at hs
                    omega⟩
                let e : Big ≃ Small ⊕ Tail :=
                  { toFun := fun v =>
                      if h : (v.val (Fin.last (M + 1))).val = 0 then
                        Sum.inl (shorten v h) else Sum.inr (lower v h)
                    invFun := Sum.elim adjoin raise
                    left_inv := by
                      intro v
                      dsimp
                      split_ifs with h
                      · apply Subtype.ext
                        funext j
                        cases j using Fin.lastCases with
                        | last => apply Fin.ext; simpa [adjoin] using h.symm
                        | cast j => simp [adjoin, shorten]
                      · apply Subtype.ext
                        funext j
                        cases j using Fin.lastCases with
                        | last =>
                            apply Fin.ext
                            simp only [Sum.elim_inr, raise, lower, Fin.snoc_last]
                            omega
                        | cast j => apply Fin.ext; simp [raise, lower]
                    right_inv := by
                      intro s
                      cases s with
                      | inl v =>
                          have h : ((adjoin v).val (Fin.last (M + 1))).val = 0 := by
                            simp [adjoin]
                          dsimp
                          rw [dif_pos h]
                          congr 1
                          apply Subtype.ext
                          funext j
                          simp [shorten, adjoin]
                      | inr v =>
                          have h : ((raise v).val (Fin.last (M + 1))).val ≠ 0 := by
                            simp [raise]
                          dsimp
                          rw [dif_neg h]
                          congr 1
                          apply Subtype.ext
                          funext j
                          cases j using Fin.lastCases with
                          | last => apply Fin.ext; simp [lower, raise]
                          | cast j => apply Fin.ext; simp [lower, raise] }
                rw [← e.symm.sum_comp
                  (fun v => (X : ℤ[X]) ^ (∑ j, j.val * (v.val j).val))]
                rw [Fintype.sum_sum_type]
                change (∑ v : Small, X ^ (∑ j, j.val * ((adjoin v).val j).val)) +
                    (∑ v : Tail, X ^ (∑ j, j.val * ((raise v).val j).val)) = _
                have wsmall (v : Small) :
                    (∑ j, j.val * ((adjoin v).val j).val) =
                      ∑ j, j.val * (v.val j).val := by
                  simp [adjoin, Fin.sum_univ_castSucc]
                have wtail (v : Tail) :
                    (∑ j, j.val * ((raise v).val j).val) =
                      (M + 1) + ∑ j, j.val * (v.val j).val := by
                  simp only [raise, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
                    Fin.val_castSucc, Fin.val_last]
                  ring
                simp_rw [wsmall, wtail, pow_add]
                rw [← Finset.mul_sum, ihM (m + 1), ihm]
                rw [show M + 1 + (m + 1) = (M + (m + 1)) + 1 by omega, gauss]
                rw [show M + (m + 1) - m = M + 1 by omega]
                simp only [show M + 1 + m = M + (m + 1) by omega, pow_add]
      by_cases hb : (∑ j, b j) ≤ N
      · rw [if_pos hb]
        let Forced := {u : Fin (M + 1) → Fin (N + 1) //
          (∀ j, b j ≤ (u j).val) ∧ ∑ j, (u j).val = N}
        let m := N - ∑ j, b j
        let subtract (u : Forced) : C M m :=
          ⟨fun j => ⟨(u.val j).val - b j, by
              have hs : (∑ j, ((u.val j).val - b j)) + ∑ j, b j = N := by
                rw [← Finset.sum_add_distrib]
                simp_rw [Nat.sub_add_cancel (u.property.1 _)]
                exact u.property.2
              have hj := Finset.single_le_sum (fun (i : Fin (M + 1)) _ =>
                Nat.zero_le ((u.val i).val - b i)) (Finset.mem_univ j)
              dsimp [m]
              omega⟩, by
            have hs : (∑ j, ((u.val j).val - b j)) + ∑ j, b j = N := by
              rw [← Finset.sum_add_distrib]
              simp_rw [Nat.sub_add_cancel (u.property.1 _)]
              exact u.property.2
            dsimp [m]
            omega⟩
        let add (u : C M m) : Forced :=
          ⟨fun j => ⟨b j + (u.val j).val, by
              have hj := Finset.single_le_sum (fun (i : Fin (M + 1)) _ =>
                Nat.zero_le (b i + (u.val i).val)) (Finset.mem_univ j)
              have hs : (∑ j, (b j + (u.val j).val)) = N := by
                rw [Finset.sum_add_distrib, u.property]
                dsimp [m]
                omega
              omega⟩, by
            constructor
            · intro j; exact Nat.le_add_right _ _
            · rw [Finset.sum_add_distrib, u.property]
              dsimp [m]
              omega⟩
        let e : Forced ≃ C M m :=
          { toFun := subtract
            invFun := add
            left_inv := by
              intro u
              apply Subtype.ext
              funext j
              apply Fin.ext
              change b j + ((u.val j).val - b j) = (u.val j).val
              have := u.property.1 j
              omega
            right_inv := by
              intro u
              apply Subtype.ext
              funext j
              apply Fin.ext
              change b j + (u.val j).val - b j = (u.val j).val
              omega }
        rw [← e.symm.sum_comp (fun u => (X : ℤ[X]) ^ (∑ j, j.val * (u.val j).val))]
        change (∑ u : C M m, X ^ (∑ j, j.val * ((add u).val j).val)) = _
        have weights (u : C M m) :
            (∑ j, j.val * ((add u).val j).val) =
              (∑ j, j.val * b j) + ∑ j, j.val * (u.val j).val := by
          dsimp [add]
          simp_rw [Nat.mul_add]
          exact Finset.sum_add_distrib
        simp_rw [weights, pow_add]
        rw [← Finset.mul_sum, free M m]
      · rw [if_neg hb]
        apply Finset.sum_eq_zero
        intro u _
        have hs : (∑ j, b j) ≤ ∑ j, (u.val j).val :=
          Finset.sum_le_sum (fun j _ => u.property.1 j)
        rw [u.property.2] at hs
        exact (hb hs).elim
    have req_zero (w : List Step) : peakRequirement w 0 = 0 := by
      cases w with
      | nil => rfl
      | cons s w =>
          cases s <;> cases w <;> simp [peakRequirement]
    have skip (w : List Step) (j : ℕ) :
        peakRequirement (Step.up :: Step.down :: w) (j + 2) = peakRequirement w j := by
      cases j <;> simp [peakRequirement, req_zero]
    have keep (s : Step) (w : List Step)
        (h : ∀ z, s = Step.up → w ≠ Step.down :: z) (j : ℕ) :
        peakRequirement (s :: w) (j + 1) = peakRequirement w j := by
      cases j with
      | zero =>
          cases s with
          | down => simp [peakRequirement, req_zero]
          | flat => simp [peakRequirement, req_zero]
          | up =>
              cases w with
              | nil => rfl
              | cons t w =>
                  cases t with
                  | up => simp [peakRequirement, req_zero]
                  | flat => simp [peakRequirement]
                  | down => exact (h w rfl rfl).elim
      | succ j =>
          cases s <;> cases w <;> simp [peakRequirement]
    have statistics (w : List Step) (offset : ℕ) :
        (∑ j : Fin (w.length + 1), peakRequirement w j.val) =
            (peakData w).2.1 + (peakData w).2.2.sum ∧
          (∑ j : Fin (w.length + 1), (offset + j.val) * peakRequirement w j.val) =
            peakWeight offset w := by
      fun_induction peakData w generalizing offset
      · rename_i w d ih
        have h := ih (offset + 2)
        constructor
        · simp only [List.length_cons]
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, req_zero, zero_add, Fin.val_succ]
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Fin.val_succ, Nat.zero_add,
            show peakRequirement (Step.up :: Step.down :: w) 1 = 1 from rfl]
          change 1 + (∑ j : Fin (w.length + 1),
            peakRequirement (Step.up :: Step.down :: w) (j.val + 1 + 1)) = _
          simp_rw [show ∀ j : ℕ, j + 1 + 1 = j + 2 by omega, skip]
          rw [h.1]
          dsimp [d]
          omega
        · simp only [List.length_cons]
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, req_zero, mul_zero, zero_add, Fin.val_succ]
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Fin.val_succ, Nat.zero_add, mul_one,
            show peakRequirement (Step.up :: Step.down :: w) 1 = 1 from rfl]
          have he (j : Fin (w.length + 1)) :
              (offset + (j.val + 1 + 1)) *
                  peakRequirement (Step.up :: Step.down :: w) (j.val + 1 + 1) =
                (offset + 2 + j.val) * peakRequirement w j.val := by
            rw [show j.val + 1 + 1 = j.val + 2 by omega, skip]
            congr 1
            omega
          simp_rw [he]
          rw [h.2]
          rfl
      · rename_i s w notpeak d ih
        have h := ih (offset + 1)
        constructor
        · simp only [List.length_cons]
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, req_zero, zero_add, Fin.val_succ]
          simp_rw [keep s w notpeak]
          rw [h.1]
          dsimp [d]
        · simp only [List.length_cons]
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, req_zero, mul_zero, zero_add, Fin.val_succ]
          simp_rw [keep s w notpeak]
          have he (j : Fin (w.length + 1)) : offset + (j.val + 1) = offset + 1 + j.val :=
            by omega
          simp_rw [he]
          rw [h.2]
          symm
          cases s with
          | down => rfl
          | flat => rfl
          | up =>
              cases w with
              | nil => rfl
              | cons s w =>
                  cases s with
                  | up => rfl
                  | flat => rfl
                  | down => exact (notpeak w rfl rfl).elim
      · simp [peakRequirement, peakWeight]
    have first (s : Step) (w : List Step) (t : ℕ) :
        (match s, w with | Step.up, Step.down :: _ => 0 < t | _, _ => True) ↔
          peakRequirement (s :: w) 1 ≤ t := by
      cases s with
      | up =>
          cases w with
          | nil => simp [peakRequirement]
          | cons s w => cases s <;> simp [peakRequirement]; omega
      | down => simp [peakRequirement, req_zero]
      | flat => simp [peakRequirement, req_zero]
    have later (s : Step) (w : List Step) (j : ℕ) :
        peakRequirement (s :: w) (j + 2) = peakRequirement w (j + 1) := by
      cases s <;> cases w <;> simp [peakRequirement]
    have admissible (w : List Step) (v : Fin (w.length + 1) → Fin (N + 1)) :
        Insertible w (v 0).val
            (List.ofFn (fun j : Fin w.length => (v j.succ).val)) ↔
          ∀ j, peakRequirement w j.val ≤ (v j).val := by
      induction w with
      | nil => simp [Insertible, peakRequirement]
      | cons s w ih =>
          let tail : Fin (w.length + 1) → Fin (N + 1) := fun j => v j.succ
          have htail := ih tail
          simp only [List.length_cons, List.ofFn_succ, Insertible]
          rw [htail]
          constructor
          · rintro ⟨hfirst, hrest⟩ j
            cases j using Fin.cases with
            | zero => simp [req_zero]
            | succ j =>
                cases j using Fin.cases with
                | zero =>
                    exact (first s w _).mp hfirst
                | succ j =>
                    have hr := hrest j.succ
                    simpa only [Fin.val_succ, show j.val + 1 + 1 = j.val + 2 by omega,
                      later, tail] using hr
          · intro h
            constructor
            · have hf := h ((0 : Fin (w.length + 1)).succ)
              exact (first s w _).mpr hf
            · intro j
              cases j using Fin.cases with
              | zero => simp [req_zero]
              | succ j =>
                  have hr := h j.succ.succ
                  simpa only [Fin.val_succ, show j.val + 1 + 1 = j.val + 2 by omega,
                    later, tail] using hr
    have indices (m : ℕ) (v : Fin m → ℕ) (offset : ℕ) :
        (((List.ofFn v).zipIdx offset).map (fun p => p.1 * p.2)).sum =
          ∑ j, (offset + j.val) * v j := by
      induction m generalizing offset with
      | zero => simp
      | succ m ih =>
          rw [List.ofFn_succ, List.zipIdx_cons, List.map_cons, List.sum_cons, ih]
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, add_zero, Fin.val_succ]
          congr 1
          · exact Nat.mul_comm _ _
          · apply Finset.sum_congr rfl
            intro j _
            congr 1
            omega
    let Forced := {v : Fin (q.length + 1) → Fin (N + 1) //
      (∀ j, peakRequirement q j.val ≤ (v j).val) ∧ ∑ j, (v j).val = N}
    let Slots := {v : Fin (q.length + 1) → Fin (N + 1) //
      Insertible q (v 0).val (List.ofFn (fun j : Fin q.length => (v j.succ).val)) ∧
        ∑ j, (v j).val = N}
    let e : Slots ≃ Forced := Equiv.subtypeEquivRight (fun v => by
      rw [admissible q v])
    obtain ⟨scan, hscan, hinv, _, hweight⟩ := peak_deletion_bijection
    have shift (w : List Step) :
        peakWeight offset w =
          offset * ((peakData w).2.1 + (peakData w).2.2.sum) + peakWeight 0 w := by
      rw [← (statistics w offset).2]
      simp_rw [Nat.add_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, (statistics w 0).1]
      congr 1
      simpa using (statistics w 0).2
    have weight (v : Slots) :
        peakWeight offset (insertPeaks q (v.val 0).val
          (List.ofFn (fun j : Fin q.length => (v.val j.succ).val))) =
            N ^ 2 + offset * N + ∑ j, j.val * (v.val j).val := by
      let d : {d : List Step × ℕ × List ℕ // Insertible d.1 d.2.1 d.2.2} :=
        ⟨(q, (v.val 0).val, List.ofFn (fun j : Fin q.length => (v.val j.succ).val)),
          v.property.1⟩
      have hw := hweight d
      rw [hinv d] at hw
      dsimp [d] at hw
      rw [List.sum_ofFn, indices] at hw
      have hn : (v.val 0).val + ∑ j : Fin q.length, (v.val j.succ).val = N := by
        simpa only [Fin.sum_univ_succ] using v.property.2
      rw [hn] at hw
      have hw' : peakWeight 0 (insertPeaks q (v.val 0).val
          (List.ofFn (fun j : Fin q.length => (v.val j.succ).val))) =
            N ^ 2 + ∑ j, j.val * (v.val j).val := by
        rw [Fin.sum_univ_succ]
        simpa only [Fin.val_zero, zero_mul, zero_add, Fin.val_succ, Nat.add_comm 1] using hw
      have hd := congrArg Subtype.val (scan.apply_symm_apply d)
      rw [hscan (scan.symm d), hinv d] at hd
      rw [shift, hw', hd]
      dsimp [d]
      rw [List.sum_ofFn, hn]
      omega
    simp_rw [weight, pow_add]
    rw [← Finset.mul_sum]
    rw [← e.symm.sum_comp (fun v : Slots => (X : ℤ[X]) ^
      (∑ j, j.val * (v.val j).val))]
    change (X ^ (N ^ 2) * X ^ (offset * N)) *
      (∑ v : Forced, X ^ (∑ j, j.val * (v.val j).val)) = _
    rw [forced q.length N (fun j => peakRequirement q j.val)]
    have hc := (statistics q 0).1
    have hw : (∑ j : Fin (q.length + 1), j.val * peakRequirement q j.val) = peakWeight 0 q :=
      by simpa using (statistics q 0).2
    rw [hc, hw]
    split_ifs
    · simp only [mul_assoc]
    · simp only [mul_zero]
  have append_up (w : List Step) (start : ℕ) :
      peakWeight start (w ++ [Step.up]) = peakWeight start w := by
    induction hn : w.length using Nat.strong_induction_on generalizing w start with
    | h n ih =>
        have smaller (v : List Step) (hv : v.length < w.length) (start : ℕ) :
            peakWeight start (v ++ [Step.up]) = peakWeight start v :=
          ih v.length (by omega) v start rfl
        cases w with
        | nil => rfl
        | cons s w =>
            cases s with
            | down =>
                simpa only [List.cons_append, peakWeight] using smaller w (by simp) (start + 1)
            | flat =>
                simpa only [List.cons_append, peakWeight] using smaller w (by simp) (start + 1)
            | up =>
                cases w with
                | nil => rfl
                | cons s w =>
                    cases s with
                    | down =>
                        simp only [List.cons_append, peakWeight]
                        rw [smaller w (by simp) (start + 2)]
                    | up =>
                        simpa only [List.cons_append, peakWeight] using
                          smaller (Step.up :: w) (by simp) (start + 1)
                    | flat =>
                        simpa only [List.cons_append, peakWeight] using
                          smaller (Step.flat :: w) (by simp) (start + 1)
  have boundary_weight (w : List Step) :
      peakWeight offset (if boundary then Step.down :: (w ++ [Step.up]) else w) =
        peakWeight (offset + boundary.toNat) w := by
    cases boundary with
    | false => rfl
    | true => exact append_up w (offset + 1)
  have unwrapped (w z : List Step)
      (h : (if boundary then Step.down :: (w ++ [Step.up]) else w) =
        (if boundary then Step.down :: (z ++ [Step.up]) else z)) : w = z := by
    cases boundary with
    | false => exact h
    | true => exact List.append_cancel_right (List.cons.inj h).2
  let Slots (q : List Step) := {v : Fin (q.length + 1) → Fin (N + 1) //
    Insertible q (v 0).val (List.ofFn (fun j : Fin q.length => (v j.succ).val)) ∧
      ∑ j, (v j).val = N}
  obtain ⟨scan, hscan, hinv, _, _⟩ := peak_deletion_bijection
  have data (q : List Step) (v : Slots q) :
      peakData (insertPeaks q (v.val 0).val
        (List.ofFn (fun j : Fin q.length => (v.val j.succ).val))) =
          (q, (v.val 0).val, List.ofFn (fun j : Fin q.length => (v.val j.succ).val)) := by
    let d : {d : List Step × ℕ × List ℕ // Insertible d.1 d.2.1 d.2.2} :=
      ⟨(q, (v.val 0).val, List.ofFn (fun j : Fin q.length => (v.val j.succ).val)),
        v.property.1⟩
    have hd := congrArg Subtype.val (scan.apply_symm_apply d)
    rw [hscan (scan.symm d), hinv d] at hd
    exact hd
  have injective (q : List Step) : Function.Injective (fun v : Slots q =>
      let w := insertPeaks q (v.val 0).val
        (List.ofFn (fun j : Fin q.length => (v.val j.succ).val))
      if boundary then Step.down :: (w ++ [Step.up]) else w) := by
    intro v u h
    have hd := congrArg peakData (unwrapped _ _ h)
    rw [data q v, data q u] at hd
    have hh := congrArg (fun d : List Step × ℕ × List ℕ => d.2.1) hd
    have ht := congrArg (fun d : List Step × ℕ × List ℕ => d.2.2) hd
    dsimp only at hh ht
    apply Subtype.ext
    have hl : List.ofFn (fun j => (v.val j).val) =
        List.ofFn (fun j => (u.val j).val) := by
      rw [List.ofFn_succ, List.ofFn_succ, hh, ht]
    have hv := List.ofFn_inj.mp hl
    funext j
    exact Fin.ext (congrFun hv j)
  have disjoint :
      (↑S : Set (List Step)).PairwiseDisjoint (fun q => insertionWords q N boundary) := by
    intro q _ r _ hqr
    apply Finset.disjoint_left.mpr
    intro w hq hr
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hq
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hr
    have hd := congrArg peakData (unwrapped _ _ (hv.trans hu.symm))
    rw [data q v, data r u] at hd
    exact hqr (congrArg Prod.fst hd)
  rw [Finset.sum_biUnion disjoint, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  unfold insertionWords
  rw [Finset.sum_image (fun v _ u _ h => injective q h)]
  simp_rw [boundary_weight]
  rw [fiber q N (offset + boundary.toNat)]
  split_ifs
  · simp only [pow_add, mul_assoc]
  · simp only [mul_zero]

end D5.S3.Combinatorics.CylindricPartition.LiUncu
