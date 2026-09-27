/- GID: D5/S3/Quantum/Dynamics/OpenIntegrableCircuitMinDepth
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/OpenIntegrableCircuitMinDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The minimum depth of the open-boundary integrable quantum circuits of Garcia Fernandez, Paletta and Retore with kappa sites carrying -kappa among N sites is floor(N/(kappa + 1)) + 1 whenever 1 <= kappa and 2 kappa <= N. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: the circuit is the path of sites
  0, 1, ..., N read in the order given by `pathOrder` (`circuit_eq_pathOrder`, `pathOrder_sorted`),
  so it fits in L layers exactly when some labelling of the sites below L increases along each
  step k -> k + 1 into S and decreases along each other step (`runsIn_iff_pathLayers`); such a
  labelling forces N < (|S| + 1) L (`pathLayers_lower`), and a balanced choice of S admits one with
  L = floor(N/(kappa + 1)) + 1 (`exists_pathLayers`)
admission_basis: escape-witness (issue #10393)
Direct frozen dependencies: D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation: `Gate`,
  `Gate.sites`, `circuit`, `RunsIn`, `depth`, `minDepth`
-/

import D5.S3.Quantum.Dynamics.OpenIntegrableCircuitDepthRefutation
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.OpenIntegrableCircuitMinDepth

open D5.S3.Quantum.Dynamics.OpenIntegrableCircuitDepthRefutation

/-!
García Fernández, Paletta and Retore, *Open-boundary integrable quantum circuits with different
geometries*, arXiv:2607.02093v1, conjecture minimum depths linear in the number `κ` of sites
carrying `-κ`; `OpenIntegrableCircuitDepthRefutation` refutes both formulas. This module proves the
correct value `⌊N/(κ + 1)⌋ + 1` for `1 ≤ κ ≤ N/2`, with the circuits, layerings and depth of that
module.
-/

/-- Site `0` stands for the boundary gate `K1`, site `N` for `KN`, and site `k` in between for the
two-site gate `U k`. -/
private def pathGate (N k : ℕ) : Gate :=
  if k = 0 then Gate.K1 else if k = N then Gate.KN else Gate.U k

/-- The sites `0, …, N` in the time order of the circuit: the sites outside `S` in decreasing order,
then `0`, then the sites of `S` in increasing order. -/
private def pathOrder (N : ℕ) (S : Finset ℕ) : List ℕ :=
  ((List.range' 1 N).filter fun k => k ∉ S).reverse ++ [0] ++
    ((List.range' 1 N).filter fun k => k ∈ S)

/-- A number increasing along `pathOrder`. -/
private def timeKey (N : ℕ) (S : Finset ℕ) (k : ℕ) : ℕ :=
  if k = 0 then N + 1 else if k ∈ S then N + 1 + k else N - k

/-- For `1 ≤ κ` and `2κ ≤ N`, the least depth over the configurations of `κ` sites is
`⌊N/(κ + 1)⌋ + 1`. -/
theorem result (N κ : ℕ) (hκ : 1 ≤ κ) (hN : 2 * κ ≤ N) : minDepth N κ = N / (κ + 1) + 1 := by
  have hN1 : 1 ≤ N := by omega
  have mem_pathOrder : ∀ (S : Finset ℕ) (k : ℕ), k ∈ pathOrder N S ↔ k ≤ N := by
    intro S k
    simp only [pathOrder, List.mem_append, List.mem_reverse, List.mem_filter,
      List.mem_singleton, decide_eq_true_eq, List.mem_range'_1]
    by_cases h : k ∈ S <;> simp [h] <;> omega
  -- the circuit is the path of sites read in `pathOrder`
  have circuit_eq_pathOrder : ∀ S : Finset ℕ, circuit N S = (pathOrder N S).map (pathGate N) := by
    intro S
    have hr : List.range' 1 N = List.range' 1 (N - 1) ++ [N] := by
      simpa [show N - 1 + 1 = N by omega, show 1 + (N - 1) = N by omega]
        using (List.range'_1_concat (s := 1) (n := N - 1))
    have hm (p : ℕ → Bool) :
        ((List.range' 1 (N - 1)).filter p).map (pathGate N) =
          ((List.range' 1 (N - 1)).filter p).map Gate.U := by
      apply List.map_congr_left
      intro k hk
      have hk' := List.mem_range'_1.mp (List.mem_filter.mp hk).1
      simp [pathGate, show k ≠ 0 by omega, show k ≠ N by omega]
    have hmr (p : ℕ → Bool) :
        (((List.range' 1 (N - 1)).filter p).reverse).map (pathGate N) =
          (((List.range' 1 (N - 1)).filter p).reverse).map Gate.U := by
      simp only [List.map_reverse, hm]
    by_cases h : N ∈ S <;>
      simp [circuit, pathOrder, hr, h, pathGate, show N ≠ 0 by omega, hm, hmr,
        List.append_assoc]
  -- `timeKey` increases along `pathOrder`
  have pathOrder_sorted : ∀ S : Finset ℕ,
      (pathOrder N S).Pairwise (fun a b => timeKey N S a < timeKey N S b) := by
    intro S
    have hs : (List.range' 1 N).Pairwise (fun a b => a < b) := List.pairwise_lt_range'
    have hr : (((List.range' 1 N).filter fun k => k ∉ S).reverse).Pairwise
        (fun a b => timeKey N S a < timeKey N S b) := by
      rw [List.pairwise_reverse, List.pairwise_filter]
      apply hs.imp_of_mem
      intro a b ha hb hab hsa hsb
      have ha' := List.mem_range'_1.mp ha
      have hb' := List.mem_range'_1.mp hb
      simp only [decide_eq_true_eq] at hsa hsb
      simp [timeKey, show a ≠ 0 by omega, show b ≠ 0 by omega, hsa, hsb]
      omega
    have ht : ((List.range' 1 N).filter fun k => k ∈ S).Pairwise
        (fun a b => timeKey N S a < timeKey N S b) := by
      rw [List.pairwise_filter]
      apply hs.imp_of_mem
      intro a b ha hb hab hsa hsb
      have ha' := List.mem_range'_1.mp ha
      have hb' := List.mem_range'_1.mp hb
      simp only [decide_eq_true_eq] at hsa hsb
      simp [timeKey, show a ≠ 0 by omega, show b ≠ 0 by omega, hsa, hsb, hab]
    simp only [pathOrder, List.pairwise_append, hr, ht, List.pairwise_singleton,
      true_and, List.mem_append, List.mem_singleton, List.mem_reverse, List.mem_filter,
      decide_eq_true_eq, List.mem_range'_1]
    constructor
    · intro a ha b hb
      subst b
      simp [timeKey, show a ≠ 0 by omega, ha.2]
      omega
    · intro a ha b hb
      rcases ha with ha | rfl
      · simp [timeKey, show a ≠ 0 by omega, show b ≠ 0 by omega, ha.2, hb.2]
        omega
      · simp [timeKey, show b ≠ 0 by omega, hb.2]
        omega
  -- consecutive sites share a site of the chain, and only consecutive ones do
  have adjacent_overlap : ∀ k < N,
      ((pathGate N k).sites N ∩ (pathGate N (k + 1)).sites N).Nonempty := by
    intro k hk
    refine ⟨k + 1, ?_⟩
    simp only [Finset.mem_inter, pathGate]
    split_ifs <;> simp_all [Gate.sites]
  have overlap_adjacent : ∀ a b : ℕ, a ≤ N → b ≤ N → a ≠ b →
      ((pathGate N a).sites N ∩ (pathGate N b).sites N).Nonempty → a + 1 = b ∨ b + 1 = a := by
    intro a b ha hb hne h
    rcases h with ⟨x, hx⟩
    simp only [Finset.mem_inter, pathGate] at hx
    split_ifs at hx <;> simp_all [Gate.sites] <;> omega
  have timeKey_adjacent : ∀ (S : Finset ℕ) (k : ℕ), k < N →
      if k + 1 ∈ S then timeKey N S k < timeKey N S (k + 1)
      else timeKey N S (k + 1) < timeKey N S k := by
    intro S k hk
    by_cases h0 : k = 0 <;> by_cases hS : k ∈ S <;> by_cases hT : k + 1 ∈ S <;>
      simp_all [timeKey] <;> omega
  have pathOrder_index_lt : ∀ (S : Finset ℕ) (a b : ℕ), a ≤ N → b ≤ N →
      timeKey N S a < timeKey N S b → (pathOrder N S).idxOf a < (pathOrder N S).idxOf b := by
    intro S a b ha hb hab
    have ha' := List.idxOf_lt_length_of_mem ((mem_pathOrder S a).mpr ha)
    have hb' := List.idxOf_lt_length_of_mem ((mem_pathOrder S b).mpr hb)
    by_contra h
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt h) with heq | hlt
    · have he : a = b := by
        calc
          a = (pathOrder N S)[(pathOrder N S).idxOf a] := (List.getElem_idxOf ha').symm
          _ = (pathOrder N S)[(pathOrder N S).idxOf b] := by simp [heq]
          _ = b := List.getElem_idxOf hb'
      simp [he] at hab
    · have ht := List.pairwise_iff_getElem.mp (pathOrder_sorted S) _ _ hb' ha' hlt
      simp only [List.getElem_idxOf] at ht
      omega
  -- a layering of the circuit is a labelling of the sites, increasing along each step `k → k + 1`
  -- into `S` and decreasing along each other step
  have runsIn_iff_pathLayers : ∀ (S : Finset ℕ) (L : ℕ),
      RunsIn N (circuit N S) L ↔ ∃ g : ℕ → ℕ, (∀ k ≤ N, g k < L) ∧
        ∀ k < N, if k + 1 ∈ S then g k < g (k + 1) else g (k + 1) < g k := by
    intro S L
    rw [circuit_eq_pathOrder S]
    have hget (i : ℕ) (hi : i < (pathOrder N S).length) :
        ((pathOrder N S).map (pathGate N)).getD i Gate.K1 =
          pathGate N (pathOrder N S)[i] := by
      rw [← List.getElem_eq_getD (h := by simpa using hi)]
      simp
    constructor
    · rintro ⟨f, hf, ho⟩
      simp only [List.length_map] at hf ho
      have hidx (k : ℕ) (hk : k ≤ N) :
          (pathOrder N S).idxOf k < (pathOrder N S).length :=
        List.idxOf_lt_length_of_mem ((mem_pathOrder S k).mpr hk)
      have hg (k : ℕ) (hk : k ≤ N) :
          ((pathOrder N S).map (pathGate N)).getD ((pathOrder N S).idxOf k) Gate.K1 =
            pathGate N k := by
        rw [hget _ (hidx k hk), List.getElem_idxOf]
      refine ⟨fun k => f ((pathOrder N S).idxOf k), ?_, ?_⟩
      · intro k hk
        exact hf _ (hidx k hk)
      · intro k hk
        have hk' : k ≤ N := by omega
        have hk1 : k + 1 ≤ N := by omega
        have ht := timeKey_adjacent S k hk
        have hov := adjacent_overlap k hk
        by_cases hm : k + 1 ∈ S
        · simp only [hm, ↓reduceIte] at ht ⊢
          apply ho _ (hidx (k + 1) hk1) _ (pathOrder_index_lt S k (k + 1) hk' hk1 ht)
          simpa only [hg k hk', hg (k + 1) hk1] using hov
        · simp only [hm, ↓reduceIte] at ht ⊢
          apply ho _ (hidx k hk') _ (pathOrder_index_lt S (k + 1) k hk1 hk' ht)
          simpa only [hg k hk', hg (k + 1) hk1, Finset.inter_comm] using hov
    · rintro ⟨g, hg⟩
      refine ⟨fun i => g ((pathOrder N S).getD i 0), ?_, ?_⟩
      · intro i hi
        have hi' : i < (pathOrder N S).length := by simpa using hi
        dsimp only
        rw [← List.getElem_eq_getD (h := hi') 0]
        exact hg.1 _ ((mem_pathOrder S _).mp (List.getElem_mem hi'))
      · intro j hj i hij hov
        have hj' : j < (pathOrder N S).length := by simpa using hj
        have hi' : i < (pathOrder N S).length := by omega
        rw [hget i hi', hget j hj'] at hov
        dsimp only
        rw [← List.getElem_eq_getD (h := hi') 0, ← List.getElem_eq_getD (h := hj') 0]
        have ht := List.pairwise_iff_getElem.mp (pathOrder_sorted S) i j hi' hj' hij
        have ha := (mem_pathOrder S _).mp (List.getElem_mem hi')
        have hb := (mem_pathOrder S _).mp (List.getElem_mem hj')
        have hne : (pathOrder N S)[i] ≠ (pathOrder N S)[j] := by
          intro he
          rw [he] at ht
          exact Nat.lt_irrefl _ ht
        rcases overlap_adjacent _ _ ha hb hne hov with he | he
        · have hk : (pathOrder N S)[i] < N := by omega
          have ht' := timeKey_adjacent S (pathOrder N S)[i] hk
          have hh := hg.2 (pathOrder N S)[i] hk
          rw [he] at ht' hh
          split_ifs at ht' hh with hm
          · exact hh
          · omega
        · have hk : (pathOrder N S)[j] < N := by omega
          have ht' := timeKey_adjacent S (pathOrder N S)[j] hk
          have hh := hg.2 (pathOrder N S)[j] hk
          rw [he] at ht' hh
          split_ifs at ht' hh with hm
          · omega
          · exact hh
  -- lower bound: every labelling with values below `L` forces `N < (|S| + 1) L`
  have pathLayers_lower : ∀ (S : Finset ℕ) (L : ℕ) (g : ℕ → ℕ), S ⊆ Finset.Icc 1 N →
      ((∀ k ≤ N, g k < L) ∧ ∀ k < N, if k + 1 ∈ S then g k < g (k + 1) else g (k + 1) < g k) →
      N < (S.card + 1) * L := by
    intro S L g hS hg
    have hind : ∀ n ≤ N, n + g n ≤ (S.filter fun k => k ≤ n).card * L + g 0 := by
      intro n hn
      induction n with
      | zero => simp
      | succ n ih =>
        have hnN : n < N := by omega
        have hp := ih (by omega)
        have hs := hg.2 n hnN
        have hb := hg.1 (n + 1) (by omega)
        by_cases hm : n + 1 ∈ S
        · have he : S.filter (fun k => k ≤ n + 1) =
              insert (n + 1) (S.filter fun k => k ≤ n) := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hk, hkn⟩
              by_cases h : k = n + 1
              · exact Or.inl h
              · exact Or.inr ⟨hk, by omega⟩
            · rintro (rfl | ⟨hk, hkn⟩)
              · exact ⟨hm, le_rfl⟩
              · exact ⟨hk, by omega⟩
          rw [he, Finset.card_insert_of_notMem (by simp)]
          simp only [Nat.add_mul, one_mul]
          omega
        · have he : S.filter (fun k => k ≤ n + 1) = S.filter (fun k => k ≤ n) := by
            ext k
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hk, hkn⟩
              refine ⟨hk, ?_⟩
              by_contra hh
              have heq : k = n + 1 := by omega
              exact hm (heq ▸ hk)
            · rintro ⟨hk, hkn⟩
              exact ⟨hk, by omega⟩
          simp only [hm, ↓reduceIte] at hs
          simpa only [show n.succ = n + 1 from rfl, he] using (by omega :
            n + 1 + g (n + 1) ≤ (S.filter fun k => k ≤ n).card * L + g 0)
    have hf : S.filter (fun k => k ≤ N) = S := by
      apply Finset.filter_eq_self.mpr
      intro k hk
      exact (Finset.mem_Icc.mp (hS hk)).2
    have hh := hind N le_rfl
    rw [hf] at hh
    have h0 := hg.1 0 (Nat.zero_le N)
    nlinarith
  -- upper bound: a balanced configuration admits a labelling below `q + 1`
  have exists_pathLayers : ∀ q κ n : ℕ, 1 ≤ q → 2 * κ ≤ n → n ≤ (κ + 1) * q + κ →
      ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ S.card = κ ∧ ∃ g : ℕ → ℕ,
        ((∀ k ≤ n, g k < q + 1) ∧
          ∀ k < n, if k + 1 ∈ S then g k < g (k + 1) else g (k + 1) < g k) ∧ g n = 0 := by
    intro q κ
    induction κ with
    | zero =>
      intro n hq hlo hhi
      refine ⟨∅, by simp, by simp, (fun k => n - k), ?_, by simp⟩
      constructor
      · intro k hk
        dsimp
        simp only [Nat.zero_add, Nat.one_mul] at hhi
        omega
      · intro k hk
        simp only [Finset.notMem_empty, ↓reduceIte]
        omega
    | succ κ ih =>
      intro n hq hlo hhi
      let d := min q (n - 2 * κ - 1)
      let M := n - d - 1
      have hd : 1 ≤ d := by dsimp [d]; omega
      have hdq : d ≤ q := min_le_left _ _
      have hdN : d ≤ n - 2 * κ - 1 := min_le_right _ _
      have hMN : M + 1 + d = n := by dsimp [M]; omega
      have hMlo : 2 * κ ≤ M := by omega
      have hMhi : M ≤ (κ + 1) * q + κ := by
        by_cases hh : q ≤ n - 2 * κ - 1
        · have he : d = q := min_eq_left hh
          nlinarith
        · have he : d = n - 2 * κ - 1 := min_eq_right (by omega)
          have heM : M = 2 * κ := by omega
          rw [heM]
          nlinarith
      rcases ih M hq hMlo hMhi with ⟨S, hS, hc, g, hg, hgM⟩
      have hnot : M + 1 ∉ S := by
        intro h
        have := (Finset.mem_Icc.mp (hS h)).2
        omega
      refine ⟨insert (M + 1) S, ?_, by simp [hnot, hc],
        (fun k => if k ≤ M then g k else n - k), ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simp only [Finset.mem_Icc]
          omega
        · have := Finset.mem_Icc.mp (hS hk)
          simp only [Finset.mem_Icc]
          omega
      · constructor
        · intro k hk
          dsimp
          split_ifs with hh
          · exact hg.1 k hh
          · omega
        · intro k hk
          by_cases hkm : k < M
          · have he : k + 1 ∈ insert (M + 1) S ↔ k + 1 ∈ S := by
              simp [show k ≠ M by omega]
            simpa only [he, if_pos (show k ≤ M by omega), if_pos (show k + 1 ≤ M by omega)]
              using hg.2 k hkm
          · by_cases he : k = M
            · subst k
              simp [hgM, show ¬M + 1 ≤ M by omega]
              omega
            · have hks : k + 1 ∉ insert (M + 1) S := by
                intro hh
                rcases Finset.mem_insert.mp hh with hh | hh
                · omega
                · have := (Finset.mem_Icc.mp (hS hh)).2
                  omega
              simp only [hks, ↓reduceIte, if_neg (show ¬k ≤ M by omega),
                if_neg (show ¬k + 1 ≤ M by omega)]
              omega
      · simp [show ¬n ≤ M by omega]
  -- the depth is attained
  have runsIn_depth : ∀ w : List Gate, RunsIn N w (depth N w) := by
    intro w
    change sInf {L | RunsIn N w L} ∈ {L | RunsIn N w L}
    exact Nat.sInf_mem ⟨w.length, id, fun _ h => h, fun _ _ _ h _ => h⟩
  have depth_lower : ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N →
      N / (S.card + 1) + 1 ≤ depth N (circuit N S) := by
    intro S hS
    rcases (runsIn_iff_pathLayers S _).mp (runsIn_depth (circuit N S)) with ⟨g, hg⟩
    have h := pathLayers_lower S _ g hS hg
    have hdiv : N / (S.card + 1) < depth N (circuit N S) :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [Nat.mul_comm] using h)
    omega
  have hq : 1 ≤ N / (κ + 1) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hmod := Nat.mod_lt N (show 0 < κ + 1 by omega)
  have hdiv := Nat.mod_add_div N (κ + 1)
  have hhi : N ≤ (κ + 1) * (N / (κ + 1)) + κ := by omega
  rcases exists_pathLayers (N / (κ + 1)) κ N hq hN hhi with ⟨S, hS, hc, g, hg, _⟩
  have hr : RunsIn N (circuit N S) (N / (κ + 1) + 1) :=
    (runsIn_iff_pathLayers S _).mpr ⟨g, hg⟩
  have hm : depth N (circuit N S) ∈
      {d | ∃ T : Finset ℕ, T ⊆ Finset.Icc 1 N ∧ T.card = κ ∧ depth N (circuit N T) = d} :=
    ⟨S, hS, hc, rfl⟩
  apply le_antisymm
  · exact (Nat.sInf_le hm).trans (Nat.sInf_le hr)
  · apply le_csInf ⟨_, hm⟩
    rintro d ⟨T, hT, hcard, rfl⟩
    simpa only [hcard] using depth_lower T hT

end D5.S3.Quantum.Dynamics.OpenIntegrableCircuitMinDepth
