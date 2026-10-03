/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterate
   mirror-E: none(waiver:nonfinal-higher-layer-classification)
   anchors: []
   utility: none
   digest: The cycle classification and fixed tails count all iterated 132 avoidance layers. -/
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateDecomposition
set_option autoImplicit false
namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterate
open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection
open ThetaFixedDefs ThetaIterateCycle ThetaBasicInverse ThetaIterateRecords ThetaIteratePosition
local notation "B" => (fun word : List ℕ => List.map (hat word) (List.range' 1 (List.length word)))
set_option maxHeartbeats 1200000 in
theorem result : ThetaIterateDefs.claim := (by {
  classical {
  have cubic_forms (size : ℕ) (hsize : 2 ≤ size) :
    let firstMax : Set (List ℕ) := {word | word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3,
      2] ∧ word.getD 0 0 = size}; (4 ≤ size →
    let parameters : Set (List ℕ) := {parameter | parameter.Perm (List.range' 1 (size - 2)) ∧ P
      parameter ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2]};
    let firstMax : Set (List ℕ) := {word | word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3,
      2] ∧ word.getD 0 0 = size};
    let nonfinalMax : Set (List ℕ) := {word | word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1,
      3, 2] ∧ word.getD (size - 1) 0 ≠ size}; firstMax = insert (size :: List.range' 2 (size -
      2) ++ [1]) (P '' parameters) ∧ firstMax.ncard = parameters.ncard + 1 ∧ nonfinalMax =
      insert (List.range' 2 (size - 1) ++ [1]) firstMax ∧ nonfinalMax.ncard =
      parameters.ncard + 2 ∧ (5 ≤ size → firstMax.ncard = {word : List ℕ | word ∈
      ThetaIterateDefs.iterateAvoiders (size - 3) 2 [1, 3, 2] ∧ word.getD 0 0 = size - 3}.ncard +
      {parameter : List ℕ | parameter.Perm (List.range' 1 (size - 2)) ∧ parameter.getD 0 0 = size -
      2 ∧ P parameter ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2]}.ncard + 2) ∧
      (ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2]).ncard = (ThetaIterateDefs.iterateAvoiders
      (size - 1) 2 [1, 3, 2]).ncard + firstMax.ncard + 1) ∧ firstMax.ncard + 1 = (if size %
      3 = 0 then (size / 3) ^ 2 + 2 * (size / 3) else if size % 3 = 1 then (size / 3) ^ 2 + 2 *
      (size / 3) + 1 else (size / 3) ^ 2 + 3 * (size / 3) + 2) ∧ (ThetaIterateDefs.iterateAvoiders
      size 2 [1, 3, 2]).ncard = ThetaIterateDefs.quadCount size := (by {
  let firstMax : ℕ → Set (List ℕ) := fun dimension => {word | word ∈
    ThetaIterateDefs.iterateAvoiders dimension 2 [1, 3, 2] ∧ word.getD 0 0 = dimension};
  have hbase (size : ℕ) (hsize : 2 ≤ size) (hsmall : size ≤ 4) : (firstMax size).ncard + 1 = (if
    size % 3 = 0 then (size / 3) ^ 2 + 2 * (size / 3) else if size % 3 = 1 then (size / 3) ^ 2 + 2 *
    (size / 3) + 1 else (size / 3) ^ 2 + 3 * (size / 3) + 2) ∧ (ThetaIterateDefs.iterateAvoiders
    size 2 [1, 3, 2]).ncard = ThetaIterateDefs.quadCount size := (by {
  let firstMax : Set (List ℕ) := {word | word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3,
    2] ∧ word.getD 0 0 = size};
  have pattern_indices (word : List ℕ) : Contains [1, 3, 2] [] 3 word ↔ ∃ first middle last
    : Fin word.length, first < middle ∧ middle < last ∧ word[first.val] < word[last.val] ∧
    word[last.val] < word[middle.val] := (by {
  constructor; {
  rintro ⟨values, hlt, _, hsub, _⟩; change List.Sublist [values 1, values 3, values 2] word at hsub;
  obtain ⟨positions, hpositions⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub;
  have hfirst : word[(positions ⟨0, (by simp)⟩).val] = values 1 :=
    (by simpa using (hpositions ⟨0, (by simp)⟩).symm);
  have hmiddle : word[(positions ⟨1, (by simp)⟩).val] = values 3 :=
    (by simpa using (hpositions ⟨1, (by simp)⟩).symm);
  have hlast : word[(positions ⟨2, (by simp)⟩).val] = values 2 :=
    (by simpa using (hpositions ⟨2, (by simp)⟩).symm);
  refine ⟨positions ⟨0, (by simp)⟩, positions ⟨1, (by simp)⟩, positions ⟨2, (by simp)⟩,
    positions.strictMono (by simp), positions.strictMono (by simp), ?_, ?_⟩;
  { simpa only [hfirst, hlast] using hlt 1 (by omega) (by omega) };
  { simpa only [hlast, hmiddle] using hlt 2 (by omega) (by omega) } }; {
  rintro ⟨first, middle, last, hfirstMiddle, hmiddleLast, hfirstLast, hlastMiddle⟩;
  let values : ℕ → ℕ := fun label => if label = 1 then word[first.val] else if label = 2 then
    word[last.val] else word[middle.val];
  have hsub : List.Sublist [word[first.val], word[middle.val], word[last.val]] word := (by {
  let positions : Fin 3 → Fin word.length := fun index => if index.val = 0 then first else if
    index.val = 1 then middle else last;
  have hmono : StrictMono positions := (by
    { intro left right hlt; fin_cases left <;> fin_cases right <;> simp_all [positions]; omega });
  apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr;
  refine ⟨OrderEmbedding.ofStrictMono positions hmono, ?_⟩; intro index;
  fin_cases index <;> simp [positions] }); refine ⟨values, ?_, ?_, ?_, (by simp)⟩; {
  intro label hlower hupper; have hcases : label = 1 ∨ label = 2 := (by omega);
  rcases hcases with rfl | rfl <;> simp [values, hfirstLast, hlastMiddle] }; {
  intro label hlower hupper; have hcases : label = 1 ∨ label = 2 ∨ label = 3 := (by omega);
  rcases hcases with rfl | rfl | rfl <;> simp [values] }; { simpa [values] using hsub } } });
  let avoids : List ℕ → Prop := fun word => ¬ ∃ first middle last : Fin word.length, first < middle
    ∧ middle < last ∧ word.getD first.val 0 < word.getD last.val 0 ∧ word.getD last.val 0 <
    word.getD middle.val 0;
  have avoids_iff (word : List ℕ) : avoids word ↔ ¬ Contains [1, 3, 2] [] 3 word := (by {
  have hget (index : Fin word.length) : word.getD index.val 0 = word[index.val] :=
    List.getD_eq_getElem _ _ index.isLt; dsimp only [avoids]; simp only [hget];
  exact not_congr (pattern_indices word).symm });
  let tests : List ℕ → Prop := fun word => ∀ power : Fin 3, avoids (theta^[power.val] word);
  let candidates := (List.permutations (List.range' 1 size)).toFinset.filter tests;
  have hset : ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2] = (candidates : Set (List ℕ)) := (by
    {
  ext word; simp only [ThetaIterateDefs.iterateAvoiders, Set.mem_ofPred_eq, candidates,
              Finset.mem_coe, Finset.mem_filter, List.mem_toFinset, List.mem_permutations];
  refine and_congr_right (fun _ => ?_); constructor;
  { intro horbit power; exact (avoids_iff _).mpr (horbit power.val (by omega)) };
  { intro horbit power hpower; exact (avoids_iff _).mp (horbit ⟨power, (by omega)⟩) } });
  have hfirst : firstMax = ((candidates.filter (fun word => word.getD 0 0 = size)) : Set (List
    ℕ)) := (by {
  ext word; simp only [firstMax, Set.mem_ofPred_eq, hset, Finset.mem_coe, Finset.mem_filter] });
  change firstMax.ncard + 1 = _ ∧ _; rw [hfirst, hset, Set.ncard_coe_finset, Set.ncard_coe_finset];
  change (Finset.filter (fun word => word.getD 0 0 = size) (Finset.filter tests (List.permutations
    (List.range' 1 size)).toFinset)).card + 1 = _ ∧ (Finset.filter tests (List.permutations
    (List.range' 1 size)).toFinset).card = _; simp only [List.filter_toFinset, List.card_toFinset];
  dsimp +zetaDelta only [candidates, tests, avoids];
  interval_cases size <;> simp only [List.range', List.permutations, List.permutationsAux_cons,
    List.permutationsAux_nil] <;> decide }); have hdecomp (size : ℕ) (hsize : 4 ≤ size) :
    let parameters : Set (List ℕ) := {parameter | parameter.Perm (List.range' 1 (size - 2)) ∧ P
      parameter ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2]};
    let firstMax : Set (List ℕ) := {word | word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3,
      2] ∧ word.getD 0 0 = size};
    let nonfinalMax : Set (List ℕ) := {word | word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1,
      3, 2] ∧ word.getD (size - 1) 0 ≠ size}; firstMax = insert (size :: List.range' 2 (size -
      2) ++ [1]) (P '' parameters) ∧ firstMax.ncard = parameters.ncard + 1 ∧ nonfinalMax =
      insert (List.range' 2 (size - 1) ++ [1]) firstMax ∧ nonfinalMax.ncard =
      parameters.ncard + 2 ∧ (5 ≤ size → firstMax.ncard = {word : List ℕ | word ∈
      ThetaIterateDefs.iterateAvoiders (size - 3) 2 [1, 3, 2] ∧ word.getD 0 0 = size - 3}.ncard +
      {parameter : List ℕ | parameter.Perm (List.range' 1 (size - 2)) ∧ parameter.getD 0 0 = size -
      2 ∧ P parameter ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2]}.ncard + 2) ∧
      (ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2]).ncard = (ThetaIterateDefs.iterateAvoiders
      (size - 1) 2 [1, 3, 2]).ncard + firstMax.ncard + 1 := (by {
  classical {
  let parameters : Set (List ℕ) := {parameter | parameter.Perm (List.range' 1 (size - 2)) ∧ P
    parameter ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2]};
  let firstMax : Set (List ℕ) := {word | word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3,
    2] ∧ word.getD 0 0 = size};
  let nonfinalMax : Set (List ℕ) := {word | word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3,
    2] ∧ word.getD (size - 1) 0 ≠ size}; let shift := List.range' 2 (size - 1) ++ [1];
  obtain ⟨hfirstSet, hfirstCount, hnoFinalSet, hnoFinalCount⟩ :=
    ThetaIterateDecomposition.second_layer_decomposition size hsize;
  change firstMax = _ at hfirstSet; change firstMax.ncard = parameters.ncard + 1 at hfirstCount;
  change nonfinalMax = insert shift firstMax at hnoFinalSet;
  change nonfinalMax.ncard = parameters.ncard + 2 at hnoFinalCount;
  have hfinite : parameters.Finite := (by {
  have hpermutations : Set.Finite {parameter : List ℕ | parameter.Perm (List.range' 1 (size - 2))}
    := (by {
  convert (List.permutations (List.range' 1 (size - 2))).finite_toSet using 1; ext parameter;
  exact List.mem_permutations.symm });
  exact hpermutations.subset (fun parameter hparameter => hparameter.1) });
  have hfirstFinite : firstMax.Finite := (by rw [hfirstSet]; exact (hfinite.image P).insert _);
  have parameter_length (parameter : List ℕ) (hparameter : parameter ∈ parameters) :
    parameter.length = size - 2 := (by simpa using hparameter.1.length_eq);
  have htotal : (ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2]).ncard =
    (ThetaIterateDefs.iterateAvoiders (size - 1) 2 [1, 3, 2]).ncard + firstMax.ncard + 1 := (by {
  let finalMaximum : Set (List ℕ) := {word | word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3,
    2] ∧ word.getD (size - 1) 0 = size}; have hpartition : ThetaIterateDefs.iterateAvoiders size 2
                                           [1, 3, 2] = finalMaximum ∪ nonfinalMax := (by {
  ext word; constructor; {
  intro hword; by_cases hfinal : word.getD (size - 1) 0 = size; { exact Or.inl ⟨hword, hfinal⟩ };
  { exact Or.inr ⟨hword, hfinal⟩ } }; { rintro (hword | hword) <;> exact hword.1 } });
  have hdisjoint : Disjoint finalMaximum nonfinalMax :=
    (by apply Set.disjoint_left.mpr; intro word hfinal hnonfinal; exact hnonfinal.2 hfinal.2);
  have hfinalFinite : finalMaximum.Finite := (by {
  have hpermutations : Set.Finite {word : List ℕ | word.Perm (List.range' 1 size)} := (by {
  convert (List.permutations (List.range' 1 size)).finite_toSet using 1; ext word;
  exact List.mem_permutations.symm }); exact hpermutations.subset (fun word hword => hword.1.1) });
  have hnonfinalFinite : nonfinalMax.Finite :=
    (by rw [hnoFinalSet]; exact hfirstFinite.insert shift);
  have hfinalCount := ThetaIterateTailCount.final_tail_count (size - 1) 2;
  rw [show size - 1 + 1 = size by { omega }] at hfinalCount;
  rw [hpartition, Set.ncard_union_eq hdisjoint hfinalFinite hnonfinalFinite];
  change finalMaximum.ncard + nonfinalMax.ncard = _;
  rw [hfinalCount, hnoFinalCount, hfirstCount]; omega });
  refine ⟨hfirstSet, hfirstCount, hnoFinalSet, hnoFinalCount, ?_, htotal⟩; intro hlarge;
  let firstParams : Set (List ℕ) := {parameter | parameter.Perm (List.range' 1 (size - 2)) ∧
    parameter.getD 0 0 = size - 2 ∧ P parameter ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3,
    2]}; let lastParams : Set (List ℕ) := {parameter | parameter.Perm (List.range' 1 (size - 2))
           ∧ parameter.getD (size - 3) 0 = size - 2 ∧ P parameter ∈ ThetaIterateDefs.iterateAvoiders
           size 2 [1, 3, 2]};
  have hpartition : parameters = firstParams ∪ lastParams := (by {
  ext parameter; constructor; {
  intro hparameter; have hlength := parameter_length parameter hparameter;
  have hperm : parameter.Perm (List.range' 1 parameter.length) :=
    (by simpa only [hlength] using hparameter.1);
  have hmember : P parameter ∈ ThetaIterateDefs.iterateAvoiders (parameter.length + 2) 2 [1, 3, 2]
    := (by rw [hlength, show size - 2 + 2 = size by { omega }]; exact hparameter.2);
  have hendpoints := (ThetaIterateEndpoints.parameter_endpoints parameter hperm (by omega)
    hmember).1; rw [hlength, show size - 2 - 1 = size - 3 by { omega }] at hendpoints;
  rcases hendpoints with hfirst | hlast; { exact Or.inl ⟨hparameter.1, hfirst, hparameter.2⟩ };
  { exact Or.inr ⟨hparameter.1, hlast, hparameter.2⟩ } }; {
  intro hparameter; rcases hparameter with hfirst | hlast; { exact ⟨hfirst.1, hfirst.2.2⟩ };
  { exact ⟨hlast.1, hlast.2.2⟩ } } });
  have hdisjoint : Disjoint firstParams lastParams := (by {
  apply Set.disjoint_left.mpr; intro parameter hfirst hlast;
  have hlength : parameter.length = size - 2 := (by simpa using hfirst.1.length_eq);
  have hnodup := hfirst.1.nodup_iff.mpr List.nodup_range';
  have hequal : parameter.getD 0 0 = parameter.getD (size - 3) 0 := hfirst.2.1.trans hlast.2.1.symm;
  rw [List.getD_eq_getElem parameter 0 ((by omega) : 0 < parameter.length), List.getD_eq_getElem
    parameter 0 ((by omega) : size - 3 < parameter.length)] at hequal;
  have := hnodup.getElem_inj_iff.mp hequal; omega });
  have hfirstParametersFinite : firstParams.Finite := hfinite.subset (fun parameter hparameter
    => ⟨hparameter.1, hparameter.2.2⟩);
  have hlastParametersFinite : lastParams.Finite := hfinite.subset (fun parameter hparameter =>
    ⟨hparameter.1, hparameter.2.2⟩);
  have hlastParametersCount := ThetaIterateEndpointCount.last_endpoint_count (size - 3) (by omega);
  rw [show size - 3 + 1 = size - 2 by { omega }, show size - 3 + 3 = size by { omega }]
    at hlastParametersCount;
  change firstMax.ncard = {word : List ℕ | word ∈ ThetaIterateDefs.iterateAvoiders (size - 3) 2
    [1, 3, 2] ∧ word.getD 0 0 = size - 3}.ncard + firstParams.ncard + 2;
  rw [hfirstCount, hpartition, Set.ncard_union_eq hdisjoint hfirstParametersFinite
    hlastParametersFinite]; rw [hlastParametersCount]; omega } }); refine ⟨hdecomp size, ?_⟩;
  { induction size using Nat.strong_induction_on with
    | h size ih => {
  by_cases hsmall : size ≤ 4; { exact hbase size hsize hsmall }; {
  have hlarge : 5 ≤ size := (by omega); have hdata := hdecomp size (by omega);
  have hrecurrence := hdata.2.2.2.2.1 hlarge;
  have hpreviousFirst := (ih (size - 3) (by omega) (by omega)).1;
  have hfamily := (ThetaIterateParametrization.first_endpoint_parametrization (size - 2)
    (by omega)).2; dsimp only at hfamily; rw [show size - 2 + 2 = size by { omega }] at hfamily;
  change (firstMax size).ncard = (firstMax (size - 3)).ncard + {parameter : List ℕ |
    parameter.Perm (List.range' 1 (size - 2)) ∧ parameter.getD 0 0 = size - 2 ∧ P parameter ∈
    ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2]}.ncard + 2 at hrecurrence;
  rw [hfamily] at hrecurrence; dsimp only [firstMax] at hrecurrence;
  have hresidues : size % 3 = 0 ∨ size % 3 = 1 ∨ size % 3 = 2 := (by omega);
  have hmodThree : (size - 3) % 3 = size % 3 := (by omega);
  have hdivThree : size / 3 = (size - 3) / 3 + 1 := (by omega);
  have hfirst : (firstMax size).ncard + 1 = (if size % 3 = 0 then (size / 3) ^ 2 + 2 * (size /
    3) else if size % 3 = 1 then (size / 3) ^ 2 + 2 * (size / 3) + 1 else (size / 3) ^ 2 + 3 * (size
    / 3) + 2) := (by {
  dsimp only [firstMax]; rcases hresidues with hzero | hone | htwo; {
  have hfloor : (2 * (size - 2) + 1) / 3 = 2 * ((size - 3) / 3) + 1 := (by omega);
  simp only [hmodThree, hzero, ite_true] at hpreviousFirst ⊢; rw [hdivThree];
  rw [hfloor] at hrecurrence; nlinarith }; {
  have hfloor : (2 * (size - 2) + 1) / 3 = 2 * ((size - 3) / 3) + 1 := (by omega);
  simp only [hmodThree, hone, Nat.one_ne_zero, ite_false, ite_true] at hpreviousFirst ⊢;
  rw [hdivThree]; rw [hfloor] at hrecurrence; nlinarith }; {
  have hfloor : (2 * (size - 2) + 1) / 3 = 2 * ((size - 3) / 3) + 2 := (by omega);
  simp only [hmodThree, htwo, show (2 : ℕ) ≠ 0 by { decide }, show (2 : ℕ) ≠ 1 by { decide },
    ite_false] at hpreviousFirst ⊢; rw [hdivThree]; rw [hfloor] at hrecurrence; nlinarith } });
  refine ⟨hfirst, ?_⟩; have hpreviousTotal := (ih (size - 1) (by omega) (by omega)).2;
  have htotal := hdata.2.2.2.2.2; change (ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2]).ncard =
                                    (ThetaIterateDefs.iterateAvoiders (size - 1) 2 [1, 3, 2]).ncard
                                    + (firstMax size).ncard + 1 at htotal;
  rw [htotal, hpreviousTotal, Nat.add_assoc, hfirst]; unfold ThetaIterateDefs.quadCount;
  rcases hresidues with hzero | hone | htwo; {
  have hmod : (size - 1) % 3 = 2 := (by omega);
  have hdiv : size / 3 = (size - 1) / 3 + 1 := (by omega);
  simp only [hzero, hmod, show (2 : ℕ) ≠ 0 by { decide }, show (2 : ℕ) ≠ 1 by { decide }, ite_false,
    ite_true]; rw [hdiv];
  have halgebra : (((size - 1) / 3 + 1) ^ 3 + 3 * ((size - 1) / 3 + 1) ^ 2 + 2 * ((size - 1) / 3 +
    1)) = (((size - 1) / 3) ^ 3 + 5 * ((size - 1) / 3) ^ 2 + 7 * ((size - 1) / 3) + 2) + (((size -
    1) / 3 + 1) ^ 2 + 2 * ((size - 1) / 3 + 1)) + 1 := (by ring); omega }; {
  have hmod : (size - 1) % 3 = 0 := (by omega); have hdiv : (size - 1) / 3 = size / 3 := (by omega);
  have hpositive : 1 ≤ (size / 3) ^ 3 + 3 * (size / 3) ^ 2 + 2 * (size / 3) :=
    (by have hquotient : 1 ≤ size / 3 := (by omega); nlinarith);
  simp only [hone, hmod, hdiv, Nat.one_ne_zero, ite_false, ite_true];
  have halgebra : (size / 3) ^ 3 + 4 * (size / 3) ^ 2 + 4 * (size / 3) + 1 = ((size / 3) ^ 3 + 3 *
    (size / 3) ^ 2 + 2 * (size / 3)) + ((size / 3) ^ 2 + 2 * (size / 3) + 1) := (by ring); omega };
  {
  have hmod : (size - 1) % 3 = 1 := (by omega); have hdiv : (size - 1) / 3 = size / 3 := (by omega);
  simp only [htwo, hmod, hdiv, Nat.one_ne_zero, show (2 : ℕ) ≠ 0 by { decide }, show (2 : ℕ) ≠ 1 by
    { decide }, ite_false, ite_true]; ring } } } } }); classical {
  have nonfinal_layers (size : ℕ) (hsize : 4 ≤ size) :
    let C := List.range' 2 (size - 1) ++ [1];
    let D := size :: List.range' 2 (size - 2) ++ [1];
    let E := P (List.range' 1 (size - 2));
    let nonfinal := fun layers => {word : List ℕ | word ∈ ThetaIterateDefs.iterateAvoiders size
      layers [1, 3, 2] ∧ word.getD (size - 1) 0 ≠ size}; nonfinal 3 = {C, D, E} ∧ nonfinal 4 = {D,
      E} ∧ nonfinal 5 = {E} ∧ (∀ layers, 6 ≤ layers → nonfinal layers = ∅) ∧ ∀ layers, 3 ≤ layers →
      (ThetaIterateDefs.iterateAvoiders size layers [1, 3, 2]).ncard =
      (ThetaIterateDefs.iterateAvoiders (size - 1) layers [1, 3, 2]).ncard + (if layers = 3 then 3
      else if layers = 4 then 2 else if layers = 5 then 1 else 0) := (by {
  have inverse_facts (word : List ℕ) (valid : word.Perm (List.range' 1 word.length)) : (∀
    seed, seed.Perm (List.range' 1 seed.length) → theta (B seed) = seed) ∧ (∀ seed, seed.Perm
    (List.range' 1 seed.length) → (B seed).Perm (List.range' 1 seed.length)) ∧ (theta word).Perm
    (List.range' 1 word.length) ∧ B (theta word) = word := (by {
  open ThetaBasicInverseGeneral ThetaBasicInverseBlocks in {
  have cuts (seed : List ℕ) (start : ℕ) (bound : start < seed.length) :
    let finish := nextBoundary (IsLtrMax seed) seed.length start; start < finish ∧ finish ≤
      seed.length ∧ (finish = seed.length ∨ IsLtrMax seed finish) ∧ ∀ index, start < index → index <
      finish → ¬ IsLtrMax seed index := (by {
  simp only [nextBoundary, dif_pos bound];
  let predicate := fun finish => start < finish ∧ finish ≤ seed.length ∧ (finish = seed.length ∨
    IsLtrMax seed finish);
  have exists_cut : ∃ finish, predicate finish := ⟨seed.length, bound, le_refl _, Or.inl rfl⟩;
  have spec := Nat.find_spec exists_cut; refine ⟨spec.1, spec.2.1, spec.2.2, ?_⟩;
  intro index after before record;
  have := Nat.find_min' exists_cut ⟨after, (by omega), Or.inr record⟩; omega });
  have inverse_left (seed : List ℕ) (valid : seed.Perm (List.range' 1 seed.length)) : theta (B seed)
    = seed := (by {
  let records := (List.Ico 0 seed.length).filter (IsLtrMax seed);
  have distinct : seed.Nodup := valid.nodup_iff.mpr List.nodup_range';
  have entry (index : ℕ) (bound : index < seed.length) : seed.getD index 0 ∈ seed :=
    (by rw [List.getD_eq_getElem _ 0 bound]; exact List.getElem_mem bound);
  have leader (index : ℕ) (bound : index < seed.length) (record : IsLtrMax seed index) :
    ThetaFixedDefs.IsLeader (B seed) (seed.getD index 0) := (by {
  have boundary := cuts seed index bound;
  rw [ThetaFixedDefs.IsLeader, cycleFrom_B_record_block seed valid index (nextBoundary (IsLtrMax
    seed) seed.length index) boundary.1 boundary.2.1 record boundary.2.2.2 boundary.2.2.1];
  intro value member; obtain ⟨offset, offset_bound, value_eq⟩ := List.mem_iff_getElem.mp member;
  have offset_limit : index + offset < nextBoundary (IsLtrMax seed) seed.length index := (by {
  have := List.length_take_le (nextBoundary (IsLtrMax seed) seed.length index - index) (seed.drop
    index); omega }); have position_bound : index + offset < seed.length := (by omega);
  have greatest : Nat.findGreatest (IsLtrMax seed) (index + offset) = index :=
    Nat.findGreatest_eq_iff.mpr ⟨(by omega), fun _ => record, fun position after before =>
    boundary.2.2.2 position after (by omega)⟩;
  rw [← value_eq, List.getElem_take, List.getElem_drop];
  simpa only [greatest, List.getD_eq_getElem _ 0 position_bound] using last_record_bounds_prefix
    seed (index + offset) position_bound (index + offset) (le_refl _) });
  have leaders : (List.range' 1 seed.length).filter (fun value => decide (ThetaFixedDefs.IsLeader (B
    seed) value)) = records.map (fun index => seed.getD index 0) := (by {
  apply List.Pairwise.eq_of_mem_iff ((List.pairwise_lt_range' 1 ((by omega) : 0 < (1 : ℕ))).filter
    _); {
  apply List.pairwise_iff_getElem.mpr; intro left right left_bound right_bound ordered;
  have left_record : left < records.length := (by simpa using left_bound);
  have right_record : right < records.length := (by simpa using right_bound);
  simp only [List.getElem_map];
  have indices := List.pairwise_iff_getElem.mp ((List.Ico.pairwise_lt 0 seed.length).filter
    (IsLtrMax seed)) left right left_record right_record ordered;
  exact (decide_eq_true_eq.mp (List.mem_filter.mp (List.getElem_mem right_record)).2) _ indices }; {
  intro value; constructor; {
  intro member; obtain ⟨in_range, is_leader⟩ := List.mem_filter.mp member;
  have in_seed := valid.mem_iff.mpr in_range;
  have record : IsLtrMax seed (seed.idxOf value) := (by {
  by_contra not_record; exact nonrecord_not_B_leader seed valid value in_seed not_record
                          (decide_eq_true_eq.mp is_leader) });
  have bound := List.idxOf_lt_length_of_mem in_seed;
  refine List.mem_map.mpr ⟨seed.idxOf value, List.mem_filter.mpr ⟨List.Ico.mem.mpr ⟨Nat.zero_le _,
    bound⟩, decide_eq_true record⟩, ?_⟩; rw [List.getD_eq_getElem _ 0 bound];
  exact List.getElem_idxOf bound }; {
  intro member; obtain ⟨index, in_records, rfl⟩ := List.mem_map.mp member;
  obtain ⟨in_interval, record⟩ := List.mem_filter.mp in_records;
  have bound := (List.Ico.mem.mp in_interval).2;
  exact List.mem_filter.mpr ⟨valid.mem_iff.mp (entry index bound), decide_eq_true (leader index
    bound (decide_eq_true_eq.mp record))⟩ } } }); unfold theta;
  rw [show (B seed).length = seed.length by { simp }, leaders, List.flatMap_map];
  have cycles : ∀ index ∈ records, ThetaFixedDefs.cycleFrom (B seed) (seed.getD index 0) =
    (seed.drop index).take (nextBoundary (IsLtrMax seed) seed.length index - index) := (by {
  intro index member; obtain ⟨in_interval, record⟩ := List.mem_filter.mp member;
  have boundary := cuts seed index (List.Ico.mem.mp in_interval).2;
  exact cycleFrom_B_record_block seed valid index _ boundary.1 boundary.2.1 (decide_eq_true_eq.mp
    record) boundary.2.2.2 boundary.2.2.1 }); rw [List.flatMap_congr cycles];
  simpa only [records, List.Ico.zero_bot, Nat.zero_le, List.drop_zero] using
    filter_interval_partition seed (IsLtrMax seed) 0 (Nat.zero_le _)
    (by intro _ index impossible; omega) });
  have inverse_valid (seed : List ℕ) (valid : seed.Perm (List.range' 1 seed.length)) : (B seed).Perm
    (List.range' 1 seed.length) := (by {
  have distinct : seed.Nodup := valid.nodup_iff.mpr List.nodup_range';
  have mapped_distinct := distinct.map_on (hat_inj_on seed distinct);
  have subset : (seed.map (hat seed)).toFinset ⊆ seed.toFinset := (by {
  intro value member;
  obtain ⟨predecessor, in_seed, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member);
  have bound := List.idxOf_lt_length_of_mem in_seed; apply List.mem_toFinset.mpr; unfold hat;
  dsimp only; split_ifs with branch;
  { rw [List.getD_eq_getElem _ 0 branch.1]; exact List.getElem_mem branch.1 }; {
  have record_bound : Nat.findGreatest (IsLtrMax seed) (seed.idxOf predecessor) < seed.length :=
    lt_of_le_of_lt (Nat.findGreatest_le _) bound; rw [List.getD_eq_getElem _ 0 record_bound];
  exact List.getElem_mem record_bound } });
  have equal_card : (seed.map (hat seed)).toFinset.card = seed.toFinset.card := (by {
  simp [List.card_toFinset, List.dedup_eq_self.mpr mapped_distinct, List.dedup_eq_self.mpr distinct]
    }); exact ((valid.symm.map _).trans (List.perm_of_nodup_nodup_toFinset_eq mapped_distinct
          distinct (Finset.eq_of_subset_of_card_le subset (by omega)))).trans valid });
  let words := {seed : List ℕ // seed.Perm (List.range' 1 word.length)};
  have finite_words : Set.Finite {seed : List ℕ | seed.Perm (List.range' 1 word.length)} := (by {
  convert (List.permutations (List.range' 1 word.length)).finite_toSet using 1; ext seed;
  exact List.mem_permutations.symm }); have : Finite words := finite_words;
  have valid_word (seed : words) : seed.val.Perm (List.range' 1 seed.val.length) := (by {
  have length_eq : seed.val.length = word.length := (by simpa using seed.property.length_eq);
  simpa only [length_eq] using seed.property });
  let inverse : words → words := fun seed => ⟨B seed.val, (by {
  have length_eq : seed.val.length = word.length := (by simpa using seed.property.length_eq);
  simpa only [length_eq] using inverse_valid seed.val (valid_word seed) })⟩;
  have injective : Function.Injective inverse := (by {
  intro left right equal; have maps_equal : B left.val = B right.val := congrArg Subtype.val equal;
  apply Subtype.ext; rw [← inverse_left left.val (valid_word left), maps_equal, inverse_left
                       right.val (valid_word right)] });
  obtain ⟨seed, equal⟩ := Finite.surjective_of_injective injective (⟨word, valid⟩ : words);
  have canonical : B seed.val = word := congrArg Subtype.val equal;
  have image_eq : theta word = seed.val := (by
    { exact (congrArg theta canonical).symm.trans (inverse_left seed.val (valid_word seed)) });
  exact ⟨inverse_left, inverse_valid, (by rw [image_eq]; exact seed.property),
    (by rw [image_eq]; exact canonical)⟩ } });
  have position (p : List ℕ) (hp : p.Perm (List.range' 1 p.length)) (havoidp : ¬ Contains
    [1, 3, 2] [] 3 p) (havoidθ : ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta p)) (hn : 3 ≤
    p.length) : p.getD 0 0 = p.length ∨ p.getD (p.length - 1) 0 = p.length ∨ p = List.range' 2
    (p.length - 1) ++ [1] := (by {
  have hat_one_block (word : List ℕ) (hmaximum : ∀ value ∈ word, value ≤ word.getD 0 0) (value : ℕ)
    (hvalue : value ∈ word) : hat word value = if word.idxOf value + 1 < word.length then word.getD
    (word.idxOf value + 1) 0 else word.getD 0 0 := (by {
  have hindex : word.idxOf value < word.length := List.idxOf_lt_length_of_mem hvalue;
  have hnonrecord (index : ℕ) (hpositive : 0 < index) (hbound : index < word.length) : ¬ IsLtrMax
    word index := (by {
  intro hrecord; have hlt := hrecord 0 hpositive;
  have hmember : word.getD index 0 ∈ word :=
    (by rw [List.getD_eq_getElem _ 0 hbound]; exact List.getElem_mem hbound);
  have hle := hmaximum _ hmember; omega });
  have hgreatest : Nat.findGreatest (IsLtrMax word) (word.idxOf value) = 0 := (by {
  apply Nat.findGreatest_eq_zero_iff.mpr; intro index hpositive hbound;
  exact hnonrecord index hpositive (by omega) }); unfold hat;
  by_cases hnext : word.idxOf value + 1 < word.length;
  { rw [if_pos ⟨hnext, hnonrecord _ (by omega) hnext⟩, if_pos hnext] };
  { rw [if_neg (fun hcase => hnext hcase.1), if_neg hnext, hgreatest] } }); let n := p.length;
  let q := ThetaFixedDefs.theta p;
  have hθ : q.Perm (List.range' 1 p.length) ∧ B q = p := ⟨(inverse_facts p hp).2.2.1,
    (inverse_facts p hp).2.2.2⟩;
  have hqLen : q.length = n := (by simpa [q, n] using hθ.1.length_eq);
  have hq : q.Perm (List.range' 1 q.length) := (by simpa [hqLen, q, n] using hθ.1);
  have hpB : B q = p := hθ.2; have havoidq : ¬ Contains [1, 3, 2] [] 3 q := havoidθ;
  have havoidB : ¬ Contains [1, 3, 2] [] 3 (B q) := (by rw [hpB]; exact havoidp);
  have hnq : 3 ≤ q.length := (by omega);
  have hnmem : q.length ∈ q := hq.mem_iff.mpr (List.mem_range'.mpr ⟨q.length - 1, (by omega),
    (by omega)⟩); let s := q.idxOf q.length;
  have hslen : s < q.length := List.idxOf_lt_length_of_mem hnmem;
  have hsmax : q.getD s 0 = q.length :=
    (by rw [List.getD_eq_getElem _ 0 hslen]; exact List.getElem_idxOf hslen);
  have hsrec : IsLtrMax q s := (by {
  intro i his; have hi : i < q.length := (by omega);
  have hmem : q.getD i 0 ∈ q := (by rw [List.getD_eq_getElem _ 0 hi]; exact List.getElem_mem hi);
  obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp hmem);
  have hnd : q.Nodup := hq.nodup_iff.mpr List.nodup_range';
  have hneq : q.getD i 0 ≠ q.getD s 0 := (by {
  intro heq;
  have hval : q[i] = q[s] := (by
    { simpa only [← List.getD_eq_getElem _ 0 hi, ← List.getD_eq_getElem _ 0 hslen] using heq });
  have := (hnd.getElem_inj_iff).mp hval; omega }); omega });
  have hnorec (i : ℕ) (hsi : s < i) (hi : i < q.length) : ¬ IsLtrMax q i := (by {
  intro hrec; have hgt := hrec s hsi;
  have hmem : q.getD i 0 ∈ q := (by rw [List.getD_eq_getElem _ 0 hi]; exact List.getElem_mem hi);
  obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp hmem); omega });
  have hnd : q.Nodup := hq.nodup_iff.mpr List.nodup_range';
  have hidxlast : q.idxOf (q.getD (q.length - 1) 0) = q.length - 1 := (by {
  rw [List.getD_eq_getElem _ 0 (by omega)];
  simpa using List.get_idxOf hnd ⟨q.length - 1, (by omega)⟩ });
  have hfinal : hat q (q.getD (q.length - 1) 0) = q.getD s 0 := (by {
  unfold hat; rw [hidxlast, if_neg (by intro hh; omega)]; congr 1;
  exact Nat.findGreatest_eq_iff.mpr ⟨(by omega), fun _ => hsrec, fun j hsj hj => hnorec j hsj
    (by omega)⟩ }); let t := q.getD (q.length - 1) 0; have htmem : t ∈ q := (by {
  dsimp [t]; rw [List.getD_eq_getElem _ 0 ((by omega) : q.length - 1 < q.length)];
  exact List.getElem_mem ((by omega) : q.length - 1 < q.length) });
  have htpos : 0 < t := (by obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp htmem); omega);
  have htbound : t ≤ q.length :=
    (by obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp htmem); omega);
  have hBget (x : ℕ) (hx0 : 0 < x) (hxn : x ≤ q.length) : (B q).getD (x - 1) 0 = hat q x := (by {
  have hindex : x - 1 < q.length := (by omega);
  rw [List.getD_eq_getElem _ 0 (by simpa using hindex)];
  simp [List.getElem_range', Nat.add_sub_of_le hx0] });
  have hhat_t : hat q t = q.length := (by simpa [t] using hfinal.trans hsmax);
  by_cases htone : t = 1; {
  left; have hBfirst : (B q).getD 0 0 = q.length :=
          (by simpa [htone] using (hBget t htpos htbound).trans hhat_t); rw [← hpB];
  simpa only [List.length_map, List.length_range', hqLen] using hBfirst };
  have httwo : 1 < t := (by omega); by_cases hslast : s = q.length - 1; {
  right; left; have htq : t = q.length := (by dsimp [t]; rw [← hslast]; exact hsmax);
  have hhatn : hat q q.length = q.length := (by simpa [htq] using hhat_t);
  have hBlast : (B q).getD (q.length - 1) 0 = q.length :=
    (by exact (hBget q.length (by omega) (le_refl _)).trans hhatn); rw [hpB] at hBlast;
  simpa only [hqLen] using hBlast }; have hs0 : s = 0 := (by {
  by_contra hsne; have htail : s + 1 < q.length := (by omega);
  have hpre := final_block_predecessor_one q hq havoidq havoidB s (by omega) htail hsmax;
  exact htone (by simpa [t] using hpre) });
  have hfirst : q.getD 0 0 = q.length := (by simpa [hs0] using hsmax);
  have hsecond : q.getD 1 0 = 1 := one_block_second_one q hq havoidq havoidB hnq hfirst httwo;
  let r := q.drop 1; have hcons : q = q.length :: r := (by {
  have hzero : q[0] = q.length :=
    (by simpa only [List.getD_eq_getElem _ 0 ((by omega) : 0 < q.length)] using hfirst);
  simpa only [List.drop_zero, Nat.zero_add, hzero, r] using (List.cons_getElem_drop_succ (l := q) (n
    := 0) (h := (by omega))).symm }); have hrperm : r.Perm (List.range' 1 (q.length - 1)) := (by {
  apply List.Perm.cons_inv (a := q.length); rw [← hcons];
  have hrange : List.range' 1 q.length = List.range' 1 (q.length - 1) ++ [q.length] := (by {
  simpa only [show q.length - 1 + 1 = q.length by { omega }, show 1 + (q.length - 1) = q.length by
    { omega }] using (List.range'_1_concat (s := 1) (n := q.length - 1)) });
  exact hq.trans (hrange ▸ List.perm_append_comm) }); have hrpair : r.Pairwise (· < ·) := (by {
  apply List.pairwise_iff_getElem.mpr; intro i j hi hj hij;
  have hil : i + 1 < q.length := (by simp [r] at hi; omega);
  have hjl : j + 1 < q.length := (by simp [r] at hj; omega); by_cases hi0 : i = 0; {
  subst i; have positive : 1 ≤ r[j] := (by {
  obtain ⟨offset, _, value⟩ := List.mem_range'.mp (hrperm.mem_iff.mp (List.getElem_mem hj));
  omega }); have first_min : r[0] = 1 := (by {
  simpa only [r, List.getElem_drop, Nat.add_zero, List.getD_eq_getElem _ 0 ((by omega) : 1 <
    q.length)] using hsecond }); have distinct : r[j] ≠ r[0] := (by {
  intro equal; have := ((hrperm.nodup_iff.mpr List.nodup_range').getElem_inj_iff).mp equal;
  omega }); omega }; {
  have increasing := suffix_after_one_increasing q hq havoidq 1 (i + 1) (j + 1) (by omega)
    (by omega) hjl hsecond; simpa only [r, List.getElem_drop, Nat.add_comm, List.getD_eq_getElem _ 0
                              hil, List.getD_eq_getElem _ 0 hjl] using increasing } });
  have hr : r = List.range' 1 (q.length - 1) := List.Pairwise.eq_of_mem_iff hrpair
    (List.pairwise_lt_range' 1 (by omega)) (fun _ => hrperm.mem_iff);
  have hmaxq : ∀ y ∈ q, y ≤ q.getD 0 0 :=
    (by intro y hy; obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp hy); omega);
  have hqentry (x : ℕ) (hx0 : 0 < x) (hxn : x < q.length) : q.getD x 0 = x := (by {
  have heq : x = (x - 1) + 1 := (by omega); rw [hcons, hr]; nth_rw 1 [heq];
  have hrange : x - 1 < (List.range' 1 (q.length - 1)).length := (by simp; omega);
  rw [List.getD_cons_succ]; rw [List.getD_eq_getElem _ 0 hrange]; simp [List.getElem_range'];
  omega }); have hhat_low (x : ℕ) (hx0 : 0 < x) (hxn : x < q.length) : hat q x = x + 1 := (by {
  have hidx : q.idxOf x = x := (by {
  have hget : q.getD x 0 = x := hqentry x hx0 hxn; rw [List.getD_eq_getElem _ 0 hxn] at hget;
  simpa [hget] using (List.get_idxOf hnd ⟨x, hxn⟩) });
  have hxmem : x ∈ q := hq.mem_iff.mpr (List.mem_range'.mpr ⟨x - 1, (by omega), (by omega)⟩);
  rw [hat_one_block q hmaxq x hxmem, hidx]; by_cases hnext : x + 1 < q.length;
  { rw [if_pos hnext, hqentry (x + 1) (by omega) hnext] };
  { have hlast : x + 1 = q.length := (by omega); rw [if_neg hnext, hfirst]; omega } });
  have hhat_max : hat q q.length = 1 := (by {
  have hidx : q.idxOf q.length = 0 := hs0;
  rw [hat_one_block q hmaxq q.length hnmem, hidx, if_pos (by omega)]; exact hsecond });
  have hC : B q = List.range' 2 (q.length - 1) ++ [1] := (by {
  apply List.ext_getElem (by simp; omega); intro index left_bound right_bound;
  have bound : index < q.length := (by simpa using left_bound);
  simp only [List.getElem_map, List.getElem_range'_1]; by_cases last : index = q.length - 1; {
  subst index; simpa only [show 1 + (q.length - 1) = q.length by { omega }, List.getElem_append,
                 List.length_range', dif_neg (Nat.lt_irrefl (q.length - 1)), Nat.sub_self,
                 List.getElem_cons_zero] using hhat_max }; {
  have inner : index < q.length - 1 := (by omega);
  simpa only [List.getElem_append, List.length_range', dif_pos inner, List.getElem_range'_1, show 1
    + index = index + 1 by { omega }, show 2 + index = index + 1 + 1 by { omega }] using hhat_low
    (index + 1) (by omega) (by omega) } }); right; right;
  simpa [hqLen, n] using hpB.symm.trans hC }); classical {
  let C := List.range' 2 (size - 1) ++ [1]; let D := size :: List.range' 2 (size - 2) ++ [1];
  let E := P (List.range' 1 (size - 2));
  let nonfinal := fun layers => {word : List ℕ | word ∈ ThetaIterateDefs.iterateAvoiders size layers
    [1, 3, 2] ∧ word.getD (size - 1) 0 ≠ size};
  have lower (word : List ℕ) (high low : ℕ) (hle : low ≤ high) (hword : word ∈
    ThetaIterateDefs.iterateAvoiders size high [1, 3, 2]) : word ∈ ThetaIterateDefs.iterateAvoiders
    size low [1, 3, 2] := ⟨hword.1, fun power hpower => hword.2 power (by omega)⟩;
  have hchain := ThetaIterateExceptional.cyclic_last_endpoint size (by omega);
  obtain ⟨hED, hE5, hnE6, hD4, hnD5, hC3, hnC4⟩ := hchain.2.2.2.2 hsize; change theta E = D at hED;
  change E ∈ ThetaIterateDefs.iterateAvoiders size 5 [1, 3, 2] at hE5;
  change E ∉ ThetaIterateDefs.iterateAvoiders size 6 [1, 3, 2] at hnE6;
  change D ∈ ThetaIterateDefs.iterateAvoiders size 4 [1, 3, 2] at hD4;
  change D ∉ ThetaIterateDefs.iterateAvoiders size 5 [1, 3, 2] at hnD5;
  change C ∈ ThetaIterateDefs.iterateAvoiders size 3 [1, 3, 2] at hC3;
  change C ∉ ThetaIterateDefs.iterateAvoiders size 4 [1, 3, 2] at hnC4;
  have hCfirst : C.getD 0 0 = 2 := (by {
  change (List.range' 2 (size - 1) ++ [1]).getD 0 0 = 2;
  rw [List.getD_append _ _ _ _ (by simp; omega)]; rw [List.getD_eq_getElem _ 0 (by simp; omega)];
  simp }); have hDfirst : D.getD 0 0 = size := (by simp [D]);
  have hClast : C.getD (size - 1) 0 = 1 := (by simp [C]);
  have hDlast : D.getD (size - 1) 0 = 1 :=
    (by simp [D, show size - 1 = (size - 2) + 1 by { omega }]);
  have hEimages := (ThetaIterateCycleReduction.P_cycle_reduction (List.range' 1 (size - 2))
    (by simp) (by simp; omega)).2.2.2; have hElast : E.getD (size - 1) 0 = 2 := (by {
  have hfirst : (List.range' 1 (size - 2)).getD 0 0 = 1 :=
    (by rw [List.getD_eq_getElem _ 0 (by simp; omega)]; simp);
  simpa only [List.length_range', show size - 2 + 1 = size - 1 by { omega }, hfirst] using
    hEimages.2.1 }); have hCnon : C.getD (size - 1) 0 ≠ size := (by omega);
  have hDnon : D.getD (size - 1) 0 ≠ size := (by omega);
  have hEnon : E.getD (size - 1) 0 ≠ size := (by omega);
  have hCD : C ≠ D :=
    (by intro heq; have := congrArg (fun word : List ℕ => word.getD 0 0) heq; omega);
  have hCE : C ≠ E :=
    (by intro heq; have := congrArg (fun word : List ℕ => word.getD (size - 1) 0) heq; omega);
  have hDE : D ≠ E :=
    (by intro heq; have := congrArg (fun word : List ℕ => word.getD (size - 1) 0) heq; omega);
  have reconstruct (word : List ℕ) (hword : word ∈ nonfinal 3) : word = C ∨ word = D ∨ word = E :=
    (by {
  have hsecond := lower word 3 2 (by omega) hword.1;
  have hdecomp := ThetaIterateDecomposition.second_layer_decomposition size hsize;
  have hnon : word ∈ {word : List ℕ | word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2] ∧
    word.getD (size - 1) 0 ≠ size} := ⟨hsecond, hword.2⟩; rw [hdecomp.2.2.1, hdecomp.1] at hnon;
  rcases Set.mem_insert_iff.mp hnon with hC | hnon; { exact Or.inl hC };
  rcases Set.mem_insert_iff.mp hnon with hD | ⟨parameter, hparameter, heq⟩;
  { exact Or.inr (Or.inl hD) }; right; right;
  have hlen : parameter.length = size - 2 := (by simpa using hparameter.1.length_eq);
  have hperm : parameter.Perm (List.range' 1 parameter.length) :=
    (by simpa only [hlen] using hparameter.1);
  have hreduce := ThetaIterateCycleReduction.P_cycle_reduction parameter hperm (by omega);
  let inner := theta parameter;
  have hinnerPerm : inner.Perm (List.range' 1 (size - 2)) :=
    (by simpa only [hlen] using (inverse_facts parameter hperm).2.2.1);
  have hinnerLen : inner.length = size - 2 := (by simpa using hinnerPerm.length_eq);
  let second := inner.map (· + 1) ++ [size, 1];
  have hsecondEq : theta (theta word) = second := (by
    { rw [← heq, hreduce.2.1]; simp only [hlen, show size - 2 + 2 = size by { omega }]; rfl });
  have hwordPerm : word.Perm (List.range' 1 word.length) := (by {
  have hlength : word.length = size := (by simpa using hword.1.1.length_eq);
  simpa only [hlength] using hword.1.1 });
  have hθperm := (inverse_facts word hwordPerm).2.2.1;
  have hθlen : (theta word).length = word.length := (by simpa using hθperm.length_eq);
  have hθperm' : (theta word).Perm (List.range' 1 (theta word).length) :=
    (by simpa only [hθlen] using hθperm);
  have hsecondPerm := (inverse_facts (theta word) hθperm').2.2.1;
  have hsecondLen : second.length = size := (by simp [second, hinnerLen]; omega);
  have hsecondPerm' : second.Perm (List.range' 1 second.length) := (by {
  have hlength : (theta (theta word)).length = (theta word).length :=
    (by simpa using hsecondPerm.length_eq); rw [← hsecondEq, hlength]; exact hsecondPerm });
  have havoidSecond : ¬ Contains [1, 3, 2] [] 3 second := (by
    { have := hword.1.2 2 (by omega); simpa [Function.iterate_succ_apply, hsecondEq] using this });
  have havoidNext : ¬ Contains [1, 3, 2] [] 3 (theta second) := (by
    { have := hword.1.2 3 (by omega); simpa [Function.iterate_succ_apply, hsecondEq] using this });
  have hfirstBound : second.getD 0 0 < size := (by {
  have hzero : 0 < inner.length := (by omega); have hmember := List.getElem_mem hzero;
  have hbound := List.mem_range'.mp (hinnerPerm.mem_iff.mp hmember);
  rw [List.getD_append _ _ _ _ (by simp only [List.length_map]; omega)];
  rw [List.getD_eq_getElem _ 0 (by simp only [List.length_map]; omega)];
  simp only [List.getElem_map]; obtain ⟨index, hindex, hvalue⟩ := hbound; omega });
  have hlast : second.getD (size - 1) 0 = 1 :=
    (by simp [second, hinnerLen, show size - 1 = (size - 2) + 1 by { omega }]);
  have hshape := position second hsecondPerm' havoidSecond havoidNext (by omega);
  rcases hshape with hfirst | hfinal | hshift; { rw [hsecondLen] at hfirst; omega };
  { rw [hsecondLen] at hfinal; omega }; {
  have hmap : inner.map (· + 1) = List.range' 2 (size - 2) := (by {
  rw [hsecondLen] at hshift;
  have hrange : List.range' 2 (size - 1) = List.range' 2 (size - 2) ++ [size] := (by {
  simpa only [show size - 2 + 1 = size - 1 by { omega }, show 2 + (size - 2) = size by { omega }]
    using (List.range'_1_concat (s := 2) (n := size - 2)) });
  rw [hrange, List.append_assoc] at hshift; exact List.append_cancel_right hshift });
  have hinner : inner = List.range' 1 (size - 2) := (by {
  apply List.ext_getElem (by simp [hinnerLen]); intro index hindex hother;
  have hvalues := congrArg (fun word : List ℕ => word[index]?) hmap;
  have hbound : index < size - 2 := (by omega); simp [hindex, hbound] at hvalues;
  simp only [List.getElem_range'_1]; omega });
  have fixed_identity (dimension : ℕ) : theta (List.range' 1 dimension) = List.range' 1 dimension :=
    (by {
  { induction dimension with
    | zero => { rfl }
    | succ dimension ih => {
  have hrange : List.range' 1 (dimension + 1) = List.range' 1 dimension ++ [dimension + 1] := (by
    { simpa [Nat.add_comm] using (List.range'_append_1 (s := 1) (m := dimension) (n := 1)).symm });
  rw [hrange];
  have happend := ThetaIterateTail.theta_append_max (List.range' 1 dimension) (by simp);
  simpa only [List.length_range', ih] using happend } } });
  have hinverse := (inverse_facts parameter hperm).2.2.2;
  have hidPerm : (List.range' 1 (size - 2)).Perm (List.range' 1 (List.range' 1 (size - 2)).length)
    := (by simp);
  have hinverseId := (inverse_facts (List.range' 1 (size - 2)) hidPerm).2.2.2;
  rw [fixed_identity] at hinverseId; change theta parameter = List.range' 1 (size - 2) at hinner;
  rw [hinner, hinverseId] at hinverse; exact heq.symm.trans (congrArg P hinverse.symm) } });
  have hthree : nonfinal 3 = {C, D, E} := (by {
  ext word; constructor;
  { intro hword; rcases reconstruct word hword with rfl | rfl | rfl <;> simp }; {
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rintro (rfl | rfl | rfl);
  { exact ⟨hC3, hCnon⟩ }; { exact ⟨lower D 4 3 (by omega) hD4, hDnon⟩ };
  { exact ⟨lower E 5 3 (by omega) hE5, hEnon⟩ } } }); have hfour : nonfinal 4 = {D, E} := (by {
  ext word; constructor; {
  intro hword;
  rcases reconstruct word ⟨lower word 4 3 (by omega) hword.1, hword.2⟩ with rfl | rfl | rfl;
  { exact False.elim (hnC4 hword.1) }; { simp }; { simp } }; {
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rintro (rfl | rfl); { exact ⟨hD4, hDnon⟩ };
  { exact ⟨lower E 5 4 (by omega) hE5, hEnon⟩ } } }); have hfive : nonfinal 5 = {E} := (by {
  ext word; constructor; {
  intro hword;
  rcases reconstruct word ⟨lower word 5 3 (by omega) hword.1, hword.2⟩ with rfl | rfl | rfl;
  { exact False.elim (hnC4 (lower C 5 4 (by omega) hword.1)) }; { exact False.elim (hnD5 hword.1) };
  { rfl } }; { rintro rfl; exact ⟨hE5, hEnon⟩ } });
  have hsix (layers : ℕ) (hlayers : 6 ≤ layers) : nonfinal layers = ∅ := (by {
  apply Set.eq_empty_iff_forall_notMem.mpr; intro word hword;
  rcases reconstruct word ⟨lower word layers 3 (by omega) hword.1, hword.2⟩ with rfl | rfl | rfl;
  { exact hnC4 (lower C layers 4 (by omega) hword.1) };
  { exact hnD5 (lower D layers 5 (by omega) hword.1) };
  { exact hnE6 (lower E layers 6 hlayers hword.1) } }); refine ⟨hthree, hfour, hfive, hsix, ?_⟩;
  intro layers hlayers; let final := {word : List ℕ | word ∈ ThetaIterateDefs.iterateAvoiders size
                          layers [1, 3, 2] ∧ word.getD (size - 1) 0 = size};
  have hpartition : ThetaIterateDefs.iterateAvoiders size layers [1, 3, 2] = final ∪ nonfinal layers
    := (by {
  ext word; constructor; {
  intro hword; by_cases hlast : word.getD (size - 1) 0 = size; { exact Or.inl ⟨hword, hlast⟩ };
  { exact Or.inr ⟨hword, hlast⟩ } }; { rintro (hword | hword) <;> exact hword.1 } });
  have hdisjoint : Disjoint final (nonfinal layers) :=
    (by apply Set.disjoint_left.mpr; intro word hfinal hnonfinal; exact hnonfinal.2 hfinal.2);
  have hfinite : Set.Finite {word : List ℕ | word.Perm (List.range' 1 size)} := (by {
  convert (List.permutations (List.range' 1 size)).finite_toSet using 1; ext word;
  exact List.mem_permutations.symm });
  have hfinalFinite : final.Finite := hfinite.subset (fun word hword => hword.1.1);
  have hnonfinalFinite : (nonfinal layers).Finite := hfinite.subset (fun word hword => hword.1.1);
  have hfinalCount := ThetaIterateTailCount.final_tail_count (size - 1) layers;
  rw [show size - 1 + 1 = size by { omega }] at hfinalCount;
  rw [hpartition, Set.ncard_union_eq hdisjoint hfinalFinite hnonfinalFinite];
  change final.ncard + (nonfinal layers).ncard = _; rw [hfinalCount]; congr 1;
  by_cases h3 : layers = 3; { simp [h3, hthree, Set.ncard_insert_of_notMem, hCD, hCE, hDE] };
  by_cases h4 : layers = 4; { simp [h4, hfour, Set.ncard_insert_of_notMem, hDE] };
  by_cases h5 : layers = 5; { simp [h5, hfive] };
  { simp [h3, h4, h5, hsix layers (by omega)] } } });
  let seeds : Finset (List ℕ) := {[1, 2, 3], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]};
  have avoids_of_check (word : List ℕ) (hcheck : ¬ ∃ first middle last : Fin word.length, first <
    middle ∧ middle < last ∧ word.getD first.val 0 < word.getD last.val 0 ∧ word.getD last.val 0 <
    word.getD middle.val 0) : ¬ Contains [1, 3, 2] [] 3 word := (by {
  rintro ⟨values, hlt, _, hsub, _⟩; change List.Sublist [values 1, values 3, values 2] word at hsub;
  obtain ⟨positions, hpositions⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub;
  have hfirst : word.getD (positions ⟨0, (by simp)⟩).val 0 = values 1 := (by {
  rw [List.getD_eq_getElem _ 0 (positions ⟨0, (by simp)⟩).isLt];
  simpa using (hpositions ⟨0, (by simp)⟩).symm });
  have hmiddle : word.getD (positions ⟨1, (by simp)⟩).val 0 = values 3 := (by {
  rw [List.getD_eq_getElem _ 0 (positions ⟨1, (by simp)⟩).isLt];
  simpa using (hpositions ⟨1, (by simp)⟩).symm });
  have hlast : word.getD (positions ⟨2, (by simp)⟩).val 0 = values 2 := (by {
  rw [List.getD_eq_getElem _ 0 (positions ⟨2, (by simp)⟩).isLt];
  simpa using (hpositions ⟨2, (by simp)⟩).symm }); apply hcheck;
  refine ⟨positions ⟨0, (by simp)⟩, positions ⟨1, (by simp)⟩, positions ⟨2, (by simp)⟩,
    positions.strictMono (by simp), positions.strictMono (by simp), ?_, ?_⟩;
  { simpa only [hfirst, hlast] using hlt 1 (by omega) (by omega) };
  { simpa only [hlast, hmiddle] using hlt 2 (by omega) (by omega) } });
  have hseedChecks : ∀ word ∈ seeds, word.Perm (List.range' 1 3) ∧ (¬ ∃ first middle last : Fin
    word.length, first < middle ∧ middle < last ∧ word.getD first.val 0 < word.getD last.val 0 ∧
    word.getD last.val 0 < word.getD middle.val 0) ∧ theta word ∈ seeds := (by decide);
  have seed_orbit (word : List ℕ) (hword : word ∈ seeds) (power : ℕ) : theta^[power] word ∈ seeds :=
    (by {
  { induction power with
    | zero => { exact hword }
    | succ power ih => { rw [Function.iterate_succ_apply']; exact (hseedChecks _ ih).2.2 } } });
  have hbase (layers : ℕ) : ThetaIterateDefs.iterateAvoiders 3 layers [1, 3, 2] = (seeds : Set (List
    ℕ)) := (by {
  ext word; constructor; {
  intro hword; have hcoverage : ∀ candidate ∈ (List.range' 1 3).permutations, candidate ∈ seeds ∨
                 candidate = [1, 3, 2] := (by {
  simp only [List.range', List.permutations, List.permutationsAux_cons, List.permutationsAux_nil];
  decide }); rcases hcoverage word (List.mem_permutations.mpr hword.1) with hseed | rfl;
  { exact hseed }; {
  have hbad : Contains [1, 3, 2] [] 3 [1, 3, 2] := (by {
  refine ⟨id, ?_, ?_, ?_, (by simp)⟩; { intro index hlower hupper; simp };
  { intro index hlower hupper; interval_cases index <;> decide }; { simp } });
  exact False.elim (hword.2 0 (by omega) hbad) } }; {
  intro hword; refine ⟨(hseedChecks word hword).1, ?_⟩; intro power _;
  exact avoids_of_check _ (hseedChecks _ (seed_orbit word hword power)).2.1 } });
  have append_max_132_iff (dimension : ℕ) (word : List ℕ) (hperm : word.Perm (List.range' 1
    dimension)) : (¬ Contains [1, 3, 2] [] 3 (word ++ [dimension + 1])) ↔ ¬ Contains [1, 3, 2] [] 3
    word := (by {
  rw [ThetaIterateScan.avoids132_append_iff]; constructor; { exact And.left }; {
  intro havoid; refine ⟨havoid, ?_⟩; intro first middle _ hmiddle hcross;
  have hmember : word.getD middle 0 ∈ word :=
    (by rw [List.getD_eq_getElem _ 0 hmiddle]; exact List.getElem_mem hmiddle);
  obtain ⟨index, hindex, hvalue⟩ := List.mem_range'.mp (hperm.mem_iff.mp hmember); omega } });
  have stable_family (extra : ℕ) :
    let family := seeds.image (fun word => word ++ List.range' 4 extra); family.card = 5 ∧ ∀ word ∈
      family, word.Perm (List.range' 1 (extra + 3)) ∧ ¬ Contains [1, 3, 2] [] 3 word ∧ theta word ∈
      family := (by {
  { induction extra with
    | zero => {
  simp only [List.range'_zero, List.append_nil]; refine ⟨(by decide), ?_⟩; intro word hword;
  exact ⟨(hseedChecks word hword).1, avoids_of_check word (hseedChecks word hword).2.1, (hseedChecks
    word hword).2.2⟩ }
    | succ extra ih => {
  let previous := seeds.image (fun word => word ++ List.range' 4 extra);
  let extend := fun word : List ℕ => word ++ [extra + 4];
  have hrange : List.range' 4 (extra + 1) = List.range' 4 extra ++ [extra + 4] :=
    (by simpa [Nat.add_comm] using (List.range'_1_concat (s := 4) (n := extra)));
  have hfamily : seeds.image (fun word => word ++ List.range' 4 (extra + 1)) = previous.image extend
    := (by
    { rw [Finset.image_image]; congr 1; funext word; simp [hrange, extend, List.append_assoc] });
  change (seeds.image (fun word => word ++ List.range' 4 (extra + 1))).card = 5 ∧ _; rw [hfamily];
  have hinjective : Function.Injective extend :=
    (by intro left right hequal; exact List.append_cancel_right hequal);
  refine ⟨(Finset.card_image_of_injective previous hinjective).trans ih.1, ?_⟩; intro word hword;
  obtain ⟨stem, hstem, rfl⟩ := Finset.mem_image.mp hword;
  obtain ⟨hperm, havoid, hnext⟩ := ih.2 stem hstem;
  have hlength : stem.length = extra + 3 := (by simpa using hperm.length_eq);
  have hperm' : stem.Perm (List.range' 1 stem.length) := (by simpa only [hlength] using hperm);
  have hrange' : List.range' 1 (extra + 1 + 3) = List.range' 1 (extra + 3) ++ [extra + 4] := (by {
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (List.range'_1_concat (s := 1) (n :=
    extra + 3)) }); refine ⟨?_, ?_, ?_⟩;
  { change (stem ++ [extra + 4]).Perm _; rw [hrange']; exact hperm.append (List.Perm.refl _) };
  { exact (append_max_132_iff (extra + 3) stem hperm).mpr havoid }; {
  have hθextend : theta (extend stem) = extend (theta stem) := (by {
  simpa only [hlength, show extra + 3 + 1 = extra + 4 by { omega }] using
    ThetaIterateTail.theta_append_max stem hperm' }); rw [hθextend];
  exact Finset.mem_image.mpr ⟨theta stem, hnext, rfl⟩ } } } });
  have counts (size : ℕ) (hsize : 3 ≤ size) : (ThetaIterateDefs.iterateAvoiders size 3 [1, 3,
    2]).ncard = 3 * size - 4 ∧ (ThetaIterateDefs.iterateAvoiders size 4 [1, 3, 2]).ncard = 2 * size
    - 1 ∧ (ThetaIterateDefs.iterateAvoiders size 5 [1, 3, 2]).ncard = size + 2 ∧
    (ThetaIterateDefs.iterateAvoiders size 6 [1, 3, 2]).ncard = 5 := (by {
  { induction size using Nat.strong_induction_on with
    | h size ih => {
  by_cases hbaseSize : size = 3;
  { subst size; have hcard : seeds.card = 5 := (by decide); simp [hbase, hcard] }; {
  have hlarge : 4 ≤ size := (by omega); have hprevious := ih (size - 1) (by omega) (by omega);
  have hrec := (nonfinal_layers size hlarge).2.2.2.2; have h3 := hrec 3 (by omega);
  have h4 := hrec 4 (by omega); have h5 := hrec 5 (by omega); have h6 := hrec 6 (by omega);
  norm_num at h3 h4 h5 h6; omega } } } }); constructor;
  { intro size hsize; exact (cubic_forms size hsize).2.2 }; {
  intro size hsize; have hcounts := counts size hsize;
  refine ⟨hcounts.1, hcounts.2.1, hcounts.2.2.1, ?_⟩; intro layers hlayers;
  have finite_avoiders (layers : ℕ) : (ThetaIterateDefs.iterateAvoiders size layers [1, 3,
    2]).Finite := (by {
  have hpermutations : Set.Finite {word : List ℕ | word.Perm (List.range' 1 size)} := (by {
  convert (List.permutations (List.range' 1 size)).finite_toSet using 1; ext word;
  exact List.mem_permutations.symm }); exact hpermutations.subset (fun word hword => hword.1) });
  have hsubset : ThetaIterateDefs.iterateAvoiders size layers [1, 3, 2] ⊆
    ThetaIterateDefs.iterateAvoiders size 6 [1, 3, 2] :=
    (by intro word hword; exact ⟨hword.1, fun power hpower => hword.2 power (by omega)⟩);
  have hupper := Set.ncard_le_ncard hsubset (finite_avoiders 6); rw [hcounts.2.2.2] at hupper;
  let family := seeds.image (fun word => word ++ List.range' 4 (size - 3));
  have hstable := stable_family (size - 3); rw [show size - 3 + 3 = size by { omega }] at hstable;
  have orbit_tail (seed : List ℕ) (hseed : seed ∈ seeds) (extra : ℕ) : theta (seed ++ List.range' 4
    extra) = theta seed ++ List.range' 4 extra := (by {
  { induction extra with
    | zero => { simp }
    | succ extra ih => {
  have hrange : List.range' 4 (extra + 1) = List.range' 4 extra ++ [extra + 4] := (by {
  simpa [Nat.add_comm] using (List.range'_1_concat (s := 4) (n := extra)) });
  rw [hrange, ← List.append_assoc, ← List.append_assoc];
  have hperm := (stable_family extra).2 (seed ++ List.range' 4 extra) (Finset.mem_image.mpr ⟨seed,
    hseed, rfl⟩); have hlength : (seed ++ List.range' 4 extra).length = extra + 3 :=
                    (by simpa using hperm.1.length_eq);
  have happend := ThetaIterateTail.theta_append_max (seed ++ List.range' 4 extra)
    (by simpa only [hlength] using hperm.1);
  simpa only [hlength, show extra + 3 + 1 = extra + 4 by { omega }, ih] using happend } } });
  have hseedPreimages : ∀ word ∈ seeds, ∃ seed ∈ seeds, theta seed = word := (by decide);
  have hinvariant : theta '' (family : Set (List ℕ)) = (family : Set (List ℕ)) := (by {
  ext word; constructor; { rintro ⟨seed, hseed, rfl⟩; exact (hstable.2 seed hseed).2.2 }; {
  intro hword; obtain ⟨seed, hseed, rfl⟩ := Finset.mem_image.mp hword;
  obtain ⟨preimage, hpreimage, hθ⟩ := hseedPreimages seed hseed;
  refine ⟨preimage ++ List.range' 4 (size - 3), Finset.mem_image.mpr ⟨preimage, hpreimage, rfl⟩,
    ?_⟩; rw [orbit_tail preimage hpreimage, hθ] } });
  have hfamilySubset : (family : Set (List ℕ)) ⊆ ThetaIterateDefs.iterateAvoiders size layers [1, 3,
    2] := (by {
  intro word hword; have horbit (power : ℕ) : theta^[power] word ∈ family := (by {
  { induction power with
    | zero => { exact hword }
    | succ power ih => {
  rw [Function.iterate_succ_apply']; have himage : theta (theta^[power] word) ∈ theta '' (family :
                                       Set (List ℕ)) := ⟨theta^[power] word, ih, rfl⟩;
  rw [hinvariant] at himage; exact himage } } }); refine ⟨(hstable.2 word hword).1, ?_⟩;
  intro power _; exact (hstable.2 _ (horbit power)).2.1 });
  have hlower := Set.ncard_le_ncard hfamilySubset (finite_avoiders layers);
  rw [Set.ncard_coe_finset, hstable.1] at hlower; omega } } } })
end D5.S3.Combinatorics.FundamentalBijection.ThetaIterate
