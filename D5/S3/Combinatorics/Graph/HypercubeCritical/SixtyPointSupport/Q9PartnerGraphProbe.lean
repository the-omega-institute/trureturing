/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9PartnerGraphProbe
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9PartnerGraphProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A vertex at distance seven agrees with the root in two unused coordinate directions. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9FourthLeafSignProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

/-! Identify the graph of distance-seven partners on the six unused directions. -/

set_option autoImplicit false

noncomputable section

open SimpleGraph
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q flip IsBalanced)
attribute [local instance] Classical.propDecidable

open private directions mem_directions regular_directions directions_card exterior_even from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private flip_comm adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private diff diff_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_symm from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport
open private diff_two_flips from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9FourthLeafSignProbe

private def antipode (x : Q 9) : Q 9 := fun i => !x i

private lemma hamming_antipode_add (x y : Q 9) :
    hammingDist x y + hammingDist (antipode x) y = 9 := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 9)))
    (fun i => x i ≠ y i)
  have he : (Finset.univ.filter (fun i => ¬x i ≠ y i)) =
      Finset.univ.filter (fun i => antipode x i ≠ y i) := by
    ext i
    cases hx : x i <;> cases hy : y i <;> simp [antipode,hx,hy]
  rw [he] at h
  simpa only [hammingDist,Finset.card_univ,Fintype.card_fin] using h

private lemma hamming_pair_antipode (x : Q 9) {i j : Fin 9} (hij : i ≠ j) :
    hammingDist x (flip (flip (antipode x) i) j) = 7 := by
  have h := hamming_antipode_add x (flip (flip (antipode x) i) j)
  have hd : hammingDist (antipode x) (flip (flip (antipode x) i) j) = 2 := by
    change (diff (antipode x) (flip (flip (antipode x) i) j)).card = 2
    rw [diff_symm, diff_two_flips _ hij]
    simp [Finset.card_insert_of_notMem, hij, Ne.symm hij]
  omega

private def unusedDirections (C : Finset (Q 9)) (x : Q 9) : Finset (Fin 9) :=
  Finset.univ \ directions C x

private lemma unused_card {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    {x : Q 9} (hx : x ∈ C) : (unusedDirections C x).card = 6 := by
  rw [unusedDirections, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    regular_directions C hr hx, Finset.card_univ, Fintype.card_fin]

private lemma agreeing_coordinate_unused {C : Finset (Q 9)}
    (hd : ∀ a ∈ C, ∀ b ∈ C, hammingDist a b ≤ 7)
    {x y : Q 9} (hy : y ∈ C) (hxy : hammingDist x y = 7)
    {i : Fin 9} (hi : x i = y i) :
    i ∈ unusedDirections C x := by
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
  intro hs
  have hxi := (mem_directions C x i).mp hs
  have hdist := hd (flip x i) hxi y hy
  have hi' : i ∉ diff x y := by simp [diff,hi]
  change (diff (flip x i) y).card ≤ 7 at hdist
  rw [diff_flip, if_neg hi', Finset.card_insert_of_notMem hi'] at hdist
  change (diff x y).card = 7 at hxy
  omega

private lemma matching_coordinate_pair_unused {C : Finset (Q 9)}
    (hd : ∀ a ∈ C, ∀ b ∈ C, hammingDist a b ≤ 7)
    {x : Q 9} {i j : Fin 9} (hij : i ≠ j)
    (hy : flip (flip (antipode x) i) j ∈ C) :
    i ∈ unusedDirections C x ∧ j ∈ unusedDirections C x := by
  have hh := hamming_pair_antipode x hij
  constructor
  · apply agreeing_coordinate_unused hd hy hh
    simp [BalancedCriticalSpectrum.flip,antipode,hij]
  · apply agreeing_coordinate_unused hd hy hh
    simp [BalancedCriticalSpectrum.flip,antipode,Ne.symm hij]

private def distanceSevenPartners (C : Finset (Q 9)) (x : Q 9) :
    SimpleGraph (unusedDirections C x : Finset _) where
  Adj i j := i ≠ j ∧ flip (flip (antipode x) i.val) j.val ∈ C
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm,by rw [flip_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private lemma distanceSeven_partner_degree {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hd : ∀ a ∈ C, ∀ b ∈ C, hammingDist a b ≤ 7)
    {x : Q 9} (hx : x ∈ C) (i : unusedDirections C x) :
    (distanceSevenPartners C x).degree i = 0 ∨
    (distanceSevenPartners C x).degree i = 2 ∨ (distanceSevenPartners C x).degree i = 4 := by
  let G := distanceSevenPartners C x
  let v := flip (antipode x) i.val
  have hv : v ∉ C := by
    intro hvC
    have h := hamming_antipode_add x v
    have h₁ : hammingDist (antipode x) v = 1 := BalancedCriticalSpectrum.flip_adj _ _
    have h₂ := hd x hx v hvC
    omega
  have hbar : antipode x ∉ C := by
    intro hbarC
    have h := hamming_antipode_add x (antipode x)
    have h₂ := hd x hx (antipode x) hbarC
    simp at h
    omega
  have hcard : (G.neighborFinset i).card = (directions C v).card := by
    apply Finset.card_bij (fun j _ => j.val)
    · intro j hj
      exact (mem_directions C v j.val).mpr ((G.mem_neighborFinset _ _).mp hj).2
    · intro j _ k _ h
      exact Subtype.ext h
    · intro j hj
      have hsel := (mem_directions C v j).mp hj
      have hne : i.val ≠ j := by
        intro he
        apply hbar
        rw [← he] at hsel
        simpa [v, BalancedCriticalSpectrum.flip_flip] using hsel
      have hjJ := (matching_coordinate_pair_unused hd hne hsel).2
      let k : unusedDirections C x := ⟨j,hjJ⟩
      refine ⟨k,(G.mem_neighborFinset _ _).mpr ⟨fun he => hne (congrArg Subtype.val he),hsel⟩,rfl⟩
  have heven := exterior_even C hr hb v hv
  rw [← hcard, G.card_neighborFinset_eq_degree] at heven
  have hV : Fintype.card (unusedDirections C x) = 6 := by
    rw [Fintype.card_coe, unused_card hr hx]
  have hmax : G.degree i ≤ 5 := by
    have hsub : G.neighborFinset i ⊆ Finset.univ.erase i := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp hj).ne.symm,Finset.mem_univ _⟩
    have h := Finset.card_le_card hsub
    rw [G.card_neighborFinset_eq_degree, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hV] at h
    omega
  obtain ⟨k,hk⟩ := heven
  change G.degree i = 0 ∨ G.degree i = 2 ∨ G.degree i = 4
  omega

#print axioms distanceSeven_partner_degree

open BalancedCriticalSpectrum (IsSwitching switchingVector)
open private switching_sq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private HuangCubeCovariance.edge edge_sq edge_curvature matrix_row from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

private def partnerPhase (C : Finset (Q 9)) (sigma : Q 9 → ℝ)
    (x : Q 9) (i j : Fin 9) : ℝ :=
  HuangCubeCovariance.edge (antipode x) i * HuangCubeCovariance.edge (flip (antipode x) i) j *
    switchingVector C sigma (flip (flip (antipode x) i) j)

private lemma partnerPhase_antisymm (C : Finset (Q 9)) (sigma : Q 9 → ℝ)
    (x : Q 9) {i j : Fin 9} (hij : i ≠ j) :
    partnerPhase C sigma x i j = -partnerPhase C sigma x j i := by
  unfold partnerPhase
  rw [edge_curvature (antipode x) hij, flip_comm (antipode x) i j, neg_mul]

private lemma partnerPhase_zero_sum {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
    (hs : IsSwitching C sigma)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hd : ∀ a ∈ C, ∀ b ∈ C, hammingDist a b ≤ 7)
    {x : Q 9} (hx : x ∈ C) (i : Fin 9) :
    ∑ j : Fin 9, partnerPhase C sigma x i j = 0 := by
  let v := flip (antipode x) i
  have hv : v ∉ C := by
    intro hvC
    have h := hamming_antipode_add x v
    have h₁ : hammingDist (antipode x) v = 1 := BalancedCriticalSpectrum.flip_adj _ _
    have h₂ := hd x hx v hvC
    omega
  have he := congrFun (BalancedCriticalSpectrum.ambient_eigenvector (d := 3) C sigma hr hs) v
  rw [matrix_row] at he
  have hrow : ∑ j : Fin 9, HuangCubeCovariance.edge v j * switchingVector C sigma (flip v j) = 0 := by
    simpa [switchingVector, hv] using he
  unfold partnerPhase
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  change HuangCubeCovariance.edge (antipode x) i *
    (∑ j : Fin 9, HuangCubeCovariance.edge v j * switchingVector C sigma (flip v j)) = 0
  rw [hrow,mul_zero]

private lemma partnerPhase_triangle_compatible {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
    (hs : IsSwitching C sigma) (x : Q 9) {i j k : Fin 9} (hjk : j ≠ k)
    (hij : flip (flip (antipode x) i) j ∈ C)
    (hik : flip (flip (antipode x) i) k ∈ C)
    (ht : flip (flip (flip (antipode x) i) j) k ∈ C) :
    partnerPhase C sigma x i j = -partnerPhase C sigma x i k := by
  let v := flip (antipode x) i
  let t := flip (flip v j) k
  have ht' : flip (flip v k) j = t := flip_comm v k j
  have hj : HuangCubeCovariance.edge (flip v j) k = sigma (flip v j) * sigma t :=
    hs.2 _ hij _ ht (BalancedCriticalSpectrum.flip_adj _ _)
  have hk : HuangCubeCovariance.edge (flip v k) j = sigma (flip v k) * sigma t := by
    rw [← ht']
    exact hs.2 _ hik _ (ht'.symm ▸ ht) (BalancedCriticalSpectrum.flip_adj (flip v k) j)
  have hsq := switching_sq hs ht
  have hj' : HuangCubeCovariance.edge (flip v j) k * sigma t = sigma (flip v j) := by
    rw [hj,mul_assoc,← pow_two,hsq,mul_one]
  have hk' : HuangCubeCovariance.edge (flip v k) j * sigma t = sigma (flip v k) := by
    rw [hk,mul_assoc,← pow_two,hsq,mul_one]
  unfold partnerPhase
  change HuangCubeCovariance.edge (antipode x) i * HuangCubeCovariance.edge v j * switchingVector C sigma (flip v j) =
      -(HuangCubeCovariance.edge (antipode x) i * HuangCubeCovariance.edge v k * switchingVector C sigma (flip v k))
  rw [show switchingVector C sigma (flip v j) = sigma (flip v j) by simp [switchingVector,hij,v],
    show switchingVector C sigma (flip v k) = sigma (flip v k) by simp [switchingVector,hik,v],
    ← hj', ← hk']
  rw [mul_assoc (HuangCubeCovariance.edge (antipode x) i), ← mul_assoc (HuangCubeCovariance.edge v j), edge_curvature v hjk]
  ring

#print axioms partnerPhase_triangle_compatible

open private pair_directions_of_flip_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9FourthLeafSignProbe
open private diff_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeTwelveSupport

private lemma distanceSeven_partner_card {C : Finset (Q 9)}
    (hd : ∀ a ∈ C, ∀ b ∈ C, hammingDist a b ≤ 7) (x : Q 9) :
    (distanceSevenPartners C x).edgeFinset.card =
      (C.filter (fun y => hammingDist x y = 7)).card := by
  let I : Finset (Fin 9) := unusedDirections C x
  let G : SimpleGraph I := distanceSevenPartners C x
  let partner : Sym2 I → Q 9 := Sym2.lift
    ⟨fun i j => flip (flip (antipode x) i.val) j.val, fun i j => flip_comm _ _ _⟩
  have adj_iff {i j : I} :
      s(i,j) ∈ G.edgeFinset ↔ i ≠ j ∧ flip (flip (antipode x) i.val) j.val ∈ C :=
    SimpleGraph.mem_edgeFinset.trans (SimpleGraph.mem_edgeSet G)
  change G.edgeFinset.card = _
  apply Finset.card_bij (fun e _ => partner e)
  · intro e he
    induction e using Sym2.inductionOn with
    | hf i j =>
      obtain ⟨hij,hC⟩ := adj_iff.mp he
      have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      exact Finset.mem_filter.mpr ⟨hC,hamming_pair_antipode x hij'⟩
  · intro e he f hf hval
    induction e using Sym2.inductionOn with
    | hf i j =>
      induction f using Sym2.inductionOn with
      | hf k l =>
        have hij : i.val ≠ j.val := fun h => (adj_iff.mp he).1 (Subtype.ext h)
        have hkl : k.val ≠ l.val := fun h => (adj_iff.mp hf).1 (Subtype.ext h)
        rcases pair_directions_of_flip_eq (antipode x) hij hkl hval with h | h
        · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h.1.symm,Subtype.ext h.2.symm⟩)
        · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h.2.symm,Subtype.ext h.1.symm⟩)
  · intro y hy
    obtain ⟨hyC,hy7⟩ := Finset.mem_filter.mp hy
    have hdif : (diff y (antipode x)).card = 2 := by
      rw [diff_symm y (antipode x)]
      have h := hamming_antipode_add x y
      change hammingDist (antipode x) y = 2
      omega
    obtain ⟨j,i,hji,hD⟩ := Finset.card_eq_two.mp hdif
    have he : y = flip (flip (antipode x) i) j := by
      apply diff_injective (x := antipode x)
      rw [diff_symm (antipode x) y, diff_symm (antipode x) (flip (flip (antipode x) i) j),
        hD,diff_two_flips _ hji.symm]
    have hp := matching_coordinate_pair_unused hd hji.symm (he ▸ hyC)
    let u : I := ⟨i,hp.1⟩
    let v : I := ⟨j,hp.2⟩
    have hUV : u ≠ v := fun h => hji (congrArg Subtype.val h.symm)
    exact ⟨s(u,v),adj_iff.mpr ⟨hUV,he ▸ hyC⟩,he.symm⟩

#print axioms distanceSeven_partner_card

private lemma partnerPhase_nonzero {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
    (hs : IsSwitching C sigma) (x : Q 9) (i j : Fin 9) :
    (partnerPhase C sigma x i j ≠ 0 ↔ flip (flip (antipode x) i) j ∈ C) ∧
      (partnerPhase C sigma x i j = -1 ∨ partnerPhase C sigma x i j = 0 ∨
        partnerPhase C sigma x i j = 1) := by
  let v := flip (flip (antipode x) i) j
  by_cases hv : v ∈ C
  · have hsq : partnerPhase C sigma x i j ^ 2 = 1 := by
      unfold partnerPhase
      rw [mul_pow, mul_pow, edge_sq, edge_sq, one_mul, one_mul]
      change switchingVector C sigma v ^ 2 = 1
      simpa [switchingVector,hv] using switching_sq hs hv
    have hsides : partnerPhase C sigma x i j = -1 ∨ partnerPhase C sigma x i j = 1 := by
      have ht : (partnerPhase C sigma x i j + 1) * (partnerPhase C sigma x i j - 1) = 0 := by
        nlinarith only [hsq]
      rcases mul_eq_zero.mp ht with h | h
      · left; linarith
      · right; linarith
    rcases hsides with h | h <;> simp [h,hv,v] at * <;> assumption
  · have hzero : partnerPhase C sigma x i j = 0 := by simp [partnerPhase,switchingVector,v, hv]
    change (partnerPhase C sigma x i j ≠ 0 ↔ v ∈ C) ∧ _
    simp [hzero,hv]

private lemma partnerPhase_diagonal {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
    (hd : ∀ a ∈ C, ∀ b ∈ C, hammingDist a b ≤ 7) {x : Q 9} (hx : x ∈ C) (i : Fin 9) :
    partnerPhase C sigma x i i = 0 := by
  have hbar : antipode x ∉ C := by
    intro hC
    have h := hamming_antipode_add x (antipode x)
    have h' := hd x hx (antipode x) hC
    simp at h
    omega
  simp [partnerPhase,switchingVector,hbar]

private lemma partnerFlow_balance {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
    (hs : IsSwitching C sigma)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hd : ∀ a ∈ C, ∀ b ∈ C, hammingDist a b ≤ 7)
    {x : Q 9} (hx : x ∈ C) (i : Fin 9) :
    ((Finset.univ : Finset (Fin 9)).filter (fun j => 0 < partnerPhase C sigma x i j)).card =
      ((Finset.univ : Finset (Fin 9)).filter (fun j => 0 < partnerPhase C sigma x j i)).card := by
  let a := partnerPhase C sigma x i
  let P := (Finset.univ : Finset (Fin 9)).filter (fun j => 0 < a j)
  let N := (Finset.univ : Finset (Fin 9)).filter (fun j => a j < 0)
  have happ (j : Fin 9) :
      a j = (if 0 < a j then (1 : ℝ) else 0) - (if a j < 0 then 1 else 0) := by
    have h := (partnerPhase_nonzero hs x i j).2
    change a j = -1 ∨ a j = 0 ∨ a j = 1 at h
    rcases h with h | h | h <;> rw [h] <;> norm_num
  have he : (P.card : ℝ) - N.card = 0 := by
    calc
      _ = ∑ j : Fin 9, ((if 0 < a j then (1 : ℝ) else 0) -
          (if a j < 0 then 1 else 0)) := by
        simp [P,N,Finset.sum_sub_distrib,Finset.sum_filter]
      _ = ∑ j : Fin 9, a j := Finset.sum_congr rfl (fun j _ => (happ j).symm)
      _ = 0 := partnerPhase_zero_sum hs hr hd hx i
  have hN : N = Finset.univ.filter (fun j => 0 < partnerPhase C sigma x j i) := by
    ext j
    simp only [N,Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases h : i = j
    · subst j
      simp [a,partnerPhase_diagonal hd hx i]
    · change partnerPhase C sigma x i j < 0 ↔ 0 < partnerPhase C sigma x j i
      rw [partnerPhase_antisymm C sigma x h, neg_lt_zero]
  change P.card = _
  rw [← hN]
  exact_mod_cast (sub_eq_zero.mp he)

private lemma compatible_triple_count {a b c : ℝ}
    (ha : a = -1 ∨ a = 0 ∨ a = 1) (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (hc : c = -1 ∨ c = 0 ∨ c = 1) :
    let m := (if a ≠ 0 then 1 else 0) + (if b ≠ 0 then 1 else 0) + (if c ≠ 0 then 1 else 0)
    let w := (if a ≠ 0 ∧ a = b then 1 else 0) +
      (if b ≠ 0 ∧ b = c then 1 else 0) + (if c ≠ 0 ∧ c = a then 1 else 0)
    let t := if m = (3 : ℕ) then 1 else 0
    t ≤ w ∧ ((a ≠ 0 → b ≠ 0 → a = b) → (b ≠ 0 → c ≠ 0 → b = c) →
      (c ≠ 0 → a ≠ 0 → c = a) → m + t ≤ 1 + w) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> norm_num

#print axioms partnerFlow_balance
#print axioms compatible_triple_count

private def wedgeVertices {V : Type*} [DecidableEq V] (a : V × V × V) : Finset V :=
  {a.1,a.2.1,a.2.2}

private def directedWedges {V : Type*} [DecidableEq V]
    (S : Finset V) (R : V → V → Prop) [DecidableRel R] : Finset (V × V × V) :=
  (S.product (S.product S)).filter (fun a => R a.2.1 a.1 ∧ R a.1 a.2.2)

private lemma directed_wedges_card {V : Type*} [DecidableEq V]
    (S : Finset V) (R : V → V → Prop) [DecidableRel R] :
    (directedWedges S R).card =
      ∑ z ∈ S, (S.filter (fun a => R a z)).card * (S.filter (R z)).card := by
  let part (z : V) : Finset (V × V × V) :=
    ({z} : Finset V).product ((S.filter (fun a => R a z)).product (S.filter (R z)))
  have hparts : directedWedges S R = S.biUnion part := by
    ext t
    rcases t with ⟨z,a,b⟩
    simp [directedWedges,part,and_assoc,and_left_comm,and_comm]
  have hdis : (S : Set V).PairwiseDisjoint part := by
    intro z hz w hw hzw
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    have he : t.1 = z := by simpa [part] using (Finset.mem_product.mp ht).1
    have he' : t.1 = w := by simpa [part] using (Finset.mem_product.mp ht').1
    exact hzw (he.symm.trans he')
  rw [hparts,Finset.card_biUnion hdis]
  simp [part]

private lemma directed_wedges_by_triple {V : Type*} [DecidableEq V]
    (S : Finset V) (R : V → V → Prop) [DecidableRel R]
    (hirr : ∀ a, ¬R a a) (hasymm : ∀ {a b}, R a b → ¬R b a) :
    (directedWedges S R).card =
      ∑ T ∈ S.powersetCard 3, (directedWedges T R).card := by
  have goal_maps (p : V × V × V) (hp : p ∈ directedWedges S R) :
      wedgeVertices p ∈ S.powersetCard 3 := by
    rcases p with ⟨i,j,k⟩
    obtain ⟨hmem,hRel⟩ := Finset.mem_filter.mp hp
    obtain ⟨hi,hinner⟩ := Finset.mem_product.mp hmem
    obtain ⟨hj,hk⟩ := Finset.mem_product.mp hinner
    have hij : i ≠ j := fun h => hirr i (by simpa [h] using hRel.1)
    have hik : i ≠ k := fun h => hirr i (by simpa [h] using hRel.2)
    have hjk : j ≠ k := fun h => hasymm hRel.1 (by simpa [h] using hRel.2)
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.insert_subset hi (Finset.insert_subset hj (Finset.singleton_subset_iff.mpr hk)),?_⟩
    simp [wedgeVertices, Finset.card_insert_of_notMem,hij,hik,hjk,
      Ne.symm hij,Ne.symm hik,Ne.symm hjk]
  calc
    _ = ∑ T ∈ S.powersetCard 3,
        ((directedWedges S R).filter (fun p => wedgeVertices p = T)).card :=
      Finset.card_eq_sum_card_fiberwise goal_maps
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T hT
      have hT' := Finset.mem_powersetCard.mp hT
      congr 1
      ext p
      constructor
      · intro hp
        obtain ⟨hW,hlabel⟩ := Finset.mem_filter.mp hp
        have hRel := (Finset.mem_filter.mp hW).2
        rw [← hlabel]
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨by simp [wedgeVertices],
          Finset.mem_product.mpr ⟨by simp [wedgeVertices],by simp [wedgeVertices]⟩⟩,hRel⟩
      · intro hp
        rcases p with ⟨i,j,k⟩
        obtain ⟨hmem,hRel⟩ := Finset.mem_filter.mp hp
        obtain ⟨hi,hinner⟩ := Finset.mem_product.mp hmem
        obtain ⟨hj,hk⟩ := Finset.mem_product.mp hinner
        have hW : (i,j,k) ∈ directedWedges S R :=
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hT'.1 hi,
            Finset.mem_product.mpr ⟨hT'.1 hj,hT'.1 hk⟩⟩,hRel⟩
        refine Finset.mem_filter.mpr ⟨hW,?_⟩
        have hw := Finset.mem_powersetCard.mp (goal_maps _ hW)
        apply Finset.eq_of_subset_of_card_le
          (Finset.insert_subset hi (Finset.insert_subset hj (Finset.singleton_subset_iff.mpr hk)))
        change T.card ≤ (wedgeVertices (i,j,k)).card
        rw [hT'.2,hw.2]

#print axioms directed_wedges_by_triple

open private diff_symm diff_triangle_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport

private def shellWithRoot (C : Finset (Q 9)) (x : Q 9) (d : ℕ) : Finset (Q 9) :=
  C.filter (fun y => hammingDist x y = d)

private lemma edge_moves_between_shells {x y z : Q 9} (h : (hypercube 9).Adj y z) :
    hammingDist x z + 1 = hammingDist x y ∨
    hammingDist x z = hammingDist x y + 1 := by
  obtain ⟨i,hi⟩ := adjacent_exists_flip h
  have he : diff x z = diff (flip y i) x := by rw [hi,diff_symm x (flip y i)]
  change (diff x z).card + 1 = (diff x y).card ∨
    (diff x z).card = (diff x y).card + 1
  rw [he, diff_symm x y, diff_flip]
  by_cases hi' : i ∈ diff y x
  · exact Or.inl (by rw [ite_eq_left hi']; exact Finset.card_erase_add_one hi')
  · exact Or.inr (by rw [ite_eq_right hi',Finset.card_insert_of_notMem hi'])

private lemma distanceSeven_incidence_sum {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hd : ∀ a ∈ C, ∀ b ∈ C, hammingDist a b ≤ 7)
    {x : Q 9} (hx : x ∈ C) :
    (∑ z ∈ shellWithRoot C x 6,
      ((shellWithRoot C x 7).filter (fun y => (hypercube 9).Adj y z)).card) =
        3 * (shellWithRoot C x 7).card := by
  let P := shellWithRoot C x 7
  let T := shellWithRoot C x 6
  let R := (hypercube 9).Adj
  have hcard (y : Q 9) (hy : y ∈ P) : (T.filter (R y)).card = 3 := by
    obtain ⟨hyC,hy7⟩ := Finset.mem_filter.mp hy
    have heq : T.filter (R y) = C.filter (R y) := by
      ext z
      simp only [T,shellWithRoot,Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1.1,h.2⟩
      · rintro ⟨hzC,hyz⟩
        refine ⟨⟨hzC,?_⟩,hyz⟩
        have hd' := hd x hx z hzC
        rcases edge_moves_between_shells (x := x) hyz with h | h <;> omega
    rw [heq, ← directions_card]
    exact regular_directions C hr hyC
  calc
    _ = ∑ y ∈ P, (T.filter (R y)).card :=
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := P) (t := T) (r := R)).symm
    _ = ∑ _y ∈ P, 3 := Finset.sum_congr rfl hcard
    _ = _ := by simp [P,Nat.mul_comm]

#print axioms distanceSeven_incidence_sum
