import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9PartnerGraphProbe

/-! Each rank-three label has limited overlap with the signed rank-two partners. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q flip IsSwitching)
attribute [local instance] Classical.propDecidable

open private directedWedges directed_wedges_card directed_wedges_by_triple
  partnerPhase partnerPhase_nonzero partnerPhase_diagonal partnerPhase_antisymm
  compatible_triple_count partnerPhase_triangle_compatible antipode
  from D5.S3.Combinatorics.Graph.HypercubeCritical.Q9PartnerGraphProbe

private lemma card_filter_triple {V : Type*} [DecidableEq V]
    (f : V → Prop) [DecidablePred f] {i j k : V}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (({i,j,k} : Finset V).filter f).card =
      (if f i then 1 else 0) + (if f j then 1 else 0) + (if f k then 1 else 0) := by
  rw [Finset.card_filter,Finset.sum_insert (by simp [hij,hik]),
    Finset.sum_insert (by simp [hjk]), Finset.sum_singleton]
  omega

private def triangleCharge {V : Type*} (a : V → V → ℝ) (T : Finset V) : ℕ :=
  if ∀ i ∈ T, ∀ j ∈ T, i ≠ j → a i j ≠ 0 then 1 else 0

private lemma triangleCharge_triple {V : Type*} [DecidableEq V]
    (a : V → V → ℝ) (hanti : ∀ i j, i ≠ j → a j i = -a i j)
    {i j k : V} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    triangleCharge a {i,j,k} =
      if (if a i j ≠ 0 then 1 else 0) + (if a j k ≠ 0 then 1 else 0) +
        (if a k i ≠ 0 then 1 else 0) = (3 : ℕ) then 1 else 0 := by
  have he : (∀ u ∈ ({i,j,k} : Finset V), ∀ v ∈ ({i,j,k} : Finset V),
      u ≠ v → a u v ≠ 0) ↔ a i j ≠ 0 ∧ a j k ≠ 0 ∧ a k i ≠ 0 := by
    constructor
    · intro h
      exact ⟨h i (by simp) j (by simp) hij, h j (by simp) k (by simp) hjk,
        h k (by simp) i (by simp) hik.symm⟩
    · rintro ⟨h₁,h₂,h₃⟩ u hu v hv hne
      simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
      rcases hu with h | h | h <;> rcases hv with g | g | g <;> subst u <;> subst v
      · exact (hne rfl).elim
      · exact h₁
      · rw [hanti k i hik.symm]; exact neg_ne_zero.mpr h₃
      · rw [hanti i j hij]; exact neg_ne_zero.mpr h₁
      · exact (hne rfl).elim
      · exact h₂
      · exact h₃
      · rw [hanti j k hjk]; exact neg_ne_zero.mpr h₂
      · exact (hne rfl).elim
  unfold triangleCharge
  simp only [he]
  by_cases h₁ : a i j = 0 <;> by_cases h₂ : a j k = 0 <;>
    by_cases h₃ : a k i = 0 <;> simp [h₁,h₂,h₃]

private lemma opposite_wedges_triple {V : Type*} [DecidableEq V]
    (a : V → V → ℝ) (hanti : ∀ i j, i ≠ j → a j i = -a i j)
    (hdiag : ∀ i, a i i = 0)
    (hunit : ∀ i j, a i j = -1 ∨ a i j = 0 ∨ a i j = 1)
    {i j k : V} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (directedWedges ({i,j,k} : Finset V) (fun u v => 0 < a u v)).card =
      (if a i j ≠ 0 ∧ a i j = a j k then 1 else 0) +
      (if a j k ≠ 0 ∧ a j k = a k i then 1 else 0) +
      (if a k i ≠ 0 ∧ a k i = a i j then 1 else 0) := by
  rw [directed_wedges_card,Finset.sum_insert (by simp [hij,hik]),
    Finset.sum_insert (by simp [hjk]),Finset.sum_singleton]
  simp_rw [card_filter_triple _ hij hik hjk]
  rw [hanti i j hij,hanti j k hjk,hanti k i hik.symm]
  rcases hunit i j with h₁ | h₁ | h₁ <;> rcases hunit j k with h₂ | h₂ | h₂ <;>
    rcases hunit k i with h₃ | h₃ | h₃ <;> norm_num [hdiag,h₁,h₂,h₃]

private lemma triangle_charge_le_wedges {V : Type*} [DecidableEq V]
    (a : V → V → ℝ) (hanti : ∀ i j, i ≠ j → a j i = -a i j)
    (hdiag : ∀ i, a i i = 0)
    (hunit : ∀ i j, a i j = -1 ∨ a i j = 0 ∨ a i j = 1)
    {T : Finset V} (hT : T.card = 3) :
    triangleCharge a T ≤ (directedWedges T (fun u v => 0 < a u v)).card := by
  obtain ⟨i,j,k,hij,hik,hjk,rfl⟩ := Finset.card_eq_three.mp hT
  rw [triangleCharge_triple a hanti hij hik hjk,
    opposite_wedges_triple a hanti hdiag hunit hij hik hjk]
  exact (compatible_triple_count (hunit i j) (hunit j k) (hunit k i)).1

#print axioms triangle_charge_le_wedges

open private diff diff_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_symm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport
open private diff_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeTwelveSupport
open private flip_comm adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private flip_triangle_commute diff_three_flips from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9FourthLeafSignProbe
open private hamming_antipode_add hamming_pair_antipode shellWithRoot from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9PartnerGraphProbe

private lemma rankThree_incidence {C : Finset (Q 9)} {x z : Q 9} {sigma : Q 9 → ℝ}
    (hs : IsSwitching C sigma)
    {i j k : Fin 9} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hz : z = flip (flip (flip (antipode x) i) j) k) :
    ((shellWithRoot C x 7).filter (fun y => (hypercube 9).Adj y z)).card =
      (if partnerPhase C sigma x i j ≠ 0 then 1 else 0) +
      (if partnerPhase C sigma x j k ≠ 0 then 1 else 0) +
      (if partnerPhase C sigma x k i ≠ 0 then 1 else 0) := by
  let U : Finset (Fin 9) := {i,j,k}
  let D := U.filter (fun l => flip z l ∈ C)
  let Z := (shellWithRoot C x 7).filter (fun y => (hypercube 9).Adj y z)
  have hi : flip z i = flip (flip (antipode x) j) k := by
    rw [hz,flip_triangle_commute (antipode x) i j k,BalancedCriticalSpectrum.flip_flip]
  have hj : flip z j = flip (flip (antipode x) k) i := by
    rw [hz,flip_comm (flip (antipode x) i) j k,BalancedCriticalSpectrum.flip_flip,
      flip_comm (antipode x) i k]
  have hk : flip z k = flip (flip (antipode x) i) j := by
    rw [hz,BalancedCriticalSpectrum.flip_flip]
  have hdif : diff z (antipode x) = {k,j,i} := by
    rw [hz,diff_three_flips _ hij hik hjk]
  have hZ : (diff z (antipode x)).card = 3 := by
    rw [hdif]
    simp [Finset.card_insert_of_notMem,Ne.symm hij,Ne.symm hik,Ne.symm hjk]
  have hZD : Z.card = D.card := by
    symm
    apply Finset.card_bij (fun l _ => flip z l)
    · intro l hl
      obtain ⟨hlU,hlC⟩ := Finset.mem_filter.mp hl
      have h7 : hammingDist x (flip z l) = 7 := by
        simp only [U,Finset.mem_insert,Finset.mem_singleton] at hlU
        rcases hlU with h | h | h
        · rw [h,hi]; exact hamming_pair_antipode x hjk
        · rw [h,hj]; exact hamming_pair_antipode x hik.symm
        · rw [h,hk]; exact hamming_pair_antipode x hij
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hlC,h7⟩,
        (BalancedCriticalSpectrum.flip_adj _ _).symm⟩
    · intro a _ b _ h
      exact flip_injective z h
    · intro y hy
      obtain ⟨hyP,hyz⟩ := Finset.mem_filter.mp hy
      obtain ⟨hyC,hy7⟩ := Finset.mem_filter.mp hyP
      obtain ⟨l,hl⟩ := adjacent_exists_flip hyz.symm
      have hRank : (diff y (antipode x)).card = 2 := by
        rw [diff_symm y (antipode x)]
        change hammingDist (antipode x) y = 2
        have := hamming_antipode_add x y
        omega
      have hlD : l ∈ diff z (antipode x) := by
        by_contra hn
        rw [hl,diff_flip,ite_eq_right hn,Finset.card_insert_of_notMem hn,hZ] at hRank
        omega
      have hlU : l ∈ U := by
        rw [hdif] at hlD
        simpa [U, or_comm, or_left_comm, or_assoc] using hlD
      exact ⟨l,Finset.mem_filter.mpr ⟨hlU,hl.symm ▸ hyC⟩,hl.symm⟩
  change Z.card = _
  rw [hZD]
  change (({i,j,k} : Finset (Fin 9)).filter (fun l => flip z l ∈ C)).card = _
  rw [card_filter_triple _ hij hik hjk,hi,hj,hk]
  simp only [← (partnerPhase_nonzero hs x j k).1,← (partnerPhase_nonzero hs x k i).1,
    ← (partnerPhase_nonzero hs x i j).1]
  omega

private lemma actual_triangle_charge_bound {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
    (hs : IsSwitching C sigma)
    (hd : ∀ a ∈ C, ∀ b ∈ C, hammingDist a b ≤ 7)
    {x z : Q 9} (hx : x ∈ C) (hzC : z ∈ C)
    {T : Finset (Fin 9)} (hT : T.card = 3) (hTz : diff z (antipode x) = T) :
    ((shellWithRoot C x 7).filter (fun y => (hypercube 9).Adj y z)).card +
        triangleCharge (partnerPhase C sigma x) T ≤
      1 + (directedWedges T (fun i j => 0 < partnerPhase C sigma x i j)).card := by
  obtain ⟨k,j,i,hkj,hki,hji,rfl⟩ := Finset.card_eq_three.mp hT
  have hij := hji.symm
  have hik := hki.symm
  have hjk := hkj.symm
  have hz : z = flip (flip (flip (antipode x) i) j) k := by
    apply diff_injective (x := antipode x)
    rw [diff_symm (antipode x) z,
      diff_symm (antipode x) (flip (flip (flip (antipode x) i) j) k),hTz,
      diff_three_flips _ hij hik hjk]
  have hSet : ({k,j,i} : Finset (Fin 9)) = {i,j,k} := by
    ext b
    simp [or_comm,or_left_comm,or_assoc]
  let A := partnerPhase C sigma x
  have hanti (u v : Fin 9) (h : u ≠ v) : A v u = -A u v :=
    partnerPhase_antisymm C sigma x h.symm
  have hdiag (u : Fin 9) : A u u = 0 := partnerPhase_diagonal hd hx u
  have hunit (u v : Fin 9) : A u v = -1 ∨ A u v = 0 ∨ A u v = 1 :=
    (partnerPhase_nonzero hs x u v).2
  have common (u v w : Fin 9) (hvw : v ≠ w)
      (hua : A u v ≠ 0) (huw : A u w ≠ 0)
      (hword : z = flip (flip (flip (antipode x) u) v) w) :
      A u v = -A u w :=
    partnerPhase_triangle_compatible hs x hvw
      ((partnerPhase_nonzero hs x u v).1.mp hua)
      ((partnerPhase_nonzero hs x u w).1.mp huw) (hword ▸ hzC)
  have h₁ (hij' : A i j ≠ 0) (hjk' : A j k ≠ 0) : A i j = A j k := by
    have h := common j i k hik (by rw [hanti i j hij]; exact neg_ne_zero.mpr hij') hjk'
      (by rw [hz,flip_comm (antipode x) i j])
    rw [hanti i j hij] at h
    exact neg_injective h
  have h₂ (hjk' : A j k ≠ 0) (hki' : A k i ≠ 0) : A j k = A k i := by
    have h := common k j i hji (by rw [hanti j k hjk]; exact neg_ne_zero.mpr hjk') hki'
      (by
        rw [hz,flip_triangle_commute (antipode x) i j k,flip_comm (antipode x) j k])
    rw [hanti j k hjk] at h
    exact neg_injective h
  have h₃ (hki' : A k i ≠ 0) (hij' : A i j ≠ 0) : A k i = A i j := by
    have h := common i k j hkj (by rw [hanti k i hki]; exact neg_ne_zero.mpr hki') hij'
      (by rw [hz,flip_comm (flip (antipode x) i) j k])
    rw [hanti k i hki] at h
    exact neg_injective h
  rw [rankThree_incidence hs hij hik hjk hz,hSet]
  change _ + triangleCharge A {i,j,k} ≤ 1 + (directedWedges {i,j,k} (fun i j => 0 < A i j)).card
  rw [triangleCharge_triple A hanti hij hik hjk,opposite_wedges_triple A hanti hdiag hunit hij hik hjk]
  exact (compatible_triple_count (hunit i j) (hunit j k) (hunit k i)).2 h₁ h₂ h₃

#print axioms actual_triangle_charge_bound

open private distanceSeven_incidence_sum from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9PartnerGraphProbe

private lemma partner_incidence_global_bound {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
    (hs : IsSwitching C sigma)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hd : ∀ a ∈ C, ∀ b ∈ C, hammingDist a b ≤ 7)
    {x : Q 9} (hx : x ∈ C) :
    3 * (shellWithRoot C x 7).card +
        (∑ B ∈ (Finset.univ : Finset (Fin 9)).powersetCard 3,
          triangleCharge (partnerPhase C sigma x) B) ≤
      (shellWithRoot C x 6).card +
        (directedWedges Finset.univ (fun i j => 0 < partnerPhase C sigma x i j)).card := by
  let S := shellWithRoot C x 6
  let A := partnerPhase C sigma x
  let R := fun i j => 0 < A i j
  let U := (Finset.univ : Finset (Fin 9)).powersetCard 3
  let mark := fun z => diff z (antipode x)
  let labels := S.image mark
  have hinj : Function.Injective mark := by
    intro a b h
    apply diff_injective (x := antipode x)
    rw [diff_symm (antipode x) a,diff_symm (antipode x) b]
    exact h
  have hrank (z : Q 9) (hz : z ∈ S) : (mark z).card = 3 := by
    have h6 := (Finset.mem_filter.mp hz).2
    have := hamming_antipode_add x z
    change (diff z (antipode x)).card = 3
    rw [diff_symm z (antipode x)]
    change hammingDist (antipode x) z = 3
    omega
  have hsub : labels ⊆ U := by
    intro T hT
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hrank z hz⟩
  have hlocal := Finset.sum_le_sum (s := S) (fun z hz =>
    actual_triangle_charge_bound hs hd hx (Finset.mem_filter.mp hz).1 (hrank z hz) rfl)
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one] at hlocal
  have hS :=
    distanceSeven_incidence_sum (C := C) hr hd hx
  have hL₁ : (∑ z ∈ S, triangleCharge A (mark z)) = ∑ T ∈ labels, triangleCharge A T :=
    (Finset.sum_image (fun _ _ _ _ h => hinj h)).symm
  have hL₂ : (∑ z ∈ S, (directedWedges (mark z) R).card) =
      ∑ T ∈ labels, (directedWedges T R).card :=
    (Finset.sum_image (s := S) (g := mark) (f := fun T => (directedWedges T R).card)
      (fun _ _ _ _ h => hinj h)).symm
  change (∑ z ∈ S, ((shellWithRoot C x 7).filter (fun y => (hypercube 9).Adj y z)).card) +
      (∑ z ∈ S, triangleCharge A (mark z)) ≤
      S.card + ∑ z ∈ S, (directedWedges (mark z) R).card at hlocal
  rw [hS,hL₁,hL₂] at hlocal
  have hanti (i j : Fin 9) (h : i ≠ j) : A j i = -A i j :=
    partnerPhase_antisymm C sigma x h.symm
  have hdiag (i : Fin 9) : A i i = 0 := partnerPhase_diagonal hd hx i
  have hunit (i j : Fin 9) : A i j = -1 ∨ A i j = 0 ∨ A i j = 1 :=
    (partnerPhase_nonzero hs x i j).2
  have hRest := Finset.sum_le_sum (s := U \ labels) (fun T hT =>
    triangle_charge_le_wedges A hanti hdiag hunit
      (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp hT).1).2)
  have hAll := directed_wedges_by_triple Finset.univ R
    (fun i hi => by
      change 0 < A i i at hi
      rw [hdiag i] at hi
      exact (lt_irrefl _ hi))
    (fun {i j} hij hji => by
      have hNE : i ≠ j := fun h => by
        subst j
        change 0 < A i i at hij
        rw [hdiag i] at hij
        exact (lt_irrefl _ hij)
      change 0 < A i j at hij
      change 0 < A j i at hji
      rw [hanti i j hNE] at hji
      linarith)
  change (∑ T ∈ U \ labels, triangleCharge A T) ≤
    ∑ T ∈ U \ labels, (directedWedges T R).card at hRest
  have hcombine₁ := Finset.sum_sdiff hsub (f := triangleCharge A)
  have hcombine₂ := Finset.sum_sdiff hsub (f := fun T => (directedWedges T R).card)
  change 3 * (shellWithRoot C x 7).card + (∑ T ∈ U, triangleCharge A T) ≤
    S.card + (directedWedges Finset.univ R).card
  change (directedWedges Finset.univ R).card = ∑ T ∈ U, (directedWedges T R).card at hAll
  omega

#print axioms partner_incidence_global_bound

open SimpleGraph
open BalancedCriticalSpectrum (IsBalanced)
open private distanceSevenPartners distanceSeven_partner_degree unusedDirections
  matching_coordinate_pair_unused partnerFlow_balance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9PartnerGraphProbe

private lemma wedge_count_plus_degree_two {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
    (hs : IsSwitching C sigma)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hd : ∀ a ∈ C, ∀ b ∈ C, hammingDist a b ≤ 7) {x : Q 9} (hx : x ∈ C) :
    (directedWedges Finset.univ (fun i j => 0 < partnerPhase C sigma x i j)).card +
      (Finset.univ.filter (fun i => (distanceSevenPartners C x).degree i = 2)).card =
      2 * (distanceSevenPartners C x).edgeFinset.card := by
  let I := unusedDirections C x
  let G := distanceSevenPartners C x
  let a := partnerPhase C sigma x
  let R := fun i j => 0 < a i j
  let In (i : Fin 9) := (Finset.univ.filter (fun j => R j i)).card
  let Out (i : Fin 9) := (Finset.univ.filter (R i)).card
  have hdiag (i : Fin 9) : a i i = 0 := partnerPhase_diagonal hd hx i
  have hloc (i j : Fin 9) (hn : a i j ≠ 0) : i ∈ I ∧ j ∈ I := by
    have hne : i ≠ j := fun h => by subst j; exact hn (hdiag i)
    exact matching_coordinate_pair_unused hd hne ((partnerPhase_nonzero hs x i j).1.mp hn)
  have hbal (i : Fin 9) : Out i = In i := partnerFlow_balance hs hr hd hx i
  have hdeg (i : I) :
      G.degree i = Out i.val + In i.val := by
    let U := (Finset.univ : Finset (Fin 9)).filter (fun j => a i.val j ≠ 0)
    have hCard : (G.neighborFinset i).card = U.card := by
      apply Finset.card_bij (fun j _ => j.val)
      · intro j hj
        have hadj := (G.mem_neighborFinset _ _).mp hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (partnerPhase_nonzero hs x i.val j.val).1.mpr hadj.2⟩
      · intro j _ k _ he
        exact Subtype.ext he
      · intro j hj
        have hn := (Finset.mem_filter.mp hj).2
        let v : I := ⟨j,(hloc i.val j hn).2⟩
        have hne : i ≠ v := fun h => by
          have he : i.val = j := congrArg Subtype.val h
          exact hn (by rw [←he,hdiag])
        exact ⟨v,(G.mem_neighborFinset _ _).mpr
          ⟨hne,(partnerPhase_nonzero hs x i.val j).1.mp hn⟩,rfl⟩
    rw [G.card_neighborFinset_eq_degree] at hCard
    rw [hCard]
    have hUnion : U = (Finset.univ.filter (R i.val)) ∪
        (Finset.univ.filter (fun j => R j i.val)) := by
      ext j
      simp only [U,R,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
      by_cases h : i.val = j
      · rw [← h]
        simp [hdiag]
      · change a i.val j ≠ 0 ↔ (0 < a i.val j ∨ 0 < a j i.val)
        rw [show a j i.val = -a i.val j from partnerPhase_antisymm C sigma x (Ne.symm h),neg_pos]
        exact ne_iff_lt_or_gt.trans or_comm
    have hDis : Disjoint (Finset.univ.filter (R i.val))
        (Finset.univ.filter (fun j => R j i.val)) := by
      apply Finset.disjoint_left.mpr
      intro j hj hj'
      have hh := (Finset.mem_filter.mp hj).2
      have hh' := (Finset.mem_filter.mp hj').2
      change 0 < a i.val j at hh
      change 0 < a j i.val at hh'
      have hne : i.val ≠ j := fun h => by rw [←h,hdiag] at hh; linarith
      rw [show a j i.val = -a i.val j from partnerPhase_antisymm C sigma x hne.symm] at hh'
      linarith
    rw [hUnion,Finset.card_union_of_disjoint hDis]
  have hW : (directedWedges Finset.univ R).card =
      ∑ i : I, In i.val * Out i.val := by
    rw [directed_wedges_card]
    change (∑ i : Fin 9, In i * Out i) = _
    have hs' : (∑ i : I, In i.val * Out i.val) = ∑ i ∈ I, In i * Out i := by
      simpa only [Finset.attach_eq_univ] using (Finset.sum_attach I (fun i => In i * Out i))
    rw [hs']
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hzero : Out i = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      exact hi ((hloc i j (ne_of_gt hj')).1)
    simp [hzero]
  have hEach (i : I) : In i.val * Out i.val + (if G.degree i = 2 then 1 else 0) = G.degree i := by
    have hD := hdeg i
    have hIO := hbal i.val
    have hcases := distanceSeven_partner_degree hr ⟨sigma,hs⟩ hd hx i
    change G.degree i = 0 ∨ G.degree i = 2 ∨ G.degree i = 4 at hcases
    rcases hcases with h0 | h₂ | h₄
    · have hi : In i.val = 0 := by omega
      simp [h0,hi]
    · have hi : In i.val = 1 := by omega
      have ho : Out i.val = 1 := by omega
      simp [h₂,hi,ho]
    · have hi : In i.val = 2 := by omega
      have ho : Out i.val = 2 := by omega
      simp [h₄,hi,ho]
  change (directedWedges Finset.univ R).card +
    (Finset.univ.filter (fun i => G.degree i = 2)).card = 2 * G.edgeFinset.card
  rw [hW,Finset.card_filter,← Finset.sum_add_distrib]
  calc
    _ = ∑ i : I, G.degree i := Finset.sum_congr rfl (fun i _ => hEach i)
    _ = _ := G.sum_degrees_eq_twice_card_edges

#print axioms wedge_count_plus_degree_two
