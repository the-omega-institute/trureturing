/- GID: D5/S3/Factorization/RankThreeBlockAvoidance
   generality: G
   mirror-B: D5/B/S3/Factorization/RankThreeBlockAvoidance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transitive finite linear incidence partitions admit whole-block avoidance. -/

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Tactic

/-! Block avoidance for a finite transitive linear incidence geometry. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.RankThreeBlockAvoidance

/-- The two incidence counts used in the distinct-closure branch cannot hold
when there are at least two blocks and each original block has at least two
points. -/
theorem incidence_count_contradiction {b m d : ℕ}
    (hb : 2 ≤ b) (hm : 2 ≤ m)
    (hB : b * (d - 1) = m - 1)
    (hL : (b + m - 1) * (d - 1) = m - 1) :
    False := by
  have hd : 1 ≤ d := by
    by_contra h
    have : d = 0 := by omega
    subst d
    simp at hB
    omega
  have hbm : b + m - 1 = b + (m - 1) := by omega
  have hsum : b * (d - 1) + (m - 1) * (d - 1) = m - 1 := by
    calc
      b * (d - 1) + (m - 1) * (d - 1) =
          (b + (m - 1)) * (d - 1) := by rw [Nat.add_mul]
      _ = (b + m - 1) * (d - 1) := by rw [hbm]
      _ = m - 1 := hL
  have hzero : (m - 1) * (d - 1) = 0 := by omega
  have hm1 : m - 1 ≠ 0 := by omega
  have hdsubzero : d - 1 = 0 :=
    (Nat.mul_eq_zero.mp hzero).resolve_left hm1
  have hBzero : b * 0 = m - 1 := by simpa [hdsubzero] using hB
  omega


/-- In a point-transitive finite partition, suppose each block has at least two
points and is contained in its assigned closure. Distinct closures have at most
one common point, and not all closures coincide. Then every closure avoids a
whole original block. The hypotheses concern the incidence geometry, rather
than presumed counting equations. -/
theorem exists_block_disjoint_of_transitive_linear_closures
    {G P I : Type*} [Group G] [Fintype P] [Finite I]
    [DecidableEq I]
    [MulAction G P] [MulAction G I] [MulAction.IsPretransitive G P]
    (owner : P → I) (L : I → Finset P)
    (hsize : ∀ i, 2 ≤ (Finset.univ.filter (fun x => owner x = i)).card)
    (hcontain : ∀ x, x ∈ L (owner x))
    (howner : ∀ (g : G) x, owner (g • x) = g • owner x)
    (hline : ∀ (g : G) i x, g • x ∈ L (g • i) ↔ x ∈ L i)
    (hsep : ∀ i j, L i ≠ L j → ∀ x ∈ L i, ∀ y ∈ L i,
      x ∈ L j → y ∈ L j → x = y)
    (hnonconstant : ∃ i j, L i ≠ L j) :
    ∀ i, ∃ j, ∀ x, owner x = j → x ∉ L i := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  have hpoint : ∀ i, ∃ x, owner x = i := by
    intro i
    have hpos : 0 < (Finset.univ.filter (fun x => owner x = i)).card :=
      lt_of_lt_of_le (by decide : 0 < 2) (hsize i)
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    exact ⟨x, (Finset.mem_filter.mp hx).2⟩
  have htrans : ∀ i j : I, ∃ g : G, g • i = j := by
    intro i j
    obtain ⟨x, hx⟩ := hpoint i
    obtain ⟨y, hy⟩ := hpoint j
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
    refine ⟨g, ?_⟩
    calc
      g • i = g • owner x := by rw [hx]
      _ = owner (g • x) := (howner g x).symm
      _ = j := by rw [hg, hy]
  intro i
  by_contra hbad
  push Not at hbad
  have hmeet : ∀ a j, ∃ x, owner x = j ∧ x ∈ L a := by
    intro a j
    obtain ⟨g, hg⟩ := htrans i a
    obtain ⟨x, hx, hxi⟩ := hbad (g⁻¹ • j)
    refine ⟨g • x, ?_, ?_⟩
    · rw [howner, hx, smul_inv_smul]
    · rw [← hg]
      exact (hline g i x).mpr hxi
  -- A repeated closure would give two different original blocks in its fiber.
  -- A different closure meets both, producing two distinct intersection points.
  have hinj : Function.Injective L := by
    intro j k heq
    obtain ⟨a, ha⟩ : ∃ a, L a ≠ L j := by
      obtain ⟨u, v, huv⟩ := hnonconstant
      by_cases hu : L u = L j
      · exact ⟨v, by intro hv; exact huv (hu.trans hv.symm)⟩
      · exact ⟨u, hu⟩
    obtain ⟨x, hx, hxa⟩ := hmeet a j
    obtain ⟨y, hy, hya⟩ := hmeet a k
    have hxj : x ∈ L j := by simpa [hx] using hcontain x
    have hyj : y ∈ L j := by simpa [heq, hy] using hcontain y
    have hxy := hsep a j ha x hxa y hya hxj hyj
    exact hx.symm.trans ((congrArg owner hxy).trans hy)
  have hblock : ∀ a j, a ≠ j →
      ((L a).filter (fun x => owner x = j)).card = 1 := by
    intro a j haj
    obtain ⟨x, hx, hxa⟩ := hmeet a j
    apply Finset.card_eq_one_iff_existsUnique.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨hxa, hx⟩, ?_⟩
    intro y hy
    obtain ⟨hya, hyj⟩ := Finset.mem_filter.mp hy
    exact hsep a j (fun h => haj (hinj h)) y hya x hxa
      (by simpa [hyj] using hcontain y) (by simpa [hx] using hcontain x)
  have hintersection : ∀ a j, a ≠ j →
      ((L a).filter (fun x => x ∈ L j)).card = 1 := by
    intro a j haj
    obtain ⟨x, hx, hxa⟩ := hmeet a j
    have hxj : x ∈ L j := by simpa [hx] using hcontain x
    apply Finset.card_eq_one_iff_existsUnique.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨hxa, hxj⟩, ?_⟩
    intro y hy
    exact hsep a j (fun h => haj (hinj h)) y
      (Finset.mem_filter.mp hy).1 x hxa (Finset.mem_filter.mp hy).2 hxj
  let degree := fun x => (Finset.univ.filter (fun j => x ∈ L j)).card
  have hdegree : ∀ x y, degree x = degree y := by
    intro x y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
    dsimp [degree]
    apply Finset.card_bij (fun j _ => g • j)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [← hg]
      exact (hline g j x).mpr hj
    · intro j _ k _ h
      exact MulAction.injective g h
    · intro j hj
      refine ⟨g⁻¹ • j, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have h := (hline g (g⁻¹ • j) x).mp
      apply h
      simpa [hg] using hj
  obtain ⟨p, hp⟩ := hpoint i
  let d := degree p
  let B := Finset.univ.filter (fun x => owner x = i)
  let b := B.card
  let m := Fintype.card I
  have hm : 2 ≤ m := by
    obtain ⟨u, v, huv⟩ := hnonconstant
    have hcard : 1 < (Finset.univ : Finset I).card :=
      Finset.one_lt_card.mpr ⟨u, Finset.mem_univ _, v, Finset.mem_univ _,
        fun h => huv (congrArg L h)⟩
    simpa only [Finset.card_univ] using Nat.succ_le_of_lt hcard
  have hb : 2 ≤ b := hsize i
  have herase : ∀ x ∈ L i,
      ((Finset.univ.erase i).filter (fun j => x ∈ L j)).card = d - 1 := by
    intro x hx
    have hfilter : (Finset.univ.erase i).filter (fun j => x ∈ L j) =
        (Finset.univ.filter (fun j => x ∈ L j)).erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
      tauto
    rw [hfilter, Finset.card_erase_of_mem (by simp [hx])]
    exact congrArg (fun n => n - 1) (hdegree x p)
  have hself : (L i).filter (fun x => owner x = i) = B := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, B]
    exact ⟨And.right, fun hx => ⟨by simpa [hx] using hcontain x, hx⟩⟩
  have hlength : (L i).card = b + m - 1 := by
    have hf := Finset.card_eq_sum_card_fiberwise
      (s := L i) (t := (Finset.univ : Finset I)) (f := owner) (by simp)
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset I)
      (fun j => ((L i).filter (fun x => owner x = j)).card) (Finset.mem_univ i)
    have hother : ∑ j ∈ (Finset.univ.erase i),
        ((L i).filter (fun x => owner x = j)).card = m - 1 := by
      calc
        _ = ∑ _j ∈ (Finset.univ.erase i), 1 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hblock i j (Finset.mem_erase.mp hj).1.symm
        _ = m - 1 := by simp [m]
    rw [hother, hself] at hsplit
    dsimp [b] at ⊢
    omega
  have countB : b * (d - 1) = m - 1 := by
    have hc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun x j => x ∈ L j) (s := B) (t := Finset.univ.erase i)
    have hleft : (∑ x ∈ B,
        ((Finset.univ.erase i).bipartiteAbove (fun x j => x ∈ L j) x).card) =
        b * (d - 1) := by
      calc
        _ = ∑ _x ∈ B, (d - 1) := by
          apply Finset.sum_congr rfl
          intro x hx
          apply herase
          have hxi := (Finset.mem_filter.mp hx).2
          simpa [hxi] using hcontain x
        _ = b * (d - 1) := by simp [b]
    have hright : (∑ j ∈ (Finset.univ.erase i),
        (B.bipartiteBelow (fun x j => x ∈ L j) j).card) = m - 1 := by
      calc
        _ = ∑ _j ∈ (Finset.univ.erase i), 1 := by
          apply Finset.sum_congr rfl
          intro j hj
          have heq : B.bipartiteBelow (fun x j => x ∈ L j) j =
              (L j).filter (fun x => owner x = i) := by
            ext x
            simp [Finset.bipartiteBelow, B, and_comm]
          rw [heq]
          exact hblock j i (Finset.mem_erase.mp hj).1
        _ = m - 1 := by simp [m]
    omega
  have countL : (b + m - 1) * (d - 1) = m - 1 := by
    have hc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun x j => x ∈ L j) (s := L i) (t := Finset.univ.erase i)
    have hleft : (∑ x ∈ L i,
        ((Finset.univ.erase i).bipartiteAbove (fun x j => x ∈ L j) x).card) =
        (b + m - 1) * (d - 1) := by
      calc
        _ = ∑ _x ∈ L i, (d - 1) := by
          apply Finset.sum_congr rfl
          exact herase
        _ = (b + m - 1) * (d - 1) := by simp [hlength]
    have hright : (∑ j ∈ (Finset.univ.erase i),
        ((L i).bipartiteBelow (fun x j => x ∈ L j) j).card) = m - 1 := by
      calc
        _ = ∑ _j ∈ (Finset.univ.erase i), 1 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hintersection i j (Finset.mem_erase.mp hj).1.symm
        _ = m - 1 := by simp [m]
    omega
  exact incidence_count_contradiction hb hm countB countL

/-- Independence-preserving permutations of the actual ground preserve actual
closure incidence. The ambient type need not equal the ground or be finite. -/
private theorem ground_closure_equivariant
    {α G : Type*} [Group G] (M : Matroid α) [MulAction G M.E]
    (hauto : ∀ (g : G) (S : Set M.E),
      M.Indep (Subtype.val '' ((fun x => g • x) '' S)) ↔
        M.Indep (Subtype.val '' S))
    (g : G) (S : Set M.E) (x : M.E) :
    (g • x).val ∈ M.closure (Subtype.val '' ((fun x => g • x) '' S)) ↔
      x.val ∈ M.closure (Subtype.val '' S) := by
  let N := M.comap (Subtype.val : M.E → α)
  have hmap : N.comap (fun x : M.E => g • x) = N := by
    apply Matroid.ext_indep
    · ext x
      simp [N]
    · intro I _
      simpa only [N, Matroid.comap_indep_iff,
        (MulAction.injective g).injOn, Subtype.val_injective.injOn, and_true] using
        hauto g I
  have hc := congrArg (fun K : Matroid M.E => K.closure S) hmap
  rw [Matroid.comap_closure_eq] at hc
  have hx := Set.ext_iff.mp hc x
  simpa only [N, Matroid.comap_closure_eq, Set.mem_preimage] using hx

/-- A finite simple rank-three matroid with a transitive automorphism action
preserving a partition into rank-two blocks admits whole-original-block
avoidance. `blocks` consists of sets of actual ground elements. `hpartition`
is exactly unique membership, and `hstable` only says that each point-action
image is again an original block; no action on block labels is supplied.
Simplicity is expressed by independence of every ground set of size at most two, and
automorphisms by preservation of independence on the actual ground. -/
theorem exists_original_block_disjoint_closure
    {α G : Type*} [Group G] (M : Matroid α) [Finite M.E]
    [MulAction G M.E] [MulAction.IsPretransitive G M.E]
    (hM : M.eRank = 3)
    (hsimple : ∀ S : Set M.E, S.encard ≤ 2 → M.Indep (Subtype.val '' S))
    (hauto : ∀ (g : G) (S : Set M.E),
      M.Indep (Subtype.val '' ((fun x => g • x) '' S)) ↔
        M.Indep (Subtype.val '' S))
    (blocks : Set (Set M.E))
    (hpartition : ∀ x : M.E, ∃! B : blocks, x ∈ B.val)
    (hstable : ∀ (g : G) (B : blocks), (fun x => g • x) '' B.val ∈ blocks)
    (hrank : ∀ B : blocks, M.eRk (Subtype.val '' B.val) = 2) :
    ∀ B : blocks, ∃ C : blocks,
      Disjoint (Subtype.val '' C.val) (M.closure (Subtype.val '' B.val)) := by
  classical
  letI : Fintype M.E := Fintype.ofFinite M.E
  letI : MulAction G blocks := {
    smul := fun g B => ⟨(fun x => g • x) '' B.val, hstable g B⟩
    one_smul := by
      intro B
      apply Subtype.ext
      change (fun x : M.E => (1 : G) • x) '' B.val = B.val
      simp
    mul_smul := by
      intro g h B
      apply Subtype.ext
      change (fun x : M.E => (g * h) • x) '' B.val =
        (fun x : M.E => g • x) '' ((fun x : M.E => h • x) '' B.val)
      simp only [Set.image_image, mul_smul, Function.comp_def] }
  let owner : M.E → blocks := fun x => (hpartition x).choose
  have hown : ∀ x, x ∈ (owner x).val := fun x => (hpartition x).choose_spec.1
  have howner_iff : ∀ x B, owner x = B ↔ x ∈ B.val := by
    intro x B
    exact ⟨fun h => h ▸ hown x, fun h => ((hpartition x).choose_spec.2 B h).symm⟩
  have howner : ∀ (g : G) x, owner (g • x) = g • owner x := by
    intro g x
    apply (howner_iff _ _).mpr
    exact Set.mem_image_of_mem _ (hown x)
  let L : blocks → Finset M.E := fun B =>
    Finset.univ.filter (fun x => x.val ∈ M.closure (Subtype.val '' B.val))
  have hmem : ∀ B x, x ∈ L B ↔ x.val ∈ M.closure (Subtype.val '' B.val) := by
    intro B x
    simp [L]
  have hsize : ∀ B, 2 ≤ (Finset.univ.filter (fun x => owner x = B)).card := by
    intro B
    have heq : B.val = (↑(Finset.univ.filter (fun x => owner x = B)) : Set M.E) := by
      ext x
      simp [howner_iff]
    have hc := M.eRk_le_encard (Subtype.val '' B.val)
    rw [hrank, Subtype.val_injective.encard_image, heq,
      Set.encard_coe_eq_coe_finsetCard] at hc
    exact_mod_cast hc
  have hcontain : ∀ x, x ∈ L (owner x) := by
    intro x
    apply (hmem _ _).mpr
    apply M.subset_closure _ (by rintro _ ⟨y, _, rfl⟩; exact y.property)
    exact Set.mem_image_of_mem _ (hown x)
  have hline : ∀ (g : G) B x, g • x ∈ L (g • B) ↔ x ∈ L B := by
    intro g B x
    rw [hmem, hmem]
    exact ground_closure_equivariant M hauto g B.val x
  have hsep : ∀ B C, L B ≠ L C → ∀ x ∈ L B, ∀ y ∈ L B,
      x ∈ L C → y ∈ L C → x = y := by
    intro B C hne x hx y hy hxC hyC
    by_contra hxy
    have hval : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    have hpair : M.eRk {x.val, y.val} = 2 := by
      have hi : M.Indep {x.val, y.val} := by
        simpa only [Set.image_pair] using hsimple {x, y}
          (by rw [Set.encard_pair hxy])
      rw [hi.eRk_eq_encard, Set.encard_pair hval]
    have hcl : ∀ D : blocks, x ∈ L D → y ∈ L D →
        M.closure {x.val, y.val} = M.closure (Subtype.val '' D.val) := by
      intro D hxD hyD
      have hsub : {x.val, y.val} ⊆ M.closure (Subtype.val '' D.val) := by
        exact Set.pair_subset ((hmem _ _).mp hxD) ((hmem _ _).mp hyD)
      have he := Matroid.IsRkFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk
        (M.isRkFinite_of_finite (Set.toFinite {x.val, y.val})) hsub
          (by rw [M.eRk_closure_eq, hrank, hpair])
      simpa only [Matroid.closure_closure] using he
    have he := (hcl B hx hy).symm.trans (hcl C hxC hyC)
    apply hne
    ext z
    rw [hmem, hmem, he]
  have hnonconstant : ∃ B C, L B ≠ L C := by
    by_contra hn
    push Not at hn
    have hE : Nonempty M.E := by
      by_contra he
      have hempty : M.E = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact he ⟨⟨x, hx⟩⟩
      have hr := M.eRk_ground
      rw [hempty, Matroid.eRk_empty, hM] at hr
      norm_num at hr
    let x : M.E := Classical.choice hE
    let B := owner x
    have hsub : M.E ⊆ M.closure (Subtype.val '' B.val) := by
      intro y hy
      have hm := hcontain (⟨y, hy⟩ : M.E)
      rw [hn (owner ⟨y, hy⟩) B] at hm
      exact (hmem _ _).mp hm
    have hr := M.eRk_mono hsub
    rw [Matroid.eRk_ground, hM, Matroid.eRk_closure_eq, hrank] at hr
    norm_num at hr
  have hav := exists_block_disjoint_of_transitive_linear_closures owner L
    hsize hcontain howner hline hsep hnonconstant
  intro B
  obtain ⟨C, hC⟩ := hav B
  refine ⟨C, Set.disjoint_left.mpr ?_⟩
  rintro _ ⟨x, hx, rfl⟩ hxl
  exact hC x ((howner_iff x C).mpr hx) ((hmem B x).mpr hxl)

end D5.S3.Factorization.RankThreeBlockAvoidance
