/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Basic]
   utility: none
   digest: Same-layer requests count the external boundary and admit cyclic gap slot bounds. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary
open D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation (gp)
def positiveRequests (n : Nat) [NeZero n] (X : Finset (Bool × Fin n)) : Finset (Bool × Fin n) := X.image (positiveShift n)
def negativeRequests (n : Nat) [NeZero n] (X : Finset (Bool × Fin n)) : Finset (Bool × Fin n) := X.image (negativeShift n)
/-- Both layer requests from selected vertices landing in occupied columns, counted with multiplicity. -/
def I (n : Nat) [NeZero n] (X : Finset (Bool × Fin n)) : Nat :=
  ((positiveRequests n X) ∩ occupiedVertices X).card +
    ((negativeRequests n X) ∩ occupiedVertices X).card
/-- Empty-column vertices requested from both directions in their layer. -/
def K (n : Nat) [NeZero n] (X : Finset (Bool × Fin n)) : Nat :=
  ((positiveRequests n X \ occupiedVertices X) ∩
    (negativeRequests n X \ occupiedVertices X)).card
/-- An empty request destination is counted once in the boundary, and twice with `K`. -/
theorem boundary_request_identity (n : Nat) [NeZero n] (hn : 14 ≤ n)
    (X : Finset (Bool × Fin n)) :
    (externalBoundary n X).card + I n X + K n X =
      2 * (columns X).card + X.card := by
  have hneighbors (q : Nat) [NeZero q] (hq : 14 ≤ q) (v w : Bool × Fin q) :
      (gp q 3).Adj v w ↔
        (if v.1 then w = (false, v.2) ∨ w = (true, v.2 + Fin.ofNat q 3) ∨ w = (true, v.2 - Fin.ofNat q 3)
         else w = (true, v.2) ∨ w = (false, v.2 + Fin.ofNat q 1) ∨ w = (false, v.2 - Fin.ofNat q 1)) := by
    have hstep (k : Nat) (hk : k < q) (hpos : 0 < k) (i : Fin q) :
        i + Fin.ofNat q k ≠ i := by
      intro h
      have hz : (Fin.ofNat q k : Fin q) = 0 := by
        apply add_left_cancel (a := i); simpa using h
      have := congrArg Fin.val hz
      simp [Nat.mod_eq_of_lt hk] at this
      omega
    have hreverse (k : Nat) (x y : Fin q) :
        x = y + Fin.ofNat q k ↔ y = x - Fin.ofNat q k := by
      constructor <;> intro h <;> rw [h] <;> simp
    have hcycle (k : Nat) (hk : k < q) (hpos : 0 < k) (x y : Fin q) :
        (x ≠ y ∧ (y = x + Fin.ofNat q k ∨ x = y + Fin.ofNat q k)) ↔
          y = x + Fin.ofNat q k ∨ y = x - Fin.ofNat q k := by
      rw [← hreverse k x y]
      constructor
      · exact And.right
      · intro h; refine ⟨?_, h⟩
        intro hxy; subst y
        rcases h with h | h <;> exact hstep k hk hpos x h.symm
    rcases v with ⟨vb, vi⟩; rcases w with ⟨wb, wi⟩
    cases vb <;> cases wb
    · simpa [gp, SimpleGraph.fromRel_adj, Fin.ext_iff, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
        using hcycle 1 (by omega) (by omega) vi wi
    · simpa [gp, SimpleGraph.fromRel_adj] using (eq_comm : vi = wi ↔ wi = vi)
    · simp [gp, SimpleGraph.fromRel_adj]
    · simpa [gp, SimpleGraph.fromRel_adj, Fin.ext_iff, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
        using hcycle 3 (by omega) (by omega) vi wi
  have hspoke : occupiedVertices X \ X ⊆ externalBoundary n X := by
    intro v hv
    obtain ⟨hvocc, hvnot⟩ := Finset.mem_sdiff.mp hv
    change v ∈ Finset.univ.product (columns X) at hvocc
    have hcol : v.2 ∈ columns X := (Finset.mem_product.mp hvocc).2
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hcol
    have hfirst : u.1 ≠ v.1 := by
      intro h
      exact hvnot ((Prod.ext h huv) ▸ hu)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hvnot, u, hu, ?_⟩
    unfold gp
    rw [SimpleGraph.fromRel_adj]
    rcases u with ⟨ub, ui⟩
    rcases v with ⟨vb, vi⟩
    cases ub <;> cases vb <;> simp_all
  have hoccupied : (occupiedVertices X \ X).card + X.card =
      2 * (columns X).card := by
    have hsub : X ⊆ occupiedVertices X := by
      intro v hv
      change v ∈ Finset.univ.product (columns X)
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
    have hcard : (occupiedVertices X).card = 2 * (columns X).card := by
      simp [occupiedVertices, Finset.card_product]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard]
    have hXle : X.card ≤ (occupiedVertices X).card := Finset.card_le_card hsub
    omega
  let O := occupiedVertices X
  let P := positiveRequests n X
  let M := negativeRequests n X
  have hboundary : externalBoundary n X \ O = (P \ O) ∪ (M \ O) := by
    ext v
    have hnotX (hvo : v ∉ O) : v ∉ X := by
      intro hv
      apply hvo
      exact Finset.mem_product.mpr
        ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
    constructor
    · intro hv
      have hb := (Finset.mem_sdiff.mp hv).1
      have hvo := (Finset.mem_sdiff.mp hv).2
      obtain ⟨u, hu, huv⟩ := (Finset.mem_filter.mp hb).2.2
      rcases u with ⟨b, i⟩
      cases b
      · rcases (hneighbors n hn (false, i) v).mp huv with hs | hp | hm
        · have : v ∈ O := by
            rw [hs]
            exact Finset.mem_product.mpr
              ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨(false, i), hu, rfl⟩⟩
          exact (hvo this).elim
        · apply Finset.mem_union.mpr
          left
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_image.mpr ⟨(false, i), hu, by simpa [P, positiveRequests,
              positiveShift] using hp.symm⟩, hvo⟩
        · apply Finset.mem_union.mpr
          right
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_image.mpr ⟨(false, i), hu, by simpa [M, negativeRequests,
              negativeShift, positiveShift] using hm.symm⟩, hvo⟩
      · rcases (hneighbors n hn (true, i) v).mp huv with hs | hp | hm
        · have : v ∈ O := by
            rw [hs]
            exact Finset.mem_product.mpr
              ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨(true, i), hu, rfl⟩⟩
          exact (hvo this).elim
        · apply Finset.mem_union.mpr
          left
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_image.mpr ⟨(true, i), hu, by simpa [P, positiveRequests,
              positiveShift] using hp.symm⟩, hvo⟩
        · apply Finset.mem_union.mpr
          right
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_image.mpr ⟨(true, i), hu, by simpa [M, negativeRequests,
              negativeShift, positiveShift] using hm.symm⟩, hvo⟩
    · intro hv
      have hvo : v ∉ O := by
        rcases Finset.mem_union.mp hv with hp | hm
        · exact (Finset.mem_sdiff.mp hp).2
        · exact (Finset.mem_sdiff.mp hm).2
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnotX hvo, ?_⟩, hvo⟩
      rcases Finset.mem_union.mp hv with hp | hm
      · obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hp).1
        refine ⟨u, hu, ?_⟩
        rw [← heq]
        rcases u with ⟨b, i⟩
        apply (hneighbors n hn _ _).2
        cases b <;> simp [positiveShift]
      · obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hm).1
        refine ⟨u, hu, ?_⟩
        rw [← heq]
        rcases u with ⟨b, i⟩
        apply (hneighbors n hn _ _).2
        cases b <;> simp [negativeShift, positiveShift]
  have hplus : P.card = X.card := Finset.card_image_iff.mpr (positiveShift n).injective.injOn
  have hminus : M.card = X.card := Finset.card_image_iff.mpr (negativeShift n).injective.injOn
  have hp := Finset.card_sdiff_add_card_inter P O
  have hm := Finset.card_sdiff_add_card_inter M O
  have hu := Finset.card_union_add_card_inter (P \ O) (M \ O)
  have hocc : externalBoundary n X ∩ O = O \ X := by
    ext v; simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hv, hvo⟩
      exact ⟨hvo, (Finset.mem_filter.mp hv).2.1⟩
    · intro hv
      exact ⟨hspoke (Finset.mem_sdiff.mpr hv), hv.1⟩
  have hb := Finset.card_sdiff_add_card_inter (externalBoundary n X) O
  rw [hocc] at hb
  have ho := hoccupied
  change P.card = X.card at hplus
  change M.card = X.card at hminus
  change (externalBoundary n X \ O).card + (O \ X).card =
    (externalBoundary n X).card at hb
  change (O \ X).card + X.card = 2 * (columns X).card at ho
  rw [← hboundary] at hu
  change (externalBoundary n X).card +
      ((P ∩ O).card + (M ∩ O).card) +
      ((P \ O) ∩ (M \ O)).card = 2 * (columns X).card + X.card
  omega
def sortedColumn {n : Nat} (C : Finset (Fin n)) : Fin C.card → Fin n := C.orderEmbOfFin rfl
def extendedColumn {n : Nat} (C : Finset (Fin n)) (i : Nat) : Nat := if hi : i < C.card then (sortedColumn C ⟨i, hi⟩).val else n
/-- The cyclic difference following the `i`th occupied column. -/
def gapWord {n : Nat} (C : Finset (Fin n)) (i : Fin C.card) : Nat :=
  extendedColumn C (i.val + 1) - extendedColumn C i.val + if i.val + 1 = C.card then extendedColumn C 0 else 0
/-- A directional slot scores immediate support or support at twice the layer step. -/
private def directionSlot {n : Nat} (C : Finset (Fin n))
    (e : Bool × Fin n ≃ Bool × Fin n) (v : Bool × Fin n) : Nat :=
  if (e v).2 ∈ C then 2 else if (e (e v)).2 ∈ C then 1 else 0
/-- The top-ten sum as a supremum over ten-element layer subsets. -/
private def geometricT (n : Nat) [NeZero n] (C : Finset (Fin n)) : Nat :=
  ((Finset.univ.product C).powersetCard 10).sup fun Y =>
    ∑ v ∈ Y,
      (directionSlot C (positiveShift n) v + directionSlot C (negativeShift n) v)
/-- Occupied requests give two source units; collisions give one at each source. -/
private theorem geometric_slot_domination (n : Nat) [NeZero n]
    (X : Finset (Bool × Fin n)) (hX : X.card = 10) :
    2 * (I n X + K n X) ≤ geometricT n (columns X) := by
  let C := columns X
  let O := occupiedVertices X
  let P := positiveRequests n X
  let M := negativeRequests n X
  let F := positiveShift n
  let G := negativeShift n
  have hcount (e : Bool × Fin n ≃ Bool × Fin n) (S : Finset (Bool × Fin n)) :
      (X.filter fun x => e x ∈ S).card = (X.image e ∩ S).card := by
    have himage : (X.filter fun x => e x ∈ S).image e = X.image e ∩ S := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
      constructor
      · rintro ⟨x, ⟨hx, hxs⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, hxs⟩
      · rintro ⟨⟨x, hx, rfl⟩, hxs⟩
        exact ⟨x, ⟨hx, hxs⟩, rfl⟩
    rw [← himage]
    exact (Finset.card_image_iff.mpr e.injective.injOn).symm
  have hIp : (X.filter fun x => (F x).2 ∈ C).card = (P ∩ O).card := by
    have h := hcount F O
    change (X.filter fun x => F x ∈ O).card = (P ∩ O).card at h
    simpa [O, occupiedVertices, C] using h
  have hIm : (X.filter fun x => (G x).2 ∈ C).card = (M ∩ O).card := by
    have h := hcount G O
    change (X.filter fun x => G x ∈ O).card = (M ∩ O).card at h
    simpa [O, occupiedVertices, C] using h
  have hKp : (X.filter fun x => F x ∈ M \ O).card = K n X := by
    have h := hcount F (M \ O)
    have heq : X.image F ∩ (M \ O) = (P \ O) ∩ (M \ O) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      change (v ∈ P ∧ v ∈ M ∧ v ∉ O) ↔
        (v ∈ P ∧ v ∉ O) ∧ v ∈ M ∧ v ∉ O
      tauto
    rw [heq] at h
    exact h
  have hKm : (X.filter fun x => G x ∈ P \ O).card = K n X := by
    have h := hcount G (P \ O)
    have heq : X.image G ∩ (P \ O) = (P \ O) ∩ (M \ O) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      change (v ∈ M ∧ v ∈ P ∧ v ∉ O) ↔
        (v ∈ P ∧ v ∉ O) ∧ v ∈ M ∧ v ∉ O
      tauto
    rw [heq] at h
    exact h
  have hlocal (e : Bool × Fin n ≃ Bool × Fin n)
      (x : Bool × Fin n) (hx : x ∈ X) :
      2 * (if (e x).2 ∈ C then 1 else 0) +
          (if e x ∈ X.image e.symm \ O then 1 else 0) ≤
        directionSlot C e x := by
    by_cases hcol : (e x).2 ∈ C
    · have heo : e x ∈ O := by
        exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hcol⟩
      have hnoc : e x ∉ X.image e.symm \ O := by
        intro h
        exact (Finset.mem_sdiff.mp h).2 heo
      simp [directionSlot, hcol, hnoc]
    · by_cases hcollision : e x ∈ X.image e.symm \ O
      · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hcollision).1
        have hy2 : y = e (e x) := by
          have h := congrArg e hyx
          simpa using h
        have hsecond : (e (e x)).2 ∈ C :=
          Finset.mem_image.mpr ⟨y, hy, congrArg Prod.snd hy2⟩
        simp [directionSlot, hcol, hcollision, hsecond]
      · simp [directionSlot, hcol, hcollision]
  have hp : 2 * (P ∩ O).card + K n X ≤ ∑ x ∈ X, directionSlot C F x := by
    have h := Finset.sum_le_sum (fun x hx => hlocal F x hx)
    have hFG : X.image F.symm = M := rfl
    rw [hFG] at h
    have hpre :
        (∑ x ∈ X,
          (2 * (if (F x).2 ∈ C then 1 else 0) +
            (if F x ∈ M \ O then 1 else 0))) =
          2 * (P ∩ O).card + K n X := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_boole, hIp]
      rw [hKp]
      simp
    rw [hpre] at h
    exact h
  have hm : 2 * (M ∩ O).card + K n X ≤ ∑ x ∈ X, directionSlot C G x := by
    have h := Finset.sum_le_sum (fun x hx => hlocal G x hx)
    have hGF : X.image G.symm = P := rfl
    rw [hGF] at h
    have hpre :
        (∑ x ∈ X,
          (2 * (if (G x).2 ∈ C then 1 else 0) +
            (if G x ∈ P \ O then 1 else 0))) =
          2 * (M ∩ O).card + K n X := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_boole, hIm]
      rw [hKm]
      simp
    rw [hpre] at h
    exact h
  have hsub : X ⊆ Finset.univ.product C := by
    intro x hx
    exact Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have htop :
      (∑ v ∈ X, (directionSlot C F v + directionSlot C G v)) ≤ geometricT n C := by
    exact Finset.le_sup
      (f := fun Y : Finset (Bool × Fin n) =>
        ∑ v ∈ Y, (directionSlot C F v + directionSlot C G v))
      (Finset.mem_powersetCard.mpr ⟨hsub, hX⟩)
  rw [Finset.sum_add_distrib] at htop
  dsimp [I, C, O, P, M, F, G] at hp hm htop ⊢
  omega
def phi (h : Nat) : Nat := if h = 1 then 2 else if h = 2 then 1 else 0
def cyclicIndex {c : Nat} (i : Fin c) (j : Nat) : Fin c := ⟨(i.val + j) % c, Nat.mod_lt _ (by exact Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩
def positivePrefix {c : Nat} (h : Fin c → Nat) (i : Fin c) (k : Nat) : Nat := ∑ j ∈ Finset.range k, h (cyclicIndex i j)
def negativePrefix {c : Nat} (h : Fin c → Nat) (i : Fin c) (k : Nat) : Nat := ∑ j ∈ Finset.range k, h (cyclicIndex i (c - (j + 1)))
/-- A direction scores two if a prefix reaches three, otherwise one if it reaches six. -/
noncomputable def prefixScore {c : Nat} (h : Fin c → Nat) (i : Fin c)
    (sums : (Fin c → Nat) → Fin c → Nat → Nat) : Nat := by
  classical
  exact if ∃ k ∈ Finset.Icc 1 c, sums h i k = 3 then 2
    else if ∃ k ∈ Finset.Icc 1 c, sums h i k = 6 then 1 else 0
/-- Outer slot from the adjacent cyclic gaps. -/
def A {c : Nat} (h : Fin c → Nat) (i : Fin c) : Nat := phi (h (cyclicIndex i (c - 1))) + phi (h i)
/-- Inner slot from the positive and negative prefix scans. -/
noncomputable def B {c : Nat} (h : Fin c → Nat) (i : Fin c) : Nat := prefixScore h i positivePrefix + prefixScore h i negativePrefix
/-- The ten largest entries of the `2c` outer and inner slots. -/
noncomputable def T {c : Nat} (h : Fin c → Nat) : Nat := by
  classical
  exact (Finset.univ : Finset (Bool × Fin c)).powersetCard 10 |>.sup fun Y =>
    ∑ v ∈ Y, (if v.1 then B h v.2 else A h v.2)
def liftedColumn {n : Nat} (C : Finset (Fin n)) (i : Fin C.card) (k : Nat) : Nat :=
  if i.val + k < C.card then extendedColumn C (i.val + k) else n + extendedColumn C (i.val + k - C.card)
/-- A gap word entry is the increment of the unwrapped sorted support sequence. -/
private theorem gapWord_lifted_step {n : Nat} (C : Finset (Fin n))
    (i : Fin C.card) (k : Nat) (hk : k < C.card) :
    gapWord C (cyclicIndex i k) =
      liftedColumn C i (k + 1) - liftedColumn C i k := by
  have hmono : Monotone (extendedColumn C) := by
    intro a b hab
    by_cases ha : a < C.card
    · by_cases hb : b < C.card
      · simp only [extendedColumn, dif_pos ha, dif_pos hb]
        exact Fin.val_le_of_le ((C.orderEmbOfFin rfl).monotone
          (Fin.mk_le_mk.mpr hab))
      · simp only [extendedColumn, dif_pos ha, dif_neg hb]
        exact (sortedColumn C ⟨a, ha⟩).isLt.le
    · have hb : ¬ b < C.card := by omega
      simp [extendedColumn, ha, hb]
  let f := extendedColumn C
  let j := i.val + k
  have hi : i.val < C.card := i.isLt
  have hj : j < 2 * C.card := by dsimp [j]; omega
  have hjv : (cyclicIndex i k).val =
      if i.val + k < C.card then i.val + k else i.val + k - C.card := by
    unfold cyclicIndex
    by_cases h : i.val + k < C.card
    · simp [h, Nat.mod_eq_of_lt h]
    · have hlt : i.val + k - C.card < C.card := by omega
      simp only [if_neg h]
      rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt h), Nat.mod_eq_of_lt hlt]
  by_cases hbefore : j + 1 < C.card
  · have hj0 : j < C.card := by omega
    have hidx : (cyclicIndex i k).val = j := by simpa [j, hj0] using hjv
    have hne : j + 1 ≠ C.card := by omega
    have hj1 : i.val + (k + 1) = j + 1 := by dsimp [j]; omega
    simp [gapWord, liftedColumn, hidx, hne, hj0, hbefore, hj1, j]
  · by_cases hcross : j < C.card
    · have heq : j + 1 = C.card := by omega
      have hidx : (cyclicIndex i k).val = j := by simpa [j, hcross] using hjv
      have hfirst : f j ≤ n := by
        have := hmono (show j ≤ C.card by omega)
        simpa [f, extendedColumn] using this
      have hj1 : i.val + (k + 1) = C.card := by dsimp [j] at heq; omega
      have hzero : i.val + (k + 1) - C.card = 0 := by omega
      have hbase : n - f j + f 0 = n + f 0 - f j := by omega
      simpa [gapWord, liftedColumn, hidx, heq, hj1, hzero, hcross, j, f,
        extendedColumn] using hbase
    · have hrem : j - C.card + 1 < C.card := by omega
      have hidx : (cyclicIndex i k).val = j - C.card := by
        simpa [j, hcross] using hjv
      have hbefore0 : ¬ i.val + k < C.card := by simpa [j] using hcross
      have hbefore1 : ¬ i.val + (k + 1) < C.card := by omega
      have hne : j - C.card + 1 ≠ C.card := by omega
      have hr1 : i.val + (k + 1) - C.card = j - C.card + 1 := by dsimp [j]; omega
      have hle := hmono
        (show j - C.card ≤ j - C.card + 1 by omega)
      have hbase : f (j - C.card + 1) - f (j - C.card) =
          (n + f (j - C.card + 1)) - (n + f (j - C.card)) := by omega
      simpa [gapWord, liftedColumn, hidx, hbefore0, hbefore1, hne, hr1, j,
        f] using hbase
/-- A positive prefix is the unwrapped displacement to a later occupied column. -/
theorem positivePrefix_lifted {n : Nat} (C : Finset (Fin n))
    (i : Fin C.card) (k : Nat) (hk : k ≤ C.card) :
    positivePrefix (gapWord C) i k =
      liftedColumn C i k - liftedColumn C i 0 := by
  have hpositive (j : Fin C.card) : 0 < gapWord C j := by
    have hi : j.val < C.card := j.isLt
    have hlt : extendedColumn C j.val < extendedColumn C (j.val + 1) := by
      by_cases hj : j.val + 1 < C.card
      · simp only [extendedColumn, dif_pos hi, dif_pos hj]
        exact Fin.lt_def.mp ((C.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (by omega)))
      · have heq : j.val + 1 = C.card := by omega
        simp only [extendedColumn, dif_pos hi, dif_neg hj]
        exact (sortedColumn C ⟨j.val, hi⟩).isLt
    unfold gapWord; omega
  have hstep (j : Nat) (hj : j < C.card) :
      liftedColumn C i j < liftedColumn C i (j + 1) := by
    have hgap := hpositive (cyclicIndex i j)
    rw [gapWord_lifted_step C i j hj] at hgap
    omega
  have hstart (j : Nat) (hj : j ≤ C.card) :
      liftedColumn C i 0 ≤ liftedColumn C i j := by
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
        have hjlt : j < C.card := by omega
        exact (ih (by omega)).trans (hstep j hjlt).le
  induction k with
  | zero => simp [positivePrefix]
  | succ k ih =>
      have hklt : k < C.card := by omega
      have hprev := ih (by omega)
      have hle := hstart k (by omega)
      have hnext := hstep k hklt
      rw [positivePrefix, Finset.sum_range_succ]
      change positivePrefix (gapWord C) i k + gapWord C (cyclicIndex i k) =
        liftedColumn C i (k + 1) - liftedColumn C i 0
      rw [hprev, gapWord_lifted_step C i k hklt]
      omega
/-- A selected column at positive displacement is reached by a cyclic gap prefix. -/
theorem positive_request_prefix {n : Nat} [NeZero n] (C : Finset (Fin n))
    (i : Fin C.card) (d : Nat) (hd0 : 0 < d) (hdn : d < n)
    (ht : sortedColumn C i + Fin.ofNat n d ∈ C) :
    ∃ k ∈ Finset.Icc 1 C.card,
      positivePrefix (gapWord C) i k = d := by
  let p := sortedColumn C i
  let t := p + Fin.ofNat n d
  let o := C.orderIsoOfFin rfl
  let j : Fin C.card := o.symm ⟨t, ht⟩
  have hj : sortedColumn C j = t := by
    change (o j).val = t; exact congrArg Subtype.val (o.apply_symm_apply ⟨t, ht⟩)
  have hval : t.val = (p.val + d) % n := by
    simp [t, Fin.val_add, Fin.val_ofNat, Nat.mod_eq_of_lt hdn, Nat.add_mod_mod]
  have hp0 : liftedColumn C i 0 = p.val := by simp [liftedColumn, extendedColumn, p, i.isLt]
  have hp_lt : p.val < n := p.isLt
  have ht_lt : t.val < n := t.isLt
  by_cases hnowrap : p.val + d < n
  · have htv : t.val = p.val + d := by rw [hval, Nat.mod_eq_of_lt hnowrap]
    have hij : i.val < j.val := by
      by_contra h
      have hji : j ≤ i := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt h)
      have hcols : (sortedColumn C j).val ≤ (sortedColumn C i).val :=
        Fin.val_le_of_le ((C.orderEmbOfFin rfl).monotone hji)
      have hcontra : t.val ≤ p.val := by simpa [p, hj] using hcols
      omega
    let k := j.val - i.val
    have hk0 : 1 ≤ k := by dsimp [k]; omega
    have hkc : k ≤ C.card := by dsimp [k]; omega
    have hik : i.val + k = j.val := by dsimp [k]; omega
    have hpk : liftedColumn C i k = t.val := by simp [liftedColumn, extendedColumn, hik, j.isLt, hj]
    refine ⟨k, Finset.mem_Icc.mpr ⟨hk0, hkc⟩, ?_⟩
    rw [positivePrefix_lifted C i k hkc, hp0, hpk]; omega
  · have hsum : p.val + d < 2 * n := by omega
    have htv : t.val = p.val + d - n := by
      rw [hval, Nat.mod_eq_sub_mod (Nat.le_of_not_gt hnowrap)]
      exact Nat.mod_eq_of_lt (by omega)
    have hji : j.val < i.val := by
      by_contra h
      have hij : i ≤ j := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt h)
      have hcols : (sortedColumn C i).val ≤ (sortedColumn C j).val :=
        Fin.val_le_of_le ((C.orderEmbOfFin rfl).monotone hij)
      have hcontra : p.val ≤ t.val := by simpa [p, hj] using hcols
      omega
    let k := C.card - i.val + j.val
    have hk0 : 1 ≤ k := by dsimp [k]; omega
    have hkc : k ≤ C.card := by dsimp [k]; omega
    have hik : i.val + k = C.card + j.val := by dsimp [k]; omega
    have hpk : liftedColumn C i k = n + t.val := by
      simp [liftedColumn, extendedColumn, hik, j.isLt, hj]
    refine ⟨k, Finset.mem_Icc.mpr ⟨hk0, hkc⟩, ?_⟩
    rw [positivePrefix_lifted C i k hkc, hp0, hpk]; omega
/-- A short positive prefix ends at the selected column reached by that displacement. -/
theorem positivePrefix_endpoint {n : Nat} [NeZero n] (C : Finset (Fin n))
    (i : Fin C.card) (k d : Nat) (hk0 : 1 ≤ k) (hkc : k ≤ C.card)
    (hdn : d < n) (hprefix : positivePrefix (gapWord C) i k = d) :
    sortedColumn C (cyclicIndex i k) = sortedColumn C i + Fin.ofNat n d := by
  let p := sortedColumn C i
  let q := sortedColumn C (cyclicIndex i k)
  have hklt : k < C.card := by
    by_contra h
    have heq : k = C.card := by omega
    have hfull : positivePrefix (gapWord C) i C.card = n := by
      have hs : liftedColumn C i 0 = (sortedColumn C i).val := by
        simp [liftedColumn, extendedColumn, i.isLt]
      have he : liftedColumn C i C.card = n + (sortedColumn C i).val := by
        simp [liftedColumn, extendedColumn, i.isLt]
      rw [positivePrefix_lifted C i C.card le_rfl, hs, he]; omega
    rw [heq, hfull] at hprefix
    omega
  have hstart : liftedColumn C i 0 = p.val := by simp [liftedColumn, extendedColumn, p, i.isLt]
  have hdisp := positivePrefix_lifted C i k hkc
  rw [hprefix, hstart] at hdisp
  have hqidx : (cyclicIndex i k).val =
      if i.val + k < C.card then i.val + k else i.val + k - C.card := by
    unfold cyclicIndex
    by_cases h : i.val + k < C.card
    · simp [h, Nat.mod_eq_of_lt h]
    · have hlt : i.val + k - C.card < C.card := by omega
      simp only [if_neg h]
      rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt h), Nat.mod_eq_of_lt hlt]
  have htarget : (p + Fin.ofNat n d).val = (p.val + d) % n := by
    simp [Fin.val_add, Fin.val_ofNat, Nat.mod_eq_of_lt hdn]
  apply Fin.ext
  rw [htarget]
  by_cases hnowrap : i.val + k < C.card
  · have hq : q.val = liftedColumn C i k := by
      have hidx : (cyclicIndex i k).val = i.val + k := by
        simpa [hnowrap] using hqidx
      have hfin : cyclicIndex i k = (⟨i.val + k, hnowrap⟩ : Fin C.card) :=
        Fin.ext hidx
      change (sortedColumn C (cyclicIndex i k)).val = liftedColumn C i k
      rw [hfin]
      simp [q, liftedColumn, extendedColumn, hnowrap]
    have hcol : p.val < q.val := by
      have hidx : i < cyclicIndex i k :=
        Fin.lt_iff_val_lt_val.mpr (by
          have := hqidx
          simp [hnowrap] at this
          omega)
      exact Fin.lt_def.mp ((C.orderEmbOfFin rfl).strictMono hidx)
    have hlt : p.val + d < n := by
      have hq_lt : q.val < n := q.isLt
      omega
    rw [Nat.mod_eq_of_lt hlt]; omega
  · have hq : n + q.val = liftedColumn C i k := by
      have hidx : (cyclicIndex i k).val = i.val + k - C.card := by
        simpa [hnowrap] using hqidx
      have hrem : i.val + k - C.card < C.card := by omega
      have hfin : cyclicIndex i k =
          (⟨i.val + k - C.card, hrem⟩ : Fin C.card) := Fin.ext hidx
      change n + (sortedColumn C (cyclicIndex i k)).val = liftedColumn C i k
      rw [hfin]
      simp [q, liftedColumn, extendedColumn, hnowrap, hrem]
    have hsum : n ≤ p.val + d := by omega
    have hlt : p.val + d - n < n := by
      have hq_lt : q.val < n := q.isLt
      omega
    rw [Nat.mod_eq_sub_mod hsum, Nat.mod_eq_of_lt hlt]; omega
/-- A selected column at negative displacement is reached by a reverse gap prefix. -/
private theorem negative_request_prefix {n : Nat} [NeZero n] (C : Finset (Fin n))
    (i : Fin C.card) (d : Nat) (hd0 : 0 < d) (hdn : d < n)
    (ht : sortedColumn C i - Fin.ofNat n d ∈ C) :
    ∃ k ∈ Finset.Icc 1 C.card,
      negativePrefix (gapWord C) i k = d := by
  letI : NeZero C.card := ⟨by have := i.isLt; omega⟩
  let t := sortedColumn C i - Fin.ofNat n d
  let o := C.orderIsoOfFin rfl
  let j : Fin C.card := o.symm ⟨t, ht⟩
  have hj : sortedColumn C j = t := by
    change (o j).val = t; exact congrArg Subtype.val (o.apply_symm_apply ⟨t, ht⟩)
  have hplus : sortedColumn C j + Fin.ofNat n d = sortedColumn C i := by
    rw [hj]; simp [t]
  have hmem : sortedColumn C j + Fin.ofNat n d ∈ C := by
    rw [hplus]; exact C.orderEmbOfFin_mem rfl i
  obtain ⟨k, hk, hpre⟩ := positive_request_prefix C j d hd0 hdn hmem
  have hkpair := Finset.mem_Icc.mp hk
  have hend := positivePrefix_endpoint C j k d hkpair.1 hkpair.2 hdn hpre
  rw [hplus] at hend
  have hidx : cyclicIndex j k = i := (C.orderEmbOfFin rfl).injective hend
  have hcyc (a : Fin C.card) (m : Nat) :
      cyclicIndex a m = a + Fin.ofNat C.card m := by
    apply Fin.ext
    change (a.val + m) % C.card = (a.val + m % C.card) % C.card
    rw [Nat.add_mod_mod]
  have hcand : cyclicIndex (cyclicIndex i (C.card - k)) k = i := by
    apply Fin.ext
    change ((i.val + (C.card - k)) % C.card + k) % C.card = i.val
    rw [Nat.mod_add_mod]
    have hsum : C.card - k + k = C.card := Nat.sub_add_cancel hkpair.2
    rw [Nat.add_assoc, hsum]
    simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  have hback : j = cyclicIndex i (C.card - k) := by
    have h : j + Fin.ofNat C.card k =
        cyclicIndex i (C.card - k) + Fin.ofNat C.card k := by
      simpa only [hcyc] using hidx.trans hcand.symm
    exact add_right_cancel h
  refine ⟨k, hk, ?_⟩
  have hreverse (k : Nat) (hk : k ≤ C.card) :
      negativePrefix (gapWord C) i k =
        positivePrefix (gapWord C) (cyclicIndex i (C.card - k)) k := by
    unfold negativePrefix positivePrefix
    rw [← Finset.sum_range_reflect
      (fun j => gapWord C (cyclicIndex (cyclicIndex i (C.card - k)) j)) k]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Fin.ext
    change (i.val + (C.card - (j + 1))) % C.card =
      ((i.val + (C.card - k)) % C.card + (k - 1 - j)) % C.card
    rw [Nat.mod_add_mod]
    congr 1
    have hjlt : j < k := Finset.mem_range.mp hj
    omega
  rw [hreverse k hkpair.2, ← hback]
  exact hpre
/-- The geometric outer-forward score is bounded by its literal gap score. -/
private theorem outer_forward_slot_le_phi (n : Nat) [NeZero n] (hn : 14 ≤ n)
    (C : Finset (Fin n)) (i : Fin C.card) :
    directionSlot C (positiveShift n) (false, sortedColumn C i) ≤
      phi (gapWord C i) := by
  have hpositive (j : Fin C.card) : 0 < gapWord C j := by
    have hi : j.val < C.card := j.isLt
    have hlt : extendedColumn C j.val < extendedColumn C (j.val + 1) := by
      by_cases hj : j.val + 1 < C.card
      · simp only [extendedColumn, dif_pos hi, dif_pos hj]
        exact Fin.lt_def.mp ((C.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (by omega)))
      · have heq : j.val + 1 = C.card := by omega
        simp only [extendedColumn, dif_pos hi, dif_neg hj]
        exact (sortedColumn C ⟨j.val, hi⟩).isLt
    unfold gapWord; omega
  let p := sortedColumn C i
  let h := gapWord C i
  have first_le_positivePrefix (k : Nat) (hk : 1 ≤ k) :
      h ≤ positivePrefix (gapWord C) i k := by
    have hs : ({0} : Finset Nat) ⊆ Finset.range k := by
      intro x hx; simp only [Finset.mem_singleton] at hx
      subst x; exact Finset.mem_range.mpr hk
    have hb := Finset.sum_le_sum_of_subset
      (f := fun j => gapWord C (cyclicIndex i j)) hs
    have hz : cyclicIndex i 0 = i := by
      apply Fin.ext
      change (i.val + 0) % C.card = i.val
      simp [Nat.mod_eq_of_lt i.isLt]
    simpa [positivePrefix, hz, h] using hb
  have h2 : (positiveShift n (positiveShift n (false, p))).2 =
      p + Fin.ofNat n 2 := by
    change p + Fin.ofNat n 1 + Fin.ofNat n 1 = p + Fin.ofNat n 2
    apply Fin.ext
    simp [Fin.val_add, Fin.val_ofNat,
      Nat.mod_eq_of_lt (show 1 < n by omega),
      Nat.mod_eq_of_lt (show 2 < n by omega), Nat.mod_add_mod, Nat.add_assoc]
  have hfirst : p + Fin.ofNat n 1 ∈ C → h = 1 := by
    intro hp
    obtain ⟨k, hk, heq⟩ := positive_request_prefix C i 1 (by omega) (by omega) hp
    have hle := first_le_positivePrefix k (Finset.mem_Icc.mp hk).1
    have hpos := hpositive i
    dsimp [h] at *; omega
  have hsecond : p + Fin.ofNat n 2 ∈ C → h ≤ 2 := by
    intro hp
    obtain ⟨k, hk, heq⟩ := positive_request_prefix C i 2 (by omega) (by omega) hp
    have hle := first_le_positivePrefix k (Finset.mem_Icc.mp hk).1
    dsimp [h] at *; omega
  have honly : h = 1 → p + Fin.ofNat n 1 ∈ C := by
    intro hh
    have hz : cyclicIndex i 0 = i := by
      apply Fin.ext
      change (i.val + 0) % C.card = i.val
      simp [Nat.mod_eq_of_lt i.isLt]
    have hpref : positivePrefix (gapWord C) i 1 = 1 := by
      simpa [positivePrefix, hz, h] using hh
    have hend := positivePrefix_endpoint C i 1 1 (by omega)
      (by have := i.isLt; omega) (by omega) hpref
    rw [← hend]
    exact C.orderEmbOfFin_mem rfl (cyclicIndex i 1)
  unfold directionSlot; rw [h2]
  change (if p + Fin.ofNat n 1 ∈ C then 2
      else if p + Fin.ofNat n 2 ∈ C then 1 else 0) ≤ phi h
  by_cases hp1 : p + Fin.ofNat n 1 ∈ C
  · have hh := hfirst hp1
    rw [if_pos hp1]; simp [phi, hh]
  · by_cases hp2 : p + Fin.ofNat n 2 ∈ C
    · have hle := hsecond hp2
      have hpos : 0 < h := hpositive i
      have hne : h ≠ 1 := fun hh => hp1 (honly hh)
      have hh : h = 2 := by omega
      rw [if_neg hp1, if_pos hp2]; simp [phi, hh]
    · rw [if_neg hp1, if_neg hp2]; exact Nat.zero_le _
private theorem negativePrefix_endpoint {n : Nat} [NeZero n] (C : Finset (Fin n))
    (i : Fin C.card) (k d : Nat) (hk0 : 1 ≤ k) (hkc : k ≤ C.card)
    (hdn : d < n) (hprefix : negativePrefix (gapWord C) i k = d) :
    sortedColumn C (cyclicIndex i (C.card - k)) =
      sortedColumn C i - Fin.ofNat n d := by
  have hreverse (k : Nat) (hk : k ≤ C.card) :
      negativePrefix (gapWord C) i k =
        positivePrefix (gapWord C) (cyclicIndex i (C.card - k)) k := by
    unfold negativePrefix positivePrefix
    rw [← Finset.sum_range_reflect
      (fun j => gapWord C (cyclicIndex (cyclicIndex i (C.card - k)) j)) k]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Fin.ext
    change (i.val + (C.card - (j + 1))) % C.card =
      ((i.val + (C.card - k)) % C.card + (k - 1 - j)) % C.card
    rw [Nat.mod_add_mod]
    congr 1
    have hjlt : j < k := Finset.mem_range.mp hj
    omega
  have hp := hreverse k hkc
  rw [hp] at hprefix
  have hend := positivePrefix_endpoint C (cyclicIndex i (C.card - k)) k d
    hk0 hkc hdn hprefix
  have hidx : cyclicIndex (cyclicIndex i (C.card - k)) k = i := by
    apply Fin.ext
    change ((i.val + (C.card - k)) % C.card + k) % C.card = i.val
    rw [Nat.mod_add_mod, Nat.add_assoc, Nat.sub_add_cancel hkc]
    simp [Nat.mod_eq_of_lt i.isLt]
  rw [hidx] at hend
  calc
    sortedColumn C (cyclicIndex i (C.card - k)) =
        (sortedColumn C (cyclicIndex i (C.card - k)) + Fin.ofNat n d) -
          Fin.ofNat n d := by simp
    _ = sortedColumn C i - Fin.ofNat n d := by rw [hend]
/-- The geometric outer-backward score is bounded by the preceding gap score. -/
private theorem outer_backward_slot_le_phi (n : Nat) [NeZero n] (hn : 14 ≤ n)
    (C : Finset (Fin n)) (i : Fin C.card) :
    directionSlot C (negativeShift n) (false, sortedColumn C i) ≤
      phi (gapWord C (cyclicIndex i (C.card - 1))) := by
  have hpositive (j : Fin C.card) : 0 < gapWord C j := by
    have hi : j.val < C.card := j.isLt
    have hlt : extendedColumn C j.val < extendedColumn C (j.val + 1) := by
      by_cases hj : j.val + 1 < C.card
      · simp only [extendedColumn, dif_pos hi, dif_pos hj]
        exact Fin.lt_def.mp ((C.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (by omega)))
      · have heq : j.val + 1 = C.card := by omega
        simp only [extendedColumn, dif_pos hi, dif_neg hj]
        exact (sortedColumn C ⟨j.val, hi⟩).isLt
    unfold gapWord; omega
  let p := sortedColumn C i
  let h := gapWord C (cyclicIndex i (C.card - 1))
  have first_le_negativePrefix (k : Nat) (hk : 1 ≤ k) :
      h ≤ negativePrefix (gapWord C) i k := by
    have hs : ({0} : Finset Nat) ⊆ Finset.range k := by
      intro x hx; simp only [Finset.mem_singleton] at hx
      subst x; exact Finset.mem_range.mpr hk
    have hb := Finset.sum_le_sum_of_subset
      (f := fun j => gapWord C (cyclicIndex i (C.card - (j + 1)))) hs
    simpa [negativePrefix, h] using hb
  have h2 : (negativeShift n (negativeShift n (false, p))).2 =
      p - Fin.ofNat n 2 := by
    change p - Fin.ofNat n 1 - Fin.ofNat n 1 = p - Fin.ofNat n 2
    have hh : (Fin.ofNat n 1 : Fin n) + Fin.ofNat n 1 = Fin.ofNat n 2 := by
      apply Fin.ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < n by omega),
        Nat.mod_eq_of_lt (show 2 < n by omega)]
    rw [sub_sub, hh]
  have hfirst : p - Fin.ofNat n 1 ∈ C → h = 1 := by
    intro hp
    obtain ⟨k, hk, heq⟩ := negative_request_prefix C i 1 (by omega) (by omega) hp
    have hle := first_le_negativePrefix k (Finset.mem_Icc.mp hk).1
    have hpos := hpositive (cyclicIndex i (C.card - 1))
    dsimp [h] at *; omega
  have hsecond : p - Fin.ofNat n 2 ∈ C → h ≤ 2 := by
    intro hp
    obtain ⟨k, hk, heq⟩ := negative_request_prefix C i 2 (by omega) (by omega) hp
    have hle := first_le_negativePrefix k (Finset.mem_Icc.mp hk).1
    dsimp [h] at *; omega
  have honly : h = 1 → p - Fin.ofNat n 1 ∈ C := by
    intro hh
    have hpref : negativePrefix (gapWord C) i 1 = 1 := by
      simpa [negativePrefix, h] using hh
    have hend := negativePrefix_endpoint C i 1 1 (by omega)
      (by have := i.isLt; omega) (by omega) hpref
    rw [← hend]
    exact C.orderEmbOfFin_mem rfl (cyclicIndex i (C.card - 1))
  unfold directionSlot; rw [h2]
  change (if p - Fin.ofNat n 1 ∈ C then 2
      else if p - Fin.ofNat n 2 ∈ C then 1 else 0) ≤ phi h
  by_cases hp1 : p - Fin.ofNat n 1 ∈ C
  · have hh := hfirst hp1
    rw [if_pos hp1]; simp [phi, hh]
  · by_cases hp2 : p - Fin.ofNat n 2 ∈ C
    · have hle := hsecond hp2
      have hpos : 0 < h := hpositive (cyclicIndex i (C.card - 1))
      have hne : h ≠ 1 := fun hh => hp1 (honly hh)
      have hh : h = 2 := by omega
      rw [if_neg hp1, if_pos hp2]; simp [phi, hh]
    · rw [if_neg hp1, if_neg hp2]; exact Nat.zero_le _
private theorem inner_forward_slot_le_score (n : Nat) [NeZero n] (hn : 14 ≤ n)
    (C : Finset (Fin n)) (i : Fin C.card) :
    directionSlot C (positiveShift n) (true, sortedColumn C i) ≤
      prefixScore (gapWord C) i positivePrefix := by
  classical
  let p := sortedColumn C i
  have h6 : (positiveShift n (positiveShift n (true, p))).2 = p + Fin.ofNat n 6 := by
    change p + Fin.ofNat n 3 + Fin.ofNat n 3 = p + Fin.ofNat n 6; apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (show 3 < n by omega),
      Nat.mod_eq_of_lt (show 6 < n by omega), Nat.mod_add_mod]
  unfold directionSlot; rw [h6]
  change (if p + Fin.ofNat n 3 ∈ C then 2 else if p + Fin.ofNat n 6 ∈ C then 1 else 0) ≤ _
  by_cases h3 : p + Fin.ofNat n 3 ∈ C
  · obtain ⟨k, hk, heq⟩ := positive_request_prefix C i 3 (by omega) (by omega) h3
    rw [if_pos h3]
    have hex : ∃ k ∈ Finset.Icc 1 C.card, positivePrefix (gapWord C) i k = 3 := ⟨k, hk, heq⟩
    change 2 ≤ if ∃ k ∈ Finset.Icc 1 C.card,
      positivePrefix (gapWord C) i k = 3 then 2 else _
    rw [if_pos hex]
  · rw [if_neg h3]
    by_cases h6' : p + Fin.ofNat n 6 ∈ C
    · obtain ⟨k, hk, heq⟩ := positive_request_prefix C i 6 (by omega) (by omega) h6'
      rw [if_pos h6']; simp only [prefixScore]
      split_ifs <;> simp_all
    · rw [if_neg h6']; exact Nat.zero_le _
private theorem inner_backward_slot_le_score (n : Nat) [NeZero n] (hn : 14 ≤ n)
    (C : Finset (Fin n)) (i : Fin C.card) :
    directionSlot C (negativeShift n) (true, sortedColumn C i) ≤
      prefixScore (gapWord C) i negativePrefix := by
  classical
  let p := sortedColumn C i
  have h6 : (negativeShift n (negativeShift n (true, p))).2 = p - Fin.ofNat n 6 := by
    change p - Fin.ofNat n 3 - Fin.ofNat n 3 = p - Fin.ofNat n 6
    have hh : (Fin.ofNat n 3 : Fin n) + Fin.ofNat n 3 = Fin.ofNat n 6 := by
      apply Fin.ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (show 3 < n by omega),
        Nat.mod_eq_of_lt (show 6 < n by omega)]
    rw [sub_sub, hh]
  unfold directionSlot; rw [h6]
  change (if p - Fin.ofNat n 3 ∈ C then 2 else if p - Fin.ofNat n 6 ∈ C then 1 else 0) ≤ _
  by_cases h3 : p - Fin.ofNat n 3 ∈ C
  · obtain ⟨k, hk, heq⟩ := negative_request_prefix C i 3 (by omega) (by omega) h3
    rw [if_pos h3]
    have hex : ∃ k ∈ Finset.Icc 1 C.card, negativePrefix (gapWord C) i k = 3 := ⟨k, hk, heq⟩
    change 2 ≤ if ∃ k ∈ Finset.Icc 1 C.card,
      negativePrefix (gapWord C) i k = 3 then 2 else _
    rw [if_pos hex]
  · rw [if_neg h3]
    by_cases h6' : p - Fin.ofNat n 6 ∈ C
    · obtain ⟨k, hk, heq⟩ := negative_request_prefix C i 6 (by omega) (by omega) h6'
      rw [if_pos h6']; simp only [prefixScore]
      split_ifs <;> simp_all
    · rw [if_neg h6']; exact Nat.zero_le _
/-- The literal cyclic-gap top-ten relaxation dominates occupied requests and collisions. -/
theorem slot_domination (n : Nat) [NeZero n] (hn : 14 ≤ n)
    (X : Finset (Bool × Fin n)) (hX : X.card = 10) :
    2 * (I n X + K n X) ≤ T (gapWord (columns X)) := by
  classical
  let C := columns X
  let e : Bool × Fin C.card → Bool × Fin n :=
    fun z => (z.1, sortedColumn C z.2)
  have heinj : Function.Injective e := by
    intro a b hab
    rcases a with ⟨a₁, a₂⟩; rcases b with ⟨b₁, b₂⟩
    have h₁ : a₁ = b₁ := congrArg Prod.fst hab
    have h₂ : sortedColumn C a₂ = sortedColumn C b₂ := congrArg Prod.snd hab
    exact Prod.ext h₁ ((C.orderEmbOfFin rfl).injective h₂)
  have hslot (z : Bool × Fin C.card) :
      directionSlot C (positiveShift n) (e z) +
        directionSlot C (negativeShift n) (e z) ≤
          if z.1 then B (gapWord C) z.2 else A (gapWord C) z.2 := by
    rcases z with ⟨b, i⟩
    cases b
    · have hp := outer_forward_slot_le_phi n hn C i
      have hm := outer_backward_slot_le_phi n hn C i
      simp only [Bool.false_eq_true, ite_false, A, e, Prod.fst] at *
      omega
    · have hp := inner_forward_slot_le_score n hn C i
      have hm := inner_backward_slot_le_score n hn C i
      simpa [B, e] using add_le_add hp hm
  have hsup : geometricT n C ≤ T (gapWord C) := by
    unfold geometricT
    apply Finset.sup_le
    intro Y hY
    obtain ⟨hYsub, hYcard⟩ := Finset.mem_powersetCard.mp hY
    let Z := (Finset.univ : Finset (Bool × Fin C.card)).filter fun z => e z ∈ Y
    have himage : Z.image e = Y := by
      ext v
      constructor
      · intro hv
        obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hv
        rw [← heq]; exact (Finset.mem_filter.mp hz).2
      · intro hv
        have hc : v.2 ∈ C := (Finset.mem_product.mp (hYsub hv)).2
        let j := (C.orderIsoOfFin rfl).symm ⟨v.2, hc⟩
        have hj : sortedColumn C j = v.2 := by
          change ((C.orderIsoOfFin rfl) j).val = v.2; exact congrArg Subtype.val ((C.orderIsoOfFin rfl).apply_symm_apply ⟨v.2, hc⟩)
        apply Finset.mem_image.mpr; refine ⟨(v.1, j), ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [e, hj] using hv⟩
        · simpa [e, hj]
    have hZcard : Z.card = 10 := by
      have hc : (Z.image e).card = Z.card := Finset.card_image_iff.mpr heinj.injOn
      rw [himage, hYcard] at hc; exact hc.symm
    have hZtop :
        (∑ z ∈ Z, (if z.1 then B (gapWord C) z.2 else A (gapWord C) z.2)) ≤
          T (gapWord C) := by
      change (∑ z ∈ Z, (if z.1 then B (gapWord C) z.2 else A (gapWord C) z.2)) ≤
        ((Finset.univ : Finset (Bool × Fin C.card)).powersetCard 10).sup
          (fun Y => ∑ z ∈ Y, (if z.1 then B (gapWord C) z.2 else A (gapWord C) z.2))
      exact Finset.le_sup
        (f := fun Y : Finset (Bool × Fin C.card) =>
          ∑ z ∈ Y, (if z.1 then B (gapWord C) z.2 else A (gapWord C) z.2))
        (Finset.mem_powersetCard.mpr
        ⟨Finset.filter_subset _ _, hZcard⟩)
    have hZle := Finset.sum_le_sum (fun z (_ : z ∈ Z) => hslot z)
    have hYsum :
        (∑ v ∈ Y, (directionSlot C (positiveShift n) v +
          directionSlot C (negativeShift n) v)) =
        ∑ z ∈ Z, (directionSlot C (positiveShift n) (e z) +
          directionSlot C (negativeShift n) (e z)) := by
      rw [← himage, Finset.sum_image heinj.injOn]
    exact hYsum.le.trans (hZle.trans hZtop)
  exact (geometric_slot_domination n X hX).trans hsup
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
