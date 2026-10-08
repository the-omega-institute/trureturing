/- GID: D5/S3/Arith/FibonacciAtomic/StageScalarAddressCertificate
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/StageScalarAddressCertificate
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sharp scalar-stage certificates on arbitrary raw address query sets. -/

import D5.S3.Arith.FibonacciAtomic.QuantityAddressCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.StageScalarAddressCertificate

open GenealogicalFiberTransport (Source substitution composition)
open ActualTreeReadoutAcquisition (Address Reply readout Positive)
open ActualImageSevenLeafSeparation (leafAddresses)
open ActualLeafHistoryRigidity (alphaLeaves subtree)
open ActualImageAddressCertificate (ActualImage Within height replace)
open QuantityAddressCertificate (QuantitySound beta_spec child_absent alpha_beta_disjoint)
local notation "B(" t ")" => Finset.filter (fun u => readout u t = Reply.beta) (leafAddresses t)
set_option quotPrecheck false
local notation "leaf_sub" =>
  ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
local notation "read_at" =>
  ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem child_ne_leaf (V : Source) (x y : Address) (b : Bool)
    (hx : x ∈ B(V)) (hy : y ∈ B(V)) : y ++ [b] ≠ x := by
  intro he
  have hz := child_absent V y hy b
  rw [he, (beta_spec V x).mp hx] at hz
  cases hz

private theorem relabel_many (V : Source) (X : Finset Address) (hX : X ⊆ B(V)) :
    ∃ W : Source,
      composition W + (0, X.card) = composition V + (X.card, 0) ∧
      ∀ u : Address, readout u W = if u ∈ X then .alpha else readout u V := by
  classical
  induction X using Finset.induction_on with
  | empty => exact ⟨V, by simp, by simp⟩
  | @insert x X hx ih =>
    obtain ⟨T, hc, ho⟩ := ih (Finset.Subset.trans (Finset.subset_insert _ _) hX)
    have hxV := (beta_spec V x).mp (hX (Finset.mem_insert_self _ _))
    have hxT : readout x T = .beta := by rw [ho, if_neg hx]; exact hxV
    obtain ⟨hr, hd, hp⟩ := ActualImageAddressCertificate.leaf_change T x false true
      (leaf_sub T x false hxT)
    refine ⟨replace T x (.of true), ?_, ?_⟩
    · apply Prod.ext
      all_goals
        have ha := congrArg Prod.fst hc
        have hb := congrArg Prod.snd hc
        have hd₁ := congrArg Prod.fst hd
        have hd₂ := congrArg Prod.snd hd
        simp only [Prod.fst_add, Prod.snd_add, composition, Finset.card_insert_of_notMem hx]
          at ha hb hd₁ hd₂ ⊢
        omega
    · intro u
      by_cases hu : u = x
      · subst u
        have he := read_at x [] (replace T x (.of true))
        simpa only [List.append_nil, hr, readout, Finset.mem_insert_self, if_true] using he
      · rw [hp u hu, ho]
        simp only [Finset.mem_insert, hu, false_or]

private theorem expand_many (V : Source) (Y : Finset Address) (hY : Y ⊆ B(V)) :
    ∃ W : Source,
      composition W + (0, Y.card) = composition V + (2 * Y.card, 0) ∧
      (∀ y ∈ Y, readout y W = .branch) ∧
      (∀ y ∈ Y, ∀ b : Bool, readout (y ++ [b]) W = .alpha) ∧
      (∀ u : Address, u ∉ Y → (∀ y ∈ Y, ∀ b : Bool, u ≠ y ++ [b]) →
        readout u W = readout u V) := by
  classical
  induction Y using Finset.induction_on with
  | empty => exact ⟨V, by simp, by simp, by simp, by simp⟩
  | @insert y Y hy ih =>
    have hYV : Y ⊆ B(V) := (Finset.subset_insert _ _).trans hY
    have hyV : y ∈ B(V) := hY (Finset.mem_insert_self _ _)
    obtain ⟨T, hc, hr, hchild, ho⟩ := ih hYV
    have hyT : readout y T = .beta :=
      (ho y hy (fun z hz b => (child_ne_leaf V y z b hyV (hYV hz)).symm)).trans
        ((beta_spec V y).mp hyV)
    obtain ⟨_, hd, hp, hat⟩ := QuantityAddressCertificate.leaf_expand T y
      (leaf_sub T y false hyT)
    let W := replace T y (.mul (.of true) (.of true))
    have hnew (z : Address) : readout (y ++ z) W = readout z (.mul (.of true) (.of true)) := by
      rw [read_at]
      have he := hat []
      simp only [List.append_nil, subtree] at he
      rw [he]
    have apart (z : Address) (hz : z ∈ Y) (b c : Bool) : z ++ [b] ≠ y ++ [c] := by
      intro he
      have he := congrArg List.dropLast he
      simp only [List.dropLast_concat] at he
      exact hy (he ▸ hz)
    refine ⟨W, ?_, ?_, ?_, ?_⟩
    · dsimp only [W]
      apply Prod.ext
      all_goals
        have ha := congrArg Prod.fst hc
        have hb := congrArg Prod.snd hc
        have hd₁ := congrArg Prod.fst hd
        have hd₂ := congrArg Prod.snd hd
        simp only [Prod.fst_add, Prod.snd_add, Finset.card_insert_of_notMem hy]
          at ha hb hd₁ hd₂ ⊢
        omega
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simpa only [List.append_nil, readout] using hnew []
      · exact (hp z (fun he => hy (he ▸ hz))
          (child_ne_leaf V z y false (hYV hz) hyV).symm
          (child_ne_leaf V z y true (hYV hz) hyV).symm).trans (hr z hz)
    · intro z hz b
      rcases Finset.mem_insert.mp hz with rfl | hz
      · cases b <;> exact hnew [_]
      · exact (hp (z ++ [b]) (child_ne_leaf V y z b hyV (hYV hz))
          (apart z hz b false) (apart z hz b true)).trans (hchild z hz b)
    · intro u hu huc
      have huY : u ∉ Y := fun hm => hu (Finset.mem_insert_of_mem hm)
      exact (hp u (fun he => hu (he ▸ Finset.mem_insert_self _ _))
        (huc y (Finset.mem_insert_self _ _) false)
        (huc y (Finset.mem_insert_self _ _) true)).trans
        (ho u huY (fun z hz b => huc z (Finset.mem_insert_of_mem hz) b))

private theorem batch_surgery (V : Source) (X Y : Finset Address)
    (hX : X ⊆ B(V)) (hY : Y ⊆ B(V)) (hXY : Disjoint X Y) :
    ∃ W : Source,
      composition W + (0, X.card + Y.card) = composition V + (X.card + 2 * Y.card, 0) ∧
      (∀ u : Address, readout u W ≠ readout u V ↔
        u ∈ X ∨ u ∈ Y ∨ ∃ y ∈ Y, ∃ b : Bool, u = y ++ [b]) ∧
      (Y.Nonempty → ¬ Positive W) := by
  classical
  obtain ⟨T, hc, ho⟩ := relabel_many V X hX
  have hYT : Y ⊆ B(T) := by
    intro y hy
    apply (beta_spec T y).mpr
    rw [ho, if_neg (fun hx => Finset.disjoint_left.mp hXY hx hy)]
    exact (beta_spec V y).mp (hY hy)
  obtain ⟨W, hd, hr, hh, hp⟩ := expand_many T Y hYT
  refine ⟨W, ?_, ?_, ?_⟩
  · apply Prod.ext
    all_goals
      have ha := congrArg Prod.fst hc
      have hb := congrArg Prod.snd hc
      have he := congrArg Prod.fst hd
      have hf := congrArg Prod.snd hd
      simp only [Prod.fst_add, Prod.snd_add] at ha hb he hf ⊢
      omega
  · intro u
    constructor
    · contrapose!
      intro hn
      rw [hp u hn.2.1 (fun y hy b he => hn.2.2 y hy b he), ho, if_neg hn.1]
    · rintro (hx | hy | ⟨y, hy, b, rfl⟩)
      · have huY : u ∉ Y := fun hy => Finset.disjoint_left.mp hXY hx hy
        rw [hp u huY (fun y hy b => (child_ne_leaf V u y b (hX hx) (hY hy)).symm),
          ho, if_pos hx, (beta_spec V u).mp (hX hx)]
        decide
      · rw [hr u hy, (beta_spec V u).mp (hY hy)]
        decide
      · rw [hh y hy b, child_absent V y (hY hy) b]
        decide
  · rintro ⟨y, hy⟩ hw
    have hl := leaf_sub W (y ++ [false]) true (hh y hy false)
    exact ActualImageAddressCertificate.no_left_alpha W hw y hl

private theorem uniform_block (f g p q : ℕ) (hp : 0 < p)
    (hf : f = p + q) (hg : g = 2 * p + q)
    (k : ℕ) (hk : 1 ≤ k) (V : Source) (h : ℕ) (Q : Finset Address)
    (hs : QuantitySound f g (3 * k) V h Q) (hr : f ≤ (B(V) \ Q).card) :
    ((B(V) \ Q).filter
      (fun y => ¬ (y ++ [false] ∈ Q ∨ y ++ [true] ∈ Q))).card < p := by
  classical
  let R := B(V) \ Q
  let U := R.filter (fun y => ¬ (y ++ [false] ∈ Q ∨ y ++ [true] ∈ Q))
  by_contra hn
  change ¬ U.card < p at hn
  change f ≤ R.card at hr
  obtain ⟨Y, hYU, hYcard⟩ := Finset.exists_subset_card_eq (show p ≤ U.card by omega)
  have hYR : Y ⊆ R := hYU.trans (Finset.filter_subset _ _)
  have hq : q ≤ (R \ Y).card := by
    rw [Finset.card_sdiff_of_subset hYR, hYcard]
    omega
  obtain ⟨X, hXR, hXcard⟩ := Finset.exists_subset_card_eq hq
  have hXY : Disjoint X Y := (Finset.sdiff_disjoint).mono_left hXR
  obtain ⟨W, hc, ho, hw⟩ := batch_surgery V X Y
    (hXR.trans (Finset.sdiff_subset.trans Finset.sdiff_subset))
    (hYR.trans Finset.sdiff_subset) hXY
  have hm : f * (composition W).1 + g * (composition W).2 =
      f * (composition V).1 + g * (composition V).2 := by
    have ha := congrArg Prod.fst hc
    have hb := congrArg Prod.snd hc
    simp only [Prod.fst_add, Prod.snd_add, hXcard, hYcard] at ha hb
    rw [hf, hg]
    nlinarith
  have hmatch : ∀ u ∈ Q, readout u W = readout u V := by
    intro u hu
    by_contra he
    rcases (ho u).mp he with hx | hy | ⟨y, hy, b, he⟩
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hXR hx)).1).2 hu
    · exact (Finset.mem_sdiff.mp (hYR hy)).2 hu
    · have hc := (Finset.mem_filter.mp (hYU hy)).2
      subst u
      cases b with
      | false => exact hc (Or.inl hu)
      | true => exact hc (Or.inr hu)
  exact hw (Finset.card_pos.mp (by omega))
    (ActualImageAddressCertificate.image_positive (d := 3 * k) (by omega) W (hs.2 W hm hmatch))

private theorem alpha_bound (f g p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hf : f = p + q) (hg : g = 2 * p + q)
    (k : ℕ) (hk : 1 ≤ k) (V : Source) (h : ℕ) (Q : Finset Address)
    (hs : QuantitySound f g (3 * k) V h Q) (hA : alphaLeaves V ⊆ Q) :
    (alphaLeaves V).card + (B(V).card + 1 - f) ≤ Q.card ∧
    (Q.card = (alphaLeaves V).card + (B(V).card + 1 - f) →
      Q = alphaLeaves V ∪ (B(V) ∩ Q) ∧ (B(V) ∩ Q).card = B(V).card + 1 - f) := by
  classical
  let R := B(V) \ Q
  have hdis := (alpha_beta_disjoint V).mono_right (Finset.inter_subset_left (s₂ := Q))
  have hbase : alphaLeaves V ∪ (B(V) ∩ Q) ⊆ Q :=
    Finset.union_subset hA Finset.inter_subset_right
  have hbcard := Finset.card_union_of_disjoint hdis
  have hrnum := Finset.card_sdiff_add_card_inter B(V) Q
  have hle := Finset.card_le_card hbase
  rw [hbcard] at hle
  by_cases hr : f ≤ R.card
  · have hu := uniform_block f g p q hp hf hg k hk V h Q hs hr
    let S := R.filter (fun y => y ++ [false] ∈ Q ∨ y ++ [true] ∈ Q)
    let U := R.filter (fun y => ¬ (y ++ [false] ∈ Q ∨ y ++ [true] ∈ Q))
    have hnum := Finset.card_filter_add_card_filter_not (s := R)
      (fun y => y ++ [false] ∈ Q ∨ y ++ [true] ∈ Q)
    have hcount := QuantityAddressCertificate.blocked_children_bound V Q S
      ((Finset.filter_subset _ _).trans Finset.sdiff_subset) hbase
      (fun y hy => (Finset.mem_filter.mp hy).2)
    rw [hbcard] at hcount
    change U.card < p at hu
    change S.card + U.card = R.card at hnum
    change (alphaLeaves V).card + (B(V) ∩ Q).card + S.card ≤ Q.card at hcount
    change R.card + (B(V) ∩ Q).card = B(V).card at hrnum
    have hstrict : (alphaLeaves V).card + (B(V).card + 1 - f) < Q.card := by
      omega
    exact ⟨by omega, fun he => (by omega : False).elim⟩
  · have hsmall : R.card < f := by omega
    have htotal : (alphaLeaves V).card + (B(V).card + 1 - f) ≤ Q.card := by
      dsimp only [R] at hsmall
      omega
    refine ⟨htotal, ?_⟩
    intro he
    have hcard : (alphaLeaves V ∪ (B(V) ∩ Q)).card = Q.card := by
      rw [hbcard]
      dsimp only [R] at hsmall
      omega
    exact ⟨(Finset.eq_of_subset_of_card_le hbase (by omega)).symm, by omega⟩

private theorem mixed_sound (f g : ℕ) (hf : 0 < f) (hfg : f < g)
    (hcop : Nat.Coprime f g) (k : ℕ) (hk : 1 ≤ k) (V : Source)
    (hV : V ∈ ActualImage (3 * k)) (h : ℕ) (hh : height V ≤ h)
    (C : Finset Address) (hC : C ⊆ B(V)) (hcard : C.card = B(V).card + 1 - f) :
    QuantitySound f g (3 * k) V h (alphaLeaves V ∪ C) := by
  classical
  refine ⟨?_, ?_⟩
  · intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact ((ActualImageAddressCertificate.leaf_data V).1 u (Finset.mem_filter.mp hu).1).trans hh
    · exact ((ActualImageAddressCertificate.leaf_data V).1 u
        (Finset.mem_filter.mp (hC hu)).1).trans hh
  · intro U hm ho
    have hmatch : ∀ u ∈ alphaLeaves V, readout u U = .alpha := by
      intro u hu
      exact (ho u (Finset.mem_union_left C hu)).trans (Finset.mem_filter.mp hu).2
    have hrecovery := ActualImageAddressCertificate.alpha_recovery V U
      (ActualImageAddressCertificate.image_structure k hk V hV).1 hmatch
    have ha := hrecovery.2.1
    have hCU : C ⊆ B(U) := by
      intro u hu
      exact (beta_spec U u).mpr
        ((ho u (Finset.mem_union_right _ hu)).trans ((beta_spec V u).mp (hC hu)))
    have hbu := Finset.card_le_card hCU
    rw [hcard, (ActualImageAddressCertificate.leaf_data V).2,
      (ActualImageAddressCertificate.leaf_data U).2] at hbu
    have hb : (composition U).2 ≤ (composition V).2 := by
      have hfa := Nat.mul_le_mul_left f ha
      nlinarith
    have hd : f * ((composition U).1 - (composition V).1) =
        g * ((composition V).2 - (composition U).2) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
      omega
    have hdvd : f ∣ (composition V).2 - (composition U).2 :=
      hcop.dvd_mul_left.mp ⟨(composition U).1 - (composition V).1, hd.symm⟩
    have hz := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    have he : composition U = composition V := by
      apply Prod.ext
      · have hbb : (composition U).2 = (composition V).2 := by omega
        rw [hbb] at hm
        nlinarith
      · omega
    exact (hrecovery.2.2 he) ▸ hV

set_option maxHeartbeats 2000000 in -- Batch construction and sharp cardinality equality cases.
/-- Exact minimum size and all minimizers at every known scalar stage. -/
theorem result (k : ℕ) (hk : 1 ≤ k) (L : ℕ) (V : Source)
    (hV : V ∈ ActualImage (3 * k)) (h : ℕ) :
    let f := Nat.fib (3 * L + 3)
    let g := Nat.fib (3 * L + 4)
    let t := B(V).card + 1 - f
    let M := min B(V).card ((alphaLeaves V).card + t)
    1 ≤ (alphaLeaves V).card ∧ (alphaLeaves V).card < B(V).card ∧
    (h < height V → ¬ ∃ Q : Finset Address, QuantitySound f g (3 * k) V h Q) ∧
    (height V ≤ h →
      (∀ Q : Finset Address, QuantitySound f g (3 * k) V h Q → M ≤ Q.card) ∧
      (∀ Q : Finset Address,
        (QuantitySound f g (3 * k) V h Q ∧ Q.card = M) ↔
          (Q = B(V) ∧ B(V).card = M) ∨
          ∃ C : Finset Address, C ⊆ B(V) ∧ C.card = t ∧
            Q = alphaLeaves V ∪ C ∧ (alphaLeaves V).card + t = M) ∧
      ∃ Q : Finset Address, QuantitySound f g (3 * k) V h Q ∧ Q.card = M) := by
  classical
  dsimp only
  let f := Nat.fib (3 * L + 3)
  let g := Nat.fib (3 * L + 4)
  let p := Nat.fib (3 * L + 2)
  let q := Nat.fib (3 * L + 1)
  let t := B(V).card + 1 - f
  let M := min B(V).card ((alphaLeaves V).card + t)
  have hp : 0 < p := Nat.fib_pos.mpr (by omega)
  have hq : 0 < q := Nat.fib_pos.mpr (by omega)
  have hf : f = p + q := by
    dsimp only [f, p, q]
    rw [show 3 * L + 3 = (3 * L + 1) + 2 by omega, Nat.fib_add_two]
    rw [show 3 * L + 1 + 1 = 3 * L + 2 by omega]
    omega
  have hg : g = 2 * p + q := by
    dsimp only [g, p, q]
    rw [show 3 * L + 4 = (3 * L + 2) + 2 by omega, Nat.fib_add_two]
    change p + f = 2 * p + q
    rw [hf]
    omega
  have hf0 : 0 < f := by omega
  have hfg : f < g := by omega
  have hgf : g < 2 * f := by omega
  have hcop : Nat.Coprime f g := Nat.fib_coprime_fib_succ (3 * L + 3)
  have ha := (QuantityAddressCertificate.result k hk V hV h).1
  have hab : (alphaLeaves V).card < B(V).card := by
    rw [ActualImageAddressCertificate.alpha_card, (ActualImageAddressCertificate.leaf_data V).2]
    exact ActualImageAddressCertificate.beta_surplus k hk V hV
  refine ⟨ha, hab, ?_, ?_⟩
  · intro hh ⟨Q, hs⟩
    apply (ActualImageAddressCertificate.result k hk V hV h).1 hh
    refine ⟨Q, hs.1, ?_⟩
    intro U hc ho
    exact hs.2 U (congrArg (fun c : ℕ × ℕ => f * c.1 + g * c.2) hc) ho
  · intro hh
    have hB := QuantityAddressCertificate.beta_sound f g hf0 hfg hgf k hk V hV h hh
    have lower (Q : Finset Address) (hs : QuantitySound f g (3 * k) V h Q) : M ≤ Q.card := by
      rcases QuantityAddressCertificate.dichotomy f g k hk V hV h Q hs with hA | hB
      · exact (Nat.min_le_right _ _).trans
          (alpha_bound f g p q hp hq hf hg k hk V h Q hs hA).1
      · exact (Nat.min_le_left _ _).trans (Finset.card_le_card hB)
    have choices (Q : Finset Address) :
        (QuantitySound f g (3 * k) V h Q ∧ Q.card = M) ↔
          (Q = B(V) ∧ B(V).card = M) ∨
          ∃ C : Finset Address, C ⊆ B(V) ∧ C.card = t ∧
            Q = alphaLeaves V ∪ C ∧ (alphaLeaves V).card + t = M := by
      constructor
      · rintro ⟨hs, hcard⟩
        rcases QuantityAddressCertificate.dichotomy f g k hk V hV h Q hs with hA | hBeta
        · have hbound := alpha_bound f g p q hp hq hf hg k hk V h Q hs hA
          have heq : Q.card = (alphaLeaves V).card + t := by
            have hmin := Nat.min_le_right B(V).card ((alphaLeaves V).card + t)
            dsimp only [M] at hcard
            omega
          obtain ⟨he, hCcard⟩ := hbound.2 heq
          exact Or.inr ⟨B(V) ∩ Q, Finset.inter_subset_left, hCcard, he, by omega⟩
        · have heq : B(V).card = M := by
            have hle := Finset.card_le_card hBeta
            have hmin := Nat.min_le_left B(V).card ((alphaLeaves V).card + t)
            dsimp only [M] at hcard
            omega
          exact Or.inl ⟨(Finset.eq_of_subset_of_card_le hBeta (by omega)).symm, heq⟩
      · rintro (⟨rfl, he⟩ | ⟨C, hC, hCcard, rfl, he⟩)
        · exact ⟨hB, he⟩
        · refine ⟨mixed_sound f g hf0 hfg hcop k hk V hV h hh C hC hCcard, ?_⟩
          rw [Finset.card_union_of_disjoint ((alpha_beta_disjoint V).mono_right hC), hCcard]
          exact he
    refine ⟨lower, choices, ?_⟩
    by_cases hb : B(V).card ≤ (alphaLeaves V).card + t
    · refine ⟨B(V), hB, ?_⟩
      exact (Nat.min_eq_left hb).symm
    · have htsmall : t ≤ B(V).card := by dsimp only [t]; omega
      obtain ⟨C, hC, hCcard⟩ := Finset.exists_subset_card_eq htsmall
      have hchoice : (alphaLeaves V).card + t = M := (Nat.min_eq_right (by omega)).symm
      exact ⟨alphaLeaves V ∪ C, (choices _).mpr (Or.inr ⟨C, hC, hCcard, rfl, hchoice⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  for n in [``result, ``child_ne_leaf, ``relabel_many, ``expand_many, ``batch_surgery,
      ``uniform_block, ``alpha_bound, ``mixed_sound,
      ``QuantityAddressCertificate.mass_pair, ``QuantityAddressCertificate.mass_min,
      ``QuantityAddressCertificate.beta_structure, ``QuantityAddressCertificate.beta_spec,
      ``QuantityAddressCertificate.beta_recovery, ``QuantityAddressCertificate.beta_sound,
      ``QuantityAddressCertificate.leaf_expand, ``QuantityAddressCertificate.dichotomy,
      ``QuantityAddressCertificate.alpha_beta_disjoint, ``QuantityAddressCertificate.child_absent,
      ``QuantityAddressCertificate.blocked_children_bound, ``QuantityAddressCertificate.result,
      ``ActualImageAddressCertificate.alpha_recovery, ``ActualImageAddressCertificate.result] do
    if let some (.thmInfo ti) := env.find? n then
      let cs := ti.value.getUsedConstants.filter fun c =>
        c.toString.startsWith "D5.S3.Arith.FibonacciAtomic" || c.toString.startsWith "_private.D5"
      Lean.logInfo m!"CONSUMPTION {n}: {cs}"

#print axioms result

end D5.S3.Arith.FibonacciAtomic.StageScalarAddressCertificate
