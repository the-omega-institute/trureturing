/- GID: D5/S3/Arith/FibonacciAtomic/QuantityAddressCertificate
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/QuantityAddressCertificate
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sharp quantity-only certificates for actual ordered tree images. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.QuantityAddressCertificate

open GenealogicalFiberTransport (Source substitution composition)
open ActualTreeReadoutAcquisition (Address Reply readout leaves Positive)
open ActualImageSevenLeafSeparation (leafAddresses)
open ActualLeafHistoryRigidity (alphaLeaves subtree)
open ActualImageAddressCertificate (ActualImage Within height replace)
local notation "m(" t ")" => GraftAffineClosure.quantity (composition t)
local notation "B(" t ")" => Finset.filter (fun u => readout u t = Reply.beta) (leafAddresses t)

/-- Exact scalar quantity is the only promise on the complete competitor tree. -/
def Sound (d : ℕ) (V : Source) (h : ℕ) (Q : Finset Address) : Prop :=
  Within h Q ∧ ∀ U : Source, m(U) = m(V) →
    (∀ u ∈ Q, readout u U = readout u V) → U ∈ ActualImage d

/-- Every branch has a beta descendant, recursively through the tree. -/
private def BetaCovered : Source → Prop
  | .of _ => True
  | .mul s t => BetaCovered s ∧ BetaCovered t ∧ ∃ u : Address, readout u (.mul s t) = .beta

private theorem mass_pair (s t : Source) : m(.mul s t) = m(s) + m(t) := by
  simp only [GraftAffineClosure.quantity, composition, Prod.fst_add, Prod.snd_add]
  ring

private theorem mass_min (t : Source) : 2 ≤ m(t) ∧ (m(t) = 2 ↔ t = .of true) ∧
    (m(t) = 3 ↔ t = .of false) := by
  induction t with
  | of b => cases b <;> simp [GraftAffineClosure.quantity, composition] <;> decide
  | mul s t hs ht =>
    rw [mass_pair]
    refine ⟨by omega, ?_, ?_⟩ <;> constructor
    all_goals intro h
    · omega
    · cases h
    · omega
    · cases h

private theorem beta_structure (t : Source) :
    BetaCovered (substitution (substitution t)) ∧
    ∃ u : Address, readout u (substitution (substitution t)) = .beta := by
  induction t with
  | of b => cases b with
    | true => exact ⟨⟨trivial, trivial, [false], rfl⟩, [false], rfl⟩
    | false => exact ⟨⟨⟨trivial, trivial, [false], rfl⟩, trivial, [true], rfl⟩, [true], rfl⟩
  | mul s t hs ht =>
    obtain ⟨hc, u, hu⟩ := hs
    obtain ⟨hd, v, hv⟩ := ht
    exact ⟨⟨hc, hd, false :: u, hu⟩, false :: u, hu⟩

private theorem beta_spec (t : Source) (u : Address) :
    u ∈ B(t) ↔ readout u t = .beta := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    exact ((ActualImageSevenLeafSeparation.seven_leaf_separation.1 t).2 u).mpr
      ⟨false, by simp [ActualImageSevenLeafSeparation.leafLabel, h]⟩

private theorem beta_recovery (V U : Source) (hc : BetaCovered V)
    (hm : ∀ u : Address, readout u V = .beta → readout u U = .beta) :
    m(V) ≤ m(U) ∧ (m(U) = m(V) → U = V) := by
  induction V generalizing U with
  | of b => cases b with
    | true => exact ⟨(mass_min U).1, fun h => (mass_min U).2.1.mp h⟩
    | false =>
      have hr := hm [] rfl
      have he : U = .of false := by
        cases U with
        | of c => cases c <;> simp_all [readout]
        | mul s t => cases hr
      subst U
      exact ⟨le_rfl, fun _ => rfl⟩
  | mul s t hs ht =>
    obtain ⟨hcs, hct, u, hu⟩ := hc
    cases U with
    | of b =>
      have hr := hm u hu
      cases u with
      | nil => cases hu
      | cons c u => simp [readout] at hr
    | mul x y =>
      obtain ⟨hsl, hse⟩ := hs x hcs (fun u hu => hm (false :: u) hu)
      obtain ⟨htl, hte⟩ := ht y hct (fun u hu => hm (true :: u) hu)
      refine ⟨by rw [mass_pair, mass_pair]; omega, ?_⟩
      intro he
      rw [mass_pair, mass_pair] at he
      exact congrArg₂ FreeMagma.mul (hse (by omega)) (hte (by omega))

private theorem beta_sound (k : ℕ) (hk : 1 ≤ k) (V : Source)
    (hV : V ∈ ActualImage (3 * k)) (h : ℕ) (hh : height V ≤ h) :
    Sound (3 * k) V h B(V) := by
  obtain ⟨T, hT⟩ := hV
  let S := substitution^[3 * k - 2] T
  have he : V = substitution (substitution S) := by
    change V = substitution^[2] S
    dsimp only [S]
    rw [← Function.iterate_add_apply, show 2 + (3 * k - 2) = 3 * k by omega]
    exact hT.symm
  refine ⟨fun u hu => ((ActualImageAddressCertificate.leaf_data V).1 u
    (Finset.mem_filter.mp hu).1).trans hh, ?_⟩
  intro U hm ho
  have hc : BetaCovered V := he ▸ (beta_structure S).1
  have hUV := (beta_recovery V U hc (fun u hu =>
    (ho u ((beta_spec V u).mpr hu)).trans hu)).2 hm
  exact hUV ▸ ⟨T, hT⟩


private theorem leaf_expand (t : Source) (s : Address)
    (hs : subtree s t = some (.of false)) :
    subtree (s ++ [false]) (replace t s (.mul (.of true) (.of true))) = some (.of true) ∧
    composition (replace t s (.mul (.of true) (.of true))) + (0, 1) = composition t + (2, 0) ∧
    (∀ u : Address, u ≠ s → u ≠ s ++ [false] → u ≠ s ++ [true] →
      readout u (replace t s (.mul (.of true) (.of true))) = readout u t) := by
  induction s generalizing t with
  | nil =>
    have he : t = .of false := Option.some.inj (by simpa only [subtree] using hs)
    subst t
    refine ⟨rfl, by rfl, ?_⟩
    intro u h hL hR
    cases u with
    | nil => exact (h rfl).elim
    | cons b u =>
      cases u with
      | nil => cases b <;> simp_all
      | cons c u => cases b <;> rfl
  | cons b s ih =>
    cases t with
    | of c => simp [subtree] at hs
    | mul v w => cases b with
      | false =>
        obtain ⟨hl, hc, ho⟩ := ih v hs
        refine ⟨hl, ?_, ?_⟩
        · change (composition (replace v s (.mul (.of true) (.of true))) + composition w) +
            (0, 1) = (composition v + composition w) + (2, 0)
          simpa only [add_assoc, add_left_comm, add_comm] using congrArg (· + composition w) hc
        · intro u h hL hR
          cases u with
          | nil => rfl
          | cons b u => cases b with
            | true => rfl
            | false =>
              exact ho u (fun he => h (congrArg (List.cons false) he))
                (fun he => hL (congrArg (List.cons false) he))
                (fun he => hR (congrArg (List.cons false) he))
      | true =>
        obtain ⟨hl, hc, ho⟩ := ih w hs
        refine ⟨hl, ?_, ?_⟩
        · change (composition v + composition (replace w s (.mul (.of true) (.of true)))) +
            (0, 1) = (composition v + composition w) + (2, 0)
          simpa only [add_assoc] using congrArg (composition v + ·) hc
        · intro u h hL hR
          cases u with
          | nil => rfl
          | cons b u => cases b with
            | false => rfl
            | true =>
              exact ho u (fun he => h (congrArg (List.cons true) he))
                (fun he => hL (congrArg (List.cons true) he))
                (fun he => hR (congrArg (List.cons true) he))

private theorem joint_surgery (V : Source) (x y : Address)
    (hx : readout x V = .beta) (hy : readout y V = .beta) (hxy : x ≠ y) :
    ∃ W : Source, m(W) = m(V) ∧
      (∀ u : Address, u ≠ x → u ≠ y → u ≠ y ++ [false] → u ≠ y ++ [true] →
        readout u W = readout u V) ∧ ¬ Positive W := by
  have leaf_sub := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let T := replace V x (.of true)
  obtain ⟨_, hc, ho⟩ := ActualImageAddressCertificate.leaf_change V x false true (leaf_sub V x false hx)
  have hyT : readout y T = .beta := (ho y hxy.symm).trans hy
  let W := replace T y (.mul (.of true) (.of true))
  obtain ⟨hl, hd, hp⟩ := leaf_expand T y (leaf_sub T y false hyT)
  refine ⟨W, ?_, ?_, ?_⟩
  · have ha := congrArg Prod.fst hc
    have hb := congrArg Prod.snd hc
    have he := congrArg Prod.fst hd
    have hf := congrArg Prod.snd hd
    simp only [Prod.fst_add, Prod.snd_add, composition] at ha hb he hf
    dsimp only [GraftAffineClosure.quantity]
    dsimp only [W, T] at *
    omega
  · intro u hu hx hyL hyR
    exact (hp u hx hyL hyR).trans (ho u hu)
  · intro hw
    exact ActualImageAddressCertificate.no_left_alpha W hw y hl

private theorem immediate_block (k : ℕ) (hk : 1 ≤ k) (V : Source)
    (Q : Finset Address) (hs : ∀ U : Source, m(U) = m(V) →
      (∀ u ∈ Q, readout u U = readout u V) → U ∈ ActualImage (3 * k))
    (x y : Address) (hx : x ∈ B(V)) (hy : y ∈ B(V))
    (hxy : x ≠ y) (hxQ : x ∉ Q) (hyQ : y ∉ Q) :
    y ++ [false] ∈ Q ∨ y ++ [true] ∈ Q := by
  classical
  by_contra hn
  obtain ⟨hL, hR⟩ := not_or.mp hn
  obtain ⟨W, hm, ho, hw⟩ := joint_surgery V x y
    ((beta_spec V x).mp hx) ((beta_spec V y).mp hy) hxy
  apply hw
  apply ActualImageAddressCertificate.image_positive (d := 3 * k) (by omega) W
  apply hs W hm
  intro u hu
  exact ho u (fun he => hxQ (he ▸ hu)) (fun he => hyQ (he ▸ hu))
    (fun he => hL (he ▸ hu)) (fun he => hR (he ▸ hu))


private theorem dichotomy (k : ℕ) (hk : 1 ≤ k) (V : Source)
    (hV : V ∈ ActualImage (3 * k)) (h : ℕ) (Q : Finset Address)
    (hs : Sound (3 * k) V h Q) : alphaLeaves V ⊆ Q ∨ B(V) ⊆ Q := by
  classical
  by_contra hn
  obtain ⟨ha, hb⟩ := not_or.mp hn
  obtain ⟨s, hsA, hsQ⟩ := Finset.not_subset.mp ha
  obtain ⟨t, htB, htQ⟩ := Finset.not_subset.mp hb
  have hsV := (ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 V s).mp hsA
  have htV := (beta_spec V t).mp htB
  have hst : s ≠ t := by intro he; rw [he, htV] at hsV; cases hsV
  obtain ⟨r, hsr, hr⟩ := (ActualImageAddressCertificate.image_structure k hk V hV).2 s hsA
  have leaf_sub := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let W₁ := replace V s (.of false)
  obtain ⟨h₁s, hc₁, ho₁⟩ := ActualImageAddressCertificate.leaf_change V s true false
    (leaf_sub V s true hsV)
  have ht₁ : readout t W₁ = .beta := (ho₁ t hst.symm).trans htV
  let W := replace W₁ t (.of true)
  obtain ⟨h₂t, hc₂, ho₂⟩ := ActualImageAddressCertificate.leaf_change W₁ t false true
    (leaf_sub W₁ t false ht₁)
  have hc : composition W = composition V :=
    ActualImageAddressCertificate.exchange_composition V s t hc₁ hc₂
  have hw := hs.2 W (congrArg GraftAffineClosure.quantity hc) (by
    intro u hu
    exact (ho₂ u (fun he => htQ (he ▸ hu))).trans
      (ho₁ u (fun he => hsQ (he ▸ hu))))
  exact ActualImageAddressCertificate.exchange_conflict V W₁ W s t r hst hsr hr htV
    h₁s h₂t ho₁ ho₂ (ActualImageAddressCertificate.image_positive (d := 3 * k) (by omega) W hw)

private theorem alpha_beta_disjoint (V : Source) : Disjoint (alphaLeaves V) B(V) := by
  classical
  apply Finset.disjoint_left.mpr
  intro u ha hb
  have he := (Finset.mem_filter.mp ha).2
  rw [(beta_spec V u).mp hb] at he
  cases he

private theorem child_absent (V : Source) (y : Address) (hy : y ∈ B(V)) (b : Bool) :
    readout (y ++ [b]) V = .absent := by
  have he := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    V y false ((beta_spec V y).mp hy)
  rw [ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y [b] V, he]
  rfl

private theorem alpha_branch_bound (k : ℕ) (hk : 1 ≤ k) (V : Source)
    (h : ℕ) (Q : Finset Address) (hs : Sound (3 * k) V h Q) (ha : alphaLeaves V ⊆ Q) :
    (alphaLeaves V).card + B(V).card - 1 ≤ Q.card ∧
    (2 ≤ (B(V) \ Q).card → (alphaLeaves V).card + B(V).card ≤ Q.card) := by
  classical
  let R := B(V) \ Q
  have hdis : Disjoint (alphaLeaves V) (B(V) ∩ Q) :=
    (alpha_beta_disjoint V).mono_right Finset.inter_subset_left
  have hbase : alphaLeaves V ∪ (B(V) ∩ Q) ⊆ Q :=
    Finset.union_subset ha Finset.inter_subset_right
  have hbcard : (alphaLeaves V ∪ (B(V) ∩ Q)).card =
      (alphaLeaves V).card + (B(V) ∩ Q).card := Finset.card_union_of_disjoint hdis
  have hrnum : R.card + (B(V) ∩ Q).card = B(V).card := by
    exact Finset.card_sdiff_add_card_inter _ _
  have hlarge (hr : 2 ≤ R.card) : (alphaLeaves V).card + B(V).card ≤ Q.card := by
    have block (y : Address) (hy : y ∈ R) : y ++ [false] ∈ Q ∨ y ++ [true] ∈ Q := by
      obtain ⟨x, hx, hxy⟩ := Finset.exists_mem_ne hr y
      exact immediate_block k hk V Q hs.2 x y (Finset.mem_sdiff.mp hx).1
        (Finset.mem_sdiff.mp hy).1 hxy (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).2
    let f : Address → Address := fun y => y ++ [if y ++ [false] ∈ Q then false else true]
    let C := R.image f
    have hinj : Function.Injective f := by
      intro y z he
      have hd := congrArg List.dropLast he
      simpa only [f, List.dropLast_concat] using hd
    have hCcard : C.card = R.card := Finset.card_image_of_injective R hinj
    have hC : C ⊆ Q := by
      intro u hu
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hu
      dsimp only [f]
      by_cases hl : y ++ [false] ∈ Q
      · simpa only [if_pos hl] using hl
      · simpa only [if_neg hl] using (block y hy).resolve_left hl
    have hsep : Disjoint (alphaLeaves V ∪ (B(V) ∩ Q)) C := by
      apply Finset.disjoint_left.mpr
      intro u hu hv
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      have hzero := child_absent V y (Finset.mem_sdiff.mp hy).1
        (if y ++ [false] ∈ Q then false else true)
      rcases Finset.mem_union.mp hu with hu | hu
      · have he := (Finset.mem_filter.mp hu).2
        rw [hzero] at he
        cases he
      · have he := (beta_spec V _).mp (Finset.mem_inter.mp hu).1
        rw [hzero] at he
        cases he
    have hle := Finset.card_le_card (Finset.union_subset hbase hC)
    rw [Finset.card_union_of_disjoint hsep, hbcard, hCcard] at hle
    omega
  refine ⟨?_, hlarge⟩
  by_cases hr : 2 ≤ R.card
  · have he := hlarge hr; omega
  · have he := Finset.card_le_card hbase
    rw [hbcard] at he
    omega


private theorem image_alpha (k : ℕ) (hk : 1 ≤ k) (V : Source)
    (hV : V ∈ ActualImage (3 * k)) :
    1 ≤ (alphaLeaves V).card ∧ ((alphaLeaves V).card = 1 →
      3 * k = 3 ∧ V = substitution^[3] (.of true) ∧ B(V).card = 2) := by
  classical
  obtain ⟨Z, hZ⟩ := ActualImageAddressCertificate.image_positive (d := 3 * k) (by omega) V hV
  refine ⟨hZ ▸ ActualImageAlphaSeparation.alpha_count_facts.1 Z, ?_⟩
  intro ha
  have hZa : Z = .of true := ActualImageAlphaSeparation.alpha_count_facts.2 Z (hZ.symm ▸ ha)
  have hVA : V = substitution^[3] (.of true) := by rw [← hZ, hZa]
  have hk1 : k = 1 := by
    by_contra hn
    obtain ⟨T, hT⟩ := hV
    let Y := substitution^[3 * k - 6] T
    have he : substitution^[3] (substitution^[3] Y) = V := by
      dsimp only [Y]
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
      rw [show 3 + 3 + (3 * k - 6) = 3 * k by omega]
      exact hT
    have hi := SourceTransportCentralizer.source_transport_centralizer.2.2.1
      (substitution^[3]) ⟨Function.Semiconj₂.iterate (fun s t => substitution.map_mul s t) 3,
        fun _ => rfl⟩
    have hY : substitution^[3] Y = .of true := hi (he.trans hVA)
    have hb := ActualImageAddressCertificate.beta_surplus 1 (by omega) (.of true) ⟨Y, hY⟩
    simp [composition] at hb
  refine ⟨by omega, hVA, ?_⟩
  rw [hVA]
  decide

private theorem small_sound (Q : Finset Address)
    (hQ : Q = {[false, false], [false, true]} ∨
      Q = {[false, false], [true]} ∨ Q = {[false, true], [true]}) :
    ∀ U : Source, m(U) = m(substitution^[3] (.of true)) →
      (∀ u ∈ Q, readout u U = readout u (substitution^[3] (.of true))) →
      U = substitution^[3] (.of true) := by
  classical
  intro U hm ho
  have root_leaf (T : Source) (b : Bool) (ht : readout [] T = readout [] (.of b)) :
      T = .of b := by
    have he := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      T [] b (by cases b <;> exact ht)
    simpa only [subtree] using Option.some.inj he
  have hmass : m(U) = 8 := hm
  rcases hQ with rfl | rfl | rfl
  · have hL := ho [false, false] (by simp)
    have hR := ho [false, true] (by simp)
    change readout [false, false] U = .beta at hL
    change readout [false, true] U = .alpha at hR
    cases U with
    | of b => simp [readout] at hR
    | mul s t =>
      cases s with
      | of b => simp [readout] at hR
      | mul x y =>
        have hx : x = .of false := root_leaf x false hL
        have hy : y = .of true := root_leaf y true hR
        subst x; subst y
        rw [mass_pair, mass_pair] at hmass
        have ht : t = .of false := (mass_min t).2.2.mp (by change 3 + 2 + m(t) = 8 at hmass; omega)
        subst t
        rfl
  · have hp := beta_recovery (substitution^[3] (.of true)) U
      (beta_structure (.of false)).1 (by
        intro u hu
        have he : u = [false, false] ∨ u = [true] := by
          have hb := (beta_spec (substitution^[3] (.of true)) u).mpr hu
          have he : B(substitution^[3] (.of true)) = {[false, false], [true]} := by decide
          rw [he] at hb
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hb
        rcases he with rfl | rfl <;> exact ho _ (by simp))
    exact hp.2 hm
  · have hL := ho [false, true] (by simp)
    have hR := ho [true] (by simp)
    change readout [false, true] U = .alpha at hL
    change readout [true] U = .beta at hR
    cases U with
    | of b => simp [readout] at hL
    | mul s t =>
      have ht : t = .of false := root_leaf t false hR
      subst t
      cases s with
      | of b => simp [readout] at hL
      | mul x y =>
        have hy : y = .of true := root_leaf y true hL
        subst y
        rw [mass_pair, mass_pair] at hmass
        have hx : x = .of false := (mass_min x).2.2.mp (by change m(x) + 2 + 3 = 8 at hmass; omega)
        subst x
        rfl

set_option maxHeartbeats 2000000 in -- Joint surgery, disjoint counting and exact equality cases.
/-- The sharp quantity certificate frontier and all of its minimum query sets. -/
theorem result (k : ℕ) (hk : 1 ≤ k) (V : Source)
    (hV : V ∈ ActualImage (3 * k)) (h : ℕ) :
    1 ≤ (alphaLeaves V).card ∧
    (h < height V → ¬ ∃ Q : Finset Address, Sound (3 * k) V h Q) ∧
    (height V ≤ h → 2 ≤ (alphaLeaves V).card →
      Sound (3 * k) V h B(V) ∧ ∀ Q : Finset Address, Sound (3 * k) V h Q →
        B(V).card ≤ Q.card ∧ (Q.card = B(V).card ↔ Q = B(V))) ∧
    ((alphaLeaves V).card = 1 →
      3 * k = 3 ∧ V = substitution^[3] (.of true) ∧ B(V).card = 2 ∧
      (height V ≤ h →
        (∀ Q : Finset Address, Sound (3 * k) V h Q →
          2 ≤ Q.card ∧ (Q.card = 2 ↔
            Q = {[false, false], [false, true]} ∨ Q = {[false, false], [true]} ∨
              Q = {[false, true], [true]})) ∧
        (∀ Q : Finset Address,
          (Q = {[false, false], [false, true]} ∨ Q = {[false, false], [true]} ∨
            Q = {[false, true], [true]}) → Sound (3 * k) V h Q))) := by
  classical
  have ha := image_alpha k hk V hV
  have lower (Q : Finset Address) (hs : Sound (3 * k) V h Q) : B(V).card ≤ Q.card := by
    rcases dichotomy k hk V hV h Q hs with hA | hB
    · have hb := (alpha_branch_bound k hk V h Q hs hA).1
      omega
    · exact Finset.card_le_card hB
  refine ⟨ha.1, ?_, ?_, ?_⟩
  · intro hh ⟨Q, hs⟩
    apply (ActualImageAddressCertificate.result k hk V hV h).1 hh
    refine ⟨Q, hs.1, ?_⟩
    intro U hc ho
    exact hs.2 U (congrArg GraftAffineClosure.quantity hc) ho
  · intro hh hlarge
    refine ⟨beta_sound k hk V hV h hh, ?_⟩
    intro Q hs
    refine ⟨lower Q hs, ?_⟩
    constructor
    · intro hc
      rcases dichotomy k hk V hV h Q hs with hA | hB
      · have hb := (alpha_branch_bound k hk V h Q hs hA).1
        omega
      · exact (Finset.eq_of_subset_of_card_le hB (by omega)).symm
    · intro he
      rw [he]
  · intro hsmall
    obtain ⟨hd, hv, hb⟩ := ha.2 hsmall
    refine ⟨hd, hv, hb, ?_⟩
    intro hh
    refine ⟨?_, ?_⟩
    · intro Q hs
      refine ⟨by have hl := lower Q hs; omega, ?_⟩
      constructor
      · intro hc
        have hQL : Q ⊆ leafAddresses V := by
          rcases dichotomy k hk V hV h Q hs with hA | hB
          · have hbound := alpha_branch_bound k hk V h Q hs hA
            have hr : (B(V) \ Q).card < 2 := by
              by_contra hn
              have he := hbound.2 (by omega)
              omega
            have hdis : Disjoint (alphaLeaves V) (B(V) ∩ Q) :=
              (alpha_beta_disjoint V).mono_right Finset.inter_subset_left
            have hbase : alphaLeaves V ∪ (B(V) ∩ Q) ⊆ Q :=
              Finset.union_subset hA Finset.inter_subset_right
            have hcount : (alphaLeaves V ∪ (B(V) ∩ Q)).card = 2 := by
              rw [Finset.card_union_of_disjoint hdis]
              have hn := Finset.card_sdiff_add_card_inter B(V) Q
              have hle := Finset.card_le_card hbase
              rw [Finset.card_union_of_disjoint hdis] at hle
              omega
            have he := Finset.eq_of_subset_of_card_le hbase (by omega)
            rw [← he]
            exact Finset.union_subset (Finset.filter_subset _ _)
              (Finset.inter_subset_left.trans (Finset.filter_subset _ _))
          · have he := Finset.eq_of_subset_of_card_le hB (by omega)
            rw [← he]
            exact Finset.filter_subset _ _
        rw [hv] at hQL
        have hleaf : leafAddresses (substitution^[3] (.of true)) =
            {[false, false], [false, true], [true]} := by decide
        rw [hleaf] at hQL
        obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
        have hx := hQL (Finset.mem_insert_self x {y})
        have hy := hQL (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
          simp_all [Finset.pair_comm]
      · intro he
        rcases he with rfl | rfl | rfl <;> decide
    · intro Q hQ
      refine ⟨?_, ?_⟩
      · intro u hu
        have hleaf : u ∈ leafAddresses V := by
          rw [hv]
          rcases hQ with rfl | rfl | rfl <;>
            simp [leafAddresses, leaves, substitution, Function.iterate_succ_apply'] at hu ⊢ <;>
              aesop
        exact ((ActualImageAddressCertificate.leaf_data V).1 u hleaf).trans hh
      · intro U hm ho
        have he : U = substitution^[3] (.of true) := small_sound Q hQ U (hm.trans (congrArg (fun t => m(t)) hv))
          (by intro u hu; exact (ho u hu).trans (congrArg (readout u) hv))
        rw [he, ← hv]
        exact hV

end D5.S3.Arith.FibonacciAtomic.QuantityAddressCertificate
