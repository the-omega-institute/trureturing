/- GID: D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sharp certificates and the weighted height frontier of actual substitution images. -/

import D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity
import D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate

open GenealogicalFiberTransport (Source substitution composition decompose)
open ActualTreeReadoutAcquisition (Address Reply readout leaves flip Positive)
open ActualImageSevenLeafSeparation (leafAddresses)
open ActualLeafHistoryRigidity (alphaLeaves subtree)

/-- Root depth is zero. Reuse the ordered shape from the existing decomposition. -/
def height (t : Source) : ℕ := (decompose t).1.height

/-- The actual image, with the complete ordered tree retained. -/
def ActualImage (d : ℕ) : Set Source := Set.range (substitution^[d])

/-- A finite query set obeys the raw path depth budget. -/
def Within (h : ℕ) (Q : Finset Address) : Prop := ∀ u ∈ Q, u.length ≤ h

/-- Soundness ranges over every complete source of the same exact composition. -/
def Sound (d : ℕ) (V : Source) (h : ℕ) (Q : Finset Address) : Prop :=
  Within h Q ∧ ∀ U : Source, composition U = composition V →
    (∀ u ∈ Q, readout u U = readout u V) → U ∈ ActualImage d

/-- Replace the subtree at a valid address; invalid addresses leave the tree alone. -/
def replace : Source → Address → Source → Source
  | _, [], v => v
  | .of b, _ :: _, _ => .of b
  | .mul s t, false :: u, v => .mul (replace s u v) t
  | .mul s t, true :: u, v => .mul s (replace t u v)

/-- Every branch has an alpha descendant, recursively through the whole tree. -/
def AlphaCovered : Source → Prop
  | .of _ => True
  | .mul s t => AlphaCovered s ∧ AlphaCovered t ∧
      (alphaLeaves (.mul s t)).Nonempty

/-- Soundness with no composition or leaf-count promise on competitors. -/
def UnSound (d : ℕ) (V : Source) (Q : Finset Address) : Prop :=
  ∀ U : Source, (∀ u ∈ Q, readout u U = readout u V) → U ∈ ActualImage d

/-- A right comb with alpha side leaves and a single terminal beta leaf. -/
def rightComb : ℕ → Source
  | 0 => .of false
  | m + 1 => .mul (.of true) (rightComb m)


theorem image_positive {d : ℕ} (hd : 3 ≤ d) (U : Source)
    (hU : U ∈ ActualImage d) : Positive U := by
  obtain ⟨T, hT⟩ := hU
  refine ⟨substitution^[d - 3] T, ?_⟩
  rw [← Function.iterate_add_apply, show 3 + (d - 3) = d by omega]
  exact hT

theorem alpha_mul (s t : Source) : alphaLeaves (s * t) =
    (alphaLeaves s).image (List.cons false) ∪ (alphaLeaves t).image (List.cons true) := by
  classical
  ext u
  cases u with
  | nil => simp [alphaLeaves, leafAddresses, leaves, readout]
  | cons b u => cases b <;> simp [alphaLeaves, leafAddresses, leaves, readout, Finset.mem_image]

private theorem alpha_of (b : Bool) :
    alphaLeaves (.of b) = if b then {[]} else ∅ := by
  cases b <;> simp [alphaLeaves, leafAddresses, leaves, Finset.filter_singleton, readout]

private theorem leaf_card (t : Source) :
    (leafAddresses t).card = (composition t).1 + (composition t).2 := by
  rw [(ActualImageSevenLeafSeparation.seven_leaf_separation.1 t).1]
  let F : Source →ₙ* Multiplicative ℕ := {
    toFun := fun t => Multiplicative.ofAdd ((composition t).1 + (composition t).2)
    map_mul' := by
      intro s t
      change (composition (.mul s t)).1 + (composition (.mul s t)).2 =
        ((composition s).1 + (composition s).2) + ((composition t).1 + (composition t).2)
      simp only [composition, Prod.fst_add, Prod.snd_add]; omega }
  let G : Source →ₙ* Multiplicative ℕ :=
    ⟨fun t => Multiplicative.ofAdd t.length, fun _ _ => rfl⟩
  have he : F = G := FreeMagma.hom_ext (by funext b; cases b <;> rfl)
  exact (congrArg (fun f : Source →ₙ* Multiplicative ℕ => Multiplicative.toAdd (f t)) he).symm

private theorem positive (t : Source) : 0 < (composition t).1 + (composition t).2 := by
  rw [← leaf_card t, (ActualImageSevenLeafSeparation.seven_leaf_separation.1 t).1]
  exact FreeMagma.length_pos t

theorem alpha_card (t : Source) : (alphaLeaves t).card = (composition t).1 := by
  have disj (A B : Finset Address) :
      Disjoint (A.image (List.cons false)) (B.image (List.cons true)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    rcases Finset.mem_image.mp hu with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨b, _, hb⟩
    simp at hb
  let F : Source →ₙ* Multiplicative ℕ := {
    toFun := fun t => Multiplicative.ofAdd (alphaLeaves t).card
    map_mul' := by
      intro s t
      change (alphaLeaves (s * t)).card = (alphaLeaves s).card + (alphaLeaves t).card
      simp only [alpha_mul, Finset.card_union_of_disjoint (disj _ _),
        Finset.card_image_of_injective _ List.cons_injective] }
  let G : Source →ₙ* Multiplicative ℕ :=
    ⟨fun t => Multiplicative.ofAdd (composition t).1, fun _ _ => rfl⟩
  have he : F = G := FreeMagma.hom_ext (by
    funext b; change Multiplicative.ofAdd (alphaLeaves (.of b)).card = Multiplicative.ofAdd (composition (.of b)).1
    cases b <;> simp [alpha_of, composition])
  exact congrArg (fun f : Source →ₙ* Multiplicative ℕ => Multiplicative.toAdd (f t)) he

theorem leaf_data (t : Source) :
    (∀ u ∈ leafAddresses t, u.length ≤ height t) ∧
    ((leafAddresses t).filter (fun u => readout u t = .beta)).card = (composition t).2 := by
  classical
  have addresses_mul (s t : Source) : leafAddresses (s * t) =
      (leafAddresses s).image (List.cons false) ∪
        (leafAddresses t).image (List.cons true) := by
    simp only [leafAddresses, leaves, List.toFinset_append]
    exact congrArg₂ (fun A B : Finset Address => A ∪ B)
      (Multiset.toFinset_map (List.cons false) (leaves s))
      (Multiset.toFinset_map (List.cons true) (leaves t))
  have prefix_disjoint (A B : Finset Address) :
      Disjoint (A.image (List.cons false)) (B.image (List.cons true)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    rcases Finset.mem_image.mp hu with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨b, _, hb⟩
    simp at hb
  induction t with
  | of b =>
    refine ⟨?_, ?_⟩
    · intro u hu
      have he : u = [] := by simpa [leafAddresses, leaves] using hu
      subst u
      exact Nat.zero_le _
    · cases b <;> simp [leafAddresses, leaves, Finset.filter_singleton, readout, composition]
  | mul s t hs ht =>
    obtain ⟨hds, hbs⟩ := hs
    obtain ⟨hdt, hbt⟩ := ht
    refine ⟨?_, ?_⟩
    · intro u hu
      rw [FreeMagma.mul_eq, addresses_mul] at hu
      rcases Finset.mem_union.mp hu with hu | hu
      · rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
        have hv := hds v hv
        have hm := Nat.le_max_left (height s) (height t)
        change v.length + 1 ≤ max (height s) (height t) + 1
        omega
      · rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
        have hv := hdt v hv
        have hm := Nat.le_max_right (height s) (height t)
        change v.length + 1 ≤ max (height s) (height t) + 1
        omega
    · have hf : (leafAddresses (.mul s t)).filter (fun u => readout u (.mul s t) = .beta) =
          ((leafAddresses s).filter (fun u => readout u s = .beta)).image (List.cons false) ∪
          ((leafAddresses t).filter (fun u => readout u t = .beta)).image (List.cons true) := by
        ext u
        cases u with
        | nil => simp [addresses_mul, readout]
        | cons b u => cases b <;> simp [addresses_mul, readout]
      rw [hf, Finset.card_union_of_disjoint (prefix_disjoint _ _),
        Finset.card_image_of_injective _ List.cons_injective,
        Finset.card_image_of_injective _ List.cons_injective, hbs, hbt]
      rfl
private theorem structural (t : Source) :
    AlphaCovered (substitution (substitution t)) ∧
    (∀ u ∈ alphaLeaves (substitution (substitution t)), ∃ r : Address,
      u = r ++ [true] ∧ subtree r (substitution (substitution t)) =
        some (.mul (.of false) (.of true))) ∧
    (∃ u ∈ alphaLeaves (substitution (substitution t)),
      u.length = height (substitution (substitution t))) := by
  induction t with
  | of b =>
    cases b with
    | true =>
      change AlphaCovered (.mul (.of false) (.of true)) ∧ _
      refine ⟨by simp [AlphaCovered, alpha_mul, alpha_of], ?_, ?_⟩
      · intro u hu
        have he : u = [true] := by simpa [alpha_mul, alpha_of, substitution] using hu
        subst u
        exact ⟨[], rfl, rfl⟩
      · exact ⟨[true], by simp [alpha_mul, alpha_of, substitution], rfl⟩
    | false =>
      change AlphaCovered (.mul (.mul (.of false) (.of true)) (.of false)) ∧ _
      refine ⟨by simp [AlphaCovered, alpha_mul, alpha_of], ?_, ?_⟩
      · intro u hu
        have he : u = [false, true] := by simpa [alpha_mul, alpha_of, substitution] using hu
        subst u
        exact ⟨[false], rfl, rfl⟩
      · exact ⟨[false, true], by simp [alpha_mul, alpha_of, substitution], rfl⟩
  | mul s t hs ht =>
    let S := substitution (substitution s)
    let T := substitution (substitution t)
    change AlphaCovered (.mul S T) ∧
      (∀ u ∈ alphaLeaves (.mul S T), ∃ r : Address,
        u = r ++ [true] ∧ subtree r (.mul S T) =
          some (.mul (.of false) (.of true))) ∧
      (∃ u ∈ alphaLeaves (.mul S T), u.length = height (.mul S T))
    obtain ⟨hsc, hst, us, hus, hds⟩ := hs
    obtain ⟨htc, htt, ut, hut, hdt⟩ := ht
    refine ⟨⟨hsc, htc, ⟨false :: us, ?_⟩⟩, ?_, ?_⟩
    · rw [FreeMagma.mul_eq, alpha_mul]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨us, hus, rfl⟩)
    · intro u hu
      rw [FreeMagma.mul_eq, alpha_mul] at hu
      rcases Finset.mem_union.mp hu with hu | hu
      · rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
        obtain ⟨r, hr, hs⟩ := hst v hv
        exact ⟨false :: r, by simp [hr], by simpa [ActualLeafHistoryRigidity.subtree] using hs⟩
      · rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
        obtain ⟨r, hr, ht⟩ := htt v hv
        exact ⟨true :: r, by simp [hr], by simpa [ActualLeafHistoryRigidity.subtree] using ht⟩
    · rw [FreeMagma.mul_eq, alpha_mul]
      rcases le_total (height S) (height T) with hle | hle
      · refine ⟨true :: ut, Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨ut, hut, rfl⟩), ?_⟩
        change ut.length + 1 = max (height S) (height T) + 1
        rw [hdt, max_eq_right hle]
      · refine ⟨false :: us, Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨us, hus, rfl⟩), ?_⟩
        change us.length + 1 = max (height S) (height T) + 1
        rw [hds, max_eq_left hle]
theorem no_left_alpha (t : Source) (ht : Positive t) (r : Address)
    (hr : subtree (r ++ [false]) t = some (.of true)) : False := by
  have ha : readout (r ++ [false]) t = .alpha := by
    rw [← List.append_nil (r ++ [false]),
      ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr]
    rfl
  obtain ⟨z, hz, _⟩ := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.1
    t ht (r ++ [false]) .alpha (Or.inl rfl) ha
  simp [ActualLeafHistoryRigidity.decodeBlock, List.reverse_append] at hz

private theorem swap_local (V : Source) (r : Address)
    (hr : subtree r V = some (.mul (.of false) (.of true))) :
    composition (replace V r (.mul (.of true) (.of false))) = composition V ∧
    subtree (r ++ [false]) (replace V r (.mul (.of true) (.of false))) =
      some (.of true) ∧
    (∀ u : Address, u ≠ r ++ [false] → u ≠ r ++ [true] →
      readout u (replace V r (.mul (.of true) (.of false))) = readout u V) := by
  induction r generalizing V with
  | nil =>
    have he : V = .mul (.of false) (.of true) :=
      Option.some.inj (by simpa only [ActualLeafHistoryRigidity.subtree] using hr)
    subst V
    refine ⟨rfl, rfl, ?_⟩
    intro u hL hR
    cases u with
    | nil => rfl
    | cons b u =>
      cases u with
      | nil => cases b <;> simp_all
      | cons c u => cases b <;> rfl
  | cons b r ih =>
    cases V with
    | of c => simp [ActualLeafHistoryRigidity.subtree] at hr
    | mul s t =>
      cases b with
      | false =>
        obtain ⟨hc, hl, ho⟩ := ih s hr
        refine ⟨congrArg (fun v => v + composition t) hc, hl, ?_⟩
        intro u hL hR
        cases u with
        | nil => rfl
        | cons b u =>
          cases b with
          | true => rfl
          | false =>
            exact ho u (fun he => hL (congrArg (List.cons false) he))
              (fun he => hR (congrArg (List.cons false) he))
      | true =>
        obtain ⟨hc, hl, ho⟩ := ih t hr
        refine ⟨congrArg (fun v => composition s + v) hc, hl, ?_⟩
        intro u hL hR
        cases u with
        | nil => rfl
        | cons b u =>
          cases b with
          | false => rfl
          | true =>
            exact ho u (fun he => hL (congrArg (List.cons true) he))
              (fun he => hR (congrArg (List.cons true) he))

set_option maxHeartbeats 2000000 in -- Combined reconstruction and swap-counting proof.
/-- Exact positive certificate cardinality for d = 3k, k at least one.
The same-composition competitor domain is all complete ordered source trees. -/
theorem result (k : ℕ) (hk : 1 ≤ k) (V : Source)
    (hV : V ∈ ActualImage (3 * k)) (h : ℕ) :
    (h < height V → ¬ ∃ Q : Finset Address, Sound (3 * k) V h Q) ∧
    (height V ≤ h → ∃ Q : Finset Address,
      Sound (3 * k) V h Q ∧ Q.card = (composition V).1) ∧
    (∀ Q : Finset Address, Sound (3 * k) V h Q → (composition V).1 ≤ Q.card) := by
  classical
  have alpha_spec (t : Source) (u : Address) :
      u ∈ alphaLeaves t ↔ readout u t = .alpha :=
    ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 t u
  have alpha_depth (t : Source) (u : Address) (hu : u ∈ alphaLeaves t) :
      u.length ≤ height t := (leaf_data t).1 u (Finset.mem_filter.mp hu).1
  have upper (V U : Source) (hc : AlphaCovered V)
      (hm : ∀ u ∈ alphaLeaves V, readout u U = .alpha) :
      (composition V).1 + (composition V).2 ≤ (composition U).1 + (composition U).2 ∧
      (composition V).1 ≤ (composition U).1 ∧
      (composition U = composition V → U = V) := by
    induction V generalizing U with
    | of b =>
      cases b with
      | false =>
        refine ⟨by have hp := positive U; change 1 ≤ _; omega, by simp [composition], ?_⟩
        intro he
        cases U with
        | of c => cases c <;> simp_all [composition]
        | mul s t =>
          have hp := positive s
          have hq := positive t
          have htotal := congrArg (fun p : ℕ × ℕ => p.1 + p.2) he
          simp only [composition, Prod.fst_add, Prod.snd_add] at htotal
          omega
      | true =>
        have hu := hm [] (by simp [alpha_mul, alpha_of])
        have he : U = .of true := by
          cases U with
          | of c => cases c <;> simp_all [readout]
          | mul s t => simp [readout] at hu
        subst U
        exact ⟨le_rfl, le_rfl, fun _ => rfl⟩
    | mul s t hs ht =>
      rcases hc with ⟨hcs, hct, u, hu⟩
      cases U with
      | of b =>
        have ho := hm u hu
        cases u with
        | nil => simp [alpha_mul, alpha_of] at hu
        | cons c u => simp [readout] at ho
      | mul x y =>
        have hms : ∀ u ∈ alphaLeaves s, readout u x = .alpha := by
          intro u hu
          exact hm (false :: u) (by rw [FreeMagma.mul_eq, alpha_mul]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
        have hmt : ∀ u ∈ alphaLeaves t, readout u y = .alpha := by
          intro u hu
          exact hm (true :: u) (by rw [FreeMagma.mul_eq, alpha_mul]; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
        obtain ⟨hls, has, hes⟩ := hs x hcs hms
        obtain ⟨hlt, hat, het⟩ := ht y hct hmt
        refine ⟨?_, ?_, ?_⟩
        · simp only [composition, Prod.fst_add, Prod.snd_add]
          omega
        · simp only [composition, Prod.fst_add]
          omega
        · intro he
          have ha := congrArg Prod.fst he
          have hb := congrArg Prod.snd he
          simp only [composition, Prod.fst_add, Prod.snd_add] at ha hb
          have hx : composition x = composition s := by
            apply Prod.ext <;> omega
          have hy : composition y = composition t := by
            apply Prod.ext <;> omega
          exact congrArg₂ FreeMagma.mul (hes hx) (het hy)
  have endpoint_parent (r s : Address) (b c : Bool)
      (he : r ++ [b] = s ++ [c]) : r = s := by
    have hr := congrArg List.reverse he
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.cons.injEq] at hr
    exact List.reverse_injective hr.2
  obtain ⟨T, hT⟩ := hV
  let S := substitution^[3 * k - 2] T
  have hv2 : V = substitution (substitution S) := by
    change V = substitution^[2] S
    dsimp only [S]
    rw [← Function.iterate_add_apply]
    rw [show 2 + (3 * k - 2) = 3 * k by omega]
    exact hT.symm
  obtain ⟨hcovered, hterminal, udeep, hudeep, hdepth⟩ := structural S
  rw [← hv2] at hcovered hterminal hudeep hdepth
  have original : V ∈ ActualImage (3 * k) := ⟨T, hT⟩
  have swapped_negative (r : Address)
      (hr : subtree r V = some (.mul (.of false) (.of true))) :
      replace V r (.mul (.of true) (.of false)) ∉ ActualImage (3 * k) := by
    intro hW
    exact no_left_alpha _ (image_positive (d := 3 * k) (by omega) _ hW) r (swap_local V r hr).2.1
  have hits (Q : Finset Address) (hQ : Sound (3 * k) V h Q)
      (u : Address) (hu : u ∈ alphaLeaves V) :
      ∃ r : Address, u = r ++ [true] ∧ (r ++ [false] ∈ Q ∨ r ++ [true] ∈ Q) := by
    obtain ⟨r, hur, hr⟩ := hterminal u hu
    refine ⟨r, hur, ?_⟩
    by_contra hn
    have hL : r ++ [false] ∉ Q := fun he => hn (Or.inl he)
    have hR : r ++ [true] ∉ Q := fun he => hn (Or.inr he)
    obtain ⟨hc, _, ho⟩ := swap_local V r hr
    apply swapped_negative r hr
    apply hQ.2 _ hc
    intro q hq
    exact ho q (fun he => hL (he ▸ hq)) (fun he => hR (he ▸ hq))
  refine ⟨?_, ?_, ?_⟩
  · intro hsmall ⟨Q, hQ⟩
    obtain ⟨r, hur, hr⟩ := hterminal udeep hudeep
    have hlen : (r ++ [false]).length = height V ∧
        (r ++ [true]).length = height V := by
      rw [hur] at hdepth
      simp only [List.length_append, List.length_singleton] at hdepth ⊢
      exact ⟨hdepth, hdepth⟩
    obtain ⟨hc, _, ho⟩ := swap_local V r hr
    apply swapped_negative r hr
    apply hQ.2 _ hc
    intro q hq
    have hb := hQ.1 q hq
    apply ho q
    · intro he
      have he := congrArg List.length he
      omega
    · intro he
      have he := congrArg List.length he
      omega
  · intro hlarge
    refine ⟨alphaLeaves V, ⟨?_, ?_⟩, alpha_card V⟩
    · intro u hu
      exact (alpha_depth V u hu).trans hlarge
    · intro U hc hm
      have hu : U = V := (upper V U hcovered (fun u hu =>
        (hm u hu).trans ((alpha_spec V u).mp hu))).2.2 hc
      exact hu ▸ original
  · intro Q hQ
    have query_for (u : {u : Address // u ∈ alphaLeaves V}) :
        ∃ q : {q : Address // q ∈ Q}, ∃ r : Address, ∃ b : Bool,
          u.val = r ++ [true] ∧ q.val = r ++ [b] := by
      obtain ⟨r, hu, hL | hR⟩ := hits Q hQ u.val u.property
      · exact ⟨⟨r ++ [false], hL⟩, r, false, hu, rfl⟩
      · exact ⟨⟨r ++ [true], hR⟩, r, true, hu, rfl⟩
    let f : {u : Address // u ∈ alphaLeaves V} → {q : Address // q ∈ Q} :=
      fun u => Classical.choose (query_for u)
    have hf : Function.Injective f := by
      intro u v he
      obtain ⟨r, b, hu, hq⟩ := Classical.choose_spec (query_for u)
      obtain ⟨s, c, hv, hp⟩ := Classical.choose_spec (query_for v)
      have heq : r ++ [b] = s ++ [c] :=
        hq.symm.trans ((congrArg Subtype.val he).trans hp)
      have hrs := endpoint_parent r s b c heq
      apply Subtype.ext
      exact hu.trans ((congrArg (fun r : Address => r ++ [true]) hrs).trans hv.symm)
    rw [← alpha_card V]
    exact Finset.card_le_card_of_injective hf
theorem leaf_change (t : Source) (s : Address) (b c : Bool)
    (hs : subtree s t = some (.of b)) :
    subtree s (replace t s (.of c)) = some (.of c) ∧
    composition (replace t s (.of c)) + composition (.of b) =
      composition t + composition (.of c) ∧
    (∀ u, u ≠ s → readout u (replace t s (.of c)) = readout u t) := by
  induction s generalizing t with
  | nil =>
    have he : t = .of b := Option.some.inj (by simpa only [ActualLeafHistoryRigidity.subtree] using hs)
    subst t
    refine ⟨rfl, add_comm _ _, ?_⟩
    intro u hu
    cases u with
    | nil => exact (hu rfl).elim
    | cons x u => simp only [replace, readout]
  | cons x s ih =>
    cases t with
    | of b => simp [ActualLeafHistoryRigidity.subtree] at hs
    | mul v w =>
      cases x with
      | false =>
        obtain ⟨hr, hc, ho⟩ := ih v hs
        refine ⟨hr, ?_, ?_⟩
        · change (composition (replace v s (.of c)) + composition w) + composition (.of b) =
            (composition v + composition w) + composition (.of c)
          simpa only [add_assoc, add_left_comm, add_comm] using congrArg (· + composition w) hc
        · intro u hu
          cases u with
          | nil => rfl
          | cons x u => cases x with
            | true => rfl
            | false => exact ho u (fun he => hu (congrArg (List.cons false) he))
      | true =>
        obtain ⟨hr, hc, ho⟩ := ih w hs
        refine ⟨hr, ?_, ?_⟩
        · change (composition v + composition (replace w s (.of c))) + composition (.of b) =
            (composition v + composition w) + composition (.of c)
          simpa only [add_assoc] using congrArg (composition v + ·) hc
        · intro u hu
          cases u with
          | nil => rfl
          | cons x u => cases x with
            | false => rfl
            | true => exact ho u (fun he => hu (congrArg (List.cons true) he))
private theorem no_beta_cherry (t : Source) (ht : Positive t) (r : Address)
    (hl : readout (r ++ [false]) t = .beta)
    (hr : readout (r ++ [true]) t = .beta) : False := by
  have hs := (ActualLeafHistoryRigidity.actual_address_geometry.2.2.1 t ht r).1 hr
  rw [ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hs] at hl
  cases hl

theorem image_structure (k : ℕ) (hk : 1 ≤ k) (U : Source) (hU : U ∈ ActualImage (3 * k)) :
    AlphaCovered U ∧ ∀ u ∈ alphaLeaves U, ∃ r : Address,
      u = r ++ [true] ∧ subtree r U = some (.mul (.of false) (.of true)) := by
  obtain ⟨T, hT⟩ := hU
  let S := substitution^[3 * k - 2] T
  have he : U = substitution (substitution S) := by
    change U = substitution^[2] S
    dsimp only [S]
    rw [← Function.iterate_add_apply, show 2 + (3 * k - 2) = 3 * k by omega]
    exact hT.symm
  rw [he]
  exact ⟨(structural S).1, (structural S).2.1⟩

theorem beta_surplus (k : ℕ) (hk : 1 ≤ k) (V : Source)
  (hV : V ∈ ActualImage (3 * k)) : (composition V).1 < (composition V).2 := by
  obtain ⟨T, hT⟩ := hV
  let Z := substitution^[3 * k - 3] T
  have he : substitution^[3] Z = V := by
    dsimp only [Z]
    rw [← Function.iterate_add_apply, show 3 + (3 * k - 3) = 3 * k by omega]
    exact hT
  have hc := (GenealogicalFiberTransport.fiberMap (composition Z) 3 ⟨Z, rfl⟩).property
  change composition (substitution^[3] Z) = GraftAffineClosure.step^[3] (composition Z) at hc
  rw [he] at hc
  have ha := congrArg Prod.fst hc
  have hb := congrArg Prod.snd hc
  simp [Function.iterate_succ_apply', GraftAffineClosure.step] at ha hb
  have hp := positive Z
  omega

theorem exchange_composition (V : Source) (s t : Address)
    (hc₁ : composition (replace V s (.of false)) + composition (.of true) =
      composition V + composition (.of false))
    (hc₂ : composition (replace (replace V s (.of false)) t (.of true)) + composition (.of false) =
      composition (replace V s (.of false)) + composition (.of true)) :
    composition (replace (replace V s (.of false)) t (.of true)) = composition V := by
  have ha₁ := congrArg Prod.fst hc₁
  have hb₁ := congrArg Prod.snd hc₁
  have ha₂ := congrArg Prod.fst hc₂
  have hb₂ := congrArg Prod.snd hc₂
  simp only [Prod.fst_add, Prod.snd_add, composition] at ha₁ hb₁ ha₂ hb₂
  apply Prod.ext <;> omega

theorem exchange_conflict (V W₁ W : Source) (s t r : Address)
    (hst : s ≠ t) (hsr : s = r ++ [true])
    (hr : subtree r V = some (.mul (.of false) (.of true)))
    (ht : readout t V = .beta) (h₁s : subtree s W₁ = some (.of false))
    (h₂t : subtree t W = some (.of true))
    (ho₁ : ∀ u : Address, u ≠ s → readout u W₁ = readout u V)
    (ho₂ : ∀ u : Address, u ≠ t → readout u W = readout u W₁)
    (hW : Positive W) : False := by
  have distinct (r : Address) : r ++ [false] ≠ r ++ [true] := by simp
  have subtree_readout (t v : Source) (r u : Address)
      (hr : subtree r t = some v) : readout (r ++ u) t = readout u v := by
    rw [ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r u t, hr]
  by_cases htl : t = r ++ [false]
  · exact no_left_alpha W hW r (htl ▸ h₂t)
  · have hl : readout (r ++ [false]) W = .beta := by
      exact (ho₂ _ (fun he => htl he.symm)).trans ((ho₁ _ (by rw [hsr]; exact distinct r)).trans
        (subtree_readout V _ r [false] hr))
    have hsW₁ : readout s W₁ = .beta := by
      simpa only [List.append_nil, readout] using subtree_readout W₁ (.of false) s [] h₁s
    have hsW : readout s W = .beta := (ho₂ s hst).trans hsW₁
    exact no_beta_cherry W hW r hl (hsr ▸ hsW)

set_option maxHeartbeats 2000000 in -- Two leaf replacements and whole-tree reconstruction.
/-- Uniqueness of the optimal fixed-composition certificate, and complete-leaf
certificates when competitors have no composition or leaf-count promise. -/
theorem rigidity (k : ℕ) (hk : 1 ≤ k) (V : Source)
    (hV : V ∈ ActualImage (3 * k)) :
    (∀ h, height V ≤ h → ∀ Q : Finset Address, Within h Q →
      (Sound (3 * k) V h Q ∧ Q.card = (composition V).1 ↔ Q = alphaLeaves V)) ∧
    (∀ h, ∀ Q : Finset Address, Within h Q →
      (UnSound (3 * k) V Q ↔ leafAddresses V ⊆ Q)) ∧
    (∀ h, h < height V → ¬ ∃ Q : Finset Address, Within h Q ∧ UnSound (3 * k) V Q) ∧
    (∀ h, height V ≤ h → Within h (leafAddresses V) ∧
      UnSound (3 * k) V (leafAddresses V) ∧
      (leafAddresses V).card = (composition V).1 + (composition V).2 ∧
      ∀ Q : Finset Address, Within h Q → UnSound (3 * k) V Q →
        (composition V).1 + (composition V).2 ≤ Q.card ∧
        (Q.card = (composition V).1 + (composition V).2 ↔ Q = leafAddresses V)) := by
  classical
  have alpha_spec (t : Source) (u : Address) :
      u ∈ alphaLeaves t ↔ readout u t = .alpha :=
    ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 t u
  have leaf_subtree (t : Source) (u : Address) (b : Bool)
      (hs : readout u t = readout [] (.of b)) : subtree u t = some (.of b) :=
    ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t u b (by cases b <;> exact hs)
  obtain ⟨hcovered, hterminal⟩ := image_structure k hk V hV
  have beta_surplus := beta_surplus k hk V hV
  have optimal_unique (h : ℕ) (Q : Finset Address)
      (hQ : Sound (3 * k) V h Q) (hcard : Q.card = (composition V).1) :
      Q = alphaLeaves V := by
    have hsub : alphaLeaves V ⊆ Q := by
      intro s hs
      by_contra hsQ
      let B := (leafAddresses V).filter (fun u => readout u V = .beta)
      have hB : B.card = (composition V).2 := (leaf_data V).2
      obtain ⟨t, htB, htQ⟩ : ∃ t ∈ B, t ∉ Q := by
        by_contra hn
        have hsub : B ⊆ Q := by
          intro t ht
          by_contra htQ
          exact hn ⟨t, ht, htQ⟩
        have hle := Finset.card_le_card hsub
        omega
      have ht : readout t V = .beta := (Finset.mem_filter.mp htB).2
      have hsA := (alpha_spec V s).mp hs
      have hst : s ≠ t := by intro he; rw [he, ht] at hsA; contradiction
      obtain ⟨r, hsr, hr⟩ := hterminal s hs
      let W₁ := replace V s (.of false)
      obtain ⟨h₁s, hc₁, ho₁⟩ := leaf_change V s true false (leaf_subtree V s true hsA)
      have h₁t : subtree t W₁ = some (.of false) :=
        leaf_subtree W₁ t false ((ho₁ t hst.symm).trans ht)
      let W := replace W₁ t (.of true)
      obtain ⟨h₂t, hc₂, ho₂⟩ := leaf_change W₁ t false true h₁t
      have hc : composition W = composition V := exchange_composition V s t hc₁ hc₂
      have hW : W ∈ ActualImage (3 * k) := hQ.2 W hc (by
        intro u hu
        exact (ho₂ u (fun he => htQ (he ▸ hu))).trans
          (ho₁ u (fun he => hsQ (he ▸ hu))))
      exact exchange_conflict V W₁ W s t r hst hsr hr ht h₁s h₂t ho₁ ho₂
        (image_positive (d := 3 * k) (by omega) W hW)
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [alpha_card V, hcard])).symm
  have leaf_iff (Q : Finset Address) : UnSound (3 * k) V Q ↔ leafAddresses V ⊆ Q := by
    constructor
    · intro hQ s hs
      by_contra hsQ
      have hsL : s ∈ leaves V := List.mem_toFinset.mp hs
      obtain ⟨T, hT⟩ := image_positive (d := 3 * k) (by omega) V hV
      have hn := ActualTreeReadoutAcquisition.source_foundation.2.1 T s (hT ▸ hsL)
      apply hn
      rw [hT]
      apply image_positive (d := 3 * k) (by omega)
      apply hQ (flip V s)
      intro u hu
      exact ActualTreeReadoutAcquisition.source_foundation.2.2.2.1 V s hsL u
        (fun he => hsQ (he ▸ hu))
    · intro hsub U hm
      have he := ActualTreeReadoutAcquisition.source_foundation.2.2.1 V U (by
        intro u hu
        exact hm u (hsub (List.mem_toFinset.mpr hu)))
      exact he ▸ hV
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h hlarge Q hwithin
    constructor
    · rintro ⟨hsound, hcard⟩
      exact optimal_unique h Q hsound hcard
    · intro he
      subst Q
      obtain ⟨R, hs, hc⟩ := (result k hk V hV h).2.1 hlarge
      have he := optimal_unique h R hs hc
      exact he ▸ ⟨hs, hc⟩
  · intro h Q _
    exact leaf_iff Q
  · intro h hsmall ⟨Q, hwithin, hsound⟩
    apply (result k hk V hV h).1 hsmall
    exact ⟨Q, hwithin, fun U _ hm => hsound U hm⟩
  · intro h hlarge
    refine ⟨fun u hu => ((leaf_data V).1 u hu).trans hlarge,
      (leaf_iff _).mpr (fun _ hu => hu), leaf_card V, ?_⟩
    intro Q _ hsound
    have hsub := (leaf_iff Q).mp hsound
    have hle := Finset.card_le_card hsub
    rw [leaf_card V] at hle
    refine ⟨hle, ?_⟩
    constructor
    · intro hcard
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [leaf_card V, hcard])).symm
    · intro he
      rw [he, leaf_card V]

set_option maxHeartbeats 4000000 in -- Weighted height induction and prescribed path witnesses.
/-- The sharp leaf budget above each height, with explicit same-composition
swaps invisible throughout the finite depth window. -/
theorem heightFrontier (k : ℕ) (hk : 1 ≤ k) (h : ℕ) :
    let d := 3 * k
    let A := substitution^[d] (.of true)
    let B := substitution^[d] (.of false)
    let a := Nat.fib (d + 1)
    let b := Nat.fib (d + 2)
    let m := h + 1 - d
    let C := if h ≤ d - 2 then a else b + a * m
    let V := if h ≤ d - 2 then A else substitution^[d] (rightComb m)
    let r := if h ≤ d - 2 then List.replicate (d - 2) false
      else List.replicate m true ++ List.replicate (d - 1) false
    let W := replace V r (.mul (.of true) (.of false))
    height A = d - 1 ∧ height B = d ∧
    composition A = (Nat.fib (d - 1), Nat.fib d) ∧
    composition B = (Nat.fib d, Nat.fib (d + 1)) ∧
    (leafAddresses A).card = a ∧ (leafAddresses B).card = b ∧
    b = a + Nat.fib d ∧ b < 2 * a ∧
    (∀ X : Source, X ∈ ActualImage d → h < height X → C ≤ (leafAddresses X).card) ∧
    V ∈ ActualImage d ∧ h < height V ∧
    subtree r V = some (.mul (.of false) (.of true)) ∧
    W ∉ ActualImage d ∧ composition W = composition V ∧
    (∀ u : Address, u.length ≤ h → readout u W = readout u V) ∧
    (leafAddresses V).card = C ∧
    (d - 1 ≤ h → composition V =
      (Nat.fib (d - 1) * m + Nat.fib d, Nat.fib d * m + Nat.fib (d + 1)) ∧
      subtree (List.replicate m true) V = some B) := by
  classical
  dsimp only
  let d := 3 * k
  let T : ℕ → Source := fun j => substitution^[j] (.of true)
  let A := T d
  let B := substitution^[d] (.of false)
  let a := Nat.fib (d + 1)
  let b := Nat.fib (d + 2)
  let N : Source → ℕ := fun X => (composition X).1 + (composition X).2
  have hd : 3 ≤ d := by dsimp only [d]; omega
  have hom (j : ℕ) : Function.Semiconj₂ (substitution^[j]) FreeMagma.mul FreeMagma.mul :=
    Function.Semiconj₂.iterate (fun s t => substitution.map_mul s t) j
  have pairN (S R : Source) : N (.mul S R) = N S + N R := by
    dsimp only [N, composition, Prod.fst_add, Prod.snd_add]; omega
  have recurrence (j : ℕ) : T (j + 2) = .mul (T (j + 1)) (T j) := by
    have he := (SourceTransportCentralizer.source_transport_centralizer.1 (T j)).mpr ⟨j, rfl⟩
    simpa only [T, Function.iterate_succ_apply', Nat.add_assoc] using he
  have blocks (j : ℕ) : height (T (j + 1)) = j ∧ height (T (j + 2)) = j + 1 ∧
      subtree (List.replicate j false) (T (j + 2)) = some (.mul (.of false) (.of true)) := by
    induction j with
    | zero => exact ⟨rfl, rfl, rfl⟩
    | succ j ih =>
      refine ⟨ih.2.1, ?_, ?_⟩
      · rw [recurrence]
        change max (height (T (j + 1 + 1))) (height (T (j + 1))) + 1 = j + 1 + 1
        rw [show j + 1 + 1 = j + 2 by omega, ih.2.1, ih.1, max_eq_left (by omega)]
      · rw [recurrence (j + 1), List.replicate_succ]
        exact ih.2.2
  have block_comp (j : ℕ) (hj : 0 < j) : composition (T j) =
      (Nat.fib (j - 1), Nat.fib j) := by
    let c := GraftAffineClosure.atomicBlock j
    have hc := (GenealogicalFiberTransport.fiberMap (1, 0) j ⟨.of true, rfl⟩).property
    change composition (T j) = c at hc
    have hall := GraftAffineClosure.result.2 1 (by decide) c
    have ha := hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j rfl
    exact hc.trans (ha.2.2.2.2.1 hj)
  have hB : B = T (d + 1) := (Function.iterate_succ_apply substitution d (.of true)).symm
  have hAheight : height A = d - 1 := by
    have he := (blocks (d - 2)).2.1
    simpa only [show d - 2 + 2 = d by omega, show d - 2 + 1 = d - 1 by omega] using he
  have hBheight : height B = d := by rw [hB]; exact (blocks d).1
  have hAc : composition A = (Nat.fib (d - 1), Nat.fib d) := block_comp d (by omega)
  have hBc : composition B = (Nat.fib d, Nat.fib (d + 1)) := by
    rw [hB, block_comp (d + 1) (by omega), Nat.add_sub_cancel]
  have hNa : N A = a := by
    dsimp only [N, a]; rw [hAc]
    have hf := Nat.fib_add_two (n := d - 1)
    rw [show d - 1 + 1 = d by omega, show d - 1 + 2 = d + 1 by omega] at hf
    exact hf.symm
  have hNb : N B = b := by dsimp only [N, b]; rw [hBc]; exact Nat.fib_add_two.symm
  have hba : b = a + Nat.fib d := by dsimp only [a, b]; rw [Nat.fib_add_two, Nat.add_comm]
  have hgap : b < 2 * a := by
    have hl := Nat.fib_lt_fib_succ (n := d) (by omega)
    dsimp only [a] at *; omega
  have envelope (X : Source) : a ≤ N (substitution^[d] X) ∧
      (d ≤ height (substitution^[d] X) →
        b + a * (height (substitution^[d] X) - d) ≤ N (substitution^[d] X)) := by
    have extend (D n p : ℕ) (hn : a ≤ n) (hp : a ≤ p)
        (he : d ≤ D → b + a * (D - d) ≤ n) (hD : d ≤ D + 1) :
        b + a * (D + 1 - d) ≤ n + p := by
      by_cases hx : d ≤ D
      · have ht := he hx
        rw [show D + 1 - d = (D - d) + 1 by omega, Nat.mul_add, Nat.mul_one]
        omega
      · have hz : D + 1 - d = 0 := by omega
        rw [hz, Nat.mul_zero, Nat.add_zero]; omega
    induction X with
    | of c => cases c with
      | true => refine ⟨by rw [hNa], ?_⟩; intro he; rw [hAheight] at he; omega
      | false => refine ⟨by rw [hNb]; omega, ?_⟩; intro _; rw [hBheight, hNb]; simp
    | mul S R hs hr =>
      rw [hom d, pairN]
      change a ≤ N (substitution^[d] S) + N (substitution^[d] R) ∧
        (d ≤ max (height (substitution^[d] S)) (height (substitution^[d] R)) + 1 →
        b + a * (max (height (substitution^[d] S)) (height (substitution^[d] R)) + 1 - d) ≤
          N (substitution^[d] S) + N (substitution^[d] R))
      refine ⟨by omega, ?_⟩
      rcases le_total (height (substitution^[d] S)) (height (substitution^[d] R)) with he | he
      · rw [max_eq_right he]; intro hl
        simpa only [Nat.add_comm] using extend _ _ _ hr.1 hs.1 hr.2 hl
      · rw [max_eq_left he]; exact extend _ _ _ hs.1 hr.1 hs.2
  have comb (m : ℕ) : height (substitution^[d] (rightComb m)) = m + d ∧
      N (substitution^[d] (rightComb m)) = b + a * m ∧
      composition (substitution^[d] (rightComb m)) =
        (Nat.fib (d - 1) * m + Nat.fib d, Nat.fib d * m + Nat.fib (d + 1)) ∧
      subtree (List.replicate m true) (substitution^[d] (rightComb m)) = some B := by
    induction m with
    | zero =>
      simp only [rightComb, Nat.zero_add, Nat.mul_zero, Nat.add_zero, List.replicate_zero]
      exact ⟨hBheight, hNb, hBc, by simp only [ActualLeafHistoryRigidity.subtree]; rfl⟩
    | succ m ih =>
      rw [rightComb, hom d]
      refine ⟨?_, ?_, ?_, ?_⟩
      · change max (height A) (height (substitution^[d] (rightComb m))) + 1 = m + 1 + d
        rw [hAheight, ih.1, max_eq_right (by omega)]; omega
      · rw [pairN]
        change N A + N (substitution^[d] (rightComb m)) = b + a * (m + 1)
        rw [hNa, ih.2.1]; ring
      · change composition A + composition (substitution^[d] (rightComb m)) = _
        rw [hAc, ih.2.2.1]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
      · rw [List.replicate_succ]; exact ih.2.2.2
  have cherryA : subtree (List.replicate (d - 2) false) A =
      some (.mul (.of false) (.of true)) := by
    simpa only [show d - 2 + 2 = d by omega] using (blocks (d - 2)).2.2
  have cherryB : subtree (List.replicate (d - 1) false) B =
      some (.mul (.of false) (.of true)) := by
    rw [hB]; simpa only [show d - 1 + 2 = d + 1 by omega] using (blocks (d - 1)).2.2
  let m := h + 1 - d
  let C := if h ≤ d - 2 then a else b + a * m
  let V := if h ≤ d - 2 then A else substitution^[d] (rightComb m)
  let r := if h ≤ d - 2 then List.replicate (d - 2) false
    else List.replicate m true ++ List.replicate (d - 1) false
  let W := replace V r (.mul (.of true) (.of false))
  have lower (X : Source) (hX : X ∈ ActualImage d) (hh : h < height X) :
      C ≤ (leafAddresses X).card := by
    obtain ⟨Y, rfl⟩ := hX
    rw [leaf_card _]
    by_cases hlo : h ≤ d - 2
    · simpa only [C, if_pos hlo] using (envelope Y).1
    · simp only [C, if_neg hlo]
      have hD : d ≤ height (substitution^[d] Y) := by omega
      have hm : m ≤ height (substitution^[d] Y) - d := by dsimp only [m]; omega
      exact (Nat.add_le_add_left (Nat.mul_le_mul_left a hm) b).trans ((envelope Y).2 hD)
  have witness : V ∈ ActualImage d ∧ h < height V ∧
      N V = C ∧ subtree r V = some (.mul (.of false) (.of true)) ∧ h < r.length + 1 := by
    by_cases hlo : h ≤ d - 2
    · simp only [V, r, C, if_pos hlo]
      exact ⟨⟨.of true, rfl⟩, by rw [hAheight]; omega, hNa, cherryA,
        by rw [List.length_replicate]; omega⟩
    · simp only [V, r, C, if_neg hlo]
      refine ⟨⟨rightComb m, rfl⟩, ?_, (comb m).2.1, ?_, ?_⟩
      · rw [(comb m).1]; dsimp only [m]; omega
      · have append_sub (X Y : Source) (u v : Address)
            (hu : subtree u X = some Y) : subtree (u ++ v) X = subtree v Y := by
          rw [ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 u v X, hu]
          rfl
        rw [append_sub _ B _ _ (comb m).2.2.2]; exact cherryB
      · rw [List.length_append, List.length_replicate, List.length_replicate]
        dsimp only [m]; omega
  obtain ⟨hV, hh, hNV, hcherry, hdepth⟩ := witness
  obtain ⟨hcomp, hleft, hobs⟩ := swap_local V r hcherry
  have hW : W ∉ ActualImage d := by
    intro hW
    exact no_left_alpha W (image_positive (d := d) hd W hW) r hleft
  refine ⟨hAheight, hBheight, hAc, hBc, (leaf_card A).trans hNa,
    (leaf_card B).trans hNb, hba, hgap, lower, hV, hh, hcherry, hW, hcomp, ?_,
    (leaf_card V).trans hNV, ?_⟩
  · intro u hu
    apply hobs u <;> intro he <;>
      have he := congrArg List.length he <;>
      simp only [List.length_append, List.length_singleton] at he <;> omega
  · intro hhigh
    have hlo : ¬ h ≤ d - 2 := by omega
    change composition V =
      (Nat.fib (d - 1) * m + Nat.fib d, Nat.fib d * m + Nat.fib (d + 1)) ∧
      subtree (List.replicate m true) V = some B
    rw [show V = substitution^[d] (rightComb m) from if_neg hlo]
    exact ⟨(comb m).2.2.1, (comb m).2.2.2⟩

end D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate
