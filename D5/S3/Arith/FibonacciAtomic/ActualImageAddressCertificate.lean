/- GID: D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sharp cardinality and depth for actual substitution image certificates. -/

import D5.S0.History.FiniteDescriptionSelfCode
import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate

open GenealogicalFiberTransport (Source substitution composition decompose)
open D5.S0.History.FiniteDescriptionSelfCode (FiniteDescription)

/-- The four original endpoint observations, including the empty root address. -/
inductive Output
  | leafAlpha | leafBeta | branch | absent
  deriving DecidableEq

/-- Read the raw endpoint along a root-first finite description: false is left
and true is right. Leaf labels use true for alpha and false for beta, as in
GenealogicalFiberTransport.Source. Continuing beyond a leaf gives absent. -/
def out : Source → FiniteDescription → Output
  | .of true, [] => .leafAlpha
  | .of false, [] => .leafBeta
  | .mul _ _, [] => .branch
  | .of _, _ :: _ => .absent
  | .mul s _, false :: u => out s u
  | .mul _ t, true :: u => out t u

/-- Root depth is zero. Reuse the ordered shape from the existing decomposition. -/
def height (t : Source) : ℕ := (decompose t).1.height

/-- The actual image, with the complete ordered tree retained. -/
def ActualImage (d : ℕ) : Set Source := Set.range (substitution^[d])

/-- A finite query set obeys the raw path depth budget. -/
def Within (h : ℕ) (Q : Finset FiniteDescription) : Prop := ∀ u ∈ Q, u.length ≤ h

/-- Soundness ranges over every complete source of the same exact composition. -/
def Sound (d : ℕ) (V : Source) (h : ℕ) (Q : Finset FiniteDescription) : Prop :=
  Within h Q ∧ ∀ U : Source, composition U = composition V →
    (∀ u ∈ Q, out U u = out V u) → U ∈ ActualImage d

/-- All addresses carrying an alpha leaf. -/
def alphaAddresses : Source → Finset FiniteDescription
  | .of true => {[]}
  | .of false => ∅
  | .mul s t => (alphaAddresses s).image (List.cons false) ∪
      (alphaAddresses t).image (List.cons true)

/-- The complete subtree at an address, absent when the path passes a leaf. -/
def subtree : Source → FiniteDescription → Option Source
  | t, [] => some t
  | .of _, _ :: _ => none
  | .mul s _, false :: u => subtree s u
  | .mul _ t, true :: u => subtree t u

/-- Replace the subtree at a valid address; invalid addresses leave the tree alone. -/
def replace : Source → FiniteDescription → Source → Source
  | _, [], v => v
  | .of b, _ :: _, _ => .of b
  | .mul s t, false :: u, v => .mul (replace s u v) t
  | .mul s t, true :: u, v => .mul s (replace t u v)

/-- Every branch has an alpha descendant, recursively through the whole tree. -/
def AlphaCovered : Source → Prop
  | .of _ => True
  | .mul s t => AlphaCovered s ∧ AlphaCovered t ∧
      (alphaAddresses (.mul s t)).Nonempty

private theorem alpha_card (t : Source) : (alphaAddresses t).card = (composition t).1 := by
  have prefix_disjoint (A B : Finset FiniteDescription) :
      Disjoint (A.image (List.cons false)) (B.image (List.cons true)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    rcases Finset.mem_image.mp hu with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨b, _, hb⟩
    simp at hb
  induction t with
  | of b => cases b <;> simp [alphaAddresses, composition]
  | mul s t hs ht =>
    simp only [alphaAddresses, Finset.card_union_of_disjoint (prefix_disjoint _ _),
      Finset.card_image_of_injective _ List.cons_injective, composition,
      Prod.fst_add, hs, ht]

private theorem alpha_spec (t : Source) (u : FiniteDescription) :
    u ∈ alphaAddresses t ↔ out t u = .leafAlpha := by
  induction t generalizing u with
  | of b => cases b <;> cases u <;> simp [alphaAddresses, out]
  | mul s t hs ht =>
    cases u with
    | nil => simp [alphaAddresses, out]
    | cons b u => cases b <;> simp [alphaAddresses, out, hs, ht]

private theorem positive (t : Source) : 0 < (composition t).1 + (composition t).2 := by
  induction t with
  | of b => cases b <;> simp [composition]
  | mul s t hs ht =>
    simp only [composition, Prod.fst_add, Prod.snd_add]
    omega

private theorem structural (t : Source) :
    AlphaCovered (substitution (substitution t)) ∧
    (∀ u ∈ alphaAddresses (substitution (substitution t)), ∃ r : FiniteDescription,
      u = r ++ [true] ∧ subtree (substitution (substitution t)) r =
        some (.mul (.of false) (.of true))) ∧
    (∃ u ∈ alphaAddresses (substitution (substitution t)),
      u.length = height (substitution (substitution t))) := by
  induction t with
  | of b =>
    cases b with
    | true =>
      change AlphaCovered (.mul (.of false) (.of true)) ∧ _
      refine ⟨by simp [AlphaCovered, alphaAddresses], ?_, ?_⟩
      · intro u hu
        have he : u = [true] := by simpa [alphaAddresses, substitution] using hu
        subst u
        exact ⟨[], rfl, rfl⟩
      · exact ⟨[true], by simp [alphaAddresses, substitution], rfl⟩
    | false =>
      change AlphaCovered (.mul (.mul (.of false) (.of true)) (.of false)) ∧ _
      refine ⟨by simp [AlphaCovered, alphaAddresses], ?_, ?_⟩
      · intro u hu
        have he : u = [false, true] := by simpa [alphaAddresses, substitution] using hu
        subst u
        exact ⟨[false], rfl, rfl⟩
      · exact ⟨[false, true], by simp [alphaAddresses, substitution], rfl⟩
  | mul s t hs ht =>
    let S := substitution (substitution s)
    let T := substitution (substitution t)
    change AlphaCovered (.mul S T) ∧
      (∀ u ∈ alphaAddresses (.mul S T), ∃ r : FiniteDescription,
        u = r ++ [true] ∧ subtree (.mul S T) r =
          some (.mul (.of false) (.of true))) ∧
      (∃ u ∈ alphaAddresses (.mul S T), u.length = height (.mul S T))
    obtain ⟨hsc, hst, us, hus, hds⟩ := hs
    obtain ⟨htc, htt, ut, hut, hdt⟩ := ht
    refine ⟨⟨hsc, htc, ⟨false :: us, ?_⟩⟩, ?_, ?_⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨us, hus, rfl⟩)
    · intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
        obtain ⟨r, hr, hs⟩ := hst v hv
        exact ⟨false :: r, by simp [hr], by simpa [subtree] using hs⟩
      · rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
        obtain ⟨r, hr, ht⟩ := htt v hv
        exact ⟨true :: r, by simp [hr], by simpa [subtree] using ht⟩
    · rcases le_total (height S) (height T) with hle | hle
      · refine ⟨true :: ut, Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨ut, hut, rfl⟩), ?_⟩
        change ut.length + 1 = max (height S) (height T) + 1
        rw [hdt, max_eq_right hle]
      · refine ⟨false :: us, Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨us, hus, rfl⟩), ?_⟩
        change us.length + 1 = max (height S) (height T) + 1
        rw [hds, max_eq_left hle]

private theorem no_left_alpha (t : Source) : ∀ r : FiniteDescription,
    subtree (substitution t) (r ++ [false]) ≠ some (.of true) := by
  have no_alpha (t : Source) : substitution t ≠ .of true := by
    have hc := (GenealogicalFiberTransport.fiberMap (composition t) 1 ⟨t, rfl⟩).property
    change composition (substitution t) = GraftAffineClosure.step (composition t) at hc
    intro he
    rw [he] at hc
    have ha := congrArg Prod.fst hc
    have hb := congrArg Prod.snd hc
    simp only [composition, GraftAffineClosure.step] at ha hb
    omega
  induction t with
  | of b =>
    cases b with
    | true =>
      intro r
      cases r <;> simp [substitution, subtree]
    | false =>
      intro r
      cases r with
      | nil =>
        change some (.of false : Source) ≠ some (.of true)
        intro he
        have he := Option.some.inj he
        injection he with hb
        cases hb
      | cons b r =>
        cases b <;> cases r <;> simp [substitution, subtree]
  | mul s t hs ht =>
    intro r
    cases r with
    | nil =>
      simp only [List.nil_append]
      rw [show substitution (.mul s t) = .mul (substitution s) (substitution t)
        from map_mul substitution s t]
      simp only [subtree]
      exact fun he => no_alpha s (Option.some.inj he)
    | cons b r => cases b <;> first | exact hs r | exact ht r

set_option maxHeartbeats 2000000 in -- Combined reconstruction and swap-counting proof.
/-- Exact positive certificate cardinality for d = 3k, k at least one.
The same-composition competitor domain is all complete ordered source trees. -/
theorem result (k : ℕ) (hk : 1 ≤ k) (V : Source)
    (hV : V ∈ ActualImage (3 * k)) (h : ℕ) :
    (h < height V → ¬ ∃ Q : Finset FiniteDescription, Sound (3 * k) V h Q) ∧
    (height V ≤ h → ∃ Q : Finset FiniteDescription,
      Sound (3 * k) V h Q ∧ Q.card = (composition V).1) ∧
    (∀ Q : Finset FiniteDescription, Sound (3 * k) V h Q → (composition V).1 ≤ Q.card) := by
  classical
  have alpha_depth (t : Source) (u : FiniteDescription) (hu : u ∈ alphaAddresses t) :
      u.length ≤ height t := by
    induction t generalizing u with
    | of b => cases b <;> simp_all [alphaAddresses, height, decompose, BinaryTree.height]
    | mul s t hs ht =>
      rcases Finset.mem_union.mp hu with hu | hu
      · rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
        have h := hs v hv
        have hm := Nat.le_max_left (height s) (height t)
        change v.length + 1 ≤ max (height s) (height t) + 1
        omega
      · rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
        have h := ht v hv
        have hm := Nat.le_max_right (height s) (height t)
        change v.length + 1 ≤ max (height s) (height t) + 1
        omega
  have upper (V U : Source) (hc : AlphaCovered V)
      (hm : ∀ u ∈ alphaAddresses V, out U u = .leafAlpha) :
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
        have hu := hm [] (by simp [alphaAddresses])
        have he : U = .of true := by
          cases U with
          | of c => cases c <;> simp_all [out]
          | mul s t => simp [out] at hu
        subst U
        exact ⟨le_rfl, le_rfl, fun _ => rfl⟩
    | mul s t hs ht =>
      rcases hc with ⟨hcs, hct, u, hu⟩
      cases U with
      | of b =>
        have ho := hm u hu
        cases u with
        | nil => simp [alphaAddresses] at hu
        | cons c u => simp [out] at ho
      | mul x y =>
        have hms : ∀ u ∈ alphaAddresses s, out x u = .leafAlpha := by
          intro u hu
          exact hm (false :: u) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
        have hmt : ∀ u ∈ alphaAddresses t, out y u = .leafAlpha := by
          intro u hu
          exact hm (true :: u) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
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
  have swap_local (V : Source) (r : FiniteDescription)
      (hr : subtree V r = some (.mul (.of false) (.of true))) :
      composition (replace V r (.mul (.of true) (.of false))) = composition V ∧
      subtree (replace V r (.mul (.of true) (.of false))) (r ++ [false]) =
        some (.of true) ∧
      (∀ u : FiniteDescription, u ≠ r ++ [false] → u ≠ r ++ [true] →
        out (replace V r (.mul (.of true) (.of false))) u = out V u) := by
    induction r generalizing V with
    | nil =>
      have he : V = .mul (.of false) (.of true) :=
        Option.some.inj (by simpa only [subtree] using hr)
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
      | of c => simp [subtree] at hr
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
  have endpoint_parent (r s : FiniteDescription) (b c : Bool)
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
  have swapped_negative (r : FiniteDescription)
      (hr : subtree V r = some (.mul (.of false) (.of true))) :
      replace V r (.mul (.of true) (.of false)) ∉ ActualImage (3 * k) := by
    rintro ⟨W, hW⟩
    have hl := (swap_local V r hr).2.1
    have hw : substitution (substitution^[3 * k - 1] W) =
        replace V r (.mul (.of true) (.of false)) := by
      rw [← Function.iterate_succ_apply' (f := (substitution : Source → Source))
        (3 * k - 1) W, show (3 * k - 1).succ = 3 * k by omega]
      exact hW
    rw [← hw] at hl
    exact no_left_alpha (substitution^[3 * k - 1] W) r hl
  have hits (Q : Finset FiniteDescription) (hQ : Sound (3 * k) V h Q)
      (u : FiniteDescription) (hu : u ∈ alphaAddresses V) :
      ∃ r : FiniteDescription, u = r ++ [true] ∧ (r ++ [false] ∈ Q ∨ r ++ [true] ∈ Q) := by
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
    refine ⟨alphaAddresses V, ⟨?_, ?_⟩, alpha_card V⟩
    · intro u hu
      exact (alpha_depth V u hu).trans hlarge
    · intro U hc hm
      have hu : U = V := (upper V U hcovered (fun u hu =>
        (hm u hu).trans ((alpha_spec V u).mp hu))).2.2 hc
      exact hu ▸ original
  · intro Q hQ
    have query_for (u : {u : FiniteDescription // u ∈ alphaAddresses V}) :
        ∃ q : {q : FiniteDescription // q ∈ Q}, ∃ r : FiniteDescription, ∃ b : Bool,
          u.val = r ++ [true] ∧ q.val = r ++ [b] := by
      obtain ⟨r, hu, hL | hR⟩ := hits Q hQ u.val u.property
      · exact ⟨⟨r ++ [false], hL⟩, r, false, hu, rfl⟩
      · exact ⟨⟨r ++ [true], hR⟩, r, true, hu, rfl⟩
    let f : {u : FiniteDescription // u ∈ alphaAddresses V} → {q : FiniteDescription // q ∈ Q} :=
      fun u => Classical.choose (query_for u)
    have hf : Function.Injective f := by
      intro u v he
      obtain ⟨r, b, hu, hq⟩ := Classical.choose_spec (query_for u)
      obtain ⟨s, c, hv, hp⟩ := Classical.choose_spec (query_for v)
      have heq : r ++ [b] = s ++ [c] :=
        hq.symm.trans ((congrArg Subtype.val he).trans hp)
      have hrs := endpoint_parent r s b c heq
      apply Subtype.ext
      exact hu.trans ((congrArg (fun r : FiniteDescription => r ++ [true]) hrs).trans hv.symm)
    rw [← alpha_card V]
    exact Finset.card_le_card_of_injective hf

/-- All leaf addresses, with both labels retained. -/
def leafAddresses : Source → Finset FiniteDescription
  | .of _ => {[]}
  | .mul s t => (leafAddresses s).image (List.cons false) ∪
      (leafAddresses t).image (List.cons true)

/-- Soundness with no composition or leaf-count promise on competitors. -/
def UnSound (d : ℕ) (V : Source) (Q : Finset FiniteDescription) : Prop :=
  ∀ U : Source, (∀ u ∈ Q, out U u = out V u) → U ∈ ActualImage d

private theorem leaf_data (t : Source) :
    (leafAddresses t).card = (composition t).1 + (composition t).2 ∧
    (∀ u, u ∈ leafAddresses t ↔ out t u = .leafAlpha ∨ out t u = .leafBeta) ∧
    (∀ u ∈ leafAddresses t, u.length ≤ height t) ∧
    ((leafAddresses t).filter (fun u => out t u = .leafBeta)).card = (composition t).2 := by
  classical
  have prefix_disjoint (A B : Finset FiniteDescription) :
      Disjoint (A.image (List.cons false)) (B.image (List.cons true)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    rcases Finset.mem_image.mp hu with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨b, _, hb⟩
    simp at hb
  induction t with
  | of b =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases b <;> simp [leafAddresses, composition]
    · intro u
      cases b <;> cases u <;> simp [leafAddresses, out]
    · intro u hu
      have he : u = [] := by simpa only [leafAddresses, Finset.mem_singleton] using hu
      subst u
      exact Nat.zero_le _
    · cases b <;> simp [leafAddresses, Finset.filter_singleton, out, composition]
  | mul s t hs ht =>
    obtain ⟨hcs, hss, hds, hbs⟩ := hs
    obtain ⟨hct, hst, hdt, hbt⟩ := ht
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [leafAddresses, Finset.card_union_of_disjoint (prefix_disjoint _ _),
        Finset.card_image_of_injective _ List.cons_injective, composition,
        Prod.fst_add, Prod.snd_add, hcs, hct]
      omega
    · intro u
      cases u with
      | nil => simp [leafAddresses, out]
      | cons b u => cases b <;> simp [leafAddresses, out, hss, hst]
    · intro u hu
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
    · have hf : (leafAddresses (.mul s t)).filter (fun u => out (.mul s t) u = .leafBeta) =
          ((leafAddresses s).filter (fun u => out s u = .leafBeta)).image (List.cons false) ∪
          ((leafAddresses t).filter (fun u => out t u = .leafBeta)).image (List.cons true) := by
        ext u
        cases u with
        | nil => simp [leafAddresses, out]
        | cons b u => cases b <;> simp [leafAddresses, out]
      rw [hf, Finset.card_union_of_disjoint (prefix_disjoint _ _),
        Finset.card_image_of_injective _ List.cons_injective,
        Finset.card_image_of_injective _ List.cons_injective, hbs, hbt]
      rfl

private theorem subtree_out (t v : Source) (r u : FiniteDescription)
    (hr : subtree t r = some v) : out t (r ++ u) = out v u := by
  induction r generalizing t with
  | nil => have he := Option.some.inj (by simpa only [subtree] using hr); subst t; rfl
  | cons b r ih =>
    cases t with
    | of c => simp [subtree] at hr
    | mul s t => cases b <;> first | exact ih s hr | exact ih t hr

private theorem leaf_subtree (t : Source) (s : FiniteDescription) (b : Bool)
    (hs : out t s = out (.of b) []) : subtree t s = some (.of b) := by
  induction s generalizing t with
  | nil => cases t with
    | of c => cases b <;> cases c <;> simp_all [out, subtree]
    | mul x y => cases b <;> simp [out] at hs
  | cons c s ih => cases t with
    | of x => cases b <;> simp [out] at hs
    | mul x y => cases c <;> first | exact ih x hs | exact ih y hs

private theorem leaf_change (t : Source) (s : FiniteDescription) (b c : Bool)
    (hs : subtree t s = some (.of b)) :
    subtree (replace t s (.of c)) s = some (.of c) ∧
    composition (replace t s (.of c)) + composition (.of b) =
      composition t + composition (.of c) ∧
    (∀ u, u ≠ s → out (replace t s (.of c)) u = out t u) := by
  induction s generalizing t with
  | nil =>
    have he : t = .of b := Option.some.inj (by simpa only [subtree] using hs)
    subst t
    refine ⟨rfl, add_comm _ _, ?_⟩
    intro u hu
    cases u with
    | nil => exact (hu rfl).elim
    | cons x u => simp only [replace, out]
  | cons x s ih =>
    cases t with
    | of b => simp [subtree] at hs
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

private theorem no_beta_cherry (t : Source) (hc : AlphaCovered t) (r : FiniteDescription)
    (hl : out t (r ++ [false]) = .leafBeta)
    (hr : out t (r ++ [true]) = .leafBeta) : False := by
  induction r generalizing t with
  | nil =>
    cases t with
    | of b => simp [out] at hl
    | mul s t =>
      have hs : s = .of false :=
        Option.some.inj (by simpa only [subtree] using leaf_subtree s [] false hl)
      have ht : t = .of false :=
        Option.some.inj (by simpa only [subtree] using leaf_subtree t [] false hr)
      subst s; subst t
      simp [AlphaCovered, alphaAddresses] at hc
  | cons b r ih =>
    cases t with
    | of c => simp [out] at hl
    | mul s t =>
      cases b with
      | false => exact ih s hc.1 hl hr
      | true => exact ih t hc.2.1 hl hr

private theorem leaf_recovery (V U : Source)
    (hm : ∀ u ∈ leafAddresses V, out U u = out V u) : U = V := by
  induction V generalizing U with
  | of b =>
    have he := hm [] (by simp [leafAddresses])
    exact Option.some.inj (by simpa only [subtree] using leaf_subtree U [] b he)
  | mul s t hs ht =>
    cases U with
    | of b =>
      have hn : (leafAddresses s).Nonempty := by
        have hp := positive s
        rw [← (leaf_data s).1] at hp
        exact Finset.card_pos.mp hp
      obtain ⟨u, hu⟩ := hn
      have he := hm (false :: u) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
      rcases ((leaf_data s).2.1 u).mp hu with ha | hb
      · simp only [out, ha] at he
        contradiction
      · simp only [out, hb] at he
        contradiction
    | mul x y =>
      apply congrArg₂ FreeMagma.mul
      · apply hs x
        intro u hu
        exact hm (false :: u) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
      · apply ht y
        intro u hu
        exact hm (true :: u) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩))

set_option maxHeartbeats 2000000 in -- Two leaf replacements and whole-tree reconstruction.
/-- Uniqueness of the optimal fixed-composition certificate, and complete-leaf
certificates when competitors have no composition or leaf-count promise. -/
theorem rigidity (k : ℕ) (hk : 1 ≤ k) (V : Source)
    (hV : V ∈ ActualImage (3 * k)) :
    (∀ h, height V ≤ h → ∀ Q : Finset FiniteDescription, Within h Q →
      (Sound (3 * k) V h Q ∧ Q.card = (composition V).1 ↔ Q = alphaAddresses V)) ∧
    (∀ h, ∀ Q : Finset FiniteDescription, Within h Q →
      (UnSound (3 * k) V Q ↔ leafAddresses V ⊆ Q)) ∧
    (∀ h, h < height V → ¬ ∃ Q : Finset FiniteDescription, Within h Q ∧ UnSound (3 * k) V Q) ∧
    (∀ h, height V ≤ h → Within h (leafAddresses V) ∧
      UnSound (3 * k) V (leafAddresses V) ∧
      (leafAddresses V).card = (composition V).1 + (composition V).2 ∧
      ∀ Q : Finset FiniteDescription, Within h Q → UnSound (3 * k) V Q →
        (composition V).1 + (composition V).2 ≤ Q.card ∧
        (Q.card = (composition V).1 + (composition V).2 ↔ Q = leafAddresses V)) := by
  classical
  have image_structure (U : Source) (hU : U ∈ ActualImage (3 * k)) :
      AlphaCovered U ∧ ∀ u ∈ alphaAddresses U, ∃ r : FiniteDescription,
        u = r ++ [true] ∧ subtree U r = some (.mul (.of false) (.of true)) := by
    obtain ⟨T, hT⟩ := hU
    let S := substitution^[3 * k - 2] T
    have he : U = substitution (substitution S) := by
      change U = substitution^[2] S
      dsimp only [S]
      rw [← Function.iterate_add_apply, show 2 + (3 * k - 2) = 3 * k by omega]
      exact hT.symm
    rw [he]
    exact ⟨(structural S).1, (structural S).2.1⟩
  obtain ⟨hcovered, hterminal⟩ := image_structure V hV
  have beta_surplus : (composition V).1 < (composition V).2 := by
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
  have distinct (r : FiniteDescription) : r ++ [false] ≠ r ++ [true] := by simp
  have optimal_unique (h : ℕ) (Q : Finset FiniteDescription)
      (hQ : Sound (3 * k) V h Q) (hcard : Q.card = (composition V).1) :
      Q = alphaAddresses V := by
    have hsub : alphaAddresses V ⊆ Q := by
      intro s hs
      by_contra hsQ
      let B := (leafAddresses V).filter (fun u => out V u = .leafBeta)
      have hB : B.card = (composition V).2 := (leaf_data V).2.2.2
      obtain ⟨t, htB, htQ⟩ : ∃ t ∈ B, t ∉ Q := by
        by_contra hn
        have hsub : B ⊆ Q := by
          intro t ht
          by_contra htQ
          exact hn ⟨t, ht, htQ⟩
        have hle := Finset.card_le_card hsub
        omega
      have ht : out V t = .leafBeta := (Finset.mem_filter.mp htB).2
      have hsA := (alpha_spec V s).mp hs
      have hst : s ≠ t := by intro he; rw [he, ht] at hsA; contradiction
      obtain ⟨r, hsr, hr⟩ := hterminal s hs
      let W₁ := replace V s (.of false)
      obtain ⟨h₁s, hc₁, ho₁⟩ := leaf_change V s true false (leaf_subtree V s true hsA)
      have h₁t : subtree W₁ t = some (.of false) :=
        leaf_subtree W₁ t false ((ho₁ t hst.symm).trans ht)
      let W := replace W₁ t (.of true)
      obtain ⟨h₂t, hc₂, ho₂⟩ := leaf_change W₁ t false true h₁t
      have hc : composition W = composition V := by
        have ha₁ := congrArg Prod.fst hc₁
        have hb₁ := congrArg Prod.snd hc₁
        have ha₂ := congrArg Prod.fst hc₂
        have hb₂ := congrArg Prod.snd hc₂
        simp only [Prod.fst_add, Prod.snd_add, composition] at ha₁ hb₁ ha₂ hb₂
        apply Prod.ext <;> dsimp only [W, W₁] at ha₁ hb₁ ha₂ hb₂ ⊢ <;> omega
      have hW : W ∈ ActualImage (3 * k) := hQ.2 W hc (by
        intro u hu
        exact (ho₂ u (fun he => htQ (he ▸ hu))).trans
          (ho₁ u (fun he => hsQ (he ▸ hu))))
      by_cases htl : t = r ++ [false]
      · obtain ⟨U, hU⟩ := hW
        have he : substitution (substitution^[3 * k - 1] U) = W := by
          rw [← Function.iterate_succ_apply' (f := (substitution : Source → Source))
            (3 * k - 1) U, show (3 * k - 1).succ = 3 * k by omega]
          exact hU
        have hl : subtree W (r ++ [false]) = some (.of true) := htl ▸ h₂t
        rw [← he] at hl
        exact no_left_alpha (substitution^[3 * k - 1] U) r hl
      · have hl : out W (r ++ [false]) = .leafBeta := by
          exact (ho₂ _ (fun he => htl he.symm)).trans ((ho₁ _ (by rw [hsr]; exact distinct r)).trans
            (subtree_out V _ r [false] hr))
        have hsW₁ : out W₁ s = .leafBeta := by
          simpa only [List.append_nil, out] using subtree_out W₁ (.of false) s [] h₁s
        have hsW : out W s = .leafBeta := (ho₂ s hst).trans hsW₁
        exact no_beta_cherry W (image_structure W hW).1 r hl (hsr ▸ hsW)
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [alpha_card V, hcard])).symm
  have leaf_iff (Q : Finset FiniteDescription) : UnSound (3 * k) V Q ↔ leafAddresses V ⊆ Q := by
    constructor
    · intro hQ s hs
      by_contra hsQ
      rcases ((leaf_data V).2.1 s).mp hs with hsA | hsB
      · obtain ⟨r, hsr, hr⟩ := hterminal s ((alpha_spec V s).mpr hsA)
        let W := replace V s (.of false)
        obtain ⟨hsW, _, ho⟩ := leaf_change V s true false (leaf_subtree V s true hsA)
        have hW := hQ W (by intro u hu; exact ho u (fun he => hsQ (he ▸ hu)))
        have hl : out W (r ++ [false]) = .leafBeta :=
          (ho _ (by rw [hsr]; exact distinct r)).trans (subtree_out V _ r [false] hr)
        have hsW : out W s = .leafBeta := by
          simpa only [List.append_nil, out] using subtree_out W (.of false) s [] hsW
        exact no_beta_cherry W (image_structure W hW).1 r hl (hsr ▸ hsW)
      · let W := replace V s (.of true)
        obtain ⟨hsW, _, ho⟩ := leaf_change V s false true (leaf_subtree V s false hsB)
        have hW := hQ W (by intro u hu; exact ho u (fun he => hsQ (he ▸ hu)))
        have hsA : out W s = .leafAlpha := by
          simpa only [List.append_nil, out] using subtree_out W (.of true) s [] hsW
        obtain ⟨r, hsr, hr⟩ := (image_structure W hW).2 s ((alpha_spec W s).mpr hsA)
        have hl : out V (r ++ [false]) = .leafBeta :=
          (ho _ (by rw [hsr]; exact distinct r)).symm.trans (subtree_out W _ r [false] hr)
        exact no_beta_cherry V hcovered r hl (hsr ▸ hsB)
    · intro hsub U hm
      have he := leaf_recovery V U (fun u hu => hm u (hsub hu))
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
    refine ⟨fun u hu => ((leaf_data V).2.2.1 u hu).trans hlarge,
      (leaf_iff _).mpr (fun _ hu => hu), (leaf_data V).1, ?_⟩
    intro Q _ hsound
    have hsub := (leaf_iff Q).mp hsound
    have hle := Finset.card_le_card hsub
    rw [(leaf_data V).1] at hle
    refine ⟨hle, ?_⟩
    constructor
    · intro hcard
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [(leaf_data V).1, hcard])).symm
    · intro he
      rw [he, (leaf_data V).1]

end D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate
