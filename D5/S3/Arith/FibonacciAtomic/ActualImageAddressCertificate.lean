/- GID: D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sharp cardinality and depth for actual substitution image certificates. -/

import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate

open GenealogicalFiberTransport (Source substitution composition decompose)

/-- Root-first paths: false is left and true is right. Leaf labels use true for
alpha and false for beta, as in GenealogicalFiberTransport.Source. -/
abbrev Address := List Bool

/-- The four original endpoint observations, including the empty root address. -/
inductive Output
  | leafAlpha | leafBeta | branch | absent
  deriving DecidableEq

/-- Read the raw endpoint; continuing beyond a leaf gives absent. -/
def out : Source → Address → Output
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
def Within (h : ℕ) (Q : Finset Address) : Prop := ∀ u ∈ Q, u.length ≤ h

/-- Soundness ranges over every complete source of the same exact composition. -/
def Sound (d : ℕ) (V : Source) (h : ℕ) (Q : Finset Address) : Prop :=
  Within h Q ∧ ∀ U : Source, composition U = composition V →
    (∀ u ∈ Q, out U u = out V u) → U ∈ ActualImage d

/-- All addresses carrying an alpha leaf. -/
def alphaAddresses : Source → Finset Address
  | .of true => {[]}
  | .of false => ∅
  | .mul s t => (alphaAddresses s).image (List.cons false) ∪
      (alphaAddresses t).image (List.cons true)

/-- The complete subtree at an address, absent when the path passes a leaf. -/
def subtree : Source → Address → Option Source
  | t, [] => some t
  | .of _, _ :: _ => none
  | .mul s _, false :: u => subtree s u
  | .mul _ t, true :: u => subtree t u

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
      (alphaAddresses (.mul s t)).Nonempty

private theorem prefix_disjoint (A B : Finset Address) :
    Disjoint (A.image (List.cons false)) (B.image (List.cons true)) := by
  apply Finset.disjoint_left.mpr
  intro u hu hv
  rcases Finset.mem_image.mp hu with ⟨a, _, rfl⟩
  rcases Finset.mem_image.mp hv with ⟨b, _, hb⟩
  simp at hb

private theorem alpha_card (t : Source) : (alphaAddresses t).card = (composition t).1 := by
  induction t with
  | of b => cases b <;> simp [alphaAddresses, composition]
  | mul s t hs ht =>
    simp only [alphaAddresses, Finset.card_union_of_disjoint (prefix_disjoint _ _),
      Finset.card_image_of_injective _ List.cons_injective, composition,
      Prod.fst_add, hs, ht]

private theorem alpha_spec (t : Source) (u : Address) :
    u ∈ alphaAddresses t ↔ out t u = .leafAlpha := by
  induction t generalizing u with
  | of b => cases b <;> cases u <;> simp [alphaAddresses, out]
  | mul s t hs ht =>
    cases u with
    | nil => simp [alphaAddresses, out]
    | cons b u => cases b <;> simp [alphaAddresses, out, hs, ht]

private theorem alpha_depth (t : Source) (u : Address) (hu : u ∈ alphaAddresses t) :
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

private theorem positive (t : Source) : 0 < (composition t).1 + (composition t).2 := by
  induction t with
  | of b => cases b <;> simp [composition]
  | mul s t hs ht =>
    simp only [composition, Prod.fst_add, Prod.snd_add]
    omega

private theorem upper (V U : Source) (hc : AlphaCovered V)
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

private theorem structural (t : Source) :
    AlphaCovered (substitution (substitution t)) ∧
    (∀ u ∈ alphaAddresses (substitution (substitution t)), ∃ r : Address,
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
      (∀ u ∈ alphaAddresses (.mul S T), ∃ r : Address,
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

private theorem no_alpha (t : Source) : substitution t ≠ .of true := by
  have hc := (GenealogicalFiberTransport.fiberMap (composition t) 1 ⟨t, rfl⟩).property
  change composition (substitution t) = GraftAffineClosure.step (composition t) at hc
  intro he
  rw [he] at hc
  have ha := congrArg Prod.fst hc
  have hb := congrArg Prod.snd hc
  simp only [composition, GraftAffineClosure.step] at ha hb
  omega

private theorem no_left_alpha (t : Source) : ∀ r : Address,
    subtree (substitution t) (r ++ [false]) ≠ some (.of true) := by
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

private theorem swap_local (V : Source) (r : Address)
    (hr : subtree V r = some (.mul (.of false) (.of true))) :
    composition (replace V r (.mul (.of true) (.of false))) = composition V ∧
    subtree (replace V r (.mul (.of true) (.of false))) (r ++ [false]) =
      some (.of true) ∧
    (∀ u : Address, u ≠ r ++ [false] → u ≠ r ++ [true] →
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
  have hits (Q : Finset Address) (hQ : Sound (3 * k) V h Q)
      (u : Address) (hu : u ∈ alphaAddresses V) :
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
    refine ⟨alphaAddresses V, ⟨?_, ?_⟩, alpha_card V⟩
    · intro u hu
      exact (alpha_depth V u hu).trans hlarge
    · intro U hc hm
      have hu : U = V := (upper V U hcovered (fun u hu =>
        (hm u hu).trans ((alpha_spec V u).mp hu))).2.2 hc
      exact hu ▸ original
  · intro Q hQ
    have query_for (u : {u : Address // u ∈ alphaAddresses V}) :
        ∃ q : {q : Address // q ∈ Q}, ∃ r : Address, ∃ b : Bool,
          u.val = r ++ [true] ∧ q.val = r ++ [b] := by
      obtain ⟨r, hu, hL | hR⟩ := hits Q hQ u.val u.property
      · exact ⟨⟨r ++ [false], hL⟩, r, false, hu, rfl⟩
      · exact ⟨⟨r ++ [true], hR⟩, r, true, hu, rfl⟩
    let f : {u : Address // u ∈ alphaAddresses V} → {q : Address // q ∈ Q} :=
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

end D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate
