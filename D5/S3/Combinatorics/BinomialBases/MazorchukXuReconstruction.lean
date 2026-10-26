/- GID: D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction
   mirror-E: none(waiver:finite-coordinate-source-reconstruction)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Admissible weak coordinate data reconstruct literal bounded edge families. -/

import D5.S3.Combinatorics.BinomialBases.MazorchukXuPatterns

/-! The reverse coordinate construction retains the literal first-column statistic. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MazorchukXu

private theorem rules_pullback {α β : Type*} [LinearOrder α] [LinearOrder β]
    {E : α → α → Prop} (hE : Rules E) {f : β → α} (hf : StrictMono f) :
    Rules (fun u v => E (f u) (f v)) := by
  refine ⟨fun h => hf.lt_iff_lt.mp (hE.ordered h), ?_, ?_⟩
  · intro a b c d hab hcd hac hcb hbd
    exact hE.propagate hab hcd (hf.monotone hac) (hf hcb) (hf hbd)
  · intro a b c d e g hab hcd heg hac hcb hae heb hbd hbg
    have hj := hE.join hab hcd heg (hf.monotone hac) (hf hcb)
      (hf.monotone hae) (hf heb) (hf.monotone hbd) (hf.monotone hbg)
    simpa only [hf.monotone.map_max] using hj

private def imageEdges {α : Type*} (E : α → α → Prop) (f : α → ℕ)
    (a b : ℕ) : Prop := ∃ u v, E u v ∧ f u = a ∧ f v = b

private theorem rules_imageEdges {α : Type*} [LinearOrder α]
    {E : α → α → Prop} (hE : Rules E) {f : α → ℕ} (hf : StrictMono f) :
    Rules (imageEdges E f) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro a b ⟨u, v, huv, rfl, rfl⟩
    exact hf (hE.ordered huv)
  · rintro a b c d ⟨u, v, huv, rfl, rfl⟩ ⟨w, x, hwx, rfl, rfl⟩ hac hcb hbd
    exact ⟨v, x, hE.propagate huv hwx (hf.le_iff_le.mp hac)
      (hf.lt_iff_lt.mp hcb) (hf.lt_iff_lt.mp hbd), rfl, rfl⟩
  · rintro a b c d e g ⟨u, v, huv, rfl, rfl⟩
      ⟨w, x, hwx, rfl, rfl⟩ ⟨y, z, hyz, rfl, rfl⟩ hac hcb hae heb hbd hbg
    exact ⟨max w y, max x z, hE.join huv hwx hyz
      (hf.le_iff_le.mp hac) (hf.lt_iff_lt.mp hcb) (hf.le_iff_le.mp hae)
      (hf.lt_iff_lt.mp heb) (hf.le_iff_le.mp hbd) (hf.le_iff_le.mp hbg),
      hf.monotone.map_max, hf.monotone.map_max⟩

/-- The actual finite edge set obtained from bounded coordinate vertices by their
canonical natural labels. Arbitrary exceptional bits are retained in their vertex order. -/
noncomputable def coordinateEdgeSet {i : ℕ} (M : ℕ) (p c : Fin i → ℕ)
    (B : Fin i → Fin i → Prop) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.univ : Finset (BoundedCoordinateVertex M p)).product (Finset.univ : Finset (BoundedCoordinateVertex M p))).filter
    (fun uv => coordinateEdges p c B uv.1.val uv.2.val) |>.image
      (fun uv => (coordinateLabel p uv.1.val, coordinateLabel p uv.2.val))

private theorem mem_coordinateEdgeSet {i M : ℕ} {p c : Fin i → ℕ}
    {B : Fin i → Fin i → Prop} {a b : ℕ} :
    (a, b) ∈ coordinateEdgeSet M p c B ↔
      imageEdges (fun u v : BoundedCoordinateVertex M p => coordinateEdges p c B u.val v.val)
        (fun u => coordinateLabel p u.val) a b := by
  classical
  unfold coordinateEdgeSet imageEdges
  constructor
  · intro h
    obtain ⟨⟨u, v⟩, huv, heq⟩ := Finset.mem_image.mp h
    exact ⟨u, v, (Finset.mem_filter.mp huv).2,
      (Prod.mk.inj heq).1, (Prod.mk.inj heq).2⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    apply Finset.mem_image.mpr
    refine ⟨(u, v), Finset.mem_filter.mpr ⟨?_, huv⟩, Prod.ext hu hv⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩

private theorem coordinateEdgeSet_firstColumn {i M : ℕ} {p c : Fin i → ℕ}
    (B : Fin i → Fin i → Prop) (hpm : Monotone p) :
    firstColumnCard (coordinateEdgeSet M p c B) = M := by
  classical
  let T := BoundedCoordinateVertex M p
  let L : T → ℕ := fun u => coordinateLabel p u.val
  have hf : StrictMono L := (coordinateLabel_strictMono p hpm).comp
    (show StrictMono (fun u : T => u.val) from fun _ _ h => h)
  let o : T := ⟨.ordinary 0, Nat.zero_le M⟩
  have hL0 : L o = 0 := by
    change 0 + (Finset.univ.filter (fun j => p j < 0)).card = 0
    simp
  let v : Fin M → T := fun r => ⟨.ordinary (r.val + 1), by
    change r.val + 1 ≤ M
    omega⟩
  have hov : ∀ r, coordinateEdges p c B o.val (v r).val := by
    intro r
    refine ⟨?_, trivial⟩
    change toLex (0, 0) < toLex (r.val + 1, 0)
    simp [Prod.Lex.toLex_lt_toLex]
  let G := Finset.univ.image (fun r : Fin M => (0, L (v r)))
  have hfilter : (coordinateEdgeSet M p c B).filter (fun z => z.1 = 0) = G := by
    ext z
    rcases z with ⟨a, b⟩
    constructor
    · intro hz
      obtain ⟨hz, ha⟩ := Finset.mem_filter.mp hz
      obtain ⟨u, w, he, hua, hwb⟩ := mem_coordinateEdgeSet.mp hz
      have hu0 : L u = L o := by change L u = a at hua; omega
      have huo : u = o := hf.injective hu0
      subst u
      rcases w with ⟨w, hw⟩
      cases w with
      | ordinary r =>
        have hr0 : r ≠ 0 := by
          intro hr
          subst r
          exact lt_irrefl o.val he.1
        change r ≤ M at hw
        let q : Fin M := ⟨r - 1, by omega⟩
        apply Finset.mem_image.mpr
        refine ⟨q, Finset.mem_univ _, ?_⟩
        apply Prod.ext
        · exact ha.symm
        · change L (v q) = b
          have hvq : v q = (⟨.ordinary r, hw⟩ : T) := by
            apply Subtype.ext
            change CoordinateVertex.ordinary (q.val + 1) = CoordinateVertex.ordinary r
            congr 1
            dsimp [q]
            omega
          exact (congrArg L hvq).trans hwb
      | exceptional j =>
        have hbad : c j < 0 := he.2
        omega
    · intro hz
      obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hz
      cases hr
      apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      apply mem_coordinateEdgeSet.mpr
      exact ⟨o, v r, hov r, hL0, rfl⟩
  have hinj : Function.Injective (fun r : Fin M => ((0 : ℕ), L (v r))) := by
    intro r s hrs
    have hh : L (v r) = L (v s) := congrArg Prod.snd hrs
    have hv := hf.injective hh
    have hval := congrArg (fun u : T => u.val) hv
    change CoordinateVertex.ordinary (r.val + 1) = CoordinateVertex.ordinary (s.val + 1) at hval
    have hnat := CoordinateVertex.ordinary.inj hval
    exact Fin.ext (by omega)
  have hG : G.card = M := by
    dsimp [G]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  unfold firstColumnCard
  rw [hfilter, hG]

/-- Every admissible bounded weak coordinate datum reconstructs an actual source-family
member with exactly M=n+1-i first-column edges, including M=0. -/
theorem coordinateEdgeSet_mem_edgeFamily {n i : ℕ} (hi : i ≤ n + 1)
    (p c : Fin i → ℕ) (B : Fin i → Fin i → Prop)
    (hpm : Monotone p) (hp : ∀ j, p j ≤ n + 1 - i) (hc : ∀ j, c j ≤ n + 1 - i)
    (hR : Rules (boundedCoordinateEdges (n + 1 - i) p c B)) :
    coordinateEdgeSet (n + 1 - i) p c B ∈ edgeFamily n (n + 1 - i) := by
  classical
  let M := n + 1 - i
  let T := BoundedCoordinateVertex M p
  let L : T → ℕ := fun u => coordinateLabel p u.val
  have hf : StrictMono L := (coordinateLabel_strictMono p hpm).comp
    (show StrictMono (fun u : T => u.val) from fun _ _ h => h)
  have hN : M + i = n + 1 := by dsimp [M]; omega
  have hbound : ∀ u, L u ≤ n + 1 := by
    intro u
    rw [← hN]
    exact coordinateLabel_bound p hp u
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_, ?_, coordinateEdgeSet_firstColumn B hpm⟩
  · intro z hz
    rcases z with ⟨a, b⟩
    obtain ⟨u, v, huv, rfl, rfl⟩ := mem_coordinateEdgeSet.mp hz
    have hab := hf huv.1
    have hb := hbound v
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by change L u < n + 2; omega),
      Finset.mem_range.mpr (by change L v < n + 2; omega)⟩, hab⟩
  · have hRfull := (coordinate_rules_bounded_iff _ p c B hp hc).mp hR
    have hsub := rules_pullback hRfull
      (show StrictMono (fun u : T => u.val) from fun _ _ h => h)
    have himg := rules_imageEdges hsub hf
    have heq : (fun a b => (a, b) ∈ coordinateEdgeSet M p c B) =
        imageEdges (fun u v : T => coordinateEdges p c B u.val v.val) L := by
      funext a b
      exact propext mem_coordinateEdgeSet
    rw [heq]
    exact himg

private theorem rules_of_subtype {α : Type*} [LinearOrder α] {S : α → Prop}
    {E : α → α → Prop} (horder : ∀ {a b}, E a b → a < b)
    (hsupport : ∀ {a b}, E a b → S a ∧ S b)
    (hE : Rules (fun u v : {a // S a} => E u.val v.val)) : Rules E := by
  have hcoe : Monotone (fun u : {a // S a} => u.val) := fun _ _ h => h
  refine ⟨horder, ?_, ?_⟩
  · intro a b c d hab hcd hac hcb hbd
    exact hE.propagate (a := ⟨a, (hsupport hab).1⟩) (b := ⟨b, (hsupport hab).2⟩)
      (c := ⟨c, (hsupport hcd).1⟩) (d := ⟨d, (hsupport hcd).2⟩) hab hcd hac hcb hbd
  · intro a b c d e f hab hcd hef hac hcb hae heb hbd hbf
    have hj := hE.join (a := ⟨a, (hsupport hab).1⟩) (b := ⟨b, (hsupport hab).2⟩)
      (c := ⟨c, (hsupport hcd).1⟩) (d := ⟨d, (hsupport hcd).2⟩)
      (e := ⟨e, (hsupport hef).1⟩) (f := ⟨f, (hsupport hef).2⟩)
      hab hcd hef hac hcb hae heb hbd hbf
    simpa only [hcoe.map_max] using hj

private theorem sourceMap_eq_coordinateLabel {M i : ℕ} (p : Fin i → ℕ)
    (hpm : Monotone p) (hp : ∀ j, p j ≤ M)
    (f : BoundedCoordinateVertex M p → ℕ) (hf : StrictMono f)
    (hbound : ∀ u, f u ≤ M + i) (hsurj : ∀ a, a ≤ M + i → ∃ u, f u = a) :
    f = fun u => coordinateLabel p u.val := by
  classical
  have hl : StrictMono (fun u : BoundedCoordinateVertex M p => coordinateLabel p u.val) :=
    (coordinateLabel_strictMono p hpm).comp (fun _ _ h => h)
  apply hf.eq_of_range_eq hl
  ext a
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := (coordinateLabel_bijective p hpm hp).2
      ⟨f u, by have := hbound u; omega⟩
    exact ⟨v, congrArg Fin.val hv⟩
  · rintro ⟨u, rfl⟩
    exact hsurj _ (coordinateLabel_bound p hp u)

private theorem coordinateEdgeSet_edges {i M : ℕ} {p c : Fin i → ℕ}
    (B : Fin i → Fin i → Prop) (hpm : Monotone p)
    (u v : BoundedCoordinateVertex M p) :
    (coordinateLabel p u.val, coordinateLabel p v.val) ∈ coordinateEdgeSet M p c B ↔
      coordinateEdges p c B u.val v.val := by
  constructor
  · intro h
    obtain ⟨x, y, hxy, hxu, hyv⟩ := mem_coordinateEdgeSet.mp h
    have hxu' := (coordinateLabel_strictMono p hpm).injective hxu
    have hyv' := (coordinateLabel_strictMono p hpm).injective hyv
    simpa only [hxu', hyv'] using hxy
  · intro h
    exact mem_coordinateEdgeSet.mpr ⟨u, v, h, rfl, rfl⟩

/-- Every literal source edge set is reconstructed by canonical bounded coordinate data.
The exceptional relation is supported on increasing labels, so it contains no unused bits. -/
theorem edgeFamily_eq_coordinateEdgeSet {n i : ℕ} (hi : i ≤ n + 1)
    {A : Finset (ℕ × ℕ)} (hA : A ∈ edgeFamily n (n + 1 - i)) :
    ∃ (p c : Fin i → ℕ) (B : Fin i → Fin i → Prop),
      Monotone p ∧ (∀ j, p j ≤ n + 1 - i) ∧ (∀ j, c j ≤ n + 1 - i) ∧
      (∀ j k, B j k → j < k) ∧
      Rules (boundedCoordinateEdges (n + 1 - i) p c B) ∧
      coordinateEdgeSet (n + 1 - i) p c B = A := by
  classical
  obtain ⟨p, c, B, f, hpm, hp, hc, hB, hf, hbound, hsurj, hedges⟩ :=
    edgeFamily_coordinate_realization hi hA
  let M := n + 1 - i
  let T := BoundedCoordinateVertex M p
  have hN : M + i = n + 1 := by dsimp [M]; omega
  have hfl : f = fun u => coordinateLabel p u.val :=
    sourceMap_eq_coordinateLabel p hpm hp f hf (by intro u; have := hbound u; dsimp [M] at hN; omega)
      (by intro a ha; apply hsurj a; dsimp [M] at hN; omega)
  have hE : Rules (fun a b => (a, b) ∈ A) := (Finset.mem_filter.mp hA).2.1
  have hsub : Rules (fun u v : T => coordinateEdges p c B u.val v.val) := by
    have h := rules_pullback hE hf
    have heq : (fun u v : T => (f u, f v) ∈ A) =
        (fun u v : T => coordinateEdges p c B u.val v.val) := by
      funext u v
      exact propext (hedges u v)
    exact heq ▸ h
  have hbounded : Rules (boundedCoordinateEdges M p c B) := by
    apply rules_of_subtype (fun h => h.1.1)
      (fun h => ⟨coordinateInside_downward M p hp h.1.1.le h.2, h.2⟩)
    have heq : (fun u v : T => boundedCoordinateEdges M p c B u.val v.val) =
        (fun u v : T => coordinateEdges p c B u.val v.val) := by
      funext u v
      exact propext (and_iff_left v.property)
    exact heq.symm ▸ hsub
  refine ⟨p, c, B, hpm, hp, hc, hB, hbounded, ?_⟩
  ext z
  rcases z with ⟨a, b⟩
  constructor
  · intro h
    obtain ⟨u, v, huv, rfl, rfl⟩ := mem_coordinateEdgeSet.mp h
    rw [hfl] at hedges
    exact (hedges u v).mpr huv
  · intro h
    have hb : b ≤ n + 1 := by
      have hm := (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1) h
      have := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hm).1).2
      omega
    obtain ⟨u, hu⟩ := hsurj a ((hE.ordered h).le.trans hb)
    obtain ⟨v, hv⟩ := hsurj b hb
    apply mem_coordinateEdgeSet.mpr
    refine ⟨u, v, (hedges u v).mp (by simpa only [hu, hv] using h), ?_, ?_⟩
    · simpa only [hfl] using hu
    · simpa only [hfl] using hv

private theorem coordinateEdgeSet_missing_anchor {i M : ℕ} {p c : Fin i → ℕ}
    (B : Fin i → Fin i → Prop) (hpm : Monotone p) (hp : ∀ j, p j ≤ M)
    (a : ℕ) (ha : 0 < a) (hab : a ≤ M + i) :
    (0, a) ∉ coordinateEdgeSet M p c B ↔ ∃ j, p j + j.val + 1 = a := by
  classical
  let T := BoundedCoordinateVertex M p
  let o : T := ⟨.ordinary 0, Nat.zero_le M⟩
  have ho : coordinateLabel p o.val = 0 := by
    change 0 + (Finset.univ.filter (fun j => p j < 0)).card = 0
    simp
  have hmissing (j : Fin i) : (0, p j + j.val + 1) ∉ coordinateEdgeSet M p c B := by
    intro h
    let v : T := ⟨.exceptional j, trivial⟩
    have hv : coordinateLabel p v.val = p j + j.val + 1 := rfl
    rw [← ho, ← hv, coordinateEdgeSet_edges B hpm] at h
    have : c j < 0 := h.2
    omega
  constructor
  · intro h
    obtain ⟨u, hlabel⟩ := (coordinateLabel_bijective p hpm hp).2 ⟨a, by omega⟩
    have hua : coordinateLabel p u.val = a := congrArg Fin.val hlabel
    rcases u with ⟨u, hinside⟩
    cases u with
    | ordinary r =>
      have hr : 0 < r := by
        by_contra hh
        have hr0 : r = 0 := by omega
        subst r
        have ha0 : a = 0 := hua.symm.trans ho
        omega
      have he : coordinateEdges p c B o.val (.ordinary r) := by
        refine ⟨?_, trivial⟩
        change toLex (0, 0) < toLex (r, 0)
        simp only [Prod.Lex.toLex_lt_toLex]
        exact Or.inl hr
      have hz := (coordinateEdgeSet_edges B hpm o ⟨.ordinary r, hinside⟩).mpr he
      exact False.elim (h (by simpa only [ho, hua] using hz))
    | exceptional j => exact ⟨j, hua⟩
  · rintro ⟨j, rfl⟩
    exact hmissing j

private theorem coordinateEdgeSet_data_injective {i M : ℕ}
    {p c q d : Fin i → ℕ} {B C : Fin i → Fin i → Prop}
    (hpm : Monotone p) (hqm : Monotone q)
    (hp : ∀ j, p j ≤ M) (hq : ∀ j, q j ≤ M)
    (hc : ∀ j, c j ≤ M) (hd : ∀ j, d j ≤ M)
    (hB : ∀ j k, B j k → j < k) (hC : ∀ j k, C j k → j < k)
    (heq : coordinateEdgeSet M p c B = coordinateEdgeSet M q d C) :
    p = q ∧ c = d ∧ B = C := by
  classical
  have hsp : StrictMono (fun j : Fin i => p j + j.val + 1) := by
    intro j k hjk
    have := hpm hjk.le
    change j.val < k.val at hjk
    change p j + j.val + 1 < p k + k.val + 1
    omega
  have hsq : StrictMono (fun j : Fin i => q j + j.val + 1) := by
    intro j k hjk
    have := hqm hjk.le
    change j.val < k.val at hjk
    change q j + j.val + 1 < q k + k.val + 1
    omega
  have hrange : Set.range (fun j : Fin i => p j + j.val + 1) =
      Set.range (fun j : Fin i => q j + j.val + 1) := by
    ext a
    constructor
    · rintro ⟨j, rfl⟩
      have ha : 0 < p j + j.val + 1 := by omega
      have hab : p j + j.val + 1 ≤ M + i := by have := hp j; have := j.isLt; omega
      have hm := (coordinateEdgeSet_missing_anchor (c := c) B hpm hp _ ha hab).mpr ⟨j, rfl⟩
      rw [heq] at hm
      exact (coordinateEdgeSet_missing_anchor (c := d) C hqm hq _ ha hab).mp hm
    · rintro ⟨j, rfl⟩
      have ha : 0 < q j + j.val + 1 := by omega
      have hab : q j + j.val + 1 ≤ M + i := by have := hq j; have := j.isLt; omega
      have hm := (coordinateEdgeSet_missing_anchor (c := d) C hqm hq _ ha hab).mpr ⟨j, rfl⟩
      rw [← heq] at hm
      exact (coordinateEdgeSet_missing_anchor (c := c) B hpm hp _ ha hab).mp hm
  have hpq : p = q := by
    have hs := hsp.eq_of_range_eq hsq hrange
    funext j
    have := congrFun hs j
    omega
  subst q
  let T := BoundedCoordinateVertex M p
  have hedge : ∀ u v : T, coordinateEdges p c B u.val v.val ↔
      coordinateEdges p d C u.val v.val := by
    intro u v
    rw [← coordinateEdgeSet_edges B hpm u v, heq, coordinateEdgeSet_edges C hpm u v]
  have hcd : c = d := by
    funext j
    have step (c d : Fin i → ℕ) (B C : Fin i → Fin i → Prop)
        (hd : ∀ j, d j ≤ M)
        (hedge : ∀ u v : T, coordinateEdges p c B u.val v.val →
          coordinateEdges p d C u.val v.val) : d j ≤ c j := by
      by_contra hdc
      have hcd : c j < d j := by omega
      let r := c j + 1
      have hr : r ≤ M := by dsimp [r]; have := hd j; omega
      let u : T := ⟨.exceptional j, trivial⟩
      let v : T := ⟨.ordinary r, hr⟩
      have hne : u ≠ v := by intro h; have := congrArg Subtype.val h; cases this
      rcases lt_or_gt_of_ne hne with huv | hvu
      · have he : coordinateEdges p c B u.val v.val := ⟨huv, by change c j < c j + 1; omega⟩
        have hbad : d j < r := (hedge u v he).2
        change d j < c j + 1 at hbad
        omega
      · have he : coordinateEdges p c B v.val u.val := ⟨hvu, by change c j < c j + 1; omega⟩
        have hbad : d j < r := (hedge v u he).2
        change d j < c j + 1 at hbad
        omega
    exact le_antisymm (step d c C B hc (fun u v => (hedge u v).mpr))
      (step c d B C hd (fun u v => (hedge u v).mp))
  subst d
  refine ⟨rfl, rfl, ?_⟩
  funext j k
  apply propext
  have horder (hjk : j < k) :
      (CoordinateVertex.exceptional j : CoordinateVertex p) < .exceptional k := by
    change toLex (p j, j.val + 1) < toLex (p k, k.val + 1)
    rw [Prod.Lex.toLex_lt_toLex]
    have hle := hpm hjk.le
    change j.val < k.val at hjk
    omega
  constructor
  · intro hjk
    have he : coordinateEdges p c B (.exceptional j) (.exceptional k) :=
      ⟨horder (hB j k hjk), hjk⟩
    exact ((hedge ⟨.exceptional j, trivial⟩ ⟨.exceptional k, trivial⟩).mp he).2
  · intro hjk
    have he : coordinateEdges p c C (.exceptional j) (.exceptional k) :=
      ⟨horder (hC j k hjk), hjk⟩
    exact ((hedge ⟨.exceptional j, trivial⟩ ⟨.exceptional k, trivial⟩).mpr he).2

/-- Finite arrays of bounded positions and cutoffs, together with exceptional-edge bits. -/
abbrev CoordinateDataCarrier (M i : ℕ) :=
  (Fin i → Fin (M + 1)) × (Fin i → Fin (M + 1)) × Finset (Fin i × Fin i)

/-- The finite admissible weak coordinate data with ordered exceptional-edge bits. -/
noncomputable def coordinateDataFamily (M i : ℕ) : Finset (CoordinateDataCarrier M i) := by
  classical
  exact Finset.univ.filter (fun d =>
    Monotone (fun j => (d.1 j).val) ∧
    (∀ j k, (j, k) ∈ d.2.2 → j < k) ∧
    Rules (boundedCoordinateEdges M (fun j => (d.1 j).val) (fun j => (d.2.1 j).val)
      (fun j k => (j, k) ∈ d.2.2)))

/-- Exact coordinate enumeration of the literal source count on its entire domain. -/
theorem count_eq_coordinateDataFamily_card {n i : ℕ} (hi : i ≤ n + 1) :
    count n (n + 1 - i) = (coordinateDataFamily (n + 1 - i) i).card := by
  classical
  rw [count_eq_edgeFamily_card]
  symm
  apply Finset.card_bij (fun d _ => coordinateEdgeSet (n + 1 - i)
    (fun j => (d.1 j).val) (fun j => (d.2.1 j).val) (fun j k => (j, k) ∈ d.2.2))
  · intro d hd
    obtain ⟨_, hpm, hB, hR⟩ := Finset.mem_filter.mp hd
    exact coordinateEdgeSet_mem_edgeFamily hi _ _ _ hpm
      (fun j => Nat.le_of_lt_succ (d.1 j).isLt)
      (fun j => Nat.le_of_lt_succ (d.2.1 j).isLt) hR
  · intro x hx y hy hxy
    obtain ⟨_, hpx, hBx, _⟩ := Finset.mem_filter.mp hx
    obtain ⟨_, hpy, hBy, _⟩ := Finset.mem_filter.mp hy
    obtain ⟨hp, hc, hB⟩ := coordinateEdgeSet_data_injective hpx hpy
      (fun j => Nat.le_of_lt_succ (x.1 j).isLt)
      (fun j => Nat.le_of_lt_succ (y.1 j).isLt)
      (fun j => Nat.le_of_lt_succ (x.2.1 j).isLt)
      (fun j => Nat.le_of_lt_succ (y.2.1 j).isLt) hBx hBy hxy
    apply Prod.ext
    · funext j
      exact Fin.ext (congrFun hp j)
    · apply Prod.ext
      · funext j
        exact Fin.ext (congrFun hc j)
      · apply Finset.ext
        rintro ⟨j, k⟩
        exact congrFun (congrFun hB j) k |>.to_iff
  · intro A hA
    obtain ⟨p, c, B, hpm, hp, hc, hB, hR, heq⟩ := edgeFamily_eq_coordinateEdgeSet hi hA
    let pp : Fin i → Fin (n + 1 - i + 1) := fun j => ⟨p j, by have := hp j; omega⟩
    let cc : Fin i → Fin (n + 1 - i + 1) := fun j => ⟨c j, by have := hc j; omega⟩
    let BB := Finset.univ.filter (fun jk : Fin i × Fin i => B jk.1 jk.2)
    have hBB : (fun j k => (j, k) ∈ BB) = B := by
      funext j k
      exact propext (by simp [BB])
    refine ⟨(pp, cc, BB), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hpm, ?_, ?_⟩
      · intro j k hjk
        exact hB j k ((Finset.mem_filter.mp hjk).2)
      · simpa only [hBB] using hR
    · simpa only [hBB] using heq

end D5.S3.Combinatorics.MazorchukXu
