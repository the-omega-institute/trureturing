/- GID: D5/S1/Dynamics/Symbolic/FiniteTypeMoore
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/FiniteTypeMoore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Same-subshift finite-collision replacement and Moore's implication. -/

import D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill

/-! Finite forbidden-pattern splicing and the relative Moore counting argument. -/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Function MeasureTheory Filter
open scoped Pointwise Topology
open SymbolicDynamics.FullShift
open D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill

universe u v
namespace D5.S1.Dynamics.Symbolic.FiniteTypeMoore
variable {G : Type u} [Group G] {A : Type v} [TopologicalSpace A]

/-- A finite family of native finite forbidden patterns defines the carrier.
The padding value is existential, rather than an alphabet-inhabitance assumption. -/
def IsFiniteType (X : MulSubshift A G) : Prop :=
  ∃ a : A, letI : Inhabited A := ⟨a⟩
    ∃ B : Finset (Pattern A G), X.carrier = mulForbidden (B : Set (Pattern A G))

/-- A finite collision in a finite-type subshift gives a uniform replacement
inside that same subshift, preserving the entire image at every translate. -/
theorem collision_replacement [Finite A] [DiscreteTopology A]
    (X : MulSubshift A G) (hft : IsFiniteType X)
    (tau : Cfg X → Cfg X) (htau : Continuous tau)
    (hequiv : ∀ g x, tau (paperShift X g x) = paperShift X g (tau x))
    (x y : Cfg X) (hne : x ≠ y) (hf : Set.Finite {g | x.val g ≠ y.val g})
    (hi : tau x = tau y) :
    ∃ C : Finset G, C.Nonempty ∧ ∃ p q : C → A,
      p ≠ q ∧ p ∈ PatX X C ∧ q ∈ PatX X C ∧
      ∀ (t : G) (z : Cfg X), (∀ c : C, z.val (t * c) = p c) →
        ∃ z' : Cfg X, (∀ c : C, z'.val (t * c) = q c) ∧
          (∀ g, g ∉ tile t C → z'.val g = z.val g) ∧ tau z' = tau z := by
  classical
  obtain ⟨a, hft⟩ := hft
  let : Inhabited A := ⟨a⟩
  obtain ⟨B, hB⟩ := hft
  obtain ⟨M, hM⟩ := finite_memory X tau htau
  let D := hf.toFinset
  let S := M ∪ B.biUnion Pattern.support
  let C := AmenableGardenOfEden.collar D S
  have hcore : ∀ g ∈ D, g ∈ C := fun _ hg => AmenableGardenOfEden.mem_collar_core D S hg
  have hout (g : G) (hg : g ∉ D) : x.val g = y.val g := by
    simpa only [D, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hg
  have hvals : x.val ≠ y.val := fun h => hne (Subtype.ext h)
  obtain ⟨d, hd⟩ := Function.ne_iff.mp hvals
  have hdD : d ∈ D := by simpa only [D, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hd
  have hdC := hcore d hdD
  let p : C → A := fun c => x.val c
  let q : C → A := fun c => y.val c
  refine ⟨C, ⟨d, hdC⟩, p, q, (fun h => hd (congrFun h ⟨d, hdC⟩)),
    ⟨x, rfl⟩, ⟨y, rfl⟩, ?_⟩
  have hMS : ∀ m ∈ M, m ∈ S := fun m hm => Finset.mem_union_left _ hm
  have hBS (b : Pattern A G) (hb : b ∈ B) : ∀ r ∈ b.support, r ∈ S := by
    intro r hr
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hb, hr⟩)
  let f (w : S → A) : A :=
    if h : ∃ z : Cfg X, ∀ s : S, z.val s = w s then (tau (Classical.choose h)).val 1 else a
  have hfval (z : Cfg X) : f (fun s : S => z.val s) = (tau z).val 1 := by
    have hh : ∃ z' : Cfg X, ∀ s : S, z'.val s = z.val s := ⟨z, fun _ => rfl⟩
    dsimp only [f]
    rw [dite_eq_left hh]
    exact hM _ z (fun m hm => Classical.choose_spec hh ⟨m, hMS m hm⟩)
  let good (w : S → A) : Prop :=
    ∀ (b : Pattern A G) (hb : b ∈ B),
      ¬ ∀ r : b.support, w ⟨r, hBS b hb r r.property⟩ = b.config r
  have hgood (z : Cfg X) (g : G) : good (fun s : S => z.val (g * s)) := by
    intro b hb hocc
    have hzB : z.val ∈ mulForbidden (B : Set (Pattern A G)) := hB ▸ z.property
    exact hzB b hb g (fun r hr => hocc ⟨r, hr⟩)
  let φ (w : S → A × Bool) : A × Bool :=
    (f (fun s => (w s).1), decide (good (fun s => (w s).1)))
  let encode (z : G → A) : G → A × Bool := fun g => (z g, false)
  have hcode (z : Cfg X) (g : G) :
      AmenableGardenOfEden.localMap S φ (encode z.val) g = ((tau z).val g, true) := by
    apply Prod.ext
    · change f (fun s : S => z.val (g * s)) = (tau z).val g
      have hh := hfval (paperShift X g⁻¹ z)
      rw [hequiv] at hh
      simpa [paperShift, mulShift] using hh
    · change decide (good (fun s : S => z.val (g * s))) = true
      exact decide_eq_true (hgood z g)
  have hcodeeq : AmenableGardenOfEden.localMap S φ (encode x.val) =
      AmenableGardenOfEden.localMap S φ (encode y.val) := by
    funext g
    rw [hcode, hcode, hi]
  have hidentity (z : Cfg X) (hz : ∀ c ∈ C, z.val c = x.val c) :
      ∃ z' : Cfg X, (∀ c ∈ C, z'.val c = y.val c) ∧
        (∀ g, g ∉ C → z'.val g = z.val g) ∧ tau z' = tau z := by
    let w : G → A := (C : Set G).piecewise y.val z.val
    have hwC (g : G) (hg : g ∈ C) : w g = y.val g :=
      Set.piecewise_eq_of_mem _ _ _ hg
    have hwout (g : G) (hg : g ∉ C) : w g = z.val g :=
      Set.piecewise_eq_of_notMem _ _ _ hg
    have henc : encode w = (C : Set G).piecewise (encode y.val) (encode z.val) := by
      funext g
      by_cases hg : g ∈ C <;> simp [encode, w, hg]
    have hsplice := AmenableGardenOfEden.localMap_piecewise_of_collar D S φ
      (x := encode x.val) (y := encode y.val) (z := encode z.val)
      (fun g hg => by simp only [encode, hout g hg]) hcodeeq
      (fun g hg => by simp only [encode, hz g hg])
    rw [← henc] at hsplice
    have hwgood (g : G) : good (fun s : S => w (g * s)) := by
      have hh := congrArg Prod.snd (congrFun hsplice g)
      rw [hcode] at hh
      exact of_decide_eq_true hh
    have hwX : w ∈ X.carrier := by
      rw [hB]
      intro b hb g hocc
      exact hwgood g b hb (fun r => hocc r r.property)
    let z' : Cfg X := ⟨w, hwX⟩
    refine ⟨z', hwC, hwout, ?_⟩
    apply Subtype.ext
    funext g
    have hh := congrArg Prod.fst (congrFun hsplice g)
    rw [show encode w = encode z'.val from rfl, hcode, hcode] at hh
    exact hh
  intro t z hz
  let z0 := paperShift X t⁻¹ z
  have hz0 : ∀ c ∈ C, z0.val c = x.val c := by
    intro c hc
    simpa [z0, paperShift, mulShift, p] using hz ⟨c, hc⟩
  obtain ⟨w, hwC, hwout, hwtau⟩ := hidentity z0 hz0
  refine ⟨paperShift X t w, ?_, ?_, ?_⟩
  · intro c
    simpa [paperShift, mulShift, q] using hwC c c.property
  · intro g hg
    have hgc : t⁻¹ * g ∉ C := by
      intro hc
      exact hg ⟨t⁻¹ * g, hc, mul_inv_cancel_left t g⟩
    simpa [paperShift, mulShift, z0] using hwout (t⁻¹ * g) hgc
  · rw [hequiv, hwtau, hequiv]
    apply Subtype.ext
    funext g
    simp [paperShift, mulShift]

private theorem erase_disjoint (X : MulSubshift A G) (tau : Cfg X → Cfg X)
    (C : Finset G) (p q : C → A) (hpq : p ≠ q)
    (herase : ∀ (t : G) (z : Cfg X), (∀ c : C, z.val (t * c) = p c) →
      ∃ z' : Cfg X, (∀ c : C, z'.val (t * c) = q c) ∧
        (∀ g, g ∉ tile t C → z'.val g = z.val g) ∧ tau z' = tau z)
    (T : Finset G)
    (hdis : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → Disjoint (tile t C) (tile s C))
    (x : Cfg X) :
    ∃ y : Cfg X, tau y = tau x ∧ ∀ t ∈ T, (fun c : C => y.val (t * c)) ≠ p := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨x, rfl, by simp⟩
  | @insert t T ht ih =>
    obtain ⟨y, hy, hay⟩ := ih (fun s hs r hr hsr =>
      hdis s (Finset.mem_insert_of_mem hs) r (Finset.mem_insert_of_mem hr) hsr)
    by_cases hp : (fun c : C => y.val (t * c)) = p
    · obtain ⟨z, hzq, hzout, hztau⟩ := herase t y (fun c => congrFun hp c)
      refine ⟨z, hztau.trans hy, ?_⟩
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · intro h
        exact hpq (h.symm.trans (funext hzq))
      · have hst : t ≠ s := fun h => ht (h ▸ hs)
        have heq : (fun c : C => z.val (s * c)) = (fun c : C => y.val (s * c)) := by
          funext c
          apply hzout
          intro hm
          exact Set.disjoint_left.mp
            (hdis t (Finset.mem_insert_self _ _) s (Finset.mem_insert_of_mem hs) hst)
            hm ⟨c, c.property, rfl⟩
        rw [heq]
        exact hay s hs
    · exact ⟨y, hy, fun s hs => by
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact hp
        · exact hay s hs⟩

private theorem image_input_avoidance_bound [Finite A]
    (X : MulSubshift A G) (tau : Cfg X → Cfg X)
    (Delta C E F U T M : Finset G) (p q : C → A) (hpq : p ≠ q)
    (hp : p ∈ PatX X C) (hX : X.carrier.Nonempty) (h1 : 1 ∈ Delta) (hSI : SI X Delta)
    (hCE : (C : Set G) * (Delta : Set G)⁻¹ ⊆ (E : Set G))
    (hin : ∀ t ∈ T, tile t E ⊆ (U : Set G))
    (hdis : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → Disjoint (tile t E) (tile s E))
    (hmem : HasMemory X tau M)
    (hequiv : ∀ g x, tau (paperShift X g x) = paperShift X g (tau x))
    (hFM : F * M ⊆ U)
    (herase : ∀ (t : G) (z : Cfg X), (∀ c : C, z.val (t * c) = p c) →
      ∃ z' : Cfg X, (∀ c : C, z'.val (t * c) = q c) ∧
        (∀ g, g ∉ tile t C → z'.val g = z.val g) ∧ tau z' = tau z) :
    Nat.card (ImagePat X tau F) * Nat.card (PatX X E) ^ T.card ≤
      Nat.card (PatX X U) * (Nat.card (PatX X E) - 1) ^ T.card := by
  classical
  have hC : (C : Set G) ⊆ (E : Set G) := by
    intro c hc
    apply hCE
    simpa only [inv_one, mul_one] using Set.mul_mem_mul hc
      (show (1 : G) ∈ (Delta : Set G)⁻¹ by simpa)
  have hdisC : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → Disjoint (tile t C) (tile s C) := by
    intro t ht s hs hts
    apply (hdis t ht s hs hts).mono
    · rintro g ⟨c, hc, rfl⟩
      exact ⟨c, hC hc, rfl⟩
    · rintro g ⟨c, hc, rfl⟩
      exact ⟨c, hC hc, rfl⟩
  let source (o : ImagePat X tau F) : Cfg X := Classical.choose o.property
  have hs (o : ImagePat X tau F) (f : F) :
      (tau (source o)).val f = o.val f := congrFun (Classical.choose_spec o.property) f
  have hn (o : ImagePat X tau F) := erase_disjoint X tau C p q hpq herase T hdisC (source o)
  choose norm hnorm havoid using hn
  let w : T → C → A := fun _ => p
  let key : ImagePat X tau F → AvoidPatX X C U T w := fun o =>
    ⟨fun f => (norm o).val f, ⟨⟨norm o, fun t => Function.ne_iff.mp (havoid o t t.property)⟩, rfl⟩⟩
  have hk : Injective key := by
    intro o o' heq
    have he : ∀ a ∈ U, (norm o).val a = (norm o').val a := by
      intro a ha
      exact congrFun (congrArg Subtype.val heq) ⟨a, ha⟩
    apply Subtype.ext
    funext f
    calc
      o.val f = (tau (norm o)).val f :=
        ((congrArg (fun z : Cfg X => z.val f) (hnorm o)).trans (hs o f)).symm
      _ = (tau (norm o')).val f := memory_at X tau M hmem hequiv f (norm o) (norm o')
        (fun m hm => he _ (hFM (Finset.mul_mem_mul f.property hm)))
      _ = o'.val f := (congrArg (fun z : Cfg X => z.val f) (hnorm o')).trans (hs o' f)
  have hw (t : T) : ∃ z : Cfg X, ∀ c : C, z.val (t.val * c.val) = w t c := by
    obtain ⟨z, hz⟩ := hp
    refine ⟨paperShift X t.val z, ?_⟩
    intro c
    simpa [paperShift, mulShift, w] using congrFun hz c
  exact (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective key hk)).trans
    (relative_pattern_bound X Delta C E U T w hX h1 hSI hCE hin hdis hw)

/-- Moore's implication for the original nonempty strongly irreducible
finite-type subshift over an arbitrary right-counting amenable group. -/
theorem moore [Finite A] [DiscreteTopology A]
    (ham : letI : MeasurableSpace G := ⊤
      NeBot (maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)))
    (X : MulSubshift A G) (hX : X.carrier.Nonempty)
    (hSI0 : ∃ Delta : Finset G, SI X Delta) (hft : IsFiniteType X)
    (tau : Cfg X → Cfg X) (htau : Continuous tau)
    (hequiv : ∀ g x, tau (paperShift X g x) = paperShift X g (tau x))
    (hsurj : Surjective tau) :
    ∀ x y : Cfg X, {g | x.val g ≠ y.val g}.Finite → tau x = tau y → x = y := by
  classical
  intro x y hf hi
  by_contra hne
  obtain ⟨C, hC, p, q, hpq, hp, _hq, herase⟩ :=
    collision_replacement X hft tau htau hequiv x y hne hf hi
  obtain ⟨Delta0, hSI0⟩ := hSI0
  let Delta := insert 1 Delta0
  have h1 : 1 ∈ Delta := Finset.mem_insert_self _ _
  have hSI : SI X Delta := by
    intro F K hsep x y
    apply hSI0 F K (hsep.mono_left ?_) x y
    rintro g ⟨f, hf, d, hd, rfl⟩
    refine Set.mul_mem_mul hf ?_
    change d⁻¹ ∈ Delta
    exact Finset.mem_insert_of_mem hd
  obtain ⟨M, hmem⟩ := finite_memory X tau htau
  obtain ⟨x0, hx0⟩ := hX
  let xbase : Cfg X := ⟨x0, hx0⟩
  let : Nonempty A := ⟨x0 1⟩
  let E := C * Delta⁻¹
  have hE : E.Nonempty := by
    obtain ⟨c, hc⟩ := hC
    refine ⟨c, ?_⟩
    simpa using Finset.mul_mem_mul hc (Finset.inv_mem_inv h1)
  have hCE : (C : Set G) * (Delta : Set G)⁻¹ ⊆ (E : Set G) := by
    intro g hg
    simpa only [E, Finset.coe_mul, Finset.coe_inv] using hg
  let K := insert 1 (E ∪ M)
  have hK : 1 ∈ K := Finset.mem_insert_self _ _
  let : MeasurableSpace G := ⊤
  let : NeBot (maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)) := ham
  let l := maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)
  let B : Set G → Finset G := AmenableGardenOfEden.finiteShape
  obtain ⟨hpos, hboundary⟩ := AmenableGardenOfEden.maximal_shapes (G := G)
  let U : Set G → Finset G := fun i => B i * K
  have hBU (i : Set G) : B i ⊆ U i := by
    intro g hg
    simpa only [mul_one] using Finset.mul_mem_mul hg hK
  have hMU (i : Set G) : B i * M ⊆ U i := by
    apply Finset.mul_subset_mul_left
    intro m hm
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hm)
  have hpack (i : Set G) := AmenableGardenOfEden.exists_dense_packing E (B i) hE
  choose T hTF hdisjoint hdense using hpack
  have hin (i : Set G) : ∀ t ∈ T i, tile t E ⊆ (U i : Set G) := by
    intro t ht g hg
    obtain ⟨e, he, rfl⟩ := hg
    exact Finset.mul_mem_mul (hTF i ht)
      (Finset.mem_insert_of_mem (Finset.mem_union_left _ he))
  have hdis (i : Set G) : ∀ t ∈ T i, ∀ s ∈ T i, t ≠ s →
      Disjoint (tile t E) (tile s E) := by
    intro t ht s hs hne
    apply Set.disjoint_left.mpr
    rintro g ⟨e, he, rfl⟩ ⟨d, hd, hed⟩
    exact hdisjoint i t ht s hs hne ⟨e, he⟩ ⟨d, hd⟩ hed.symm
  have hcardpos (F : Finset G) : 0 < Nat.card (PatX X F) := by
    let : Nonempty (PatX X F) := ⟨⟨_, ⟨xbase, rfl⟩⟩⟩
    exact Nat.card_pos
  have hfull (F : Finset G) : ImagePat X tau F = PatX X F := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨tau z, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨y, rfl⟩ := hsurj z
      exact ⟨y, rfl⟩
  have hcount (i : Set G) : Nat.card (PatX X E) ^ (T i).card ≤
      Nat.card A ^ (U i \ B i).card * (Nat.card (PatX X E) - 1) ^ (T i).card := by
    have hupper := image_input_avoidance_bound X tau Delta C E (B i) (U i) (T i) M
      p q hpq hp ⟨x0, hx0⟩ h1 hSI hCE (hin i) (hdis i) hmem hequiv (hMU i) herase
    rw [hfull] at hupper
    have hpad := pattern_padding X (B i) (U i) (hBU i)
    have hh : Nat.card (PatX X (B i)) * Nat.card (PatX X E) ^ (T i).card ≤
        Nat.card (PatX X (B i)) * (Nat.card A ^ (U i \ B i).card *
          (Nat.card (PatX X E) - 1) ^ (T i).card) := by
      calc
        _ ≤ Nat.card (PatX X (U i)) * (Nat.card (PatX X E) - 1) ^ (T i).card := hupper
        _ ≤ (Nat.card (PatX X (B i)) * Nat.card A ^ (U i \ B i).card) *
            (Nat.card (PatX X E) - 1) ^ (T i).card := Nat.mul_le_mul_right _ hpad
        _ = _ := by ring
    nlinarith only [hh, hcardpos (B i)]
  have hratio := AmenableGardenOfEden.mul_ratio_tendsto B hpos hboundary K hK
  have hextra : Tendsto (fun i => ((U i \ B i).card : ℝ) / (B i).card) l (𝓝 0) := by
    have hz : Tendsto (fun i => ((U i).card : ℝ) / (B i).card - 1) l (𝓝 0) := by
      simpa only [sub_self, U] using hratio.sub_const 1
    apply hz.congr'
    filter_upwards [hpos] with i hi
    have hv : (0 : ℝ) < (B i).card := by exact_mod_cast hi.card_pos
    rw [Finset.card_sdiff_of_subset (hBU i), Nat.cast_sub (Finset.card_le_card (hBU i)),
      sub_div, div_self hv.ne']
  apply relative_limit_contradiction (l := l) (a := Nat.card A)
    (rho := Nat.card (PatX X E)) (b := E.card) Nat.card_pos (hcardpos E) hE.card_pos
    (fun i => (B i).card) (fun i => (U i \ B i).card) (fun i => (T i).card) ?_ hextra
  filter_upwards [hpos] with i hi
  exact ⟨hi.card_pos, hdense i, hcount i⟩

end D5.S1.Dynamics.Symbolic.FiniteTypeMoore
