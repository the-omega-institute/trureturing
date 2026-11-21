/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteSpecialGermSeparation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteSpecialGermSeparation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialGerms]
   utility: none
   digest: The four special lifts have distinct normalized observation germs. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialGerms

/-! Pairwise separation of the normalized observation germs. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialGermSeparation

open Set hiding center
open Filter PeriodicMPSFiveSiteLocalGraphs PeriodicMPSFiveSitePhysicalObservation
  PeriodicMPSFiveSiteCompactSource PeriodicMPSFiveSiteCompactChart
  PeriodicMPSFiveSiteJetCoordinates PeriodicMPSFiveSiteSpecialGerms
open scoped Topology

open private ambientDomain isOpen_ambientDomain
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactChart
open private continuousAt_rebuild rebuild rebuild_center raw_rebuild eventually_valid
  continuous_trace_raw rawTrace_pos_center special_coordinates
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialGerms

noncomputable section

private theorem compatible_rebuild {V : Set source} {u : E}
    (hg : u 8 ≠ 0) (hτ : rawTrace (raw u) ≠ 0)
    (hV : ∀ w ∈ V, w.val ∈ ambientDomain)
    (h : measured (rawSource u) ∈ (fun w : source => measured w.val) '' V) :
    ∃ w ∈ V, raw (rebuild w.val (rawTrace (raw u))) = raw u := by
  obtain ⟨w, hw, he⟩ := h
  change measured w.val = measured (rawSource u) at he
  have he' : normalizeEntries (raw u) = measured (rawSource u) := raw_measured_eq u hg
  have hr := raw_rebuild w.property (hV w hw) hτ
  rw [he, ← he', restore_normalize _ hτ] at hr
  exact ⟨w, hw, hr⟩

private theorem equal_graph_values {e : OpenPartialHomeomorph E E}
    (he : (e : E → E) = tangent) {z u t : E} {a b : ℝ}
    (hz : z ∈ e.source) (hraw : raw z = raw u)
    (ha : (tangent u, normal u) = (t, a))
    (hb : (tangent (e.symm t), normal (e.symm t)) = (t, b)) : a = b := by
  have htan : tangent z = tangent u := funext fun k => congrFun hraw k.castSucc
  have hnr : normal z = normal u := congrFun hraw 9
  have hze : z = e.symm t := by
    have ht : e z = t := by
      rw [show e z = tangent z from congrFun he z, htan]
      exact congrArg Prod.fst ha
    rw [← ht, e.left_inv hz]
  calc
    a = normal u := (congrArg Prod.snd ha).symm
    _ = normal z := hnr.symm
    _ = normal (e.symm t) := congrArg normal hze
    _ = b := congrArg Prod.snd hb

private theorem rectangle_in_preimage {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X × Y → Z} {x : X} {y : Y} {D : Set Z}
    (hf : ContinuousAt f (x, y)) (hD : D ∈ 𝓝 (f (x, y))) :
    ∃ (W : Set X) (I : Set Y), W ∈ 𝓝 x ∧ I ∈ 𝓝 y ∧
      ∀ w ∈ W, ∀ t ∈ I, f (w, t) ∈ D := by
  have h : f ⁻¹' D ∈ 𝓝 (x, y) := hf hD
  obtain ⟨W, hW, I, hI, hWI⟩ := mem_nhds_prod_iff.mp h
  exact ⟨W, I, hW, hI, fun w hw t ht => hWI (mk_mem_prod hw ht)⟩

private theorem rebuild_neighborhood {p : source} {τ : ℝ}
    {e : OpenPartialHomeomorph E E} (hp : p.val ∈ ambientDomain)
    (hz : rebuild p.val τ ∈ e.source) :
    ∃ (V : Set source) (I : Set ℝ), V ∈ 𝓝 p ∧ I ∈ 𝓝 τ ∧
      ∀ w ∈ V, w.val ∈ ambientDomain ∧ ∀ t ∈ I, rebuild w.val t ∈ e.source := by
  let f : Ambient × ℝ → E := fun q => rebuild q.1 q.2
  have h : e.source ∈ 𝓝 (f (p.val, τ)) := e.open_source.mem_nhds hz
  obtain ⟨W, I, hW, hI, hWI⟩ :=
    rectangle_in_preimage (f := f) (continuousAt_rebuild hp) h
  let V : Set source := Subtype.val ⁻¹' (W ∩ ambientDomain)
  have hV : V ∈ 𝓝 p := continuous_subtype_val.continuousAt
    (inter_mem hW (isOpen_ambientDomain.mem_nhds hp))
  refine ⟨V, I, hV, ?_⟩
  refine ⟨hI, fun w hw => ?_⟩
  change w.val ∈ W ∩ ambientDomain at hw
  exact ⟨hw.2, hWI w.val hw.1⟩

private theorem eventually_measured {u : E} {p : source}
    (he : rawSource u = p.val) (hU : ∀ᶠ v in 𝓝 u, rawSource v ∈ source)
    {V : Set source}
    (h : ∀ᶠ q in 𝓝 p, measured q.val ∈ (fun w : source => measured w.val) '' V) :
    ∀ᶠ v in 𝓝 u, measured (rawSource v) ∈ (fun w : source => measured w.val) '' V := by
  classical
  let s : E → source := fun v => if hv : rawSource v ∈ source then ⟨rawSource v, hv⟩ else p
  have hs : Tendsto s (𝓝 u) (𝓝 p) := by
    rw [tendsto_subtype_rng, ← he]
    exact continuous_rawSource.continuousAt.tendsto.congr'
      (hU.mono fun v hv => by simp [s, hv])
  have ho : ∀ᶠ v in 𝓝 u, measured (s v).val ∈ (fun w : source => measured w.val) '' V := hs h
  filter_upwards [ho, hU] with v hv hv'
  simpa only [s, dite_eq_left hv'] using hv

private theorem branch_value_eq {u t : E} {V : Set source} {I : Set ℝ}
    {e : OpenPartialHomeomorph E E} {a b : ℝ} (he : (e : E → E) = tangent)
    (hV : ∀ w ∈ V, w.val ∈ ambientDomain ∧ ∀ r ∈ I, rebuild w.val r ∈ e.source)
    (hτ : rawTrace (raw u) ∈ I) (hn : rawTrace (raw u) ≠ 0) (hu : u 8 ≠ 0)
    (hm : measured (rawSource u) ∈ (fun w : source => measured w.val) '' V)
    (hg : (tangent u, normal u) = (t, a))
    (hh : (tangent (e.symm t), normal (e.symm t)) = (t, b)) : a = b := by
  have hC (w : source) (hw : w ∈ V) : w.val ∈ ambientDomain := (hV w hw).1
  obtain ⟨w, hw, hraw⟩ := compatible_rebuild (V := V) (u := u) hu hn hC hm
  let z : E := rebuild w.val (rawTrace (raw u))
  have hz : z ∈ e.source := (hV w hw).2 _ hτ
  exact equal_graph_values (e := e) (z := z) (u := u) (t := t) (a := a) (b := b)
    he hz hraw hg hh

private theorem eventually_branch_equal {l : Filter E} {x : E → E}
    {V : Set source} {I : Set ℝ} {e : OpenPartialHomeomorph E E} {g h : E → ℝ}
    (he : (e : E → E) = tangent)
    (hV : ∀ w ∈ V, w.val ∈ ambientDomain ∧ ∀ t ∈ I, rebuild w.val t ∈ e.source)
    (hτ : ∀ᶠ t in l, rawTrace (raw (x t)) ∈ I ∧ rawTrace (raw (x t)) ≠ 0)
    (hu : ∀ᶠ t in l, x t 8 ≠ 0)
    (hm : ∀ᶠ t in l, measured (rawSource (x t)) ∈ (fun w : source => measured w.val) '' V)
    (hg : ∀ᶠ t in l, (tangent (x t), normal (x t)) = (t, g t))
    (hh : ∀ᶠ t in l, (tangent (e.symm t), normal (e.symm t)) = (t, h t)) :
    ∀ᶠ t in l, g t = h t := by
  filter_upwards [hτ, hu, hm, hg, hh] with t ht hva hmeas hgt hht
  exact branch_value_eq (u := x t) (t := t) (V := V) (I := I) (e := e) (a := g t) (b := h t)
    he hV ht.1 ht.2 hva hmeas hgt hht

private theorem tendsTo_inverse {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {u : X} {y : Y} (hu : u ∈ e.source) (hy : e u = y) :
    Tendsto e.symm (𝓝 y) (𝓝 u) := by
  have ht : y ∈ e.target := hy ▸ e.map_source hu
  have he : e.symm y = u := hy ▸ e.left_inv hu
  exact he ▸ e.continuousAt_symm ht

private theorem eventually_in_of_tendsto {X Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {l : Filter X} {f : X → Y} {g : Y → Z} {y : Y} {S : Set Z}
    (hf : Tendsto f l (𝓝 y)) (hg : ContinuousAt g y) (hS : S ∈ 𝓝 (g y)) :
    ∀ᶠ x in l, g (f x) ∈ S :=
  (hg.tendsto.comp hf) hS

private theorem nearby_trace {u : E} {l : Filter E} {x : E → E} {I : Set ℝ}
    (hx : Tendsto x l (𝓝 u)) (hI : I ∈ 𝓝 (rawTrace (raw u)))
    (htrace : rawTrace (raw u) ≠ 0) :
    ∀ᶠ t in l, rawTrace (raw (x t)) ∈ I ∧ rawTrace (raw (x t)) ≠ 0 := by
  let S : Set ℝ := I ∩ {z | z ≠ 0}
  have hS : S ∈ 𝓝 (rawTrace (raw u)) := inter_mem hI (isOpen_ne.mem_nhds htrace)
  exact eventually_in_of_tendsto (g := rawTrace ∘ raw) (S := S)
    hx continuous_trace_raw.continuousAt hS

private theorem nearby_gain {u : E} {l : Filter E} {x : E → E}
    (hx : Tendsto x l (𝓝 u)) (hgain : u 8 ≠ 0) : ∀ᶠ t in l, x t 8 ≠ 0 :=
  eventually_in_of_tendsto (g := fun v : E => v 8) (S := {z : ℝ | z ≠ 0})
    hx (continuous_apply (8 : Fin 9)).continuousAt (isOpen_ne.mem_nhds hgain)

private theorem rebuild_at_branch {u v : E} {q : source}
    {ej : OpenPartialHomeomorph E E} (hq : q.val ∈ ambientDomain) (hv : v ∈ ej.source)
    (hr : raw u = raw v) (hbase : rebuild q.val (rawTrace (raw v)) = v) :
    ∃ (V : Set source) (I : Set ℝ), V ∈ 𝓝 q ∧ I ∈ 𝓝 (rawTrace (raw u)) ∧
      ∀ w ∈ V, w.val ∈ ambientDomain ∧ ∀ t ∈ I, rebuild w.val t ∈ ej.source := by
  have hτ : rawTrace (raw u) = rawTrace (raw v) := congrArg rawTrace hr
  have h : rebuild q.val (rawTrace (raw u)) ∈ ej.source := by
    rw [hτ, hbase]
    exact hv
  exact rebuild_neighborhood hq h

private theorem eventual_measured_along {u : E} {p : source} {V : Set source}
    {l : Filter E} {x : E → E} (hx : Tendsto x l (𝓝 u))
    (hp : rawSource u = p.val) (hvalid : ∀ᶠ z in 𝓝 u, rawSource z ∈ source)
    (h : ∀ᶠ z in 𝓝 p, measured z.val ∈ (fun w : source => measured w.val) '' V) :
    ∀ᶠ t in l, measured (rawSource (x t)) ∈ (fun w : source => measured w.val) '' V :=
  Tendsto.eventually (p := fun z => measured (rawSource z) ∈
    (fun w : source => measured w.val) '' V) hx (eventually_measured hp hvalid h)

private theorem equality_of_observation_germs {u : E} {p : source} {V : Set source}
    {I : Set ℝ} {ei ej : OpenPartialHomeomorph E E} {gi gj : E → ℝ}
    (hej : (ej : E → E) = tangent)
    (hx : Tendsto ei.symm (𝓝 (tangent u)) (𝓝 u))
    (hp : rawSource u = p.val) (hvalid : ∀ᶠ z in 𝓝 u, rawSource z ∈ source)
    (hV : ∀ w ∈ V, w.val ∈ ambientDomain ∧ ∀ t ∈ I, rebuild w.val t ∈ ej.source)
    (hI : I ∈ 𝓝 (rawTrace (raw u))) (htrace : rawTrace (raw u) ≠ 0) (hgain : u 8 ≠ 0)
    (hi : ∀ᶠ t in 𝓝 (tangent u), (tangent (ei.symm t), normal (ei.symm t)) = (t, gi t))
    (hj : ∀ᶠ t in 𝓝 (tangent u), (tangent (ej.symm t), normal (ej.symm t)) = (t, gj t))
    (h : ∀ᶠ x in 𝓝 p, measured x.val ∈ (fun w : source => measured w.val) '' V) :
    ∀ᶠ t in 𝓝 (tangent u), gi t = gj t :=
  eventually_branch_equal (l := 𝓝 (tangent u)) (x := ei.symm) (V := V) (I := I)
    (e := ej) (g := gi) (h := gj) hej hV
    (nearby_trace (x := ei.symm) hx hI htrace)
    (nearby_gain (x := ei.symm) hx hgain)
    (eventual_measured_along (x := ei.symm) hx hp hvalid h) hi hj

private theorem distinct_of_branches {u v : E} {p q : source}
    {ei ej : OpenPartialHomeomorph E E} {Ui Uj : Set E} {gi gj : E → ℝ}
    (hei : (ei : E → E) = tangent) (hej : (ej : E → E) = tangent)
    (hxi : u ∈ ei.source) (hxj : v ∈ ej.source)
    (hUi : IsOpen Ui) (hUj : IsOpen Uj) (hyi : tangent u ∈ Ui) (hyj : tangent v ∈ Uj)
    (hgi : ∀ t ∈ Ui, (tangent (ei.symm t), normal (ei.symm t)) = (t, gi t))
    (hgj : ∀ t ∈ Uj, (tangent (ej.symm t), normal (ej.symm t)) = (t, gj t))
    (hr : raw u = raw v) (hp : rawSource u = p.val) (hq : q.val ∈ ambientDomain)
    (hbase : rebuild q.val (rawTrace (raw v)) = v)
    (hvalid : ∀ᶠ z in 𝓝 u, rawSource z ∈ source)
    (hgain : u 8 ≠ 0) (htrace : rawTrace (raw u) ≠ 0)
    (hne : ¬ gi =ᶠ[𝓝 (tangent u)] gj) :
    ∃ V : Set source, V ∈ 𝓝 q ∧
      ¬ ∀ᶠ x in 𝓝 p, measured x.val ∈ (fun w : source => measured w.val) '' V := by
  obtain ⟨V, I, hV, hI, hVI⟩ := rebuild_at_branch (u := u) hq hxj hr hbase
  have hy : tangent u = tangent v := funext fun k => congrFun hr k.castSucc
  have hi : ∀ᶠ t in 𝓝 (tangent u), t ∈ Ui := hUi.mem_nhds hyi
  have hj : ∀ᶠ t in 𝓝 (tangent u), t ∈ Uj := hUj.mem_nhds (hy.symm ▸ hyj)
  have hx := tendsTo_inverse ei hxi (congrFun hei u)
  exact ⟨V, hV, fun h => hne (equality_of_observation_germs (u := u) (ei := ei) (ej := ej)
    (gi := gi) (gj := gj) hej hx hp hvalid hVI hI htrace hgain (hi.mono hgi) (hj.mono hgj) h)⟩

/-- A neighborhood of the second lift cannot contain representatives of all
nearby observations of the first lift. -/
theorem specialPoint_germs_distinct (i j : Fin 4) (hij : i ≠ j) :
    ∃ V : Set source, V ∈ 𝓝 (specialPoint j) ∧
      ¬ ∀ᶠ p in 𝓝 (specialPoint i), measured p.val ∈ (fun x : source => measured x.val) '' V := by
  obtain ⟨ei, Ui, gi, hei, hxi, hUi, hyi, _, _, hgi, hji⟩ := exists_certified_graph i
  obtain ⟨ej, Uj, gj, hej, hxj, hUj, hyj, _, _, hgj, hjj⟩ := exists_certified_graph j
  have hg : center i 8 ≠ 0 := (special_coordinates i).2.2.symm ▸ one_ne_zero
  exact distinct_of_branches (u := center i) (v := center j) (p := specialPoint i)
    (q := specialPoint j) (ei := ei) (ej := ej) (Ui := Ui) (Uj := Uj) (gi := gi) (gj := gj)
    hei hej hxi hxj hUi hUj hyi hyj hgi hgj (raw_center_eq i j) rfl (specialPoint_in_chart j)
    (rebuild_center j) (eventually_valid i) hg (rawTrace_pos_center i).ne'
    (normal_germs_ne hij hji hjj)

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialGermSeparation
