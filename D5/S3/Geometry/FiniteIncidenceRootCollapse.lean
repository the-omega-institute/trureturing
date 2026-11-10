/- GID: D5/S3/Geometry/FiniteIncidenceRootCollapse
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteIncidenceRootCollapse
   mirror-E: none(waiver:finite-incidence-pruning-construction)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Original-ground finite incidence root-K collapse certificates. -/
/-

  SOURCE ATTEMPT — UNCOMPILED.

  Released ordinary finite incidence certificate for the restricted
  bipartite-distance-hereditary (pendant/twin-pruning) class.  This file is
  deliberately an implementation owner: its input certificate contains only
  incidence/pruning hypotheses.  The collapse sequence, retained frames,
  critical face, core and all coordinate maps are constructed below.

  No kernel, axiom, Scribe, Reg, admission, gate, repository or publication
  result is claimed by this source-only artifact.
   Metadata author classification (source only; independent review pending):
   State and rootK retain arbitrary finite «I», J and Prop-valued incidence; Pruning and build construct Result by structural pruning. This is a parametrized geometric construction, not a bounded computation, certificate checker, numerical reduction or certified finite instance.
   No empirical mirror or compilation/acceptance claim is supplied.
-/
import D5.S3.Geometry.FiniteRelativeSimplicialCollapse
import D5.S3.Geometry.FiniteIncidenceRootPruning
import D5.S3.Geometry.FiniteVertexDominationCollapse
import D5.S3.Geometry.FiniteAlexanderDualCollapse

noncomputable section

open Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteIncidenceRootCollapse

open FiniteConeCollapse FiniteConeUnionWedge FiniteSimplicialJoin
open FiniteCoordinateTruncation FiniteElementaryCollapse
open FiniteRelativeSimplicialCollapse
open FiniteVertexDominationCollapse
open FiniteAlexanderDualCollapse
open FiniteComponentClosure (vertexComplex)

variable {«I» J : Type*} [Fintype «I»] [DecidableEq «I»] [Fintype J] [DecidableEq J]


open private D5.S3.Geometry.FiniteIncidenceRootCollapse.simplex_singleton D5.S3.Geometry.FiniteIncidenceRootCollapse.simplex_empty D5.S3.Geometry.FiniteIncidenceRootCollapse.cone_bot_simplex D5.S3.Geometry.FiniteIncidenceRootCollapse.rootK_le_full D5.S3.Geometry.FiniteIncidenceRootCollapse.fresh_of_active_erase D5.S3.Geometry.FiniteIncidenceRootCollapse.singleton_active D5.S3.Geometry.FiniteIncidenceRootCollapse.cone_sup D5.S3.Geometry.FiniteIncidenceRootCollapse.cone_simplex D5.S3.Geometry.FiniteIncidenceRootCollapse.witness_core_le_endpoint D5.S3.Geometry.FiniteIncidenceRootCollapse.witness_critical_support from D5.S3.Geometry.FiniteIncidenceRootPruning


/-! ### Recursive constructor -/

def build {ρ : «I» → J → Prop} : {q : State ρ} → (c : Pruning ρ q) → Result ρ q
  | q, .void _ hrows =>
      .terminal .void (rootK_empty_rows ρ q hrows) hrows
  | q, .unit _ hrows hfull =>
      .terminal .unit (rootK_full_rows ρ q hrows hfull) ⟨hrows, hfull⟩
  | q, .emptyRow _ b hb hempty => by
      classical
      have hK := rootK_empty_row ρ q hb hempty
      by_cases hA : q.active.Nonempty
      · let p := Classical.choose hA
        have hp := Classical.choose_spec hA
        exact .regular {
          endpoint := vertexComplex p
          sequence := (simplexCollapse q.active p hp).cast hK.symm rfl
          core := vertexComplex p
          pivot := p
          pivot_mem := hp
          core_sequence := Sequence.refl _
          critical := none
          endpoint_eq_core := by intro; rfl
          endpoint_eq_attach := by intro «σ» h; cases h
          critical_nonempty := by intro «σ» h; cases h
          critical_outside := by intro «σ» h; cases h
          critical_boundary := by intro «σ» h; cases h }
      · have hAE : q.active = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => hA ⟨x, hx⟩)
        have hfull : ∀ c ∈ q.rows, rowNeighborhood ρ q c = q.active := by
          intro c hc
          apply Finset.Subset.antisymm
          · intro x hx
            exact ((mem_rowNeighborhood ρ q x c).mp hx).1
          · rw [hAE]
            exact Finset.empty_subset _
        exact .terminal .unit (rootK_full_rows ρ q ⟨b, hb⟩ hfull) ⟨⟨b, hb⟩, hfull⟩
  | q, .isolatedColumn _ x hx hrows hiso => by
      exact .regular {
        endpoint := vertexComplex x
        sequence := isolatedCollapse ρ q x hx hrows hiso
        core := vertexComplex x
        pivot := x
        pivot_mem := hx
        core_sequence := Sequence.refl _
        critical := none
        endpoint_eq_core := by intro; rfl
        endpoint_eq_attach := by intro «σ» h; cases h
        critical_nonempty := by intro «σ» h; cases h
        critical_outside := by intro «σ» h; cases h
        critical_boundary := by intro «σ» h; cases h }
  | q, .redundantRow _ b c hb hc hbc hsub child => by
      classical
      have hK := rootK_row_erase ρ q hb hc hbc hsub
      have hbchild : b ∈ (eraseRow ρ q c).rows := Finset.mem_erase.mpr ⟨hbc, hb⟩
      cases build child with
      | terminal tag hchild hLaw =>
          cases tag with
          | void =>
              change (eraseRow ρ q c).rows = ∅ at hLaw
              rw [hLaw] at hbchild
              exact (Finset.notMem_empty b hbchild).elim
          | unit =>
              change (eraseRow ρ q c).rows.Nonempty ∧
                (∀ d ∈ (eraseRow ρ q c).rows,
                  rowNeighborhood ρ (eraseRow ρ q c) d = (eraseRow ρ q c).active) at hLaw
              have hfull : ∀ d ∈ q.rows, rowNeighborhood ρ q d = q.active := by
                intro d hd
                by_cases hdc : d = c
                · subst d
                  have hbfull : rowNeighborhood ρ q b = q.active := hLaw.2 b hbchild
                  apply Finset.Subset.antisymm
                  · intro x hx
                    exact ((mem_rowNeighborhood ρ q x c).mp hx).1
                  · intro x hx
                    apply rowSubset_neighborhood ρ q hsub
                    rw [hbfull]
                    exact hx
                · exact hLaw.2 d (Finset.mem_erase.mpr ⟨hdc, hd⟩)
              exact .terminal .unit (hK.trans hchild) ⟨⟨b, hb⟩, hfull⟩
      | regular w =>
          exact .regular {
            endpoint := w.endpoint
            sequence := w.sequence.cast hK.symm rfl
            core := w.core
            pivot := w.pivot
            pivot_mem := w.pivot_mem
            core_sequence := w.core_sequence
            critical := w.critical
            endpoint_eq_core := w.endpoint_eq_core
            endpoint_eq_attach := w.endpoint_eq_attach
            critical_nonempty := w.critical_nonempty
            critical_outside := w.critical_outside
            critical_boundary := w.critical_boundary }
  | q, .dominatedColumn _ x y hx hy hxy hsub child => by
      classical
      have hExt : Extends (rootK ρ q) x y := by
        rintro s ⟨hs, b, hb, hsb⟩ hyS
        refine ⟨Finset.insert_nonempty _ _, b, hb, ?_⟩
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · refine Finset.mem_sdiff.mpr ⟨hx, ?_⟩
          intro hxb
          exact (Finset.mem_sdiff.mp (hsb hyS)).2
            (columnSubset_neighborhood ρ q hy hsub b hb hxb)
        · exact hsb hz
      let P := sequence (rootK ρ q) x y hxy hExt
      cases build child with
      | terminal tag hchild hLaw =>
          cases tag with
          | void =>
              have hrows : q.rows = ∅ := hLaw
              exact .terminal .void (rootK_empty_rows ρ q hrows) hrows
          | unit =>
              change (eraseColumn ρ q y).rows.Nonempty ∧
                (∀ b ∈ (eraseColumn ρ q y).rows,
                  rowNeighborhood ρ (eraseColumn ρ q y) b = (eraseColumn ρ q y).active) at hLaw
              have hfull : ∀ b ∈ q.rows, rowNeighborhood ρ q b = q.active := by
                intro b hb
                have hρx : ρ x b := by
                  apply ((mem_rowNeighborhood ρ (eraseColumn ρ q y) x b).mp ?_).2
                  rw [hLaw.2 b hb]
                  exact Finset.mem_erase.mpr ⟨hxy, hx⟩
                apply Finset.Subset.antisymm
                · intro z hz
                  exact ((mem_rowNeighborhood ρ q z b).mp hz).1
                · intro z hz
                  apply (mem_rowNeighborhood ρ q z b).mpr
                  refine ⟨hz, ?_⟩
                  by_cases hzy : z = y
                  · subst z
                    exact hsub b hb hρx
                  · apply ((mem_rowNeighborhood ρ (eraseColumn ρ q y) z b).mp ?_).2
                    rw [hLaw.2 b hb]
                    exact Finset.mem_erase.mpr ⟨hzy, hz⟩
              exact .terminal .unit (rootK_full_rows ρ q hLaw.1 hfull) ⟨hLaw.1, hfull⟩
      | regular w =>
          have hdel := rootK_column_delete ρ q hy hxy hsub
          exact .regular {
            endpoint := w.endpoint
            sequence := P.append (w.sequence.cast hdel.symm rfl)
            core := w.core
            pivot := w.pivot
            pivot_mem := Finset.mem_of_mem_erase w.pivot_mem
            core_sequence := w.core_sequence
            critical := w.critical
            endpoint_eq_core := w.endpoint_eq_core
            endpoint_eq_attach := w.endpoint_eq_attach
            critical_nonempty := w.critical_nonempty
            critical_outside := w.critical_outside
            critical_boundary := w.critical_boundary }
  | q, .singletonRow _ b a hsingle child => by
      classical
      let U := q.active.erase a
      let D := incidenceSimplex U
      have haA : a ∈ q.active := singleton_active ρ q hsingle
      have haD : Fresh a D := fresh_of_active_erase q.active a
      cases build child with
      | terminal tag hchild hLaw =>
          cases tag with
          | void =>
              change (singletonChild ρ q a).rows = ∅ at hLaw
              have hK := singleton_no_apex ρ q a hsingle hLaw
              by_cases hU : U.Nonempty
              · let p := Classical.choose hU
                have hp := Classical.choose_spec hU
                exact .regular {
                  endpoint := vertexComplex p
                  sequence := (simplexCollapse U p hp).cast hK.symm rfl
                  core := vertexComplex p
                  pivot := p
                  pivot_mem := Finset.mem_of_mem_erase hp
                  core_sequence := Sequence.refl _
                  critical := none
                  endpoint_eq_core := by intro; rfl
                  endpoint_eq_attach := by intro «σ» h; cases h
                  critical_nonempty := by intro «σ» h; cases h
                  critical_outside := by intro «σ» h; cases h
                  critical_boundary := by intro «σ» h; cases h }
              · have hUE : U = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => hU ⟨x, hx⟩)
                have hact : q.active = {a} := by
                  apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
                  refine ⟨⟨a, haA⟩, ?_⟩
                  intro z hz
                  by_contra hza
                  exact hU ⟨z, Finset.mem_erase.mpr ⟨hza, hz⟩⟩
                have hfull : ∀ c ∈ q.rows, rowNeighborhood ρ q c = q.active := by
                  intro c hc
                  have hac : ρ a c := by
                    by_contra hnot
                    have hcf : c ∈ (singletonChild ρ q a).rows :=
                      Finset.mem_filter.mpr ⟨hc, hnot⟩
                    rw [hLaw] at hcf
                    exact Finset.notMem_empty c hcf
                  apply Finset.Subset.antisymm
                  · intro z hz
                    exact ((mem_rowNeighborhood ρ q z c).mp hz).1
                  · intro z hz
                    have hza : z = a := by
                      rw [hact] at hz
                      exact Finset.mem_singleton.mp hz
                    subst z
                    exact (mem_rowNeighborhood ρ q a c).mpr ⟨haA, hac⟩
                exact .terminal .unit (hK.trans (by
                  change incidenceSimplex U = ⊥
                  rw [hUE]
                  exact simplex_empty))
                  ⟨⟨b, hsingle.1⟩, hfull⟩
          | unit =>
              change (singletonChild ρ q a).rows.Nonempty ∧
                (∀ c ∈ (singletonChild ρ q a).rows,
                  rowNeighborhood ρ (singletonChild ρ q a) c =
                    (singletonChild ρ q a).active) at hLaw
              have hapex := singleton_apex_of_child_rows ρ q a hsingle hLaw.1
              have hdec := singleton_decomposition ρ q a hsingle hapex
              by_cases hU : U.Nonempty
              · let p := Classical.choose hU
                have hp := Classical.choose_spec hU
                let Kparent := D ⊔ cone a (⊥ : PreAbstractSimplicialComplex «I»)
                have hparent : rootK ρ q = Kparent := by
                  rw [hdec, hchild]
                exact .regular {
                  endpoint := Kparent
                  sequence := (Sequence.refl Kparent).cast hparent.symm rfl
                  core := D
                  pivot := p
                  pivot_mem := Finset.mem_of_mem_erase hp
                  core_sequence := simplexCollapse U p hp
                  critical := some ({a} : Finset «I»)
                  endpoint_eq_core := by intro h; cases h
                  endpoint_eq_attach := by
                    intro «σ» hσ
                    have he : ({a} : Finset «I») = «σ» := Option.some.inj hσ
                    subst «σ»
                    change D ⊔ cone a (⊥ : PreAbstractSimplicialComplex «I») =
                      D ⊔ incidenceSimplex {a}
                    rw [cone_bot_simplex]
                  critical_nonempty := by
                    intro «σ» hσ
                    have he : ({a} : Finset «I») = «σ» := Option.some.inj hσ
                    subst «σ»
                    exact Finset.singleton_nonempty _
                  critical_outside := by
                    intro «σ» hσ hmem
                    have he : ({a} : Finset «I») = «σ» := Option.some.inj hσ
                    subst «σ»
                    exact haD {a} hmem (Finset.mem_singleton_self _)
                  critical_boundary := by
                    intro «σ» hσ t ht
                    have he : ({a} : Finset «I») = «σ» := Option.some.inj hσ
                    subst «σ»
                    left
                    by_contra hne
                    have hte : t = {a} :=
                      Finset.eq_singleton_iff_nonempty_unique_mem.mpr
                        ⟨Finset.nonempty_iff_ne_empty.mpr hne,
                          fun z hz => Finset.mem_singleton.mp (ht.subset hz)⟩
                    exact ht.ne hte }
              · have hUE : U = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => hU ⟨x, hx⟩)
                have hparent : rootK ρ q = vertexComplex a := by
                  rw [hdec, hchild]
                  change incidenceSimplex U ⊔ cone a (⊥ : PreAbstractSimplicialComplex «I») = _
                  simp [hUE, simplex_empty, cone_bot_simplex, simplex_singleton]
                exact .regular {
                  endpoint := vertexComplex a
                  sequence := (Sequence.refl (vertexComplex a)).cast hparent.symm rfl
                  core := vertexComplex a
                  pivot := a
                  pivot_mem := haA
                  core_sequence := Sequence.refl _
                  critical := none
                  endpoint_eq_core := by intro; rfl
                  endpoint_eq_attach := by intro «σ» h; cases h
                  critical_nonempty := by intro «σ» h; cases h
                  critical_outside := by intro «σ» h; cases h
                  critical_boundary := by intro «σ» h; cases h }
      | regular w =>
          have hsourceD : rootK ρ (singletonChild ρ q a) ≤ D :=
            rootK_le_full ρ (singletonChild ρ q a)
          have hcoreRoot : w.core ≤ rootK ρ (singletonChild ρ q a) :=
            (witness_core_le_endpoint w).trans w.sequence.monotone
          have hcoreD : w.core ≤ D := hcoreRoot.trans hsourceD
          have hpU : w.pivot ∈ U := w.pivot_mem
          have hap : a ≠ w.pivot := by
            intro he
            exact (Finset.mem_erase.mp hpU).1 he.symm
          have hpCore : ({w.pivot} : Finset «I») ∈ w.core :=
            w.core_sequence.monotone (show ({w.pivot} : Finset «I») ∈ vertexComplex w.pivot from rfl)
          have hapex := singleton_apex_of_child_face ρ q a hsingle (hcoreRoot hpCore)
          have hdec := singleton_decomposition ρ q a hsingle hapex
          let main := (w.sequence.liftOver D a hsourceD haD).cast hdec.symm rfl
          let coreSeq := liftCoreToBase U w.core a w.pivot hcoreD haD
            w.core_sequence hpU hap
          exact .regular {
            endpoint := D ⊔ cone a w.endpoint
            sequence := main
            core := D ⊔ cone a w.core
            pivot := w.pivot
            pivot_mem := Finset.mem_of_mem_erase hpU
            core_sequence := coreSeq
            critical := w.critical.map (insert a)
            endpoint_eq_core := by
              intro h
              cases hc : w.critical with
              | none => rw [w.endpoint_eq_core hc]
              | some τ => simp [hc] at h
            endpoint_eq_attach := by
              intro «σ» hσ
              cases hc : w.critical with
              | none => simp [hc] at hσ
              | some τ =>
                  have he : insert a τ = «σ» := Option.some.inj (by simpa [hc] using hσ)
                  subst «σ»
                  rw [w.endpoint_eq_attach τ hc, cone_sup, cone_simplex, sup_assoc]
            critical_nonempty := by
              intro «σ» hσ
              cases hc : w.critical with
              | none => simp [hc] at hσ
              | some τ =>
                  have he : insert a τ = «σ» := Option.some.inj (by simpa [hc] using hσ)
                  subst «σ»
                  exact Finset.insert_nonempty _ _
            critical_outside := by
              intro «σ» hσ hmem
              cases hc : w.critical with
              | none => simp [hc] at hσ
              | some τ =>
                  have he : insert a τ = «σ» := Option.some.inj (by simpa [hc] using hσ)
                  subst «σ»
                  have hτU : τ ⊆ U := witness_critical_support w hc
                  have haτ : a ∉ τ := fun ha => (Finset.mem_erase.mp (hτU ha)).1 rfl
                  rcases hmem with hD | hcone
                  · exact haD (insert a τ) hD (Finset.mem_insert_self _ _)
                  · have haug : AugmentedFace w.core τ := by
                      simpa only [Finset.erase_insert haτ] using hcone.2
                    rcases haug with he | hτC
                    · exact (w.critical_nonempty τ hc).ne_empty he
                    · exact w.critical_outside τ hc hτC
            critical_boundary := by
              intro «σ» hσ t ht
              cases hc : w.critical with
              | none => simp [hc] at hσ
              | some τ =>
                  have he : insert a τ = «σ» := Option.some.inj (by simpa [hc] using hσ)
                  subst «σ»
                  have hτU : τ ⊆ U := witness_critical_support w hc
                  by_cases hte : t = ∅
                  · exact Or.inl hte
                  · right
                    have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr hte
                    by_cases hat : a ∈ t
                    · have het : t.erase a ⊆ τ := by
                        intro z hz
                        rcases Finset.mem_insert.mp (ht.subset (Finset.mem_of_mem_erase hz)) with hza | hzτ
                        · exact ((Finset.mem_erase.mp hz).1 hza).elim
                        · exact hzτ
                      have hstrict : t.erase a ⊂ τ := by
                        refine Finset.ssubset_iff_subset_ne.mpr ⟨het, ?_⟩
                        intro heq
                        apply ht.ne
                        calc
                          t = insert a (t.erase a) := (Finset.insert_erase hat).symm
                          _ = insert a τ := congrArg (insert a) heq
                      exact Or.inr ⟨htne, w.critical_boundary τ hc (t.erase a) hstrict⟩
                    · exact Or.inl ⟨htne, fun z hz => hτU (by
                        rcases Finset.mem_insert.mp (ht.subset hz) with hza | hzτ
                        · exact (hat (hza ▸ hz)).elim
                        · exact hzτ)⟩ }
termination_by structural q c => c

/-! ### Public native-map and replay contracts -/

def nativeSDR {ρ : «I» → J → Prop} {q : State ρ} (w : Witness ρ q) :
    RelativeSDR (rootK ρ q) w.endpoint w.sequence.monotone := w.sequence.realize

def nativeInclusion {ρ : «I» → J → Prop} {q : State ρ} (w : Witness ρ q) :
    C(Space w.endpoint, Space (rootK ρ q)) := w.sequence.inclusion

def nativeRetraction {ρ : «I» → J → Prop} {q : State ρ} (w : Witness ρ q) :
    C(Space (rootK ρ q), Space w.endpoint) := w.sequence.sequenceRetraction

theorem nativeRetraction_inclusion {ρ : «I» → J → Prop} {q : State ρ}
    (w : Witness ρ q) (x : Space w.endpoint) :
    nativeRetraction w (nativeInclusion w x) = x :=
  w.sequence.sequenceRetraction_inclusion x

theorem nativeHomotopy_fixed {ρ : «I» → J → Prop} {q : State ρ}
    (w : Witness ρ q) (t : Set.Icc (0 : ℝ) 1) (x : Space (rootK ρ q))
    (hx : x.val ∈ realization w.endpoint) :
    w.sequence.collapseHomotopy (t, x) = x :=
  w.sequence.collapseHomotopy_fixed t x hx

def rootCertificate {ρ : «I» → J → Prop} {q : State ρ} (c : Pruning ρ q) :
    Result ρ q := build c

end D5.S3.Geometry.FiniteIncidenceRootCollapse
