/- GID: D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CoverConnectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Connected canonical countercovers and exact triangle scope. -/

import D5.S3.Combinatorics.Graph.StarForming.CoverStability
import D5.S3.Combinatorics.Graph.StarForming.FiniteCover
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The connected-countercover argument and examples in
COVER_STABLE_MINIMAL_SELECTIONS at subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0. -/
namespace D5.S3.Combinatorics.Graph.StarForming.CoverConnectivity
open Regular CoverPullback
variable {V : Type} (G : SimpleGraph V) (S : V → Prop) (d : V)

def canonicalGraph : SimpleGraph (V × Bool) where
  Adj := CanonicalAdj G.Adj S d
  symm := ⟨canonical_symmetric d (fun _ _ => G.adj_symm)⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

private def flip : canonicalGraph G S d ≃g canonicalGraph G S d where
  toFun x := (x.1,!x.2)
  invFun x := (x.1,!x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_rel_iff' := by
    rintro ⟨x,a⟩ ⟨y,b⟩
    cases a <;> cases b <;> simp [canonicalGraph,CanonicalAdj]

private theorem lift_reachable {v w : V} (h : G.Reachable v w) (a : Bool) :
    ∃ b, (canonicalGraph G S d).Reachable (v,a) (w,b) := by
  obtain ⟨p⟩ := h
  induction p generalizing a with
  | nil => exact ⟨a,.rfl⟩
  | @cons v w x hvw p ih =>
    obtain ⟨y,hy,hproj⟩ := (canonical_cover (adjacency := G.Adj) (selection := S) d).neighbor_surjective
      (v,a) w hvw
    obtain ⟨b,hb⟩ := ih y.2
    refine ⟨b,SimpleGraph.Reachable.trans ?_ hb⟩
    have he : y=(w,y.2) := Prod.ext hproj rfl
    exact SimpleGraph.Adj.reachable (he ▸ hy)

private theorem preconnected_of_fiber (hG : G.Preconnected)
    (hroot : (canonicalGraph G S d).Reachable (d,false) (d,true)) :
    (canonicalGraph G S d).Preconnected := by
  have hr (v : V) (a : Bool) : (canonicalGraph G S d).Reachable (d,false) (v,a) := by
    obtain ⟨b,hb⟩ := lift_reachable G S d (hG d v) false
    have hf := hb.map (flip G S d).toHom
    cases a <;> cases b
    · exact hb
    · exact hroot.trans hf
    · exact hroot.trans hf
    · exact hb
  intro x y
  exact (hr x.1 x.2).symm.trans (hr y.1 y.2)

/-- A missing safe certificate in a minimal selection forces a fragile
triangle. Its one crossed edge connects the two root sheets, and lifting
base paths proves that the actual canonical countercover is connected. -/
theorem canonical_preconnected (hG : G.Preconnected)
    (hS : Minimal G.Adj S) (hd : S d)
    (hmissing : ¬ ((¬ TwoAt G.Adj (fun v => S v ∧ v≠d) d) ∨
      ∃ outside, SafeFailure G.Adj S d outside)) :
    (canonicalGraph G S d).Preconnected := by
  classical
  have hself : TwoAt G.Adj (fun v => S v ∧ v≠d) d := by
    by_contra hn
    exact hmissing (Or.inl hn)
  obtain ⟨x,hfail⟩ := covered_deletion_has_failure G.Adj S hS d hd hself
  have hunsafe : ¬ (G.Adj x d → ∀ c, S c → G.Adj x c → ¬G.Adj c d) := by
    intro hs
    exact hmissing (Or.inr ⟨x,hfail,hs⟩)
  have hxd : G.Adj x d := by
    by_contra hn
    exact hunsafe (fun h => (hn h).elim)
  have hc : ∃ c, S c ∧ G.Adj x c ∧ G.Adj c d := by
    by_contra hn
    apply hunsafe
    intro _ c hs hxc hcd
    exact hn ⟨c,hs,hxc,hcd⟩
  obtain ⟨c,hc,hxc,hcd⟩ := hc
  have hne : c≠d := fun h => G.irrefl (h ▸ hcd)
  apply preconnected_of_fiber G S d hG
  have h1 : (canonicalGraph G S d).Adj (d,false) (x,true) :=
    ⟨G.adj_symm hxd,Or.inl ⟨Or.inl ⟨rfl,hfail.1⟩,by simp⟩⟩
  have h2 : (canonicalGraph G S d).Adj (x,true) (c,true) :=
    canonical_retained_edge d x c true hc hne hxc
  have h3 : (canonicalGraph G S d).Adj (c,true) (d,true) :=
    canonical_selected_edge d c d true hc hd hcd
  exact h1.reachable.trans (h2.reachable.trans h3.reachable)

/-- Restricting tests to connected two-sheeted covers still detects every
missing safe certificate over a connected base. -/
theorem connected_countercover (hG : G.Preconnected)
    (hS : Minimal G.Adj S) (hd : S d)
    (hmissing : ¬ ((¬ TwoAt G.Adj (fun v => S v ∧ v≠d) d) ∨
      ∃ outside, SafeFailure G.Adj S d outside)) :
    (canonicalGraph G S d).Preconnected ∧
    NeighborhoodCover G.Adj (canonicalGraph G S d).Adj Prod.fst ∧
    ¬ Minimal (canonicalGraph G S d).Adj (fun v => S v.1) :=
  ⟨canonical_preconnected G S d hG hS hd hmissing,canonical_cover d,
    canonical_nonminimal_of_missing_certificate (fun _ => G.irrefl)
      (fun _ _ => G.adj_symm) d hd hmissing⟩

/-- For a connected base, safe certificates are exactly preservation of
minimality in every connected two-sheeted neighborhood cover. -/
theorem safe_iff_connected_covers (hG : G.Preconnected) (hS : Minimal G.Adj S) :
    HasSafeCertificates G.Adj S ↔
    ∀ H : SimpleGraph (V × Bool),
      NeighborhoodCover G.Adj H.Adj Prod.fst → H.Preconnected →
      Minimal H.Adj (fun v => S v.1) := by
  constructor
  · intro hs H hc _
    exact minimal_pullback_of_safe_certificates hc (fun _ => G.irrefl)
      (fun _ _ => G.adj_symm) (fun _ _ => H.adj_symm) hS.1 hs
  · intro hall d hd
    by_contra hm
    have hh := connected_countercover G S d hG hS hd hm
    exact hh.2.2 (hall (canonicalGraph G S d) hh.2.1 hh.1)

/-- In the complete triangle a selected pair has safe self-failures even
though boundary triangle-freeness fails. -/
theorem triangle_scope :
    let A : Fin 3 → Fin 3 → Prop := (·≠·)
    let T : Fin 3 → Prop := (·≠2)
    Minimal A T ∧ HasSafeCertificates A T ∧ ¬BoundaryTriangleFree A T := by
  dsimp
  have hf : Forms (fun a b : Fin 3 => a≠b) (fun v => v≠2) := by
    unfold Forms TwoAt
    decide +kernel
  have hs : ∀ d : Fin 3, d≠2 →
      ¬ TwoAt (fun a b : Fin 3 => a≠b) (fun v => v≠2 ∧ v≠d) d := by
    unfold TwoAt
    decide +kernel
  refine ⟨?_,?_,?_⟩
  · apply minimal_of_single_deletions hf
    intro d hd hforms
    exact hs d hd (hforms d (fun h => h.2 rfl))
  · intro d hd
    exact Or.inl (hs d hd)
  · intro h
    exact h 2 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def sevenNeighbors (v : Fin 7) : List (Fin 7) :=
  match v.val with
  | 0 => [1,2,6]
  | 1 => [0,4,6]
  | 2 => [0,5]
  | 3 => [4,5]
  | 4 => [1,3]
  | 5 => [2,3]
  | _ => [0,1]

def sevenGraph : SimpleGraph (Fin 7) where
  Adj v w := w∈sevenNeighbors v
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel sevenGraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_∈_))

def sevenSelected (v : Fin 7) : Prop := v.val<4
instance (v : Fin 7) : Decidable (sevenSelected v) := inferInstanceAs (Decidable (_<_))

private theorem seven_minimal : Minimal sevenGraph.Adj sevenSelected := by
  have hf : Forms sevenGraph.Adj sevenSelected := by
    unfold Forms TwoAt
    decide +kernel
  let failure : Fin 7 → Fin 7 := fun v =>
    match v.val with
    | 0 => 6
    | 1 => 4
    | 2 => 5
    | 3 => 3
    | _ => 0
  have hd : ∀ d : Fin 7, sevenSelected d →
      ¬ (sevenSelected (failure d) ∧ failure d≠d) ∧
      ¬ TwoAt sevenGraph.Adj (fun v => sevenSelected v ∧ v≠d) (failure d) := by
    unfold TwoAt
    decide +kernel
  apply minimal_of_single_deletions hf
  intro d hd' hforms
  exact (hd d hd').2 (hforms (failure d) (hd d hd').1)

private theorem seven_preconnected : sevenGraph.Preconnected := by
  have root (v : Fin 7) : sevenGraph.Reachable 0 v := by
    have edge {a b : Fin 7} (h : sevenGraph.Adj a b) : sevenGraph.Reachable a b := h.reachable
    fin_cases v
    · exact .rfl
    · exact edge (by decide)
    · exact edge (by decide)
    · exact (edge (a := 0) (b := 1) (by decide)).trans
        ((edge (a := 1) (b := 4) (by decide)).trans (edge (by decide)))
    · exact (edge (a := 0) (b := 1) (by decide)).trans (edge (by decide))
    · exact (edge (a := 0) (b := 2) (by decide)).trans (edge (by decide))
    · exact edge (by decide)
  intro v w
  exact (root v).symm.trans (root w)

private theorem seven_missing : ¬ ((¬ TwoAt sevenGraph.Adj
    (fun v => sevenSelected v ∧ v≠0) 0) ∨
    ∃ outside, SafeFailure sevenGraph.Adj sevenSelected 0 outside) := by
  unfold SafeFailure Failure TwoAt
  decide +kernel

/-- The source seven-vertex connected triangle example is actually minimal,
but its actual connected double cover has a nonminimal full pullback. This
refutes unrestricted minimal pullback, not a maximum-parameter inequality. -/
theorem seven_counterexample :
    Minimal sevenGraph.Adj sevenSelected ∧ sevenGraph.Preconnected ∧
    (canonicalGraph sevenGraph sevenSelected 0).Preconnected ∧
    NeighborhoodCover sevenGraph.Adj (canonicalGraph sevenGraph sevenSelected 0).Adj Prod.fst ∧
    ¬Minimal (canonicalGraph sevenGraph sevenSelected 0).Adj (fun v => sevenSelected v.1) :=
  ⟨seven_minimal,seven_preconnected,
    connected_countercover sevenGraph sevenSelected 0 seven_preconnected seven_minimal
      (by decide) seven_missing⟩

end D5.S3.Combinatorics.Graph.StarForming.CoverConnectivity
