/- GID: D5/S3/Combinatorics/Graph/StarForming/BinaryLift
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/BinaryLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual binary voltage lifts, switching isomorphisms and connectivity. -/

import D5.S3.Combinatorics.Graph.StarForming.Isomorphism
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring

/-! The binary-cover construction in HEAWOOD_DOUBLE_COVER_GAIN at
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. Switching is an actual vertex permutation. The connectivity
criterion is symbolic and applies to arbitrary connected base graphs. -/

namespace D5.S3.Combinatorics.Graph.StarForming.BinaryLift
abbrev F2 := ZMod 2
variable {V : Type} (G : SimpleGraph V)

structure Voltage where
  sign : V → V → F2
  symmetric : ∀ v w, G.Adj v w → sign v w = sign w v

private theorem char2 (a : F2) : a+a=0 := by
  have h : ∀ a : F2, a+a=0 := by decide +kernel
  exact h a

def graph (s : Voltage G) : SimpleGraph (V × F2) where
  Adj x y := G.Adj x.1 y.1 ∧ x.2+y.2=s.sign x.1 y.1
  symm := ⟨fun x y h => ⟨G.adj_symm h.1,by rw [add_comm,h.2,s.symmetric _ _ h.1]⟩⟩
  loopless := ⟨fun x h => G.irrefl h.1⟩

noncomputable instance (s : Voltage G) : DecidableRel (graph G s).Adj := Classical.decRel _

def switched (s : Voltage G) (t : V → F2) : Voltage G where
  sign v w := s.sign v w+t v+t w
  symmetric v w h := by rw [s.symmetric _ _ h]; ring

private def switchEquiv (t : V → F2) : (V × F2) ≃ (V × F2) where
  toFun x := (x.1,x.2+t x.1)
  invFun x := (x.1,x.2+t x.1)
  left_inv x := by ext <;> simp [add_assoc,char2]
  right_inv x := by ext <;> simp [add_assoc,char2]

/-- Adding a vertex coboundary really gives an isomorphic graph. -/
def switchIso (s : Voltage G) (t : V → F2) :
    graph G s ≃g graph G (switched G s t) where
  toEquiv := switchEquiv t
  map_rel_iff' := by
    intro x y
    change (G.Adj x.1 y.1 ∧
      (x.2+t x.1)+(y.2+t y.1)=s.sign x.1 y.1+t x.1+t y.1) ↔ _
    have he : (x.2+t x.1)+(y.2+t y.1) = (x.2+y.2)+t x.1+t y.1 := by ring
    rw [he]
    simp only [add_left_inj,graph]

/-- The two sheets are exchanged by the nontrivial deck involution. -/
def flipIso (s : Voltage G) : graph G s ≃g graph G s where
  toEquiv := switchEquiv (fun _ => 1)
  map_rel_iff' := by
    intro x y
    change (G.Adj x.1 y.1 ∧ (x.2+1)+(y.2+1)=s.sign x.1 y.1) ↔ _
    have he : (x.2+1)+(y.2+1) = x.2+y.2 := by
      calc
        _ = x.2+y.2+(1+1) := by ring
        _ = _ := by rw [char2,add_zero]
    rw [he]
    rfl

/-- Projection has exactly one lifted neighbor over every base neighbor. -/
theorem cover (s : Voltage G) :
    CoverPullback.NeighborhoodCover G.Adj (graph G s).Adj Prod.fst where
  map_edge _ _ h := h.1
  neighbor_surjective x v hv := by
    refine ⟨(v,x.2+s.sign x.1 v),⟨hv,?_⟩,rfl⟩
    rw [← add_assoc,char2,zero_add]
  neighbor_injective x a b ha hb he := by
    apply Prod.ext he
    have hh : x.2+a.2=x.2+b.2 := by rw [ha.2,hb.2,he]
    exact add_left_cancel hh

private theorem reachable_lift (s : Voltage G) {v w : V} (h : G.Reachable v w)
    (a : F2) : ∃ b, (graph G s).Reachable (v,a) (w,b) := by
  obtain ⟨p⟩ := h
  induction p generalizing a with
  | nil => exact ⟨a,.rfl⟩
  | @cons u v w huv p ih =>
    obtain ⟨b,hb⟩ := ih (a+s.sign u v)
    refine ⟨b,SimpleGraph.Reachable.trans ?_ hb⟩
    exact SimpleGraph.Adj.reachable ⟨huv,by rw [← add_assoc,char2,zero_add]⟩

private theorem preconnected_of_root_fiber (s : Voltage G) (hG : G.Preconnected) (r : V)
    (hroot : (graph G s).Reachable (r,0) (r,1)) : (graph G s).Preconnected := by
  have hreach (v : V) (a : F2) : (graph G s).Reachable (r,0) (v,a) := by
    obtain ⟨b,hb⟩ := reachable_lift G s (hG r v) 0
    have hf := hb.map (flipIso G s).toHom
    have hcases : ∀ a b : F2, a=b ∨ a=b+1 := by decide +kernel
    rcases hcases a b with rfl | rfl
    · exact hb
    · exact hroot.trans hf
  intro x y
  exact (hreach x.1 x.2).symm.trans (hreach y.1 y.2)

private theorem coboundary_of_not_preconnected (s : Voltage G) (hG : G.Preconnected)
    (r : V) (hn : ¬ (graph G s).Preconnected) :
    ∃ t : V → F2, ∀ v w, G.Adj v w → s.sign v w=t v+t w := by
  classical
  have hroot : ¬ (graph G s).Reachable (r,0) (r,1) :=
    fun h => hn (preconnected_of_root_fiber G s hG r h)
  have huniq (v : V) (a b : F2) (ha : (graph G s).Reachable (r,0) (v,a))
      (hb : (graph G s).Reachable (r,0) (v,b)) : a=b := by
    by_contra he
    have hadd : ∀ a b : F2, a≠b → b=a+1 := by decide +kernel
    have hf := ha.map (flipIso G s).toHom
    have hpath : (graph G s).Reachable (r,1) (v,b) := by
      change (graph G s).Reachable (r,(0 : F2)+1) (v,a+1) at hf
      simpa only [zero_add,← hadd a b he] using hf
    exact hroot (hb.trans hpath.symm)
  choose t ht using fun v => reachable_lift G s (hG r v) 0
  refine ⟨t,?_⟩
  intro v w hvw
  have hedge : (graph G s).Adj (v,t v) (w,t v+s.sign v w) :=
    ⟨hvw,by rw [← add_assoc,char2,zero_add]⟩
  have he := huniq w (t v+s.sign v w) (t w) ((ht v).trans hedge.reachable) (ht w)
  have hsolve : ∀ a b c : F2, a+b=c → b=a+c := by decide +kernel
  exact hsolve _ _ _ he

/-- Over a connected base, a binary lift is connected precisely when its
voltage is not a vertex coboundary. No spanning-tree enumeration is used. -/
theorem preconnected_iff (s : Voltage G) (hG : G.Preconnected) (r : V) :
    (graph G s).Preconnected ↔
      ¬ ∃ t : V → F2, ∀ v w, G.Adj v w → s.sign v w=t v+t w := by
  constructor
  · intro h ⟨t,ht⟩
    have hinv {x y : V × F2} (hp : (graph G s).Reachable x y) :
        x.2+t x.1=y.2+t y.1 := by
      obtain ⟨p⟩ := hp
      induction p with
      | nil => rfl
      | @cons x y z hxy p ih =>
        have he : x.2+y.2=t x.1+t y.1 := hxy.2.trans (ht _ _ hxy.1)
        have hsolve : ∀ a b c d : F2, a+b=c+d → a+c=b+d := by decide +kernel
        exact (hsolve _ _ _ _ he).trans ih
    have he := hinv (h (r,0) (r,1))
    have hbad : (0 : F2) = 1 := add_right_cancel he
    exact (by decide : (0 : F2) ≠ 1) hbad
  · intro h
    by_contra hn
    exact h (coboundary_of_not_preconnected G s hG r hn)

end D5.S3.Combinatorics.Graph.StarForming.BinaryLift
