/- GID: D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CayleyColoring/CayleyCode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An anchor-based tree code preserves the target at each non-root coordinate. -/

import D5.S3.Combinatorics.Graph.CayleyColoring.RootedCoordinates
import Mathlib.Dynamics.PeriodicPts.Lemmas

section

namespace CayleyCore

open Function CayleyParent

universe u
variable {V : Type u}

private theorem enters_congr {C : Set V} {f g : V → V}
    (he : ∀ x ∉ C, f x = g x) (x : V) :
    (∃ n : Nat, (f^[n]) x ∈ C) ↔ ∃ n : Nat, (g^[n]) x ∈ C := by
  classical
  have aux {p q : V → V} (h : ∀ v ∉ C, p v = q v) (k : Nat) (z : V)
      (hz : (p^[k]) z ∈ C) : ∃ n : Nat, (q^[n]) z ∈ C := by
    induction k generalizing z with
    | zero => exact ⟨0,hz⟩
    | succ k ih =>
      by_cases hm : z ∈ C
      · exact ⟨0,hm⟩
      · rw [iterate_succ_apply] at hz
        obtain ⟨n,hn⟩ := ih (p z) hz
        exact ⟨n+1, by rw [iterate_succ_apply, ← h z hm]; exact hn⟩
  exact ⟨fun ⟨k,hk⟩ => aux he k x hk, fun ⟨k,hk⟩ => aux (fun v hv => (he v hv).symm) k x hk⟩

structure Frame (a : V) where
  core : Set V
  anchor_mem : a ∈ core
  outside : V → V
  fixedInside : ∀ x ∈ core, outside x = x
  enters : ∀ x, ∃ n : Nat, (outside^[n]) x ∈ core

namespace Frame

variable {a : V}

def anchor (F : Frame a) : F.core := ⟨a,F.anchor_mem⟩

private theorem ext_frame {F G : Frame a} (hc : F.core = G.core) (ho : F.outside = G.outside) : F = G := by
  cases F
  cases G
  cases hc
  cases ho
  rfl

noncomputable def ofFunction (f : V → V) (C : Set V) (ha : a ∈ C)
    (h : ∀ x, ∃ n : Nat, (f^[n]) x ∈ C) : Frame a := by
  classical
  let g (x : V) := if x ∈ C then x else f x
  have eq (x : V) (hx : x ∉ C) : g x = f x := ite_eq_right hx
  exact ⟨C,ha,g,fun x hx => ite_eq_left hx,fun x => (enters_congr eq x).mpr (h x)⟩

@[simp] theorem ofFunction_outside (f : V → V) (C : Set V) (ha : a ∈ C)
    (h : ∀ x, ∃ n : Nat, (f^[n]) x ∈ C) {x : V} (hx : x ∉ C) :
    (ofFunction f C ha h).outside x = f x := by
  classical
  exact ite_eq_right hx

noncomputable def patch (F : Frame a) (g : F.core → F.core) (x : V) : V := by
  classical
  exact if hx : x ∈ F.core then (g ⟨x,hx⟩).val else F.outside x

@[simp] theorem patch_in (F : Frame a) (g : F.core → F.core) (x : F.core) :
    F.patch g x.val = (g x).val := by
  classical
  simp [patch, x.prop]

@[simp] theorem patch_out (F : Frame a) (g : F.core → F.core) {x : V} (hx : x ∉ F.core) :
    F.patch g x = F.outside x := by
  classical
  simp [patch, hx]

private theorem patch_iter (F : Frame a) (g : F.core → F.core) (n : Nat) (x : F.core) :
    ((F.patch g)^[n]) x.val = ((g^[n]) x).val := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, iterate_succ_apply, patch_in, ih]

private theorem patch_enters (F : Frame a) (g : F.core → F.core) (x : V) :
    ∃ n : Nat, ((F.patch g)^[n]) x ∈ F.core :=
  (enters_congr (fun _ hx => F.patch_out g hx) x).mpr (F.enters x)

private theorem patch_recover (f : V → V) (C : Set V) (ha : a ∈ C)
    (enters : ∀ x, ∃ n : Nat, (f^[n]) x ∈ C) (closed : Set.MapsTo f C C) :
    (ofFunction f C ha enters).patch (fun x => ⟨f x.val, closed x.prop⟩) = f := by
  funext x
  by_cases hx : x ∈ C
  · exact (ofFunction f C ha enters).patch_in _ ⟨x,hx⟩
  · rw [patch_out _ _ hx, ofFunction_outside _ _ _ _ hx]

end Frame

private theorem eventually_periodic [Finite V] (f : V → V) (x : V) :
    ∃ n : Nat, (f^[n]) x ∈ periodicPts f := by
  have hn := not_injective_infinite_finite (fun n : Nat => (f^[n]) x)
  obtain ⟨m, n, he, hne⟩ : ∃ m n : Nat, (f^[m]) x = (f^[n]) x ∧ m ≠ n := by
    simpa [Injective] using hn
  have aux {i j : Nat} (hij : i < j) (e : (f^[i]) x = (f^[j]) x) :
      (f^[i]) x ∈ periodicPts f := by
    apply mk_mem_periodicPts (Nat.sub_pos_of_lt hij)
    change (f^[j-i]) ((f^[i]) x) = (f^[i]) x
    rw [← iterate_add_apply, Nat.sub_add_cancel hij.le, ← e]
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨m, aux h he⟩
  · exact ⟨n, aux h he.symm⟩

private theorem periodic_closed (f : V → V) : Set.MapsTo f (periodicPts f) (periodicPts f) := by
  intro x hx
  obtain ⟨n,hn,hp⟩ := mem_periodicPts.mp hx
  apply mk_mem_periodicPts hn
  change (f^[n]) (f x) = f x
  rw [← iterate_succ_apply, iterate_succ_apply', show (f^[n]) x = x from hp]

private theorem periodic_restrict [Finite V] (f : V → V) : Bijective
    (fun x : periodicPts f => (⟨f x.val, periodic_closed f x.prop⟩ : periodicPts f)) := by
  let g : periodicPts f → periodicPts f := fun x => ⟨f x.val, periodic_closed f x.prop⟩
  have hi (n : Nat) (x : periodicPts f) : ((g^[n]) x).val = (f^[n]) x.val := by
    induction n generalizing x with
    | zero => rfl
    | succ n ih => rw [iterate_succ_apply, iterate_succ_apply, ih]
  have hg : periodicPts g = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n, hn, hp⟩ := mem_periodicPts.mp x.prop
    exact mk_mem_periodicPts hn (Subtype.ext ((hi n x).trans hp))
  exact (Finite.injective_iff_bijective).mp ((injective_iff_periodicPts_eq_univ).mpr hg)

/-- A patched permutation makes precisely the vertices of its core periodic. -/
private theorem periodic_patch [Finite V] {a : V} (F : Frame a) (e : Equiv.Perm F.core) :
    periodicPts (F.patch e) = F.core := by
  ext x
  constructor
  · intro hx
    let f := F.patch e
    obtain ⟨n,hn,hp⟩ := mem_periodicPts.mp hx
    obtain ⟨m,hm⟩ := F.patch_enters e x
    let t := n*(m+1) - m
    have ht : t + m = n*(m+1) := by
      dsimp [t]
      have : m + 1 ≤ n * (m + 1) := by
        simpa using Nat.mul_le_mul_right (m+1) hn
      omega
    have hper : (f^[n*(m+1)]) x = x := hp.mul_const _
    change (f^[m]) x ∈ F.core at hm
    have hk : (f^[t]) ((f^[m]) x) ∈ F.core := by
      rw [F.patch_iter e t ⟨(f^[m]) x,hm⟩]
      exact Subtype.prop _
    rw [← iterate_add_apply, ht, hper] at hk
    exact hk
  · intro hx
    obtain ⟨n, hn, hp⟩ := mem_periodicPts.mp (e.injective.mem_periodicPts (⟨x,hx⟩ : F.core))
    exact mk_mem_periodicPts hn ((F.patch_iter e n ⟨x,hx⟩).trans (congrArg Subtype.val hp))

abbrev Anchored (a : V) := {f : V → V // f a = a}
abbrev FixedPerm {a : V} (F : Frame a) := {e : Equiv.Perm F.core // e F.anchor = F.anchor}

private noncomputable def cyclicSplit [Finite V] (a : V) (f : Anchored a) :
    Σ F : Frame a, FixedPerm F := by
  let F := Frame.ofFunction f.val (periodicPts f.val)
    (mk_mem_periodicPts Nat.one_pos f.prop) (eventually_periodic f.val)
  let e : Equiv.Perm F.core := Equiv.ofBijective _ (periodic_restrict f.val)
  exact ⟨F, ⟨e, Subtype.ext f.prop⟩⟩

private noncomputable def cyclicJoin {a : V} (d : Σ F : Frame a, FixedPerm F) : Anchored a :=
  ⟨d.1.patch d.2.val, (d.1.patch_in d.2.val d.1.anchor).trans (congrArg Subtype.val d.2.prop)⟩

private theorem cyclic_join_split [Finite V] (a : V) (f : Anchored a) :
    cyclicJoin (cyclicSplit a f) = f := by
  apply Subtype.ext
  exact Frame.patch_recover f.val (periodicPts f.val)
    (mk_mem_periodicPts Nat.one_pos f.prop) (eventually_periodic f.val) (periodic_closed f.val)

private theorem cyclic_split_join [Finite V] {a : V} (d : Σ F : Frame a, FixedPerm F) :
    cyclicSplit a (cyclicJoin d) = d := by
  rcases d with ⟨F,e⟩
  have hc : (cyclicSplit a (cyclicJoin ⟨F,e⟩)).1.core = F.core := periodic_patch F e.val
  have h₁ : (cyclicSplit a (cyclicJoin ⟨F,e⟩)).1 = F := by
    apply Frame.ext_frame hc
    funext x
    by_cases hx : x ∈ F.core
    · exact ((cyclicSplit a (cyclicJoin ⟨F,e⟩)).1.fixedInside x (hc.symm ▸ hx)).trans
        (F.fixedInside x hx).symm
    · have hxx : x ∉ (cyclicSplit a (cyclicJoin ⟨F,e⟩)).1.core := hc.symm ▸ hx
      let g := cyclicJoin (⟨F,e⟩ : Σ F : Frame a, FixedPerm F)
      exact (Frame.ofFunction_outside g.val (periodicPts g.val) (mk_mem_periodicPts Nat.one_pos g.prop)
        (eventually_periodic g.val) hxx).trans (F.patch_out e.val hx)
  let d := cyclicSplit a (cyclicJoin ⟨F,e⟩)
  change d = ⟨F,e⟩
  change d.1 = F at h₁
  have spec (x : d.1.core) : (d.2.val x).val = F.patch e.val x.val := rfl
  rcases d with ⟨F',e'⟩
  cases h₁
  apply congrArg (Sigma.mk F')
  apply Subtype.ext
  ext x
  exact (spec x).trans (F'.patch_in e.val x)

private noncomputable def cyclicEquiv [Finite V] (a : V) :
    Anchored a ≃ Σ F : Frame a, FixedPerm F where
  toFun := cyclicSplit a
  invFun := cyclicJoin
  left_inv := cyclic_join_split a
  right_inv := cyclic_split_join

end CayleyCore

end

section

namespace CayleyCore

open Function CayleyParent

universe u
variable {V : Type u} {a : V}

private theorem depth_iterate {r : V} (f : RootMap r) (x : V) (n : Nat) :
    depth r f ((f.val^[n]) x) = depth r f x - n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply, ih]
    by_cases hx : x = r
    · subst x
      rw [f.prop.1, (depth_zero r f r).mpr rfl]
      simp
    · have hs := depth_step r f hx
      omega

def orbitCore (a : V) {r : V} (f : RootMap r) : Set V := {x | Hits f.val a x}

private theorem orbit_mem_root (a : V) {r : V} (f : RootMap r) :
    r ∈ orbitCore a f := f.prop.2 a

private theorem orbit_closed (a : V) {r : V} (f : RootMap r) :
    Set.MapsTo f.val (orbitCore a f) (orbitCore a f) :=
  fun x hx => hits_trans hx (hits_step f.val x)

private theorem enters_orbit (a : V) {r : V} (f : RootMap r) (x : V) :
    ∃ n, (f.val^[n]) x ∈ orbitCore a f := by
  obtain ⟨n,hn⟩ := f.prop.2 x
  exact ⟨n, hn.symm ▸ orbit_mem_root a f⟩

/-- The actual anchor-to-root orbit is enumerated without repetitions, ending at the root. -/
noncomputable def orbitEquiv (a : V) {r : V} (f : RootMap r) :
    Fin (depth r f a + 1) ≃ orbitCore a f := by
  apply Equiv.ofBijective (fun i => ⟨(f.val^[i.val]) a, i.val, rfl⟩)
  constructor
  · intro i j he
    have h := congrArg (fun x : orbitCore a f => depth r f x.val) he
    change depth r f ((f.val^[i.val]) a) = depth r f ((f.val^[j.val]) a) at h
    rw [depth_iterate, depth_iterate] at h
    exact Fin.ext (by have := i.isLt; have := j.isLt; omega)
  · rintro ⟨x,n,hn⟩
    by_cases h : n ≤ depth r f a
    · exact ⟨⟨n, by omega⟩, Subtype.ext hn⟩
    · have hz : depth r f ((f.val^[n]) a) = 0 := by rw [depth_iterate]; omega
      exact ⟨Fin.last _, Subtype.ext ((depth_hits r f a).trans
        (((depth_zero r f _).mp hz).symm.trans hn))⟩

def successor (m : Nat) (i : Fin (m + 1)) : Fin (m + 1) :=
  ⟨min (i.val+1) m, by omega⟩

private theorem successor_iterate (m n : Nat) (i : Fin (m + 1)) :
    ((successor m)^[n] i).val = min (i.val + n) m := by
  induction n with
  | zero =>
    change i.val = min (i.val + 0) m
    have hi := i.isLt
    omega
  | succ n ih =>
    rw [iterate_succ_apply']
    change min (((successor m)^[n] i).val + 1) m = _
    rw [ih]
    omega

@[simp] theorem successor_last (m : Nat) : successor m (Fin.last m) = Fin.last m := by
  apply Fin.ext
  change min (m+1) m = m
  omega

abbrev PathData (F : Frame a) :=
  Σ m : Nat, {e : Fin (m + 1) ≃ F.core // e 0 = F.anchor}

def pathSelf {F : Frame a} (p : PathData F) (x : F.core) : F.core :=
  p.2.val (successor p.1 (p.2.val.symm x))

def pathRoot {F : Frame a} (p : PathData F) : F.core := p.2.val (Fin.last _)

private theorem pathSelf_equivariant {F : Frame a} (p : PathData F) (i : Fin (p.1 + 1)) :
    pathSelf p (p.2.val i) = p.2.val (successor p.1 i) := by
  simp [pathSelf]

private theorem pathSelf_iterate {F : Frame a} (p : PathData F) (n : Nat) (i : Fin (p.1 + 1)) :
    ((pathSelf p)^[n]) (p.2.val i) = p.2.val ((successor p.1)^[n] i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih, pathSelf_equivariant]

private theorem pathSelf_hits {F : Frame a} (p : PathData F) (x : F.core) :
    Hits (pathSelf p) x (pathRoot p) := by
  let i := p.2.val.symm x
  refine ⟨p.1, ?_⟩
  rw [show x = p.2.val i from (p.2.val.apply_symm_apply x).symm, pathSelf_iterate]
  apply congrArg p.2.val
  apply Fin.ext
  rw [successor_iterate]
  change min (i.val + p.1) p.1 = p.1
  omega

noncomputable def pathJoin (d : Σ F : Frame a, PathData F) : Σ r : V, RootMap r := by
  obtain ⟨F,p⟩ := d
  let r := pathRoot p
  let f := F.patch (pathSelf p)
  refine ⟨r.val, f, ?_, ?_⟩
  · change F.patch (pathSelf p) (pathRoot p).val = (pathRoot p).val
    rw [F.patch_in]
    change (pathSelf p (p.2.val (Fin.last _))).val = _
    rw [pathSelf_equivariant, successor_last]
    rfl
  · intro x
    obtain ⟨n,hn⟩ := F.patch_enters (pathSelf p) x
    let y : F.core := ⟨(f^[n]) x, hn⟩
    obtain ⟨m,hm⟩ := pathSelf_hits p y
    refine hits_trans (y := y.val) ⟨n,rfl⟩ ⟨m, ?_⟩
    rw [F.patch_iter (pathSelf p) m y, hm]

noncomputable def pathSplit (a : V) (d : Σ r : V, RootMap r) :
    Σ F : Frame a, PathData F := by
  let F := Frame.ofFunction d.2.val (orbitCore a d.2) (hits_refl _ _) (enters_orbit a d.2)
  exact ⟨F, depth d.1 d.2 a, orbitEquiv a d.2, rfl⟩

private theorem pathJoin_root (F : Frame a) (p : PathData F) :
    (pathJoin ⟨F,p⟩).1 = (pathRoot p).val := rfl

private theorem pathJoin_function (F : Frame a) (p : PathData F) :
    (pathJoin ⟨F,p⟩).2.val = F.patch (pathSelf p) := rfl

private theorem pathJoin_iterate (F : Frame a) (p : PathData F) (n : Nat) :
    (((pathJoin ⟨F,p⟩).2.val)^[n]) a =
      (p.2.val ⟨min n p.1, by omega⟩).val := by
  rw [pathJoin_function]
  have h : a = (p.2.val 0).val := by rw [p.2.prop]; rfl
  calc
    _ = ((F.patch (pathSelf p))^[n]) (p.2.val 0).val := congrArg _ h
    _ = _ := by
      rw [F.patch_iter, pathSelf_iterate]
      apply congrArg (fun x => (p.2.val x).val)
      apply Fin.ext
      rw [successor_iterate]
      simp

private theorem pathJoin_depth (F : Frame a) (p : PathData F) :
    depth (pathJoin ⟨F,p⟩).1 (pathJoin ⟨F,p⟩).2 a = p.1 := by
  apply Nat.le_antisymm
  · apply depth_min
    rw [pathJoin_iterate, pathJoin_root]
    congr 2
    exact Fin.ext (by simp)
  · have h := depth_hits (pathJoin ⟨F,p⟩).1 (pathJoin ⟨F,p⟩).2 a
    change (((pathJoin ⟨F,p⟩).2.val)^[depth (pathJoin ⟨F,p⟩).1 (pathJoin ⟨F,p⟩).2 a]) a =
      (p.2.val (Fin.last p.1)).val at h
    rw [pathJoin_iterate] at h
    have he := p.2.val.injective (Subtype.ext h)
    have hv := congrArg Fin.val he
    change min (depth (pathJoin ⟨F,p⟩).1 (pathJoin ⟨F,p⟩).2 a) p.1 = p.1 at hv
    omega

private theorem pathJoin_core (F : Frame a) (p : PathData F) :
    orbitCore a (pathJoin ⟨F,p⟩).2 = F.core := by
  ext x
  constructor
  · rintro ⟨n,hn⟩
    rw [pathJoin_iterate] at hn
    exact hn ▸ (p.2.val _).prop
  · intro hx
    let i := p.2.val.symm ⟨x,hx⟩
    refine ⟨i.val, ?_⟩
    rw [pathJoin_iterate]
    have eq : (⟨min i.val p.1, by omega⟩ : Fin (p.1+1)) = i := by
      apply Fin.ext
      have := i.isLt
      simp [Nat.min_eq_left (by omega : i.val ≤ p.1)]
    rw [eq, Equiv.apply_symm_apply]

private theorem pathSplit_join (d : Σ F : Frame a, PathData F) :
    pathSplit a (pathJoin d) = d := by
  rcases d with ⟨F,p⟩
  let d := pathSplit a (pathJoin ⟨F,p⟩)
  have hc : d.1.core = F.core := pathJoin_core F p
  have hf : d.1 = F := by
    apply Frame.ext_frame hc
    funext x
    by_cases hx : x ∈ F.core
    · exact (d.1.fixedInside x (hc.symm ▸ hx)).trans (F.fixedInside x hx).symm
    · have hxx : x ∉ d.1.core := hc.symm ▸ hx
      let g := (pathJoin ⟨F,p⟩).2
      exact (Frame.ofFunction_outside g.val (orbitCore a g) (hits_refl _ _)
        (enters_orbit a g) hxx).trans (F.patch_out _ hx)
  have hn : d.2.1 = p.1 := pathJoin_depth F p
  have he (i : Fin (d.2.1+1)) :
      (d.2.2.val i).val = (p.2.val (Fin.cast (congrArg (·+1) hn) i)).val := by
    change ((((pathJoin ⟨F,p⟩).2.val)^[i.val]) a) = _
    rw [pathJoin_iterate]
    apply congrArg (fun j => (p.2.val j).val)
    apply Fin.ext
    change min i.val p.1 = i.val
    have hlt : i.val < p.1+1 := hn ▸ i.isLt
    omega
  change d = ⟨F,p⟩
  rcases d with ⟨F',m,e⟩
  rcases p with ⟨n,t⟩
  dsimp only at hf hn he
  cases hf
  cases hn
  apply congrArg (Sigma.mk F)
  apply congrArg (Sigma.mk m)
  apply Subtype.ext
  ext i
  exact he i

private theorem pathJoin_split (a : V) (d : Σ r : V, RootMap r) :
    pathJoin (pathSplit a d) = d := by
  rcases d with ⟨r,f⟩
  let F := (pathSplit a ⟨r,f⟩).1
  let p := (pathSplit a ⟨r,f⟩).2
  have hr : (pathJoin ⟨F,p⟩).1 = r := depth_hits r f a
  let ds := pathJoin ⟨F,p⟩
  change ds = ⟨r,f⟩
  change ds.1 = r at hr
  have hfun : ds.2.val = f.val := by
    change F.patch (pathSelf p) = _
    rw [← Frame.patch_recover f.val (orbitCore a f) (hits_refl _ _) (enters_orbit a f)
      (orbit_closed a f)]
    apply congrArg F.patch
    funext x
    apply Subtype.ext
    let i := p.2.val.symm x
    have hi : x = p.2.val i := (p.2.val.apply_symm_apply x).symm
    conv_lhs => rw [hi, pathSelf_equivariant]
    change ((p.2.val (successor p.1 i)) : V) = f.val x.val
    rw [hi]
    change (f.val^[min (i.val+1) (depth r f a)]) a = f.val ((f.val^[i.val]) a)
    by_cases ht : i.val < depth r f a
    · rw [Nat.min_eq_left (by omega), iterate_succ_apply']
    · have htop : i.val = depth r f a := by have := i.isLt; change i.val < depth r f a+1 at this; omega
      rw [htop, Nat.min_eq_right (by omega), depth_hits, f.prop.1]
  rcases ds with ⟨r',g⟩
  cases hr
  apply congrArg (Sigma.mk r')
  exact Subtype.ext hfun

private noncomputable def pathEquiv (a : V) :
    (Σ r : V, RootMap r) ≃ Σ F : Frame a, PathData F where
  toFun := pathSplit a
  invFun := pathJoin
  left_inv := pathJoin_split a
  right_inv := pathSplit_join

end CayleyCore

end

section

namespace CayleyCore

open Function CayleyParent CayleyColors

universe u
variable {V : Type u} {a : V}

private theorem card_core_pos [Finite V] (F : Frame a) : 0 < Nat.card F.core := by
  let : Nonempty F.core := ⟨F.anchor⟩
  exact Nat.card_pos

private noncomputable def baseOrder [Finite V] (F : Frame a) : PathData F := by
  classical
  let m := Nat.card F.core - 1
  have h : m + 1 = Nat.card F.core := Nat.sub_add_cancel (card_core_pos F)
  let e : Fin (m + 1) ≃ F.core :=
    (Fin.castOrderIso h).toEquiv.trans (Nat.equivFinOfCardPos (card_core_pos F).ne').symm
  let e' := (Equiv.swap 0 (e.symm F.anchor)).trans e
  exact ⟨m, e', by simp [e']⟩

private theorem path_length_unique {F : Frame a} (p q : PathData F) : p.1 = q.1 := by
  have hp := Nat.card_congr p.2.val
  have hq := Nat.card_congr q.2.val
  simp only [Nat.card_fin] at hp hq
  omega

abbrev OrdersOfLength (F : Frame a) (m : Nat) :=
  {e : Fin (m+1) ≃ F.core // e 0 = F.anchor}

private noncomputable def pathAtLength {F : Frame a} (m : Nat) (h : ∀ p : PathData F, p.1 = m) :
    PathData F ≃ OrdersOfLength F m where
  toFun p :=
    ⟨(Fin.castOrderIso (congrArg (·+1) (h p).symm)).toEquiv.trans p.2.val, p.2.prop⟩
  invFun e := ⟨m,e⟩
  left_inv p := by
    rcases p with ⟨j,e⟩
    have h' : j = m := h ⟨j,e⟩
    subst j
    apply congrArg (Sigma.mk m)
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change e.val (Fin.cast (congrArg (·+1) (h ⟨m,e⟩).symm) x) = e.val x
    simp
  right_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change e.val (Fin.cast (congrArg (·+1) (h ⟨m,e⟩).symm) x) = e.val x
    simp

private noncomputable def orderByPerm {F : Frame a} {m : Nat} (base : OrdersOfLength F m) :
    FixedPerm F ≃ OrdersOfLength F m where
  toFun e := ⟨base.val.trans e.val, by simpa only [Equiv.trans_apply, base.prop] using e.prop⟩
  invFun e := ⟨base.val.symm.trans e.val, by
    change e.val (base.val.symm F.anchor) = F.anchor
    have hz : base.val.symm F.anchor = 0 :=
      (congrArg base.val.symm base.prop).symm.trans (base.val.symm_apply_apply 0)
    rw [hz]
    exact e.prop⟩
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change e.val (base.val (base.val.symm x)) = e.val x
    rw [Equiv.apply_symm_apply]
  right_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change e.val (base.val.symm (base.val x)) = e.val x
    rw [Equiv.symm_apply_apply]

/-- A cycle permutation and a linear traversal on the same core carry the same information.
The choice of the anchor-first enumeration fixes the equivalence once for that core. -/
private noncomputable def permPathEquiv [Finite V] (F : Frame a) : FixedPerm F ≃ PathData F :=
  let base := baseOrder F
  (orderByPerm base.2).trans (pathAtLength base.1 (fun p => path_length_unique p base)).symm

abbrev Outside (F : Frame a) := {x : V // x ∉ F.core}
abbrev CoreAway {F : Frame a} (p : F.core) := {x : F.core // x ≠ p}

def fromOutside {F : Frame a} (p : F.core) (x : Outside F) : Away p.val :=
  ⟨x.val, fun he => x.prop (he.symm ▸ p.prop)⟩

def fromInside {F : Frame a} (p : F.core) (x : CoreAway p) : Away p.val :=
  ⟨x.val.val, fun he => x.prop (Subtype.ext he)⟩

private noncomputable def splitAway (F : Frame a) (p : F.core) :
    Outside F ⊕ CoreAway p ≃ Away p.val := by
  classical
  let f : Outside F ⊕ CoreAway p → Away p.val := Sum.elim (fromOutside p) (fromInside p)
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (Subtype.ext (congrArg (fun t : Away p.val => t.val) h))
    · exact (x.prop (show x.val ∈ F.core from (congrArg (fun t : Away p.val => t.val) h).symm ▸ y.val.prop)).elim
    · exact (y.prop (show y.val ∈ F.core from congrArg (fun t : Away p.val => t.val) h ▸ x.val.prop)).elim
    · exact congrArg Sum.inr (Subtype.ext (Subtype.ext (congrArg (fun t : Away p.val => t.val) h)))
  · intro x
    by_cases hx : x.val ∈ F.core
    · exact ⟨Sum.inr ⟨⟨x.val,hx⟩,fun he => x.prop (congrArg Subtype.val he)⟩, rfl⟩
    · exact ⟨Sum.inl ⟨x.val,hx⟩,rfl⟩

private noncomputable def cycleTarget {F : Frame a} (e : FixedPerm F) :
    CoreAway F.anchor ≃ CoreAway F.anchor :=
  e.val.subtypeEquiv fun x => ⟨fun hn h => hn (e.val.injective (h.trans e.prop.symm)),
    fun hn h => hn (h ▸ e.prop)⟩

noncomputable def indexBeforeLast (m : Nat) : Fin m ≃ {i : Fin (m+1) // i ≠ Fin.last m} := by
  let f (i : Fin m) : {i : Fin (m+1) // i ≠ Fin.last m} :=
    ⟨i.castSucc, fun he => by have := i.isLt; have ht := congrArg Fin.val he; change i.val = m at ht; omega⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    exact Fin.ext (congrArg (fun v => v.val.val) h)
  · intro i
    have hn : i.val.val ≠ m := fun h => i.prop (Fin.ext h)
    have hi := i.val.isLt
    exact ⟨⟨i.val.val, by omega⟩, rfl⟩

private noncomputable def indexAfterFirst (m : Nat) : Fin m ≃ {i : Fin (m+1) // i ≠ 0} := by
  let f (i : Fin m) : {i : Fin (m+1) // i ≠ 0} :=
    ⟨i.succ, Fin.succ_ne_zero _⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    exact Fin.succ_injective _ (congrArg Subtype.val h)
  · rintro ⟨i,hi⟩
    cases i using Fin.cases with
    | zero => exact (hi rfl).elim
    | succ j => exact ⟨j,rfl⟩

private theorem index_successor (m : Nat) (i : {i : Fin (m+1) // i ≠ Fin.last m}) :
    (indexAfterFirst m ((indexBeforeLast m).symm i)).val = successor m i.val := by
  let j := (indexBeforeLast m).symm i
  have hj : j.castSucc = i.val := congrArg Subtype.val ((indexBeforeLast m).apply_symm_apply i)
  change j.succ = successor m i.val
  rw [← hj]
  apply Fin.ext
  change j.val + 1 = min (j.val + 1) m
  have := j.isLt
  omega

private noncomputable def chainTarget {F : Frame a} (p : PathData F) :
    CoreAway (pathRoot p) ≃ CoreAway F.anchor :=
  (p.2.val.symm.subtypeEquiv fun x => by
    change x ≠ p.2.val (Fin.last p.1) ↔ p.2.val.symm x ≠ Fin.last p.1
    simp only [ne_eq, Equiv.symm_apply_eq]).trans <|
    (indexBeforeLast p.1).symm.trans <| (indexAfterFirst p.1).trans <|
      p.2.val.subtypeEquiv fun x => by
        exact ⟨fun hn he => hn (p.2.val.injective (he.trans p.2.prop.symm)),
          fun hn he => hn ((congrArg p.2.val he).trans p.2.prop)⟩

private theorem chainTarget_value {F : Frame a} (p : PathData F) (x : CoreAway (pathRoot p)) :
    (chainTarget p x).val = pathSelf p x.val := by
  change p.2.val _ = p.2.val _
  apply congrArg p.2.val
  exact index_successor p.1 ⟨p.2.val.symm x.val,
    fun h => x.prop (by simpa [pathRoot] using congrArg p.2.val h)⟩

private noncomputable def matchedCoordinates {F : Frame a} (e : FixedPerm F) (p : PathData F) :
    Away a ≃ Away (pathRoot p).val :=
  (splitAway F F.anchor).symm.trans
    ((Equiv.sumCongr (Equiv.refl _) ((cycleTarget e).trans (chainTarget p).symm)).trans
      (splitAway F (pathRoot p)))

/-- A coordinate bijection preserves every individual target, including multiplicities. -/
private theorem matchedTargets {F : Frame a} (e : FixedPerm F) (p : PathData F) (x : Away a) :
    (F.patch (pathSelf p)) (matchedCoordinates e p x).val = (F.patch e.val) x.val := by
  obtain ⟨s,rfl⟩ := (splitAway F F.anchor).surjective x
  rcases s with s | s
  · change F.patch (pathSelf p) (((splitAway F F.anchor).symm) ((splitAway F F.anchor) (Sum.inl s)) |>
      (Equiv.sumCongr (Equiv.refl _) ((cycleTarget e).trans (chainTarget p).symm)) |>
      (splitAway F (pathRoot p)) |>.val) = F.patch e.val s.val
    rw [Equiv.symm_apply_apply]
    change F.patch (pathSelf p) s.val = F.patch e.val s.val
    rw [F.patch_out _ s.prop, F.patch_out _ s.prop]
  · change F.patch (pathSelf p) (((splitAway F F.anchor).symm) ((splitAway F F.anchor) (Sum.inr s)) |>
      (Equiv.sumCongr (Equiv.refl _) ((cycleTarget e).trans (chainTarget p).symm)) |>
      (splitAway F (pathRoot p)) |>.val) = F.patch e.val s.val.val
    rw [Equiv.symm_apply_apply]
    let t := (chainTarget p).symm (cycleTarget e s)
    change F.patch (pathSelf p) t.val.val = F.patch e.val s.val.val
    rw [F.patch_in, F.patch_in, ← chainTarget_value p t]
    exact congrArg (fun x : CoreAway F.anchor => x.val.val)
      ((chainTarget p).apply_symm_apply (cycleTarget e s))

private noncomputable def extendAnchor (a : V) : (Away a → V) ≃ Anchored a := by
  classical
  refine ⟨fun f => ⟨fun v => if h : v = a then a else f ⟨v,h⟩, by simp⟩,
    fun f v => f.val v.val, ?_, ?_⟩
  · intro f
    funext x
    simp [x.prop]
  · intro f
    apply Subtype.ext
    funext v
    by_cases h : v = a
    · subst v
      simpa using f.prop.symm
    · simp [h]

private noncomputable def nativeRootedEquiv : (Σ _ : V, CayleyProbe.Tree V) ≃
    (Σ r : V, RootMap r) :=
  Equiv.sigmaCongrRight rootMapEquiv

noncomputable def rootedCode [Finite V] (a : V) :
    (Away a → V) ≃ (Σ _ : V, CayleyProbe.Tree V) :=
  (extendAnchor a).trans <| (cyclicEquiv a).trans <|
    (Equiv.sigmaCongrRight permPathEquiv).trans <| (pathEquiv a).symm.trans nativeRootedEquiv.symm

noncomputable def codeCoordinates [Finite V] (a : V) (f : Away a → V) :
    Away a ≃ Away ((rootedCode a) f).1 :=
  let d := cyclicEquiv a (extendAnchor a f)
  matchedCoordinates d.2 (permPathEquiv d.1 d.2)

theorem rootedCode_targets [Finite V] (a : V) (f : Away a → V) (i : Away a) :
    parent ((rootedCode a) f).2 ((rootedCode a) f).1 (codeCoordinates a f i) = f i := by
  let d := cyclicEquiv a (extendAnchor a f)
  let p := permPathEquiv d.1 d.2
  have h := congrArg Subtype.val ((cyclicEquiv a).symm_apply_apply (extendAnchor a f))
  have hx := congrFun h i.val
  change d.1.patch d.2.val i.val = (extendAnchor a f).val i.val at hx
  rw [← fromTree_child]
  change fromTree (toTree (pathJoin ⟨d.1,p⟩).1 (pathJoin ⟨d.1,p⟩).2)
    (pathJoin ⟨d.1,p⟩).1 (matchedCoordinates d.2 p i).val = f i
  have ht := congrArg Subtype.val ((rootMapEquiv (pathJoin ⟨d.1,p⟩).1).apply_symm_apply
    (pathJoin ⟨d.1,p⟩).2)
  change fromTree (toTree (pathJoin ⟨d.1,p⟩).1 (pathJoin ⟨d.1,p⟩).2)
    (pathJoin ⟨d.1,p⟩).1 = (pathJoin ⟨d.1,p⟩).2.val at ht
  rw [ht, pathJoin_function, matchedTargets, hx]
  exact congrFun ((extendAnchor a).symm_apply_apply f) i

end CayleyCore

end
