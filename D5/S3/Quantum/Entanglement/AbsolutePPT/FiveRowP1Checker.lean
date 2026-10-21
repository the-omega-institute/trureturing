/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Checker
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Checker
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N25A.accepted
   digest: Rational forest checker and real-domain soundness using complete closed split halves and original scalar hypotheses. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Analytic
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Caps
import D5.S0.Certificates.BoxCover.FiniteSublevelCover
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
open D5.S0.Certificates.BoxCover.QuadraticCorner
open D5.S0.Certificates.BoxCover.FiniteSublevelCover
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Algebra
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Caps
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Analytic

inductive Mode where
  | leftEnd | rightEnd | vertex
  deriving DecidableEq, Inhabited
inductive Rule where
  | localRegion
  | infeasible (index : Fin 17)
  | boxTail
  | capInfeasible (m b : ℚ)
  | bound (mode : Mode) (index : Fin 9) (m b : ℚ)
  | split (axis : Fin 4) (cut : ℚ) (left right : Nat)
  deriving Inhabited
structure Node where
  box : Box 4
  rule : Rule
instance : Inhabited Node := ⟨⟨fun _ => (0,0), .localRegion⟩⟩

def node (a : Array Node) (i : Nat) : Node := a[i]?.getD default

def leftBox (box : Box 4) (axis : Fin 4) (cut : ℚ) : Box 4 :=
  fun i => if i=axis then ((box i).1,cut) else box i
def rightBox (box : Box 4) (axis : Fin 4) (cut : ℚ) : Box 4 :=
  fun i => if i=axis then (cut,(box i).2) else box i

def rootBox : Box 4 := ![(0,1/2),(0,5),(0,5),(0,3)]
def base (N : Nat) : Mode → P
  | .leftEnd => target N 10
  | .rightEnd => target N ((N : ℚ)-15)
  | .vertex => vertex N

def upperCap (branch : Bool) (box : Box 4) (index : Fin 9) (m b : ℚ) : P :=
  if hi : index.val < 8 then fixed ⟨index.val,hi⟩ else cap branch box m b

def modeOK (N : Nat) (box : Box 4) : Mode → Prop
  | .leftEnd => 0 ≤ lower (toPoly (derivative N 10)) box
  | .rightEnd => upper (toPoly (derivative N ((N : ℚ)-15))) box ≤ 0
  | .vertex => True
instance (N : Nat) (box : Box 4) (m : Mode) : Decidable (modeOK N box m) := by
  cases m <;> unfold modeOK <;> infer_instance

def capOK (branch : Bool) (box : Box 4) (m b : ℚ) : Prop :=
  branch=true ∨ chordOK box m b
instance (branch : Bool) (box : Box 4) (m b : ℚ) : Decidable (capOK branch box m b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Every local check is rational. Infeasibility is strict; target bounds are
closed. Both split children must be earlier and equal the entire closed halves. -/
def NodeOK (N : Nat) (branch : Bool) (a : Array Node) (i : Nat) : Prop :=
  let b := (node a i).box
  match (node a i).rule with
  | .localRegion => (b 0).2 ≤ 1/10 ∧ (b 2).2 ≤ 1/4
  | .infeasible k => upper (toPoly (necessary branch k)) b < 0
  | .boxTail => max 2 (2*(b 2).2/3) < (b 3).1
  | .capInfeasible m c => capOK branch b m c ∧
      upper (toPoly (addP (cap branch b m c) (scaleP (-1) amin))) b < 0
  | .bound mode k m c => (k.val < 8 ∨ capOK branch b m c) ∧ modeOK N b mode ∧
      0 ≤ lower (toPoly (addP (base N mode) (scaleP (-1) (upperCap branch b k m c)))) b
  | .split axis cut l r => l < i ∧ r < i ∧
      (b axis).1 < cut ∧ cut < (b axis).2 ∧
      (∀ k, (node a l).box k=leftBox b axis cut k) ∧
      (∀ k, (node a r).box k=rightBox b axis cut k)
instance (N : Nat) (branch : Bool) (a : Array Node) (i : Nat) :
    Decidable (NodeOK N branch a i) := by
  unfold NodeOK
  split <;> infer_instance

/-- Postorder traversal is compared to the full list of indices. Thus there
can be no unused, duplicate or omitted record in an accepted data instance.
Fuel failure returns an empty list, which cannot cover a nonempty root. -/
def walk (a : Array Node) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel+1, i => match (node a i).rule with
    | .split _ _ l r => walk a fuel l ++ walk a fuel r ++ [i]
    | _ => [i]

def check (N : Nat) (branch : Bool) (a : Array Node) : Bool := decide
  (0 < a.size ∧ (∀ i : Fin a.size, NodeOK N branch a i.val) ∧
   walk a a.size (a.size-1)=List.range a.size ∧
   ∀ k, (node a (a.size-1)).box k=rootBox k)

private theorem split_retains (b : Box 4) (k : Fin 4) (cut : ℚ) (x : X)
    (hx : Inside b x) : Inside (leftBox b k cut) x ∨ Inside (rightBox b k cut) x := by
  by_cases ht : x k ≤ (cut : ℝ)
  · left; intro i; by_cases hi : i=k
    · subst i; simpa [leftBox] using And.intro (hx k).1 ht
    · simpa [leftBox, hi] using hx i
  · right; intro i; by_cases hi : i=k
    · subst i; simpa [rightBox] using And.intro (le_of_not_ge ht) (hx k).2
    · simpa [rightBox, hi] using hx i

private theorem base_sound (N : Nat) (hN : 25 ≤ N) (box : Box 4)
    (r H D q a j : ℝ) (h : Hyp r H D q a)
    (hx : Inside box ![r,H,D,q]) (hj : 10 ≤ j) (hj' : j ≤ (N : ℝ)-15)
    (mode : Mode) (hm : modeOK N box mode) :
    ev (base N mode) ![r,H,D,q]-a ≤ gap N j r H D q a := by
  have hnr : (25 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have ht : 0 ≤ theta N := by dsimp [theta]; positivity
  cases mode with
  | leftEnd =>
      have he := (encloses (toPoly (derivative N 10)) box ![r,H,D,q] hx).1
      have hm' : (0 : ℝ) ≤ lower (toPoly (derivative N 10)) box :=
        (Rat.cast_nonneg (K := ℝ)).mpr hm
      have hd : 0 ≤ 2*theta N*(mass N 10 r H D)-(2+r) := by
        have hh : 0 ≤ ev (derivative N 10) ![r,H,D,q] := hm'.trans he
        simpa [derivative_value] using hh
      change ev (target N 10) ![r,H,D,q]-a ≤ _
      rw [target_value]
      simpa using target_left N j r H D q a ht h.r0 hj hd
  | rightEnd =>
      have he := (encloses (toPoly (derivative N ((N : ℚ)-15))) box ![r,H,D,q] hx).2
      have hm' : (upper (toPoly (derivative N ((N : ℚ)-15))) box : ℝ) ≤ 0 :=
        (Rat.cast_nonpos (K := ℝ)).mpr hm
      have hd : 2*theta N*(mass N ((N : ℝ)-15) r H D)-(2+r) ≤ 0 := by
        have hh := he.trans hm'
        change ev (derivative N ((N : ℚ)-15)) ![r,H,D,q] ≤ 0 at hh
        rw [derivative_value] at hh
        simpa using hh
      have hh := target_right N j r H D q a ht h.r0 hj' hd
      change ev (target N ((N : ℚ)-15)) ![r,H,D,q]-a ≤ _
      rw [target_value]
      simpa using hh
  | vertex => exact vertex_value N j r H D q a hN

private theorem leaf_sound (N : Nat) (hN : 25 ≤ N) (hN' : N ≤ 90)
    (branch : Bool) (arr : Array Node) (i : Nat)
    (hnode : NodeOK N branch arr i)
    (r H D q a j : ℝ) (h : Hyp r H D q a) (hb : Branch branch r H D q a)
    (hx : Inside (node arr i).box ![r,H,D,q]) (hj : 10 ≤ j) (hj' : j ≤ (N : ℝ)-15) :
    match (node arr i).rule with
    | .split _ _ _ _ => True
    | _ => 0 ≤ gap N j r H D q a := by
  let b := (node arr i).box
  have hnr : (25 : ℝ) ≤ N := by exact_mod_cast hN
  have hnr' : (N : ℝ) ≤ 90 := by exact_mod_cast hN'
  cases he : (node arr i).rule with
  | localRegion =>
      simp only [NodeOK, he] at hnode
      have hrq := (Rat.cast_le (K := ℝ)).mpr hnode.1
      have hDq := (Rat.cast_le (K := ℝ)).mpr hnode.2
      norm_num at hrq hDq
      have hr : r ≤ 1/10 := (hx 0).2.trans hrq
      have hD : D ≤ 1/4 := (hx 2).2.trans hDq
      exact analytic_region N j r H D q a hnr hnr' hj hj' h hr hD
  | infeasible k =>
      simp only [NodeOK, he] at hnode
      have hu := (encloses (toPoly (necessary branch k)) b ![r,H,D,q] hx).2
      change ev (necessary branch k) ![r,H,D,q] ≤ _ at hu
      have hn := necessary_sound h branch hb k
      have hneg : (upper (toPoly (necessary branch k)) b : ℝ) < 0 :=
        (Rat.cast_lt_zero (K := ℝ)).mpr hnode
      exact False.elim (not_lt_of_ge (hn.trans hu) hneg)
  | boxTail =>
      simp only [NodeOK, he] at hnode
      have hneg : max (2 : ℝ) (2*((b 2).2 : ℝ)/3) < ((b 3).1 : ℝ) := by exact_mod_cast hnode
      have hd : D ≤ ((b 2).2 : ℝ) := by simpa [b] using (hx 2).2
      have hql : ((b 3).1 : ℝ) ≤ q := by simpa [b] using (hx 3).1
      have hmon : max (2 : ℝ) (2*D/3) ≤ max 2 (2*((b 2).2 : ℝ)/3) :=
        max_le_max_left _ (by linarith only [hd])
      exact False.elim (not_lt_of_ge hql (lt_of_le_of_lt (h.boxTail.trans hmon) hneg))
  | capInfeasible m c =>
      simp only [NodeOK, he] at hnode
      obtain ⟨hc, hu⟩ := hnode
      have hch : branch=false → chordOK b m c := by
        intro hb'; rcases hc with hb'' | hc
        · cases hb'; cases hb''
        · exact hc
      have hcap := cap_sound h branch hb b hx m c hch
      have heval := (encloses
        (toPoly (addP (cap branch b m c) (scaleP (-1) amin))) b ![r,H,D,q] hx).2
      have hneg : (upper (toPoly (addP (cap branch b m c) (scaleP (-1) amin))) b : ℝ) < 0 :=
        (Rat.cast_lt_zero (K := ℝ)).mpr hu
      have hmin : ev amin ![r,H,D,q] = H^2/9 := by norm_num [amin, ev_formula]; ring
      change ev (addP (cap branch b m c) (scaleP (-1) amin)) ![r,H,D,q] ≤ _ at heval
      simp only [ev_add, ev_scale, Rat.cast_neg, Rat.cast_one] at heval
      rw [hmin] at heval
      exact False.elim (by linarith [h.amin])
  | bound mode k m c =>
      simp only [NodeOK, he] at hnode
      obtain ⟨hc, hm, hl⟩ := hnode
      have hcap : a ≤ ev (upperCap branch b k m c) ![r,H,D,q] := by
        by_cases hk : k.val < 8
        · simpa [upperCap, hk] using fixed_sound h ⟨k.val,hk⟩
        · have hcc : capOK branch b m c := hc.resolve_left hk
          have hch : branch=false → chordOK b m c := by
            intro hb'; rcases hcc with hb'' | hcc
            · cases hb'; cases hb''
            · exact hcc
          simpa [upperCap, hk] using cap_sound h branch hb b hx m c hch
      have hlow := (encloses
        (toPoly (addP (base N mode) (scaleP (-1) (upperCap branch b k m c)))) b ![r,H,D,q] hx).1
      have hl' : (0 : ℝ) ≤ lower (toPoly (addP (base N mode)
        (scaleP (-1) (upperCap branch b k m c)))) b :=
        (Rat.cast_nonneg (K := ℝ)).mpr hl
      have hbase := base_sound N hN b r H D q a j h hx hj hj' mode hm
      change (_ : ℝ) ≤ ev (addP (base N mode) (scaleP (-1) (upperCap branch b k m c))) ![r,H,D,q] at hlow
      simp only [ev_add, ev_scale, Rat.cast_neg, Rat.cast_one] at hlow
      linarith
  | split axis cut l r => trivial

/-- Generic local-step cover is reused. The finite node index never replaces
the real scalar domain. No check truth is a premise of the final consumer. -/
theorem checked_scalar_bound (N : Nat) (hN : 25 ≤ N) (hN' : N ≤ 90)
    (branch : Bool) (arr : Array Node) (accepted : check N branch arr=true)
    (r H D q a j : ℝ) (h : Hyp r H D q a) (hb : Branch branch r H D q a)
    (hj : 10 ≤ j) (hj' : j ≤ (N : ℝ)-15) :
    energy N j r H D q a ≤ theta N*(mass N j r H D)^2 := by
  obtain ⟨hsize, hnodes, _, hroot⟩ := of_decide_eq_true accepted
  let region (i : Fin arr.size) : Set (Fin 6 → ℝ) :=
    {z | Inside (node arr i.val).box ![z 0,z 1,z 2,z 3] ∧
      Hyp (z 0) (z 1) (z 2) (z 3) (z 4) ∧
      Branch branch (z 0) (z 1) (z 2) (z 3) (z 4) ∧
      10 ≤ z 5 ∧ z 5 ≤ (N : ℝ)-15}
  let targetSet : Set (Fin 6 → ℝ) :=
    {z | 0 ≤ gap N (z 5) (z 0) (z 1) (z 2) (z 3) (z 4)}
  have steps : ∀ i, LocalStep region targetSet (fun (_ : Fin 6 → ℝ) (_ : Fin 0) => 0) 0 i := by
    intro i
    have hn := hnodes i
    cases he : (node arr i.val).rule with
    | split axis cut l r =>
        simp only [NodeOK, he] at hn
        obtain ⟨hl,hr,_,_,hbl,hbr⟩ := hn
        let li : Fin arr.size := ⟨l,lt_trans hl i.isLt⟩
        let ri : Fin arr.size := ⟨r,lt_trans hr i.isLt⟩
        apply LocalStep.split li ri hl hr
        intro z hz
        obtain ⟨hx,hzrest⟩ := hz
        rcases split_retains (node arr i.val).box axis cut ![z 0,z 1,z 2,z 3] hx with hx | hx
        · left
          exact ⟨by simpa only [← funext hbl] using hx,hzrest⟩
        · right
          exact ⟨by simpa only [← funext hbr] using hx,hzrest⟩
    | localRegion | infeasible _ | boxTail | capInfeasible _ _ | bound _ _ _ _ =>
        apply LocalStep.covered
        intro z hz
        obtain ⟨hx,hh,hb',hj0,hj1⟩ := hz
        have hs := leaf_sound N hN hN' branch arr i.val hn
          (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) hh hb' hx hj0 hj1
        change 0 ≤ gap N (z 5) (z 0) (z 1) (z 2) (z 3) (z 4)
        simpa only [he] using hs
  let root : Fin arr.size := ⟨arr.size-1, Nat.sub_lt hsize (by decide)⟩
  have hx : Inside rootBox ![r,H,D,q] := by
    have hH : H ≤ 5 := by linarith [h.budget, h.D0, h.r0]
    have hD : D ≤ 5 := by linarith [h.budget, h.H0, h.r0]
    have hq : q ≤ 3 := by linarith [h.q3, h.r0]
    intro k; fin_cases k <;> norm_num [rootBox]
    · exact ⟨h.r0,h.rhalf⟩
    · exact ⟨h.H0,hH⟩
    · exact ⟨h.D0,hD⟩
    · exact ⟨h.q0,hq⟩
  have hxroot : Inside (node arr root.val).box ![r,H,D,q] := by
    simpa only [root, funext hroot] using hx
  have hout := sublevel_mem_target_of_local_steps region targetSet
    (fun (_ : Fin 6 → ℝ) (_ : Fin 0) => 0) 0 steps root ![r,H,D,q,a,j]
    (show ![r,H,D,q,a,j] ∈ region root from ⟨hxroot,h,hb,hj,hj'⟩)
    (by intro k; exact Fin.elim0 k)
  change 0 ≤ gap N j r H D q a at hout
  exact sub_nonneg.mp hout

end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
