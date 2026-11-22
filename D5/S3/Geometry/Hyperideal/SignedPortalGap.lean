/- GID: D5/S3/Geometry/Hyperideal/SignedPortalGap
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/SignedPortalGap
   mirror-E: none(waiver:parametric-signed-portal-graph)
   anchors: []
   utility: none
   digest: Six signed cyclic sheets can have bounded physical distance and arbitrarily large one-crossing distance. -/

import Std
set_option autoImplicit false

/-! The general path-pricing step is a connected-cell overlay argument
(cf. Delling et al., Customizable Route Planning, §2). The family result
concerns the exact signed reciprocal portal constraint, not a new claim
about general shortest-path overlays, hyperbolic metrics or manifolds. -/
namespace D5.S3.Geometry.Hyperideal.SignedPortalGap
universe u v

/-- Exact step-count, rather than only reachability. -/
inductive Walk {X : Type u} (R : X → X → Prop) : Nat → X → X → Prop
  | refl (x : X) : Walk R 0 x x
  | cons {n : Nat} {x y z : X} : R x y → Walk R n y z → Walk R (n+1) x z

/-- Exact total length and exact number of portal uses. -/
inductive CountedWalk {S : Type u} {C : Type v} (inside : C → C → Prop)
    (portal : S → C → S → C → Prop) : Nat → Nat → S×C → S×C → Prop
  | refl (x : S×C) : CountedWalk inside portal 0 0 x x
  | stay {n k : Nat} {s : S} {a b : C} {y : S×C} :
      inside a b → CountedWalk inside portal n k (s,b) y →
      CountedWalk inside portal (n+1) k (s,a) y
  | hop {n k : Nat} {s t : S} {a b : C} {y : S×C} :
      portal s a t b → CountedWalk inside portal n k (t,b) y →
      CountedWalk inside portal (n+1) (k+1) (s,a) y

inductive CountedPlan {S : Type u} {C : Type v} (d : C → C → Nat)
    (portal : S → C → S → C → Prop) : Nat → Nat → S×C → S×C → Prop
  | last (s : S) (a b : C) : CountedPlan d portal (d a b) 0 (s,a) (s,b)
  | cross {s t : S} {a b c : C} {n k : Nat} {z : S×C} :
      portal s b t c → CountedPlan d portal n k (t,c) z →
      CountedPlan d portal (d a b+1+n) (k+1) (s,a) z

private theorem attach_inside {S : Type u} {C : Type v} {inside : C → C → Prop}
    {portal : S → C → S → C → Prop} {m n k : Nat} {a b : C} {s : S} {z : S×C}
    (p : Walk inside m a b) (q : CountedWalk inside portal n k (s,b) z) :
    CountedWalk inside portal (m+n) k (s,a) z := by
  induction p with
  | refl => simpa using q
  | @cons m a b c h _ ih =>
    simpa [Nat.succ_add] using CountedWalk.stay h (ih q)

private theorem realize_counted {S : Type u} {C : Type v} {inside : C → C → Prop}
    {portal : S → C → S → C → Prop} {d : C → C → Nat}
    (hex : ∀ a b, Walk inside (d a b) a b) {n k : Nat} {x y : S×C}
    (p : CountedPlan d portal n k x y) : CountedWalk inside portal n k x y := by
  induction p with
  | last s a b => simpa using attach_inside (hex a b) (CountedWalk.refl (s,b))
  | @cross s t a b c n k z h _ ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      attach_inside (hex a b) (CountedWalk.hop h ih)

private theorem prepend_counted {S : Type u} {C : Type v} {inside : C → C → Prop}
    {portal : S → C → S → C → Prop} {d : C → C → Nat}
    (hex : ∀ a b, Walk inside (d a b) a b)
    (hmin : ∀ {n a b}, Walk inside n a b → d a b ≤ n)
    {n k : Nat} {s : S} {a b : C} {z : S×C} (h : inside a b)
    (p : CountedPlan d portal n k (s,b) z) : ∃ m ≤ n+1, CountedPlan d portal m k (s,a) z := by
  cases p with
  | last _ _ c => exact ⟨d a c,hmin (.cons h (hex b c)),.last s a c⟩
  | @cross _ t _ c e n k z hp plan =>
    refine ⟨d a c+1+n,?_,.cross hp plan⟩
    have hh : d a c ≤ d b c+1 := hmin (.cons h (hex b c))
    omega

private theorem compress_counted {S : Type u} {C : Type v} {inside : C → C → Prop}
    {portal : S → C → S → C → Prop} {d : C → C → Nat}
    (hex : ∀ a b, Walk inside (d a b) a b)
    (hmin : ∀ {n a b}, Walk inside n a b → d a b ≤ n)
    {n k : Nat} {x y : S×C} (p : CountedWalk inside portal n k x y) :
    ∃ m ≤ n, CountedPlan d portal m k x y := by
  have hz (a : C) : d a a=0 := Nat.eq_zero_of_le_zero (hmin (.refl a))
  induction p with
  | refl x => exact ⟨d x.2 x.2,by rw [hz]; exact Nat.zero_le _,.last x.1 x.2 x.2⟩
  | @stay n k s a b z h _ ih =>
    obtain ⟨m,hm,hp⟩ := ih
    obtain ⟨r,hr,hq⟩ := prepend_counted hex hmin h hp
    exact ⟨r,by omega,hq⟩
  | @hop n k s t a b z h _ ih =>
    obtain ⟨m,hm,hp⟩ := ih
    exact ⟨d a a+1+m,by rw [hz]; omega,.cross h hp⟩

/-- The constrained min-plus reduction preserves the exact portal count,
so it computes length optima for any upper bound on portal use as well. -/
private theorem budget_iff_counted_portal_plan {S : Type u} {C : Type v}
    (inside : C → C → Prop) (portal : S → C → S → C → Prop) (d : C → C → Nat)
    (hex : ∀ a b, Walk inside (d a b) a b)
    (hmin : ∀ {n a b}, Walk inside n a b → d a b ≤ n)
    (budget k : Nat) (x y : S×C) :
    (∃ n ≤ budget, CountedWalk inside portal n k x y) ↔
      (∃ n ≤ budget, CountedPlan d portal n k x y) := by
  constructor
  · rintro ⟨n,hn,p⟩
    obtain ⟨m,hm,q⟩ := compress_counted hex hmin p
    exact ⟨m,Nat.le_trans hm hn,q⟩
  · rintro ⟨n,hn,p⟩
    exact ⟨n,hn,realize_counted hex p⟩

/-- Same-cell portals contribute zero to projected base distance, but
still each contribute a full step to the physical path. -/
private theorem same_cell_projection {S : Type u} {C : Type v}
    {inside : C → C → Prop} {portal : S → C → S → C → Prop}
    (hsame : ∀ {s a t b}, portal s a t b → a=b) {n k : Nat} {x y : S×C}
    (p : CountedWalk inside portal n k x y) :
    k ≤ n ∧ Walk inside (n-k) x.2 y.2 ∧
      Walk (fun s t => ∃ a b, portal s a t b) k x.1 y.1 := by
  induction p with
  | refl x => exact ⟨Nat.le_refl 0,.refl x.2,.refl x.1⟩
  | @stay n k s a b z h _ ih =>
    have he : n+1-k = (n-k)+1 := by have := ih.1; omega
    exact ⟨by have := ih.1; omega,he ▸ Walk.cons h ih.2.1,ih.2.2⟩
  | @hop n k s t a b z h _ ih =>
    have he : a=b := hsame h
    subst b
    simpa using And.intro (by have := ih.1; omega : k+1 ≤ n+1)
      (And.intro ih.2.1 (Walk.cons (show ∃ p q, portal s p t q from ⟨a,a,h⟩) ih.2.2))

namespace Family

abbrev Sheet := Bool × Fin 3

def origin : Sheet := (false,0)
def target : Sheet := (true,2)

private def forward (r : Nat) (s t : Sheet) : Prop :=
  s.1=false ∧ t.1=true ∧ (s.2.val+r)%3=t.2.val

private def shift (r : Nat) (s t : Sheet) : Prop :=
  forward r s t ∨ forward r t s

/-- The two near matchings have offsets 0 and 1; the far matching has offset 2.
All three are signed involutive pairings with a fixed base coordinate. -/
def portal (L : Nat) (s : Sheet) (a : Nat) (t : Sheet) (b : Nat) : Prop :=
  a=b ∧ ((a=0 ∧ (shift 0 s t ∨ shift 1 s t)) ∨ (a=L ∧ shift 2 s t))

def inside (a b : Nat) : Prop := a+1=b ∨ b+1=a

def distance (a b : Nat) : Nat := (a-b)+(b-a)

private theorem up (a n : Nat) : Walk inside n a (a+n) := by
  induction n generalizing a with
  | zero => exact .refl a
  | succ n ih =>
    rw [show a+(n+1) = (a+1)+n by omega]
    exact .cons (.inl rfl) (ih (a+1))

private theorem down (a n : Nat) : Walk inside n (a+n) a := by
  induction n with
  | zero => exact .refl a
  | succ n ih =>
    have h : inside (a+(n+1)) (a+n) := .inr (by omega)
    exact .cons h ih

private theorem dist_witness (a b : Nat) : Walk inside (distance a b) a b := by
  by_cases h : a ≤ b
  · have f := up a (b-a)
    rwa [show a+(b-a)=b by omega,show b-a=distance a b by unfold distance; omega] at f
  · have f := down b (a-b)
    rwa [show b+(a-b)=a by omega,show a-b=distance a b by unfold distance; omega] at f

private theorem dist_lower {n a b : Nat} (p : Walk inside n a b) : distance a b ≤ n := by
  induction p with
  | refl a => simp [distance]
  | @cons n a c b h _ ih =>
    unfold inside at h
    unfold distance at ih ⊢
    omega

private theorem near01₁ (L : Nat) : portal L origin 0 (true,1) 0 :=
  ⟨rfl,.inl ⟨rfl,.inr (.inl ⟨rfl,rfl,rfl⟩)⟩⟩

private theorem near01₂ (L : Nat) : portal L (true,1) 0 (false,1) 0 :=
  ⟨rfl,.inl ⟨rfl,.inl (.inr ⟨rfl,rfl,rfl⟩)⟩⟩

private theorem near01₃ (L : Nat) : portal L (false,1) 0 target 0 :=
  ⟨rfl,.inl ⟨rfl,.inr (.inl ⟨rfl,rfl,rfl⟩)⟩⟩

private theorem direct_far (L : Nat) : portal L origin L target L :=
  ⟨rfl,.inr ⟨rfl,.inl ⟨rfl,rfl,rfl⟩⟩⟩

private theorem direct_only_far {L a b : Nat} (h : portal L origin a target b) : a=L ∧ b=L := by
  have h0 : ¬ shift 0 origin target := by
    unfold shift forward origin target; decide
  have h1 : ¬ shift 1 origin target := by
    unfold shift forward origin target; decide
  rcases h with ⟨hab,⟨_,h⟩ | ⟨ha,_⟩⟩
  · exact (h.elim h0 h1).elim
  · exact ⟨ha,hab.symm.trans ha⟩

private theorem sign_flip {L : Nat} {s t : Sheet} {a b : Nat}
    (h : portal L s a t b) : s.1 = !t.1 := by
  rcases h.2 with ⟨_,h | h⟩ | ⟨_,h⟩
  all_goals
    rcases h with h | h
    · rw [h.1,h.2.1]; rfl
    · rw [h.1,h.2.1]; rfl

private theorem parity {L n k : Nat} {x y : Sheet × Nat}
    (p : CountedWalk inside (portal L) n k x y) :
    x.1.1 = if k%2=0 then y.1.1 else !y.1.1 := by
  induction p with
  | refl => rfl
  | stay _ _ ih => exact ih
  | @hop n k s t a b z h _ ih =>
    have hf := sign_flip h
    by_cases hk : k%2=0
    · have hh : (k+1)%2 ≠ 0 := by omega
      dsimp at ih ⊢
      simpa [ite_eq_right hh,ite_eq_left hk,ih] using hf
    · have hh : (k+1)%2 = 0 := by omega
      dsimp at ih ⊢
      simp only [ite_eq_right hk] at ih
      simp only [ite_eq_left hh]
      rw [hf,ih]
      exact Bool.not_not _

private theorem three_steps (L : Nat) :
    CountedWalk inside (portal L) 3 3 (origin,0) (target,0) :=
  .hop (near01₁ L) (.hop (near01₂ L) (.hop (near01₃ L) (.refl _)))

private theorem one_cost_exact {L n : Nat}
    (p : CountedPlan distance (portal L) n 1 (origin,0) (target,0)) :
    n=2*L+1 := by
  cases p with
  | @cross _ t _ a b m _ _ h q =>
    cases q with
    | last =>
      obtain ⟨ha,hb⟩ := direct_only_far h
      unfold distance
      omega

private theorem one_plan_exists (L : Nat) :
    CountedPlan distance (portal L) (2*L+1) 1 (origin,0) (target,0) := by
  have h := CountedPlan.cross (d:=distance) (a:=0) (direct_far L) (CountedPlan.last target L 0)
  have he : distance 0 L + 1 + distance L 0 = 2*L+1 := by unfold distance; omega
  rwa [he] at h

/-- Signed sheet matchings can make the minimum-crossing policy arbitrarily
worse, even with six sheets, same-cell reciprocal portals and path interiors.
The one-crossing optimum is 2L+1; permitting more crossings gives exactly 3. -/
private theorem signed_shift_unbounded_gap (L : Nat) (hL : 0 < L) :
    CountedWalk inside (portal L) 3 3 (origin,0) (target,0) ∧
    (∀ n k, CountedWalk inside (portal L) n k (origin,0) (target,0) → 3 ≤ n) ∧
    (∃ n ≤ 2*L+1, CountedWalk inside (portal L) n 1 (origin,0) (target,0)) ∧
    (∀ n, CountedWalk inside (portal L) n 1 (origin,0) (target,0) → 2*L+1 ≤ n) := by
  have hmin (n : Nat) (w : CountedWalk inside (portal L) n 1 (origin,0) (target,0)) :
      2*L+1 ≤ n := by
    obtain ⟨r,hr,p⟩ := (budget_iff_counted_portal_plan inside (portal L) distance
      dist_witness dist_lower n 1 (origin,0) (target,0)).mp ⟨n,Nat.le_refl _,w⟩
    simpa [one_cost_exact p] using hr
  refine ⟨three_steps L,?_,?_,hmin⟩
  · intro n k w
    by_cases hn : 3 ≤ n
    · exact hn
    · have hh := parity w
      have hk0 : k%2≠0 := by
        intro hz
        simp [origin,target,hz] at hh
      have hk := (same_cell_projection (fun h=>h.1) w).1
      have he : k=1 := by omega
      subst k
      have h := hmin n w
      omega
  · exact (budget_iff_counted_portal_plan inside (portal L) distance dist_witness dist_lower
      (2*L+1) 1 (origin,0) (target,0)).mpr ⟨_,Nat.le_refl _,one_plan_exists L⟩


def insideFin {L : Nat} (a b : Fin (L+1)) : Prop := inside a.val b.val

def portalFin {L : Nat} (s : Sheet) (a : Fin (L+1)) (t : Sheet) (b : Fin (L+1)) : Prop :=
  portal L s a.val t b.val

private def toNatNode {L : Nat} (x : Sheet × Fin (L+1)) : Sheet × Nat :=
  (x.1,x.2.val)

private theorem forget_bound {L n k : Nat} {x y : Sheet × Fin (L+1)}
    (p : CountedWalk insideFin portalFin n k x y) :
    CountedWalk inside (portal L) n k (toNatNode x) (toNatNode y) := by
  induction p with
  | refl => exact .refl _
  | stay h _ ih => exact .stay h ih
  | hop h _ ih => exact .hop h ih

private theorem bounded_up {L : Nat} (a n : Nat) (h : a+n≤L) :
    Walk (@insideFin L) n ⟨a,by omega⟩ ⟨a+n,by omega⟩ := by
  induction n generalizing a with
  | zero => exact .refl _
  | succ n ih =>
    have he : (⟨a+(n+1),by omega⟩ : Fin (L+1)) =
        ⟨(a+1)+n,by omega⟩ := Fin.ext (by simp; omega)
    rw [he]
    exact .cons (.inl rfl) (ih (a+1) (by omega))

private theorem bounded_down {L : Nat} (a n : Nat) (h : a+n≤L) :
    Walk (@insideFin L) n ⟨a+n,by omega⟩ ⟨a,by omega⟩ := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    have he : insideFin (⟨a+n+1,by omega⟩ : Fin (L+1)) ⟨a+n,by omega⟩ := .inr rfl
    exact .cons he (ih (by omega))

private theorem pricedFin {L : Nat} (a b : Fin (L+1)) :
    Walk insideFin (distance a.val b.val) a b := by
  have ha := a.isLt
  have hb := b.isLt
  by_cases h : a.val ≤ b.val
  · have hwalk := bounded_up (L:=L) a.val (b.val-a.val) (by omega)
    have hidx : (⟨a.val+(b.val-a.val),by omega⟩ : Fin (L+1)) = b := Fin.ext (by simp; omega)
    rw [hidx] at hwalk
    change Walk (@insideFin L) (b.val-a.val) a b at hwalk
    rwa [show b.val-a.val=distance a.val b.val by unfold distance; omega] at hwalk
  · have hwalk := bounded_down (L:=L) b.val (a.val-b.val) (by omega)
    have hidx : (⟨b.val+(a.val-b.val),by omega⟩ : Fin (L+1)) = a := Fin.ext (by simp; omega)
    rw [hidx] at hwalk
    change Walk (@insideFin L) (a.val-b.val) a b at hwalk
    rwa [show a.val-b.val=distance a.val b.val by unfold distance; omega] at hwalk

private theorem forget_inside {L n : Nat} {a b : Fin (L+1)}
    (p : Walk insideFin n a b) : Walk inside n a.val b.val := by
  induction p with
  | refl => exact .refl _
  | cons h _ ih => exact .cons h ih

/-- The arbitrarily large gap holds on finite graphs, with exactly six signed
sheets and L+1 base vertices per sheet, not only in an ambient infinite path. -/
theorem finite_signed_shift_unbounded_gap (L : Nat) (hL : 0 < L) :
    let zero : Fin (L+1) := ⟨0,by omega⟩
    CountedWalk insideFin portalFin 3 3 (origin,zero) (target,zero) ∧
    (∀ n k, CountedWalk insideFin portalFin n k (origin,zero) (target,zero) → 3 ≤ n) ∧
    (∃ n ≤ 2*L+1, CountedWalk insideFin portalFin n 1 (origin,zero) (target,zero)) ∧
    (∀ n, CountedWalk insideFin portalFin n 1 (origin,zero) (target,zero) → 2*L+1 ≤ n) := by
  let zero : Fin (L+1) := ⟨0,by omega⟩
  let far : Fin (L+1) := ⟨L,by omega⟩
  have h := signed_shift_unbounded_gap L hL
  have h1 : portalFin origin zero (true,1) zero := near01₁ L
  have h2 : portalFin (true,1) zero (false,1) zero := near01₂ L
  have h3 : portalFin (false,1) zero target zero := near01₃ L
  refine ⟨.hop h1 (.hop h2 (.hop h3 (.refl _))),
    fun n k w => h.2.1 n k (forget_bound w),?_,
    fun n w => h.2.2.2 n (forget_bound w)⟩
  let d (a b : Fin (L+1)) := distance a.val b.val
  have hplan : CountedPlan d portalFin (2*L+1) 1 (origin,zero) (target,zero) := by
    have hp : portalFin origin far target far := direct_far L
    have w := CountedPlan.cross (d:=d) (a:=zero) hp (CountedPlan.last target far zero)
    have he : d zero far + 1 + d far zero = 2*L+1 := by
      change distance 0 L + 1 + distance L 0 = 2*L+1
      unfold distance
      omega
    rwa [he] at w
  exact (budget_iff_counted_portal_plan insideFin portalFin d pricedFin
    (fun w => dist_lower (forget_inside w)) (2*L+1) 1 (origin,zero) (target,zero)).mpr
    ⟨_,Nat.le_refl _,hplan⟩

end Family
end D5.S3.Geometry.Hyperideal.SignedPortalGap
