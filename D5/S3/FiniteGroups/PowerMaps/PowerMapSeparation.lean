/- GID: D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/PowerMaps/PowerMapSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.claim; result=D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.result; claim=D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.claim
   digest: Fixed finite groups with separate integer-power conjugacies but no joint square-cube conjugacy. -/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Explicit original-coordinate semidirect products for the power-map counterexample. -/

@[expose] public section

namespace D5.S3.FiniteGroups.PowerMaps.PowerMapSeparation

abbrev F := ZMod 3

/-- Original (uncentered) coordinates of the two semidirect products. -/
@[ext] structure S (i : Bool) where
  a : F
  b : F
  x : F
  y : F
  z : F
  s : F
  t : F
  e : Bool
  deriving DecidableEq

def productEquiv (i : Bool) :
    S i ≃ (F × F) × (F × F × F) × (F × F) × Bool where
  toFun p := ((p.a,p.b),(p.x,p.y,p.z),(p.s,p.t),p.e)
  invFun p := ⟨p.1.1,p.1.2,p.2.1.1,p.2.1.2.1,p.2.1.2.2,
    p.2.2.1.1,p.2.2.1.2,p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (i : Bool) : Fintype (S i) := Fintype.ofEquiv _ (productEquiv i).symm

def sign (e : Bool) : F := if e then -1 else 1
def B1 (i : Bool) (a b x y : F) : F := if i then a*x-b*y else a*x+b*y
def B2 (i : Bool) (a b x y z : F) : F := if i then b*x+a*y else a*y+b*z

def mulS {i : Bool} (p q : S i) : S i := ⟨p.a+q.a, p.b+q.b, p.x+sign p.e*q.x, p.y+sign p.e*q.y,
    p.z+sign p.e*q.z, p.s+sign p.e*q.s+sign p.e*B1 i p.a p.b q.x q.y,
    p.t+sign p.e*q.t+sign p.e*B2 i p.a p.b q.x q.y q.z, p.e ^^ q.e⟩
def oneS (i : Bool) : S i := ⟨0,0,0,0,0,0,0,false⟩
def invS {i : Bool} (p : S i) : S i := ⟨-p.a,-p.b,-sign p.e*p.x,-sign p.e*p.y,-sign p.e*p.z,
    -sign p.e*p.s+sign p.e*B1 i p.a p.b p.x p.y,
    -sign p.e*p.t+sign p.e*B2 i p.a p.b p.x p.y p.z,p.e⟩

instance (i : Bool) : Group (S i) where
  mul := mulS
  one := oneS i
  inv := invS
  mul_assoc p q r := by
    change mulS (mulS p q) r = mulS p (mulS q r)
    rcases p with ⟨a,b,x,y,z,s,t,e⟩
    rcases q with ⟨a',b',x',y',z',s',t',e'⟩
    rcases r with ⟨a'',b'',x'',y'',z'',s'',t'',e''⟩
    cases i <;> cases e <;> cases e' <;>
      apply S.ext <;> simp [mulS, sign, B1, B2, Bool.xor_assoc, add_assoc] <;> ring
  one_mul p := by
    change mulS (oneS i) p = p
    rcases p with ⟨a,b,x,y,z,s,t,e⟩
    cases i <;> cases e <;> apply S.ext <;>
      simp [mulS, oneS, sign, B1, B2]
  mul_one p := by
    change mulS p (oneS i) = p
    rcases p with ⟨a,b,x,y,z,s,t,e⟩
    cases i <;> cases e <;> apply S.ext <;>
      simp [mulS, oneS, sign, B1, B2]
  inv_mul_cancel p := by
    change mulS (invS p) p = oneS i
    rcases p with ⟨a,b,x,y,z,s,t,e⟩
    cases i <;> cases e <;> apply S.ext <;>
      simp only [mulS, oneS, invS, sign, B1, B2, Bool.false_eq_true,
        Bool.true_eq_false, ↓reduceIte, Bool.xor_self] <;> ring

private theorem card_S (i : Bool) : Fintype.card (S i) = 4374 := by
  rw [Fintype.card_congr (productEquiv i)]
  norm_num [Fintype.card_prod, F]

/-- The same underlying coordinates with the central term centered. -/
private def center (i : Bool) : S i ≃ S false where
  toFun p := ⟨p.a,p.b,p.x,p.y,p.z,p.s+B1 i p.a p.b p.x p.y,
    p.t+B2 i p.a p.b p.x p.y p.z,p.e⟩
  invFun p := ⟨p.a,p.b,p.x,p.y,p.z,p.s-B1 i p.a p.b p.x p.y,
    p.t-B2 i p.a p.b p.x p.y p.z,p.e⟩
  left_inv p := by apply S.ext <;> simp
  right_inv p := by apply S.ext <;> simp

private def squareC (i : Bool) (p : S false) : S false :=
  if p.e then ⟨-p.a,-p.b,0,0,0,-B1 i p.a p.b p.x p.y,
    -B2 i p.a p.b p.x p.y p.z,false⟩
  else ⟨-p.a,-p.b,-p.x,-p.y,-p.z,-p.s,-p.t,false⟩

private def cubeC (p : S false) : S false :=
  if p.e then ⟨0,0,p.x,p.y,p.z,p.s,p.t,true⟩ else oneS false

private theorem two_F : (2 : F) = -1 := by decide
private theorem three_F : (3 : F) = 0 := by decide
private theorem five_F : (5 : F) = -1 := by decide
private theorem cases_F (a : F) : a = 0 ∨ a = 1 ∨ a = -1 := by revert a; decide

private theorem center_square (i : Bool) (p : S i) :
    center i (p^2) = squareC i (center i p) := by
  rw [pow_two]
  change center i (mulS p p) = squareC i (center i p)
  rcases p with ⟨a,b,x,y,z,s,t,e⟩
  cases i <;> cases e <;> apply S.ext <;>
    simp [center, squareC, mulS, sign, B1, B2] <;> ring_nf <;> simp [two_F, three_F, five_F] <;> ring

private theorem center_cube (i : Bool) (p : S i) :
    center i (p^3) = cubeC (center i p) := by
  rw [pow_succ, pow_two]
  change center i (mulS (mulS p p) p) = cubeC (center i p)
  rcases p with ⟨a,b,x,y,z,s,t,e⟩
  cases i <;> cases e <;> apply S.ext <;>
    simp [center, cubeC, mulS, oneS, sign, B1, B2] <;> ring_nf <;>
      simp [three_F, show (4 : F) = 1 by decide, show (12 : F) = 0 by decide]

private theorem center_inv (i : Bool) (p : S i) :
    center i p⁻¹ =
      (if p.e then ⟨-p.a,-p.b,p.x,p.y,p.z,(center i p).s,(center i p).t,true⟩
       else ⟨-p.a,-p.b,-p.x,-p.y,-p.z,-(center i p).s,-(center i p).t,false⟩) := by
  change center i (invS p) = _
  rcases p with ⟨a,b,x,y,z,s,t,e⟩
  cases i <;> cases e <;> apply S.ext <;>
    simp [center, invS, sign, B1, B2] <;> ring_nf <;> simp [two_F, three_F, five_F] <;> ring

private def transportAxis : (F × F × F) ≃ (F × F × F) where
  toFun w := (w.2.2, -w.2.1, w.1)
  invFun w := (w.2.2, -w.2.1, w.1)
  left_inv w := by rcases w with ⟨x,y,z⟩; simp
  right_inv w := by rcases w with ⟨x,y,z⟩; simp

private def transportPlus : (F × F × F) ≃ (F × F × F) where
  toFun w := (-w.1 + w.2.1 - w.2.2, w.1 - w.2.2, w.2.2)
  invFun w := (w.2.1 + w.2.2, w.1 + w.2.1 - w.2.2, w.2.2)
  left_inv w := by
    rcases w with ⟨x,y,z⟩
    ext <;> dsimp <;> ring_nf <;> simp [three_F]
  right_inv w := by
    rcases w with ⟨x,y,z⟩
    ext <;> dsimp <;> ring_nf <;> simp [three_F]

private def transportMinus : (F × F × F) ≃ (F × F × F) where
  toFun w := (-w.1 - w.2.1 - w.2.2, -w.1 + w.2.2, w.2.2)
  invFun w := (w.2.2 - w.2.1, w.2.1 + w.2.2 - w.1, w.2.2)
  left_inv w := by
    rcases w with ⟨x,y,z⟩
    ext <;> dsimp <;> ring_nf <;> simp [three_F]
  right_inv w := by
    rcases w with ⟨x,y,z⟩
    ext <;> dsimp <;> ring_nf <;> simp [three_F]

private def transport (a b : F) : (F × F × F) ≃ (F × F × F) :=
  if a = 0 then
    if b = 0 then Equiv.refl _ else transportAxis
  else if b = 0 then Equiv.refl _
  else if a = b then transportPlus else transportMinus

private theorem one_ne_neg_one_F : (1 : F) ≠ -1 := by decide

private theorem transport_B1 (a b x y z : F) :
    B1 true a b (transport a b (x,y,z)).1 (transport a b (x,y,z)).2.1 =
      B1 false a b x y := by
  rcases cases_F a with rfl | rfl | rfl <;>
    rcases cases_F b with rfl | rfl | rfl <;>
    norm_num [transport, transportAxis, transportPlus, transportMinus, B1, one_ne_neg_one_F, Ne.symm one_ne_neg_one_F] <;>
      (try ring_nf) <;> simp [two_F, three_F, five_F] <;> ring

private theorem transport_B2 (a b x y z : F) :
    B2 true a b (transport a b (x,y,z)).1 (transport a b (x,y,z)).2.1
      (transport a b (x,y,z)).2.2 = B2 false a b x y z := by
  rcases cases_F a with rfl | rfl | rfl <;>
    rcases cases_F b with rfl | rfl | rfl <;>
    norm_num [transport, transportAxis, transportPlus, transportMinus, B2, one_ne_neg_one_F, Ne.symm one_ne_neg_one_F] <;>
      (try ring_nf) <;> simp [two_F, three_F, five_F] <;> ring

private def evenC : S false ≃ S false where
  toFun p := if p.e then
    let w := transport p.a p.b (p.x,p.y,p.z)
    ⟨p.a,p.b,w.1,w.2.1,w.2.2,p.s,p.t,p.e⟩ else p
  invFun p := if p.e then
    let w := (transport p.a p.b).symm (p.x,p.y,p.z)
    ⟨p.a,p.b,w.1,w.2.1,w.2.2,p.s,p.t,p.e⟩ else p
  left_inv p := by
    rcases p with ⟨a,b,x,y,z,s,t,e⟩
    cases e <;> simp
  right_inv p := by
    rcases p with ⟨a,b,x,y,z,s,t,e⟩
    cases e <;> simp

private theorem evenC_square (p : S false) :
    evenC (squareC false p) = squareC true (evenC p) := by
  rcases p with ⟨a,b,x,y,z,s,t,e⟩
  cases e <;> simp [evenC, squareC, transport_B1, transport_B2]

private def oddEquiv : S false ≃ S true := (center false).trans (center true).symm
private def evenEquiv : S false ≃ S true :=
  ((center false).trans evenC).trans (center true).symm

private theorem odd_center (p : S false) :
    center true (oddEquiv p) = center false p := by simp [oddEquiv]
private theorem even_center (p : S false) :
    center true (evenEquiv p) = evenC (center false p) := by simp [evenEquiv]
private theorem center_one (i : Bool) : center i 1 = oneS false := by
  apply S.ext <;> cases i <;> rfl

private theorem odd_one : oddEquiv 1 = 1 := by
  apply (center true).injective
  rw [odd_center, center_one, center_one]

private theorem odd_cube (p : S false) : oddEquiv (p^3) = (oddEquiv p)^3 := by
  apply (center true).injective
  rw [odd_center, center_cube, center_cube, odd_center]

private theorem odd_inv (p : S false) : oddEquiv p⁻¹ = (oddEquiv p)⁻¹ := by
  apply (center true).injective
  rw [odd_center, center_inv, center_inv]
  simp only [oddEquiv, Equiv.trans_apply, center, Equiv.coe_fn_mk, Equiv.symm_mk]
  simp only [sub_add_cancel]

private theorem even_square (p : S false) : evenEquiv (p^2) = (evenEquiv p)^2 := by
  apply (center true).injective
  rw [even_center, center_square, evenC_square, center_square, even_center]

private theorem even_fourth (p : S false) : evenEquiv (p^4) = (evenEquiv p)^4 := by
  simpa only [← pow_mul] using
    (even_square (p^2)).trans (congrArg (fun q : S true => q^2) (even_square p))

private theorem sixth_power (i : Bool) (p : S i) : p^6 = 1 := by
  apply (center i).injective
  rw [show (6 : ℕ) = 3*2 by decide, pow_mul, center_square, center_cube, center_one]
  rcases p with ⟨a,b,x,y,z,s,t,e⟩
  cases i <;> cases e <;> simp [center, cubeC, squareC, oneS, B1, B2]

private theorem fifth_power (i : Bool) (p : S i) : p^5 = p⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  simpa only [← pow_succ] using sixth_power i p

private theorem zpow_mod_six (i : Bool) (p : S i) (m : ℤ) : p^m = p^(m%6) := by
  have h : p^(6 : ℤ) = 1 := by exact_mod_cast sixth_power i p
  calc
    p^m = p^(m%6+6*(m/6)) := congrArg (fun k : ℤ => p^k) (by omega : m = m%6+6*(m/6))
    _ = p^(m%6) := by rw [zpow_add, zpow_mul, h, one_zpow, mul_one]

private theorem separate_powers (m : ℤ) :
    ∃ f : S false ≃ S true, ∀ p, f (p^m) = (f p)^m := by
  have lo := Int.emod_nonneg m (by decide : (6 : ℤ) ≠ 0)
  have hi := Int.emod_lt_of_pos m (by decide : (0 : ℤ) < 6)
  generalize hr : m%6 = r at lo hi
  interval_cases r
  · refine ⟨oddEquiv, fun p => ?_⟩
    simp only [zpow_mod_six, hr, zpow_zero, odd_one]
  · refine ⟨oddEquiv, fun p => ?_⟩
    simp only [zpow_mod_six, hr, zpow_one]
  · refine ⟨evenEquiv, fun p => ?_⟩
    simpa only [zpow_mod_six, hr, zpow_ofNat] using even_square p
  · refine ⟨oddEquiv, fun p => ?_⟩
    simpa only [zpow_mod_six, hr, zpow_ofNat] using odd_cube p
  · refine ⟨evenEquiv, fun p => ?_⟩
    simpa only [zpow_mod_six, hr, zpow_ofNat] using even_fourth p
  · refine ⟨oddEquiv, fun p => ?_⟩
    simp only [zpow_mod_six, hr, zpow_ofNat, fifth_power, odd_inv]


private def powerNeighborhood {G : Type*} [Group G] (t : G) : Set G :=
  {y | ∃ x : G, x ^ (3 : ℕ) = t ∧ x ^ (2 : ℕ) = y}

private def powerInvolution {G : Type*} [Group G] (t : G) : Prop :=
  t ^ (2 : ℕ) = 1 ∧ t ≠ 1

private def powerNeighborhoodClass {G : Type*} [Group G] (t : G) : Set G :=
  {u | powerInvolution u ∧ powerNeighborhood u = powerNeighborhood t}

private theorem joint_map_one {G H : Type*} [Group G] [Group H]
    (f : G ≃ H) (h₂ : ∀ x : G, f (x ^ (2 : ℕ)) = (f x) ^ (2 : ℕ)) :
    f 1 = 1 := by
  have h : f 1 * f 1 = f 1 * 1 := by
    simpa only [one_pow, pow_two, mul_one] using (h₂ 1).symm
  exact mul_left_cancel h

private theorem joint_neighborhood_mem {G H : Type*} [Group G] [Group H]
    (f : G ≃ H) (h₂ : ∀ x : G, f (x ^ (2 : ℕ)) = (f x) ^ (2 : ℕ))
    (h₃ : ∀ x : G, f (x ^ (3 : ℕ)) = (f x) ^ (3 : ℕ)) (t y : G) :
    y ∈ powerNeighborhood t ↔ f y ∈ powerNeighborhood (f t) := by
  constructor
  · rintro ⟨x, hx₃, hx₂⟩
    exact ⟨f x, (h₃ x).symm.trans (congrArg f hx₃),
      (h₂ x).symm.trans (congrArg f hx₂)⟩
  · rintro ⟨x, hx₃, hx₂⟩
    refine ⟨f.symm x, ?_, ?_⟩
    · apply f.injective
      rw [h₃, f.apply_symm_apply]
      exact hx₃
    · apply f.injective
      rw [h₂, f.apply_symm_apply]
      exact hx₂

private theorem joint_neighborhood_eq {G H : Type*} [Group G] [Group H]
    (f : G ≃ H) (h₂ : ∀ x : G, f (x ^ (2 : ℕ)) = (f x) ^ (2 : ℕ))
    (h₃ : ∀ x : G, f (x ^ (3 : ℕ)) = (f x) ^ (3 : ℕ)) (t u : G) :
    powerNeighborhood t = powerNeighborhood u ↔
      powerNeighborhood (f t) = powerNeighborhood (f u) := by
  constructor
  · intro h
    apply Set.ext
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    rw [← joint_neighborhood_mem f h₂ h₃ t x,
      ← joint_neighborhood_mem f h₂ h₃ u x, h]
  · intro h
    apply Set.ext
    intro y
    rw [joint_neighborhood_mem f h₂ h₃ t y,
      joint_neighborhood_mem f h₂ h₃ u y, h]

private theorem joint_involution {G H : Type*} [Group G] [Group H]
    (f : G ≃ H) (h₂ : ∀ x : G, f (x ^ (2 : ℕ)) = (f x) ^ (2 : ℕ)) (t : G) :
    powerInvolution t ↔ powerInvolution (f t) := by
  have h₁ := joint_map_one f h₂
  have hs : t ^ (2 : ℕ) = 1 ↔ (f t) ^ (2 : ℕ) = 1 := by
    constructor
    · intro ht
      rw [← h₂, ht, h₁]
    · intro ht
      apply f.injective
      rw [h₂, h₁, ht]
  have hn : t ≠ 1 ↔ f t ≠ 1 := by
    constructor
    · intro ht he
      exact ht (f.injective (he.trans h₁.symm))
    · intro ht he
      exact ht ((congrArg f he).trans h₁)
  exact and_congr hs hn

private def joint_neighborhood_class_equiv {G H : Type*} [Group G] [Group H]
    (f : G ≃ H) (h₂ : ∀ x : G, f (x ^ (2 : ℕ)) = (f x) ^ (2 : ℕ))
    (h₃ : ∀ x : G, f (x ^ (3 : ℕ)) = (f x) ^ (3 : ℕ)) (t : G) :
    {u : G // u ∈ powerNeighborhoodClass t} ≃
      {u : H // u ∈ powerNeighborhoodClass (f t)} :=
  f.subtypeEquiv fun u =>
    and_congr (joint_involution f h₂ u) (joint_neighborhood_eq f h₂ h₃ u t)

private theorem joint_neighborhood_class_card {G H : Type*} [Group G] [Group H]
    (f : G ≃ H) (h₂ : ∀ x : G, f (x ^ (2 : ℕ)) = (f x) ^ (2 : ℕ))
    (h₃ : ∀ x : G, f (x ^ (3 : ℕ)) = (f x) ^ (3 : ℕ)) (t : G)
    [Fintype {u : G // u ∈ powerNeighborhoodClass t}]
    [Fintype {u : H // u ∈ powerNeighborhoodClass (f t)}] :
    Fintype.card {u : G // u ∈ powerNeighborhoodClass t} =
      Fintype.card {u : H // u ∈ powerNeighborhoodClass (f t)} :=
  Fintype.card_congr (joint_neighborhood_class_equiv f h₂ h₃ t)

private def involutionPoint (i : Bool) (x y z s t : F) : S i :=
  ⟨0,0,x,y,z,s,t,true⟩

private def neighborhoodPoint (i : Bool) (a b x y z : F) : S i :=
  ⟨a,b,0,0,0,B1 i a b x y,B2 i a b x y z,false⟩

private theorem square_of_cube_point (i : Bool) (q : S i) (x y z s t : F)
    (h : q ^ (3 : ℕ) = involutionPoint i x y z s t) :
    q ^ (2 : ℕ) = neighborhoodPoint i (-q.a) (-q.b) x y z := by
  have hc := congrArg (center i) h
  rw [center_cube] at hc
  rcases q with ⟨a,b,u,v,w,c,d,e⟩
  cases e with
  | false => simp [cubeC, center, involutionPoint, oneS] at hc
  | true =>
    simp [cubeC, center, involutionPoint, B1, B2] at hc
    rcases hc with ⟨rfl, rfl, rfl, hc, hd⟩
    apply (center i).injective
    rw [center_square]
    cases i <;> apply S.ext <;>
      simp [squareC, center, neighborhoodPoint, B1, B2] <;> ring

private theorem neighborhood_point_mem (i : Bool) (a b x y z s t : F) :
    neighborhoodPoint i a b x y z ∈ powerNeighborhood (involutionPoint i x y z s t) := by
  refine ⟨(center i).symm ⟨-a,-b,x,y,z,s,t,true⟩, ?_, ?_⟩
  · apply (center i).injective
    rw [center_cube, (center i).apply_symm_apply]
    apply S.ext <;> simp [cubeC, center, involutionPoint, B1, B2]
  · apply (center i).injective
    rw [center_square, (center i).apply_symm_apply]
    cases i <;> apply S.ext <;>
      simp [squareC, center, neighborhoodPoint, B1, B2] <;> ring

private theorem neighborhood_point_range (i : Bool) (x y z s t : F) :
    powerNeighborhood (involutionPoint i x y z s t) =
      Set.range (fun ab : F × F => neighborhoodPoint i ab.1 ab.2 x y z) := by
  apply Set.ext
  intro p
  constructor
  · rintro ⟨q, h₃, h₂⟩
    exact ⟨(-q.a,-q.b), (square_of_cube_point i q x y z s t h₃).symm.trans h₂⟩
  · rintro ⟨⟨a,b⟩, rfl⟩
    exact neighborhood_point_mem i a b x y z s t

private theorem neighborhood_eq_bilinear (i : Bool) (x y z s t x' y' z' s' t' : F) :
    powerNeighborhood (involutionPoint i x y z s t) =
        powerNeighborhood (involutionPoint i x' y' z' s' t') ↔
      ∀ a b : F, B1 i a b x y = B1 i a b x' y' ∧
        B2 i a b x y z = B2 i a b x' y' z' := by
  constructor
  · intro h a b
    have hm := neighborhood_point_mem i a b x y z s t
    rw [h, neighborhood_point_range] at hm
    rcases hm with ⟨⟨a',b'⟩, he⟩
    have ha := congrArg S.a he
    have hb := congrArg S.b he
    change a' = a at ha
    change b' = b at hb
    subst a'; subst b'
    exact ⟨(congrArg S.s he).symm, (congrArg S.t he).symm⟩
  · intro h
    rw [neighborhood_point_range, neighborhood_point_range]
    congr 1
    funext ab
    apply S.ext <;> simp [neighborhoodPoint, (h ab.1 ab.2).1, (h ab.1 ab.2).2]

private theorem neighborhood_eq_zero (x y z s t x' y' z' s' t' : F) :
    powerNeighborhood (involutionPoint false x y z s t) =
        powerNeighborhood (involutionPoint false x' y' z' s' t') ↔
      x = x' ∧ y = y' ∧ z = z' := by
  rw [neighborhood_eq_bilinear]
  constructor
  · intro h
    have h₁ := h 1 0
    have h₂ := h 0 1
    simp [B1, B2] at h₁ h₂
    exact ⟨h₁.1,h₁.2,h₂.2⟩
  · rintro ⟨rfl,rfl,rfl⟩
    simp

private theorem neighborhood_eq_one (x y z s t x' y' z' s' t' : F) :
    powerNeighborhood (involutionPoint true x y z s t) =
        powerNeighborhood (involutionPoint true x' y' z' s' t') ↔
      x = x' ∧ y = y' := by
  rw [neighborhood_eq_bilinear]
  constructor
  · intro h
    simpa [B1, B2] using h 1 0
  · rintro ⟨rfl,rfl⟩
    simp [B1, B2]

private theorem involution_point_valid (i : Bool) (x y z s t : F) :
    powerInvolution (involutionPoint i x y z s t) := by
  constructor
  · apply (center i).injective
    rw [center_square]
    change squareC i (center i (involutionPoint i x y z s t)) = center i (oneS i)
    cases i <;> apply S.ext <;>
      simp [center, squareC, involutionPoint, oneS, B1, B2]
  · intro h
    have he := congrArg S.e h
    change true = false at he
    cases he

private theorem involution_coordinates (i : Bool) (p : S i) :
    powerInvolution p ↔ p.a = 0 ∧ p.b = 0 ∧ p.e = true := by
  constructor
  · rintro ⟨hp, hn⟩
    have hc := congrArg (center i) hp
    rw [center_square] at hc
    change squareC i (center i p) = center i (oneS i) at hc
    have ha : p.a = 0 := by
      have h := congrArg S.a hc
      cases he : p.e <;> simpa [squareC, center, oneS, he] using h
    have hb : p.b = 0 := by
      have h := congrArg S.b hc
      cases he : p.e <;> simpa [squareC, center, oneS, he] using h
    refine ⟨ha, hb, ?_⟩
    rcases p with ⟨a,b,x,y,z,s,t,e⟩
    change a = 0 at ha
    change b = 0 at hb
    subst a; subst b
    cases e with
    | true => rfl
    | false =>
      simp [squareC, center, oneS, B1, B2] at hc
      rcases hc with ⟨hx,hy,hz,hs,ht⟩
      exfalso
      apply hn
      change S.mk 0 0 x y z s t false = oneS i
      apply S.ext <;> simp_all [oneS]
  · intro h
    rcases p with ⟨a,b,x,y,z,s,t,e⟩
    rcases h with ⟨ha,hb,he⟩
    change a = 0 at ha
    change b = 0 at hb
    change e = true at he
    subst a; subst b; subst e
    exact involution_point_valid i x y z s t

private theorem class_zero_coordinates (x y z s t : F) (u : S false) :
    u ∈ powerNeighborhoodClass (involutionPoint false x y z s t) ↔
      u = involutionPoint false x y z u.s u.t := by
  constructor
  · rintro ⟨hi,hn⟩
    have hc := (involution_coordinates false u).mp hi
    rcases u with ⟨a,b,x',y',z',s',t',e⟩
    rcases hc with ⟨ha,hb,he⟩
    change a = 0 at ha
    change b = 0 at hb
    change e = true at he
    subst a; subst b; subst e
    change powerNeighborhood (involutionPoint false x' y' z' s' t') = _ at hn
    rcases (neighborhood_eq_zero x' y' z' s' t' x y z s t).mp hn with ⟨hx,hy,hz⟩
    subst x'; subst y'; subst z'
    rfl
  · intro h
    rw [h]
    exact ⟨involution_point_valid false _ _ _ _ _,
      (neighborhood_eq_zero _ _ _ _ _ _ _ _ _ _).mpr ⟨rfl,rfl,rfl⟩⟩

private theorem class_one_coordinates (x y z s t : F) (u : S true) :
    u ∈ powerNeighborhoodClass (involutionPoint true x y z s t) ↔
      u = involutionPoint true x y u.z u.s u.t := by
  constructor
  · rintro ⟨hi,hn⟩
    have hc := (involution_coordinates true u).mp hi
    rcases u with ⟨a,b,x',y',z',s',t',e⟩
    rcases hc with ⟨ha,hb,he⟩
    change a = 0 at ha
    change b = 0 at hb
    change e = true at he
    subst a; subst b; subst e
    change powerNeighborhood (involutionPoint true x' y' z' s' t') = _ at hn
    rcases (neighborhood_eq_one x' y' z' s' t' x y z s t).mp hn with ⟨hx,hy⟩
    subst x'; subst y'
    rfl
  · intro h
    rw [h]
    exact ⟨involution_point_valid true _ _ _ _ _,
      (neighborhood_eq_one _ _ _ _ _ _ _ _ _ _).mpr ⟨rfl,rfl⟩⟩

private def class_zero_equiv (x y z s t : F) :
    {u : S false // u ∈ powerNeighborhoodClass (involutionPoint false x y z s t)} ≃
      F × F where
  toFun u := (u.val.s,u.val.t)
  invFun p := ⟨involutionPoint false x y z p.1 p.2,
    (class_zero_coordinates _ _ _ _ _ _).mpr rfl⟩
  left_inv u := Subtype.ext ((class_zero_coordinates _ _ _ _ _ _).mp u.property).symm
  right_inv _ := rfl

private def class_one_equiv (x y z s t : F) :
    {u : S true // u ∈ powerNeighborhoodClass (involutionPoint true x y z s t)} ≃
      F × F × F where
  toFun u := (u.val.z,u.val.s,u.val.t)
  invFun p := ⟨involutionPoint true x y p.1 p.2.1 p.2.2,
    (class_one_coordinates _ _ _ _ _ _).mpr rfl⟩
  left_inv u := Subtype.ext ((class_one_coordinates _ _ _ _ _ _).mp u.property).symm
  right_inv _ := rfl

private theorem class_zero_card (x y z s t : F)
    [Fintype {u : S false // u ∈ powerNeighborhoodClass (involutionPoint false x y z s t)}] :
    Fintype.card {u : S false // u ∈ powerNeighborhoodClass (involutionPoint false x y z s t)} = 9 := by
  rw [Fintype.card_congr (class_zero_equiv x y z s t)]
  norm_num [Fintype.card_prod, F]

private theorem class_one_card (x y z s t : F)
    [Fintype {u : S true // u ∈ powerNeighborhoodClass (involutionPoint true x y z s t)}] :
    Fintype.card {u : S true // u ∈ powerNeighborhoodClass (involutionPoint true x y z s t)} = 27 := by
  rw [Fintype.card_congr (class_one_equiv x y z s t)]
  norm_num [Fintype.card_prod, F]

private theorem no_joint_square_cube :
    ¬ ∃ f : S false ≃ S true, ∀ p : S false,
      f (p ^ (2 : ℕ)) = (f p) ^ (2 : ℕ) ∧
      f (p ^ (3 : ℕ)) = (f p) ^ (3 : ℕ) := by
  classical
  rintro ⟨f,hf⟩
  have h₂ := fun p => (hf p).1
  have h₃ := fun p => (hf p).2
  let t₀ := involutionPoint false 0 0 0 0 0
  have ht₀ : powerInvolution t₀ := involution_point_valid false 0 0 0 0 0
  have hi := (joint_involution f h₂ t₀).mp ht₀
  have hc := (involution_coordinates true (f t₀)).mp hi
  have he : f t₀ = involutionPoint true (f t₀).x (f t₀).y (f t₀).z
      (f t₀).s (f t₀).t := by
    apply S.ext <;> simp [involutionPoint, hc.1, hc.2.1, hc.2.2]
  have hcard := joint_neighborhood_class_card f h₂ h₃ t₀
  rw [he] at hcard
  change Fintype.card {u : S false // u ∈ powerNeighborhoodClass
    (involutionPoint false 0 0 0 0 0)} = _ at hcard
  rw [class_zero_card, class_one_card] at hcard
  norm_num at hcard

/-- The fixed-pair implication refuted by the complete construction. -/
def claim : Prop :=
  (Fintype.card (S false) = 4374 ∧ Fintype.card (S true) = 4374 ∧
    ∀ m : ℤ, ∃ f : S false ≃ S true, ∀ p, f (p^m) = (f p)^m) →
  ∃ f : S false ≃ S true, ∀ p,
    f (p^(2 : ℕ)) = (f p)^(2 : ℕ) ∧ f (p^(3 : ℕ)) = (f p)^(3 : ℕ)

/-- Separate conjugacy of every integer-power map does not imply joint conjugacy. -/
theorem result : ¬ claim := by
  intro h
  exact no_joint_square_cube (h ⟨card_S false, card_S true, separate_powers⟩)

end D5.S3.FiniteGroups.PowerMaps.PowerMapSeparation
