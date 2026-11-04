/- GID: D5/S3/Combinatorics/TorusTilings/KageyKeehnRectangularTorus
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TorusTilings/KageyKeehnRectangularTorus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A rectangular-torus plane lift fixed by any of the four transposing right actions descends to the gcd square torus. -/

import Mathlib

namespace D5.S3.Combinatorics.TorusTilings.KageyKeehnRectangularTorus

set_option autoImplicit false

/- Public theorem admission:
   proof_shape: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (#23394; Proved)
   utility: none

The source-action bridge is explicit in the owning Blueprint Scribe and source
note: source r uses internal .r3, source r^3 uses .r, and rf/r^3f retain .rf/.r3f.
The source graph fixedness, translation representative, affine center and
identical-plane readout are part of that exposition. The escape audit remains
unfinished under #23394; no declared_validated registration is claimed.
-/

/- The constructors are internal coordinate maps, so their labels are kept
distinct from the source's right-action names.  The source's operational maps
are r ↦ (-y,x) (internal .r3), r^3 ↦ (y,-x) (internal .r),
rf ↦ (y,x) (internal .rf), and r^3f ↦ (-y,-x) (internal .r3f).
The arbitrary translation records both the cyclic shift and the center constants
used by finite rectangular representatives. -/
inductive RightAction
  | r
  | r3
  | rf
  | r3f
  deriving DecidableEq

def linear : RightAction → ℤ × ℤ → ℤ × ℤ
  | .r, z => (z.2, -z.1)
  | .r3, z => (-z.2, z.1)
  | .rf, z => (z.2, z.1)
  | .r3f, z => (-z.2, -z.1)

def PlaneLift {T : Type*} {g : ℕ} (H : ZMod g → ZMod g → T) : ℤ × ℤ → T :=
  fun z => H (z.1 : ZMod g) (z.2 : ZMod g)

def PlaneEquivalent {T : Type*} (F G : ℤ × ℤ → T) : Prop :=
  ∀ z, F z = G z

private def Period {T : Type*} (F : ℤ × ℤ → T) : AddSubgroup (ℤ × ℤ) where
  carrier := {p | ∀ z, F (z + p) = F z}
  zero_mem' := by intro z; simp
  add_mem' := by
    intro p q hp hq z
    calc
      F (z + (p + q)) = F ((z + p) + q) := by rw [add_assoc]
      _ = F (z + p) := hq (z + p)
      _ = F z := hp z
  neg_mem' := by
    intro p hp z
    have h := hp (z - p)
    simpa [sub_eq_add_neg, add_assoc] using h.symm

private theorem linear_add (a : RightAction) (z w : ℤ × ℤ) :
    linear a (z + w) = linear a z + linear a w := by
  cases a <;> cases z <;> cases w <;> ext <;> dsimp [linear] <;> abel

private theorem linear_surjective (a : RightAction) : Function.Surjective (linear a) := by
  intro w
  cases a with
  | r =>
      refine ⟨(-w.2, w.1), ?_⟩
      ext <;> simp [linear]
  | r3 =>
      refine ⟨(w.2, -w.1), ?_⟩
      ext <;> simp [linear]
  | rf =>
      refine ⟨(w.2, w.1), ?_⟩
      ext <;> simp [linear]
  | r3f =>
      refine ⟨(-w.2, -w.1), ?_⟩
      ext <;> simp [linear]

private theorem source_x_period {T : Type*} {n m : ℕ}
    (F : ℤ × ℤ → T) (f : ZMod n → ZMod m → T)
    (lift_eq : ∀ x y, F (x, y) = f (x : ZMod n) (y : ZMod m))
    : ((n : ℤ), 0) ∈ Period F := by
  intro z
  rcases z with ⟨x, y⟩
  rw [lift_eq, lift_eq]
  simp [Int.cast_add, ZMod.natCast_self]

private theorem source_y_period {T : Type*} {n m : ℕ}
    (F : ℤ × ℤ → T) (f : ZMod n → ZMod m → T)
    (lift_eq : ∀ x y, F (x, y) = f (x : ZMod n) (y : ZMod m))
    : (0, (m : ℤ)) ∈ Period F := by
  intro z
  rcases z with ⟨x, y⟩
  rw [lift_eq, lift_eq]
  simp [Int.cast_add, ZMod.natCast_self]

private theorem transport_period {T : Type*} (F : ℤ × ℤ → T)
    (a : RightAction) (translation : ℤ × ℤ) (rho : T → T)
    (fixed : ∀ z, F (linear a z + translation) = rho (F z))
    {p : ℤ × ℤ} (hp : p ∈ Period F) : linear a p ∈ Period F := by
  intro w
  obtain ⟨z, hz⟩ := linear_surjective a (w - translation)
  calc
    F (w + linear a p) = F (linear a (z + p) + translation) := by
      rw [linear_add, hz]
      congr 1
      ext <;> dsimp <;> abel
    _ = rho (F (z + p)) := fixed (z + p)
    _ = rho (F z) := by rw [hp z]
    _ = F (linear a z + translation) := (fixed z).symm
    _ = F w := by
      rw [hz]
      congr 1
      ext <;> dsimp <;> abel

private theorem transported_x_axis {T : Type*} (F : ℤ × ℤ → T)
    (a : RightAction) (translation : ℤ × ℤ) (rho : T → T)
    (fixed : ∀ z, F (linear a z + translation) = rho (F z))
    {n : ℕ} (hp : ((n : ℤ), (0 : ℤ)) ∈ Period F) :
      ((0 : ℤ), (n : ℤ)) ∈ Period F := by
  have h := transport_period F a translation rho fixed hp
  cases a with
  | r =>
      have hn := (Period F).neg_mem h
      simpa [linear] using hn
  | r3 => simpa [linear] using h
  | rf => simpa [linear] using h
  | r3f =>
      have hn := (Period F).neg_mem h
      simpa [linear] using hn

private theorem transported_y_axis {T : Type*} (F : ℤ × ℤ → T)
    (a : RightAction) (translation : ℤ × ℤ) (rho : T → T)
    (fixed : ∀ z, F (linear a z + translation) = rho (F z))
    {m : ℕ} (hp : ((0 : ℤ), (m : ℤ)) ∈ Period F) :
      ((m : ℤ), (0 : ℤ)) ∈ Period F := by
  have h := transport_period F a translation rho fixed hp
  cases a with
  | r => simpa [linear] using h
  | r3 =>
      have hn := (Period F).neg_mem h
      simpa [linear] using hn
  | rf => simpa [linear] using h
  | r3f =>
      have hn := (Period F).neg_mem h
      simpa [linear] using hn

private theorem gcd_axis_periods {T : Type*} (F : ℤ × ℤ → T)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hx : ((n : ℤ), (0 : ℤ)) ∈ Period F) (hy : ((m : ℤ), (0 : ℤ)) ∈ Period F)
    (hx' : ((0 : ℤ), (n : ℤ)) ∈ Period F) (hy' : ((0 : ℤ), (m : ℤ)) ∈ Period F) :
    (((Nat.gcd n m : ℤ), (0 : ℤ)) ∈ Period F) ∧
      (((0 : ℤ), (Nat.gcd n m : ℤ)) ∈ Period F) := by
  have bez := Nat.gcd_eq_gcd_ab n m
  have hfirst : ((Nat.gcd n m : ℤ), (0 : ℤ)) =
      Nat.gcdA n m • ((n : ℤ), (0 : ℤ)) + Nat.gcdB n m • ((m : ℤ), (0 : ℤ)) := by
    ext <;> simp [Prod.smul_mk, smul_eq_mul, bez] <;> ring
  have hsecond : ((0 : ℤ), (Nat.gcd n m : ℤ)) =
      Nat.gcdA n m • ((0 : ℤ), (n : ℤ)) + Nat.gcdB n m • ((0 : ℤ), (m : ℤ)) := by
    ext <;> simp [Prod.smul_mk, smul_eq_mul, bez] <;> ring
  constructor
  · rw [hfirst]
    exact (Period F).add_mem ((Period F).zsmul_mem hx (Nat.gcdA n m))
      ((Period F).zsmul_mem hy (Nat.gcdB n m))
  · rw [hsecond]
    exact (Period F).add_mem ((Period F).zsmul_mem hx' (Nat.gcdA n m))
      ((Period F).zsmul_mem hy' (Nat.gcdB n m))

private theorem period_difference {T : Type*} (F : ℤ × ℤ → T)
    {g : ℕ} (hx : ((g : ℤ), 0) ∈ Period F) (hy : (0, (g : ℤ)) ∈ Period F)
    {x x₀ y y₀ : ℤ} (dx : (g : ℤ) ∣ x₀ - x) (dy : (g : ℤ) ∣ y₀ - y) :
    (x₀ - x, y₀ - y) ∈ Period F := by
  obtain ⟨qx, hqx⟩ := dx
  obtain ⟨qy, hqy⟩ := dy
  have hvec : (x₀ - x, y₀ - y) =
      qx • ((g : ℤ), 0) + qy • (0, (g : ℤ)) := by
    ext <;> simp [smul_eq_mul, hqx, hqy, mul_comm]
  rw [hvec]
  exact (Period F).add_mem ((Period F).zsmul_mem hx qx)
    ((Period F).zsmul_mem hy qy)

/-- Every source rectangular torus whose literal decorated plane is fixed by one
of the four transposing right actions has the same plane as a genuine gcd-square
torus.  The translation is arbitrary, so the source's cyclic shifts and affine
center constants are both included. -/
theorem rectangular_torus_gcd_descent {T : Type*} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (f : ZMod n → ZMod m → T) (F : ℤ × ℤ → T)
    (lift_eq : ∀ x y, F (x, y) = f (x : ZMod n) (y : ZMod m))
    (a : RightAction) (shift center : ℤ × ℤ) (rho : T → T)
    (fixed : ∀ z, F (linear a (z + shift) + center) = rho (F z)) :
    ∃ H : ZMod (Nat.gcd n m) → ZMod (Nat.gcd n m) → T,
      0 < Nat.gcd n m ∧ PlaneEquivalent F (PlaneLift H) := by
  let P := Period F
  have hnx : ((n : ℤ), 0) ∈ P := source_x_period F f lift_eq
  have hmy : (0, (m : ℤ)) ∈ P := source_y_period F f lift_eq
  have fixed' : ∀ z, F (linear a z + (linear a shift + center)) = rho (F z) := by
    intro z
    calc
      F (linear a z + (linear a shift + center)) =
          F (linear a (z + shift) + center) := by rw [linear_add, add_assoc]
      _ = rho (F z) := fixed z
  have hny : (0, (n : ℤ)) ∈ P :=
    transported_x_axis F a (linear a shift + center) rho fixed' hnx
  have hmx : ((m : ℤ), 0) ∈ P :=
    transported_y_axis F a (linear a shift + center) rho fixed' hmy
  have haxes := gcd_axis_periods F hn hm hnx hmx hny hmy
  have hg : 0 < Nat.gcd n m := Nat.gcd_pos_of_pos_left m hn
  let H : ZMod (Nat.gcd n m) → ZMod (Nat.gcd n m) → T := fun u v =>
    F (ZMod.cast u, ZMod.cast v)
  refine ⟨H, hg, ?_⟩
  intro z
  rcases z with ⟨x, y⟩
  let x₀ : ℤ := ZMod.cast (x : ZMod (Nat.gcd n m))
  let y₀ : ℤ := ZMod.cast (y : ZMod (Nat.gcd n m))
  have hxcast : (x : ZMod (Nat.gcd n m)) = (x₀ : ZMod (Nat.gcd n m)) := by
    simpa [x₀] using (ZMod.intCast_zmod_cast (x : ZMod (Nat.gcd n m))).symm
  have hycast : (y : ZMod (Nat.gcd n m)) = (y₀ : ZMod (Nat.gcd n m)) := by
    simpa [y₀] using (ZMod.intCast_zmod_cast (y : ZMod (Nat.gcd n m))).symm
  have dx : ((Nat.gcd n m : ℤ) ∣ x₀ - x) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact hxcast
  have dy : ((Nat.gcd n m : ℤ) ∣ y₀ - y) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact hycast
  have hd := period_difference F haxes.1 haxes.2 dx dy (x := x) (x₀ := x₀)
      (y := y) (y₀ := y₀)
  have heq := hd (x, y)
  change F (x, y) = H (x : ZMod (Nat.gcd n m)) (y : ZMod (Nat.gcd n m))
  dsimp [H]
  rw [← heq]
  congr 1
  ext <;> dsimp [x₀, y₀] <;> ring

end D5.S3.Combinatorics.TorusTilings.KageyKeehnRectangularTorus
