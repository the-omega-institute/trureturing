/- GID: D5/S3/Quantum/Transport/FibonacciHistoryImage
   generality: I
   mirror-B: D5/B/S3/Quantum/Transport/FibonacciHistoryImage
   mirror-E: none(waiver:unbounded-symbolic-transport)
   anchors: []
   utility: none
   digest: Every native Fibonacci carry image obeys the complete Fibonacci and golden-power bounds. -/

import D5.S3.Quantum.Transport.FibonacciPrefix
import D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Order.CountableDenseLinearOrder

/-!+# All-point Fibonacci histories

Native carries are reconstructed from integer layers of the real Fibonacci
evolution. A simultaneous positive perturbation preserves every finite floor
vector and realizes it away from the layers, including histories based at seams.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Quantum.Transport.FibonacciHistoryImage

open D5.S3.Quantum.Transport.FibonacciPrefix
open D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra (fibonacci carry)
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step)
open D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling (iterate_first iterate_second)

/-- The canonical unit-square representative of an actual modular state. -/
def normalizedState (d : ℕ) (a : ZMod d × ZMod d) : ℝ × ℝ :=
  ((a.1.val : ℝ) / d, (a.2.val : ℝ) / d)

/-- The first coordinate of the unquotiented real Fibonacci evolution. -/
def linearLayer (m : ℕ) (z : ℝ × ℝ) : ℝ := (step^[m] z).1

/-- Integer-layer reconstruction of the complete one-sided carry word. -/
def layerHistory (N : ℕ) (z : ℝ × ℝ) : Fin N → ℕ := fun j =>
  (⌊linearLayer (j.val + 2) z⌋ - ⌊linearLayer j.val z⌋ -
    ⌊linearLayer (j.val + 1) z⌋).toNat

private theorem layer_formula (m : ℕ) (z : ℝ × ℝ) :
    linearLayer m z = if m = 0 then z.1 else
      (Nat.fib (m - 1) : ℝ) * z.1 + (Nat.fib m : ℝ) * z.2 := by
  by_cases hm : m = 0
  · subst m; simp [linearLayer]
  · simpa [linearLayer, hm] using iterate_first m (by omega) z

private theorem layer_translate (m : ℕ) (z : ℝ × ℝ) (t : ℝ) :
    linearLayer m (z.1 + t, z.2 + t) =
      linearLayer m z + t * linearLayer m (1, 1) := by
  rw [layer_formula, layer_formula, layer_formula]
  split_ifs <;> ring

private theorem layer_weight_pos (m : ℕ) : 0 < linearLayer m (1, 1) := by
  rw [layer_formula]
  split_ifs with hm
  · norm_num
  · have hf : 0 < (Nat.fib m : ℝ) := by exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < m)
    have hg : 0 ≤ (Nat.fib (m - 1) : ℝ) := Nat.cast_nonneg _
    nlinarith

private theorem layer_normalized (d m : ℕ) (a : ZMod d × ZMod d) :
    linearLayer m (normalizedState d a) =
      (((step^[m] (a.1.val, a.2.val)).1 : ℕ) : ℝ) / d := by
  by_cases hm : m = 0
  · subst m; simp [linearLayer, normalizedState]
  · rw [layer_formula, if_neg hm, iterate_first m (by omega)]
    simp only [normalizedState, Nat.cast_id, Nat.cast_add, Nat.cast_mul]
    ring

private theorem native_layer_floor (d : ℕ) [NeZero d]
    (a : ZMod d × ZMod d) (m : ℕ) :
    (lowTrajectory d m a).1.val = (step^[m] (a.1.val, a.2.val)).1 % d ∧
    ⌊linearLayer m (normalizedState d a)⌋ =
      ((step^[m] (a.1.val, a.2.val)).1 / d : ℕ) := by
  have hs : Function.Semiconj
      (fun p : ℕ × ℕ => ((p.1 : ZMod d), (p.2 : ZMod d))) step step := by
    intro p
    simp [step]
  have ht := hs.iterate_right m (a.1.val, a.2.val)
  have hlow : lowTrajectory d m a =
      (((step^[m] (a.1.val, a.2.val)).1 : ZMod d),
       ((step^[m] (a.1.val, a.2.val)).2 : ZMod d)) := by
    rw [low_power, Equiv.Perm.coe_pow]
    change step^[m] a = _
    simpa using ht.symm
  constructor
  · rw [hlow, ZMod.val_natCast]
  · rw [layer_normalized]
    have hn : 0 ≤ (((step^[m] (a.1.val, a.2.val)).1 : ℕ) : ℝ) / d := by positivity
    rw [← Int.natCast_floor_eq_floor hn, Nat.floor_div_eq_div]

private theorem native_carry_layers (d : ℕ) [NeZero d]
    (a : ZMod d × ZMod d) (j : ℕ) :
    (carryHistory d a j : ℤ) =
      ⌊linearLayer (j + 2) (normalizedState d a)⌋ -
        ⌊linearLayer j (normalizedState d a)⌋ -
        ⌊linearLayer (j + 1) (normalizedState d a)⌋ := by
  let u := (step^[j] (a.1.val, a.2.val)).1
  let v := (step^[j] (a.1.val, a.2.val)).2
  have hu := native_layer_floor d a j
  have hv := native_layer_floor d a (j + 1)
  have hw := native_layer_floor d a (j + 2)
  have hv' : (step^[j + 1] (a.1.val, a.2.val)).1 = v := by
    simp [v, Function.iterate_succ_apply', step]
  have hw' : (step^[j + 2] (a.1.val, a.2.val)).1 = u + v := by
    simp [u, v, Function.iterate_succ_apply', step]
  have hlow : (lowTrajectory d j a).2.val = v % d := by
    have h := hv.1
    rw [hv'] at h
    simpa only [lowTrajectory, Equiv.trans_apply, fibonacci, Equiv.coe_fn_mk] using h
  rw [hu.2, hv.2, hw.2, hv', hw']
  change ((((lowTrajectory d j a).1.val + (lowTrajectory d j a).2.val) / d : ℕ) : ℤ) = _
  rw [hu.1, hlow]
  have hdiv : (u + v) / d = u / d + v / d + (u % d + v % d) / d := by
    rw [Nat.add_div (NeZero.pos d)]
    by_cases h : d ≤ u % d + v % d
    · have hrem : (u % d + v % d) / d = 1 :=
        Nat.div_eq_of_lt_le (k := 1) (by simpa using h) (by
        have hu := Nat.mod_lt u (NeZero.pos d)
        have hv := Nat.mod_lt v (NeZero.pos d)
        omega)
      rw [if_pos h, hrem]
    · have hrem : (u % d + v % d) / d = 0 := Nat.div_eq_of_lt (by omega)
      rw [if_neg h, hrem]
  change ((u % d + v % d) / d : ℕ) =
    (((u + v) / d : ℕ) : ℤ) - ((u / d : ℕ) : ℤ) - ((v / d : ℕ) : ℤ)
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hdiv
  push_cast at hcast
  omega

private theorem positive_finite_margin {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i ∈ s, t < r i := by
  classical
  obtain ⟨t, ht, htr⟩ := Order.exists_between_finsets ({0} : Finset ℝ) (s.image r)
    (by
      intro x hx y hy
      obtain rfl := Finset.mem_singleton.mp hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact hr i hi)
  exact ⟨t, ht 0 (Finset.mem_singleton_self 0),
    fun i hi => htr (r i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)⟩

private theorem strict_layer_realization (N : ℕ) (z : ℝ × ℝ)
    (hx : 0 ≤ z.1 ∧ z.1 < 1) (hy : 0 ≤ z.2 ∧ z.2 < 1) :
    ∃ w : ℝ × ℝ, (0 < w.1 ∧ w.1 < 1) ∧ (0 < w.2 ∧ w.2 < 1) ∧
      (∀ m < N + 2, ⌊linearLayer m w⌋ = ⌊linearLayer m z⌋ ∧
        0 < Int.fract (linearLayer m w)) := by
  let r : Fin (N + 2) ⊕ Bool → ℝ := fun i => match i with
    | .inl m => ((⌊linearLayer m z⌋ : ℝ) + 1 - linearLayer m z) /
        linearLayer m (1, 1)
    | .inr false => 1 - z.1
    | .inr true => 1 - z.2
  have hr : ∀ i : Fin (N + 2) ⊕ Bool, 0 < r i := by
    intro i
    rcases i with m | b
    · exact div_pos (sub_pos.mpr (Int.lt_floor_add_one _)) (layer_weight_pos m)
    · cases b <;> dsimp [r] <;> linarith
  obtain ⟨t, ht, htr⟩ := positive_finite_margin Finset.univ r (by simpa using hr)
  have htx : t < 1 - z.1 := htr (.inr false) (Finset.mem_univ _)
  have hty : t < 1 - z.2 := htr (.inr true) (Finset.mem_univ _)
  refine ⟨(z.1 + t, z.2 + t), ⟨by dsimp; linarith, by dsimp; linarith⟩,
    ⟨by dsimp; linarith, by dsimp; linarith⟩, ?_⟩
  intro m hm
  have hm' : t < ((⌊linearLayer m z⌋ : ℝ) + 1 - linearLayer m z) /
      linearLayer m (1, 1) := htr (.inl ⟨m, hm⟩) (Finset.mem_univ _)
  have htm := (lt_div_iff₀ (layer_weight_pos m)).mp hm'
  have hpos := mul_pos ht (layer_weight_pos m)
  have hlo := Int.floor_le (linearLayer m z)
  have heq : ⌊linearLayer m (z.1 + t, z.2 + t)⌋ = ⌊linearLayer m z⌋ := by
    apply Int.floor_eq_iff.mpr
    rw [layer_translate]
    constructor <;> linarith
  refine ⟨heq, ?_⟩
  rw [Int.fract, heq, layer_translate]
  linarith

/-- Every canonical modular prefix is an integer-layer history, and the same
word occurs strictly inside the unit square away from all its integer layers. -/
theorem native_history_interior_realization (d N : ℕ) (hd : 2 ≤ d)
    (a : ZMod d × ZMod d) :
    (∀ j : ℕ, (carryHistory d a j : ℤ) =
      ⌊linearLayer (j + 2) (normalizedState d a)⌋ -
        ⌊linearLayer j (normalizedState d a)⌋ -
        ⌊linearLayer (j + 1) (normalizedState d a)⌋) ∧
    carryPrefix d N a = layerHistory N (normalizedState d a) ∧
    ∃ w : ℝ × ℝ, (0 < w.1 ∧ w.1 < 1) ∧ (0 < w.2 ∧ w.2 < 1) ∧
      (∀ m < N + 2, ⌊linearLayer m w⌋ = ⌊linearLayer m (normalizedState d a)⌋ ∧
        0 < Int.fract (linearLayer m w)) ∧
      carryPrefix d N a = layerHistory N w := by
  letI : NeZero d := ⟨by omega⟩
  have hc := native_carry_layers d a
  have hp : carryPrefix d N a = layerHistory N (normalizedState d a) := by
    funext j
    change carryHistory d a j =
      (⌊linearLayer (j.val + 2) (normalizedState d a)⌋ -
        ⌊linearLayer j.val (normalizedState d a)⌋ -
        ⌊linearLayer (j.val + 1) (normalizedState d a)⌋).toNat
    rw [← hc j, Int.toNat_natCast]
  have hx : 0 ≤ (normalizedState d a).1 ∧ (normalizedState d a).1 < 1 := by
    dsimp [normalizedState]
    constructor
    · positivity
    · exact (div_lt_one (by positivity)).mpr (by exact_mod_cast a.1.val_lt)
  have hy : 0 ≤ (normalizedState d a).2 ∧ (normalizedState d a).2 < 1 := by
    dsimp [normalizedState]
    constructor
    · positivity
    · exact (div_lt_one (by positivity)).mpr (by exact_mod_cast a.2.val_lt)
  obtain ⟨w, hwx, hwy, hw⟩ := strict_layer_realization N (normalizedState d a) hx hy
  refine ⟨hc, hp, w, hwx, hwy, hw, ?_⟩
  rw [hp]
  funext j
  dsimp [layerHistory]
  rw [(hw (j.val + 2) (by omega)).1, (hw j.val (by omega)).1,
    (hw (j.val + 1) (by omega)).1]


private theorem corner_exists {ι : Type} [Fintype ι] [DecidableEq ι]
    (o : ι) (r l u : ι → ℝ) (hr0 : r o = 0) (hl0 : l o = 0) (hu0 : u o = 1)
    (w : ℝ × ℝ) (hwx : 0 < w.1 ∧ w.1 < 1)
    (hw : ∀ i, l i - r i * w.1 < w.2 ∧ w.2 < u i - r i * w.1) :
    ∃ x y : ℝ, (0 ≤ x ∧ x < 1) ∧ (0 ≤ y ∧ y ≤ 1) ∧
      (∀ i, l i - r i * x ≤ y ∧ y ≤ u i - r i * x) ∧
      ((x = 0 ∧ (∃ i, y = l i - r i * x) ∧ ∀ i, y < u i - r i * x) ∨
       ∃ i j, y = l i - r i * x ∧ y = u j - r j * x ∧ r j < r i ∧
         (∀ k, y = l k - r k * x → r i ≤ r k) ∧
         (∀ k, y = u k - r k * x → r k ≤ r j)) := by
  classical
  let layerPairCount : Finset (ι × ι) := Finset.univ.filter (fun ij => r ij.2 < r ij.1)
  let cross : ι × ι → ℝ := fun ij => (l ij.1 - u ij.2) / (r ij.1 - r ij.2)
  let cuts : Finset ℝ := insert 0 (layerPairCount.image cross)
  have hcne : cuts.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  let x := cuts.max' hcne
  have hxmem : x ∈ cuts := Finset.max'_mem _ _
  have hx0 : 0 ≤ x := Finset.le_max' cuts 0 (Finset.mem_insert_self _ _)
  have hxcross (i j : ι) (h : r j < r i) : cross (i,j) ≤ x := by
    apply Finset.le_max' cuts
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
  have hxw : x < w.1 := by
    rcases Finset.mem_insert.mp hxmem with hz | hz
    · exact hz ▸ hwx.1
    · obtain ⟨⟨i,j⟩, hij, heq⟩ := Finset.mem_image.mp hz
      have hrij : r j < r i := (Finset.mem_filter.mp hij).2
      rw [← heq]
      dsimp [cross]
      apply (div_lt_iff₀ (sub_pos.mpr hrij)).mpr
      have hi := hw i
      have hj := hw j
      nlinarith
  have hlu (i j : ι) : l i - r i * x ≤ u j - r j * x := by
    by_cases hrij : r j < r i
    · have hc := (div_le_iff₀ (sub_pos.mpr hrij)).mp (hxcross i j hrij)
      nlinarith
    · have hi := hw i
      have hj := hw j
      have hr : r i ≤ r j := le_of_not_gt hrij
      have hprod := mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hxw.le)
      nlinarith
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image Finset.univ
    (fun i => l i - r i * x) ⟨o, Finset.mem_univ o⟩
  let y := l i - r i * x
  have hlo (k : ι) : l k - r k * x ≤ y := himax k (Finset.mem_univ _)
  have hup (k : ι) : y ≤ u k - r k * x := hlu i k
  have hy0 : 0 ≤ y := by simpa [hr0, hl0] using hlo o
  have hy1 : y ≤ 1 := by simpa [hr0, hu0] using hup o
  refine ⟨x, y, ⟨hx0, hxw.trans hwx.2⟩, ⟨hy0,hy1⟩,
    fun k => ⟨hlo k, hup k⟩, ?_⟩
  by_cases ha : ∃ j, y = u j - r j * x
  · let lowers := Finset.univ.filter (fun k => y = l k - r k * x)
    let uppers := Finset.univ.filter (fun k => y = u k - r k * x)
    have hln : lowers.Nonempty := ⟨i, by simp [lowers,y]⟩
    have hun : uppers.Nonempty := by
      obtain ⟨j,hj⟩ := ha
      exact ⟨j, by simp [uppers,hj]⟩
    obtain ⟨p,hp,hpmin⟩ := Finset.exists_max_image lowers (fun k => -r k) hln
    obtain ⟨q,hq,hqmax⟩ := Finset.exists_max_image uppers r hun
    have hp' : y = l p - r p * x := (Finset.mem_filter.mp hp).2
    have hq' : y = u q - r q * x := (Finset.mem_filter.mp hq).2
    have hrpq : r q < r p := by
      by_contra hn
      have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn))
        (sub_nonneg.mpr hxw.le)
      have hpw := hw p
      have hqw := hw q
      nlinarith
    right
    refine ⟨p,q,hp',hq',hrpq,?_,?_⟩
    · intro k hk
      have h := hpmin k (by simp [lowers,hk])
      linarith
    · intro k hk
      exact hqmax k (by simp [uppers,hk])
  · have hstrict (k : ι) : y < u k - r k * x :=
      lt_of_le_of_ne (hup k) (fun h => ha ⟨k,h⟩)
    left
    refine ⟨?_, ⟨i,rfl⟩, hstrict⟩
    rcases Finset.mem_insert.mp hxmem with hz | hz
    · exact hz
    · obtain ⟨⟨p,q⟩, hpq, heq⟩ := Finset.mem_image.mp hz
      have hrpq : r q < r p := (Finset.mem_filter.mp hpq).2
      have hx : x * (r p - r q) = l p - u q := by
        rw [← heq]
        exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hrpq))
      have hpl := hlo p
      have hqu := hstrict q
      nlinarith


private theorem floor_decoder (v r p q : ℝ) (k : ℤ) (hpq : q < p)
    (hv : (k:ℝ) ≤ v ∧ v ≤ (k:ℝ)+1)
    (hl : v = k → p ≤ r) (hu : v = (k:ℝ)+1 → r ≤ q) :
    k = ⌊v⌋ - if r < (p+q)/2 ∧ Int.fract v = 0 then 1 else 0 := by
  by_cases he : v = (k:ℝ)+1
  · have hf : ⌊v⌋ = k+1 := by simp [he]
    have hg : Int.fract v = 0 := by rw [he]; simp [Int.fract]
    have hr := hu he
    rw [hf,if_pos ⟨by linarith,hg⟩]
    omega
  · have hf : ⌊v⌋ = k := Int.floor_eq_iff.mpr ⟨hv.1, lt_of_le_of_ne hv.2 he⟩
    have hn : ¬ (r < (p+q)/2 ∧ Int.fract v = 0) := by
      rintro ⟨hr,hv0⟩
      have hve : v = k := by simpa [Int.fract,hf,sub_eq_zero] using hv0
      have h := hl hve
      linarith
    rw [hf,if_neg hn,sub_zero]


private abbrev Circle := AddCircle (1 : ℝ)
private def torus (z : ℝ × ℝ) : Circle × Circle := (z.1,z.2)
private def Corners (i j : ℕ) : Set (ℝ × ℝ) :=
  {z | (0 ≤ z.1 ∧ z.1 < 1) ∧ (0 ≤ z.2 ∧ z.2 ≤ 1) ∧
    (∃ k : ℤ, linearLayer i z = k) ∧ (∃ k : ℤ, linearLayer j z = k)}

private theorem torus_iter (n : ℕ) (z : ℝ × ℝ) :
    torus (step^[n] z) = step^[n] (torus z) := by
  have h : Function.Semiconj torus step step := by intro z; simp [torus,step]
  exact h.iterate_right n z

private theorem layer_torus (n : ℕ) (z : ℝ × ℝ) :
    (linearLayer n z : Circle) = (step^[n] (torus z)).1 := by
  exact congrArg Prod.fst (torus_iter n z)

private theorem step_injective {A : Type*} [AddCommGroup A] :
    Function.Injective (step : A × A → A × A) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp [step] at h1 h2
  exact Prod.ext (by rw [h1] at h2; exact add_right_cancel h2) h1

private theorem step_zero (n : ℕ) (t : Circle) :
    step^[n] (0,t) = (Nat.fib n • t, Nat.fib (n+1) • t) := by
  let f : ℕ × ℕ → Circle × Circle := fun p => (p.1 • t, p.2 • t)
  have h : Function.Semiconj f step step := by
    intro p
    simp [f, step, add_nsmul]
  have hfirst : (step^[n] ((0, 1) : ℕ × ℕ)).1 = Nat.fib n := by
    by_cases hn : n = 0
    · subst n; simp
    · simpa using iterate_first n (by omega) ((0, 1) : ℕ × ℕ)
  have hsecond : (step^[n] ((0, 1) : ℕ × ℕ)).2 = Nat.fib (n+1) := by
    simpa using iterate_second n ((0, 1) : ℕ × ℕ)
  simpa [f, hfirst, hsecond] using (h.iterate_right n (0, 1)).symm

private theorem corner_torsion (i j : ℕ) (hij : i < j) (z : Corners i j) :
    Nat.fib (j-i) • (step^[i] (torus z.val)).2 = 0 := by
  obtain ⟨ki,hki⟩ := z.property.2.2.1
  obtain ⟨kj,hkj⟩ := z.property.2.2.2
  have hi : (step^[i] (torus z.val)).1 = 0 := by
    rw [← layer_torus,hki]
    simp
  have hj : (step^[j] (torus z.val)).1 = 0 := by
    rw [← layer_torus,hkj]
    simp
  have ht : step^[j-i] (step^[i] (torus z.val)) = step^[j] (torus z.val) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  have he : step^[i] (torus z.val) = (0,(step^[i] (torus z.val)).2) :=
    Prod.ext hi rfl
  rw [he,step_zero] at ht
  exact (congrArg Prod.fst ht).trans hj

private theorem corner_code_injective (i j : ℕ) :
    Function.Injective (fun z : Corners i j =>
      ((step^[i] (torus z.val)).2, decide (z.val.2 = 1))) := by
  intro z w h
  have hs := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  obtain ⟨kz,hkz⟩ := z.property.2.2.1
  obtain ⟨kw,hkw⟩ := w.property.2.2.1
  have hz : (step^[i] (torus z.val)).1 = 0 := by
    rw [← layer_torus,hkz]
    simp
  have hw : (step^[i] (torus w.val)).1 = 0 := by
    rw [← layer_torus,hkw]
    simp
  have ht : torus z.val = torus w.val :=
    (step_injective.iterate i) (Prod.ext (hz.trans hw.symm) hs)
  apply Subtype.ext
  apply Prod.ext
  · exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (by simpa using z.property.1 : z.val.1 ∈ Set.Ico (0:ℝ) (0+1))
      (by simpa using w.property.1 : w.val.1 ∈ Set.Ico (0:ℝ) (0+1))).mp
      (congrArg Prod.fst ht)
  · have he : (z.val.2 = 1) ↔ (w.val.2 = 1) := decide_eq_decide.mp hb
    by_cases hz1 : z.val.2 = 1
    · exact hz1.trans (he.mp hz1).symm
    · have hw1 : w.val.2 ≠ 1 := fun h => hz1 (he.mpr h)
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (by constructor; exact z.property.2.1.1; simpa using lt_of_le_of_ne z.property.2.1.2 hz1)
        (by constructor; exact w.property.2.1.1; simpa using lt_of_le_of_ne w.property.2.1.2 hw1)).mp
        (congrArg Prod.snd ht)

private theorem corner_count (i j : ℕ) (hij : i < j) :
    (Corners i j).encard ≤ 2 * Nat.fib (j-i) := by
  let f : Corners i j → {t : Circle | Nat.fib (j-i) • t = 0} × Bool :=
    fun z => (⟨(step^[i] (torus z.val)).2, corner_torsion i j hij z⟩,
      decide (z.val.2 = 1))
  have hf : Function.Injective f := by
    intro z w h
    apply corner_code_injective i j
    exact Prod.ext (by simpa [f] using congrArg (fun p : {t : Circle | Nat.fib (j-i) • t = 0} × Bool => p.1.val) h) (by simpa [f] using congrArg (fun p : {t : Circle | Nat.fib (j-i) • t = 0} × Bool => p.2) h)
  have hc := ENat.card_le_card_of_injective hf
  have hn : Nat.fib (j-i) ≠ 0 := Nat.ne_of_gt (Nat.fib_pos.mpr (by omega))
  have hreg : IsSMulRegular ℝ (Nat.fib (j-i)) :=
    .of_right_eq_zero_of_smul (fun x hx => by
      have : (Nat.fib (j-i) : ℝ) ≠ 0 := by exact_mod_cast hn
      simpa [nsmul_eq_mul,this] using hx)
  have hb := AddCircle.card_torsion_le_of_isSMulRegular (1:ℝ) _ hn hreg
  rw [ENat.card_prod] at hc
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_bool] at hc
  exact hc.trans (by simpa [mul_comm] using mul_le_mul_right hb 2)


private def layerXCoefficient (m : ℕ) : ℝ := Nat.fib (m-1)
private def layerYCoefficient (m : ℕ) : ℝ := Nat.fib m
private def layerSlope (m : ℕ) : ℝ := layerXCoefficient m / layerYCoefficient m

private def correctedFloor (i j m : ℕ) (z : ℝ × ℝ) : ℤ :=
  if i = 0 then ⌊linearLayer m z⌋ else
  ⌊linearLayer m z⌋ - if m ≠ 0 ∧ layerSlope m < (layerSlope i + layerSlope j)/2 ∧
    Int.fract (linearLayer m z) = 0 then 1 else 0

private def decode (N i j : ℕ) (z : ℝ × ℝ) : Fin N → ℕ := fun k =>
  (correctedFloor i j (k.val+2) z - correctedFloor i j k.val z -
    correctedFloor i j (k.val+1) z).toNat

private theorem positive_layer_formula (m : ℕ) (hm : 0 < m) (z : ℝ × ℝ) :
    linearLayer m z = layerXCoefficient m * z.1 + layerYCoefficient m * z.2 := by
  simpa [layerXCoefficient,layerYCoefficient,if_neg (by omega : m ≠ 0)] using layer_formula m z

private theorem scaled_strict (a b k x y : ℝ) (hb : 0 < b) :
    (k / b - a / b * x < y ∧ y < (k+1) / b - a / b * x) ↔
    (k < a*x+b*y ∧ a*x+b*y < k+1) := by
  have h1 : b * (k / b - a / b * x) = k-a*x := by field_simp
  have h2 : b * ((k+1) / b - a / b * x) = k+1-a*x := by field_simp
  constructor
  · rintro ⟨hl,hu⟩
    have hl' := mul_lt_mul_of_pos_left hl hb
    have hu' := mul_lt_mul_of_pos_left hu hb
    rw [h1] at hl'
    rw [h2] at hu'
    constructor <;> linarith
  · rintro ⟨hl,hu⟩
    constructor
    · apply (mul_lt_mul_iff_right₀ hb).mp
      rw [h1]
      linarith
    · apply (mul_lt_mul_iff_right₀ hb).mp
      rw [h2]
      linarith

private theorem scaled_closed (a b k x y : ℝ) (hb : 0 < b) :
    (k / b - a / b * x ≤ y ∧ y ≤ (k+1) / b - a / b * x) ↔
    (k ≤ a*x+b*y ∧ a*x+b*y ≤ k+1) := by
  have h1 : b * (k / b - a / b * x) = k-a*x := by field_simp
  have h2 : b * ((k+1) / b - a / b * x) = k+1-a*x := by field_simp
  constructor
  · rintro ⟨hl,hu⟩
    have hl' := mul_le_mul_of_nonneg_left hl hb.le
    have hu' := mul_le_mul_of_nonneg_left hu hb.le
    rw [h1] at hl'
    rw [h2] at hu'
    constructor <;> linarith
  · rintro ⟨hl,hu⟩
    constructor
    · apply (mul_le_mul_iff_right₀ hb).mp
      rw [h1]
      linarith
    · apply (mul_le_mul_iff_right₀ hb).mp
      rw [h2]
      linarith

private theorem native_corner_exists (N : ℕ) (w : ℝ × ℝ)
    (hwx : 0 < w.1 ∧ w.1 < 1) (hwy : 0 < w.2 ∧ w.2 < 1)
    (hwf : ∀ m < N+2, 0 < Int.fract (linearLayer m w)) :
    ∃ (i j : Fin (N+2)) (hij : i.val < j.val) (z : Corners i.val j.val),
      layerHistory N w = decode N i.val j.val z.val := by
  classical
  let k : ℕ → ℤ := fun m => ⌊linearLayer m w⌋
  let idx : Fin (N+1) → ℕ := fun t => t.val+1
  let r : Fin (N+1) → ℝ := fun t => layerSlope (idx t)
  let l : Fin (N+1) → ℝ := fun t => (k (idx t) : ℝ) / layerYCoefficient (idx t)
  let u : Fin (N+1) → ℝ := fun t => ((k (idx t) : ℝ)+1) / layerYCoefficient (idx t)
  have hb (t : Fin (N+1)) : 0 < layerYCoefficient (idx t) := by
    change 0 < (Nat.fib (idx t) : ℝ)
    exact_mod_cast (Nat.fib_pos.mpr (by dsimp [idx]; omega) : 0 < Nat.fib (idx t))
  have hk0 : k 0 = 0 := by
    apply Int.floor_eq_iff.mpr
    simpa [k,linearLayer] using ⟨hwx.1.le,hwx.2⟩
  have hk1 : k 1 = 0 := by
    apply Int.floor_eq_iff.mpr
    simpa [k,linearLayer,D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.step] using ⟨hwy.1.le,hwy.2⟩
  have hr0 : r (0 : Fin (N+1)) = 0 := by simp [r,layerSlope,layerXCoefficient,layerYCoefficient,idx]
  have hl0 : l (0 : Fin (N+1)) = 0 := by simp [l,idx,hk1]
  have hu0 : u (0 : Fin (N+1)) = 1 := by simp [u,idx,hk1,layerYCoefficient]
  have hstrip (t : Fin (N+1)) : l t-r t*w.1 < w.2 ∧ w.2 < u t-r t*w.1 := by
    apply (scaled_strict (layerXCoefficient (idx t)) (layerYCoefficient (idx t)) (k (idx t)) w.1 w.2 (hb t)).mpr
    rw [← positive_layer_formula (idx t) (by dsimp [idx]; omega)]
    have hf := hwf (idx t) (by have := t.isLt; dsimp [idx]; omega)
    have hlo := Int.floor_le (linearLayer (idx t) w)
    have hhi := Int.lt_floor_add_one (linearLayer (idx t) w)
    constructor
    · rw [Int.fract] at hf
      dsimp [k]
      linarith
    · exact hhi
  obtain ⟨x,y,hx,hy,hclosed,hcase⟩ := corner_exists (0 : Fin (N+1)) r l u hr0 hl0 hu0 w hwx hstrip
  let z : ℝ × ℝ := (x,y)
  have hbounds (t : Fin (N+1)) : (k (idx t) : ℝ) ≤ linearLayer (idx t) z ∧
      linearLayer (idx t) z ≤ (k (idx t) : ℝ)+1 := by
    rw [positive_layer_formula (idx t) (by dsimp [idx]; omega)]
    exact (scaled_closed _ _ _ _ _ (hb t)).mp (hclosed t)
  have heql (t : Fin (N+1)) : y = l t-r t*x ↔ linearLayer (idx t) z = (k (idx t) : ℝ) := by
    rw [positive_layer_formula (idx t) (by dsimp [idx]; omega)]
    have h1 : layerYCoefficient (idx t) * (l t-r t*x) = (k (idx t):ℝ)-layerXCoefficient (idx t)*x := by
      dsimp [l,r,layerSlope]
      field_simp [ne_of_gt (hb t)]
    constructor
    · intro he; rw [← he] at h1; dsimp [z]; linarith
    · intro he; dsimp [z] at he
      apply (mul_right_inj' (ne_of_gt (hb t))).mp
      linarith
  have hequ (t : Fin (N+1)) : y = u t-r t*x ↔ linearLayer (idx t) z = (k (idx t) : ℝ)+1 := by
    rw [positive_layer_formula (idx t) (by dsimp [idx]; omega)]
    have h1 : layerYCoefficient (idx t) * (u t-r t*x) = (k (idx t):ℝ)+1-layerXCoefficient (idx t)*x := by
      dsimp [u,r,layerSlope]
      field_simp [ne_of_gt (hb t)]
    constructor
    · intro he; rw [← he] at h1; dsimp [z]; linarith
    · intro he; dsimp [z] at he
      apply (mul_right_inj' (ne_of_gt (hb t))).mp
      linarith
  rcases hcase with ⟨hx0,⟨p,hp⟩,hu⟩ | ⟨p,q,hp,hq,hpq,hpl,hqu⟩
  · have hall (m : ℕ) (hm : m < N+2) : k m = ⌊linearLayer m z⌋ := by
      by_cases hm0 : m = 0
      · subst m
        simp [linearLayer,z,hx0,hk0]
      · let t : Fin (N+1) := ⟨m-1, by omega⟩
        have htm : idx t = m := by dsimp [idx,t]; omega
        have hc := hbounds t
        have hstrict : linearLayer (idx t) z < (k (idx t):ℝ)+1 := by
          apply lt_of_le_of_ne hc.2
          exact fun h => (ne_of_lt (hu t)) ((hequ t).mpr h)
        rw [htm] at hc hstrict
        exact (Int.floor_eq_iff.mpr ⟨hc.1,hstrict⟩).symm
    have hz : z ∈ Corners 0 (idx p) := by
      refine ⟨hx,hy,⟨0,?_⟩,⟨k (idx p),(heql p).mp hp⟩⟩
      simp [linearLayer,z,hx0]
    refine ⟨⟨0,by omega⟩,⟨idx p,by have := p.isLt; dsimp [idx]; omega⟩,by dsimp [idx]; omega,⟨z,hz⟩,?_⟩
    funext t
    dsimp [layerHistory,decode,correctedFloor]
    rw [← hall (t.val+2) (by omega),← hall t.val (by omega),← hall (t.val+1) (by omega)]
  · have hneq : idx p ≠ idx q := by
      intro h
      have : p = q := by apply Fin.ext; dsimp [idx] at h; omega
      subst q
      exact (lt_irrefl _ hpq)
    let i := min (idx p) (idx q)
    let j := max (idx p) (idx q)
    have hij : i < j := by dsimp [i,j]; omega
    have hi0 : i ≠ 0 := by dsimp [i,idx]; omega
    have hsum : layerSlope i + layerSlope j = r p+r q := by
      dsimp [i,j]
      rcases le_total (idx p) (idx q) with h | h
      · simp [min_eq_left h,max_eq_right h,r]
      · simp [min_eq_right h,max_eq_left h,r,add_comm]
    have hz : z ∈ Corners i j := by
      have hpz : ∃ v : ℤ, linearLayer (idx p) z = v := ⟨k (idx p),(heql p).mp hp⟩
      have hqz : ∃ v : ℤ, linearLayer (idx q) z = v := ⟨k (idx q)+1,by exact_mod_cast (hequ q).mp hq⟩
      refine ⟨hx,hy,?_,?_⟩ <;> dsimp [i,j] <;>
        rcases le_total (idx p) (idx q) with h | h
      · simpa [min_eq_left h] using hpz
      · simpa [min_eq_right h] using hqz
      · simpa [max_eq_right h] using hqz
      · simpa [max_eq_left h] using hpz
    have hall (m : ℕ) (hm : m < N+2) : k m = correctedFloor i j m z := by
      rw [correctedFloor,if_neg hi0]
      by_cases hm0 : m = 0
      · subst m
        have hxf : ⌊x⌋ = (0:ℤ) := Int.floor_eq_iff.mpr (by simpa using hx)
        simp [hk0,linearLayer,z,hxf]
      · let t : Fin (N+1) := ⟨m-1,by omega⟩
        have htm : idx t = m := by dsimp [idx,t]; omega
        have hf := floor_decoder (linearLayer (idx t) z) (r t) (r p) (r q)
          (k (idx t)) hpq (hbounds t)
          (fun h => hpl t ((heql t).mpr h)) (fun h => hqu t ((hequ t).mpr h))
        rw [htm] at hf
        simpa [r,htm,hsum,hm0] using hf
    refine ⟨⟨i,by dsimp [i,idx]; have := p.isLt; have := q.isLt; omega⟩,
      ⟨j,by dsimp [j,idx]; have := p.isLt; have := q.isLt; omega⟩,hij,⟨z,hz⟩,?_⟩
    funext t
    dsimp [layerHistory,decode]
    rw [← hall (t.val+2) (by omega),← hall t.val (by omega),← hall (t.val+1) (by omega)]


private def layerPairRow (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, Nat.fib (j-i)
private def layerPairCount (N : ℕ) : ℕ := ∑ j ∈ Finset.range (N+2), layerPairRow j

private theorem inner_formula (j : ℕ) : layerPairRow j + 1 = Nat.fib (j+2) := by
  have hs := Nat.fib_succ_eq_succ_sum (j+1)
  have he : layerPairRow j = ∑ i ∈ Finset.range j, Nat.fib (i+1) := by
    calc
      _ = ∑ i ∈ Finset.range j, Nat.fib (j-1-i+1) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        have := Finset.mem_range.mp hi
        omega
      _ = _ := Finset.sum_range_reflect (fun i => Nat.fib (i+1)) j
  rw [he]
  simpa [Finset.sum_range_succ'] using hs.symm

private theorem pairs_formula (N : ℕ) : layerPairCount N = Nat.fib (N+5)-N-4 := by
  have hrows : layerPairCount N + (N+2) =
      ∑ j ∈ Finset.range (N+2), Nat.fib (j+2) := by
    calc
      _ = ∑ j ∈ Finset.range (N+2), (layerPairRow j + 1) := by
        simp [layerPairCount, Finset.sum_add_distrib]
      _ = _ := Finset.sum_congr rfl (fun j _ => inner_formula j)
  have hs := Nat.fib_succ_eq_succ_sum (N+4)
  rw [show N+4 = (N+2)+1+1 by omega,
    Finset.sum_range_succ', Finset.sum_range_succ'] at hs
  simp only [Nat.fib_zero, Nat.fib_one, zero_add, Nat.add_assoc, Nat.reduceAdd] at hs
  omega

private theorem golden_bound (N : ℕ) :
    (((4*(Nat.fib (N+5)-N-4) : ℕ) : ℝ) ≤
      4 * ((1+Real.sqrt 5)/2)^(N+4)) ∧
    (((Nat.fib (N+5)-N-4 : ℕ) : ℝ) = (Nat.fib (N+5) : ℝ)-N-4) := by
  have hs := Nat.le_fib_self (n := N+5) (by omega)
  have hcast : (((Nat.fib (N+5)-N-4 : ℕ) : ℝ)) = (Nat.fib (N+5) : ℝ)-N-4 := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    norm_num
  have hphi := Real.goldenRatio_mul_fib_succ_add_fib (N+3)
  change Real.goldenRatio * (Nat.fib (N+4) : ℝ) + (Nat.fib (N+3) : ℝ) = Real.goldenRatio^(N+4) at hphi
  have hrec : Nat.fib (N+5) = Nat.fib (N+3)+Nat.fib (N+4) := Nat.fib_add_two
  have hmul : (Nat.fib (N+4) : ℝ) ≤ Real.goldenRatio*(Nat.fib (N+4) : ℝ) := by
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) Real.one_lt_goldenRatio.le
  have hf : (Nat.fib (N+5) : ℝ) ≤ Real.goldenRatio^(N+4) := by
    rw [hrec,Nat.cast_add]
    calc
      _ ≤ (Nat.fib (N+3) : ℝ)+Real.goldenRatio*(Nat.fib (N+4) : ℝ) := by linarith
      _ = _ := by rw [add_comm]; exact hphi
  refine ⟨?_,hcast⟩
  push_cast
  rw [hcast]
  change 4*((Nat.fib (N+5) : ℝ)-N-4) ≤ 4*Real.goldenRatio^(N+4)
  have hn : (0:ℝ) ≤ N := Nat.cast_nonneg _
  linarith


private abbrev Charge (N : ℕ) := Σ j : Fin (N+2), Σ i : Fin j.val, Corners i.val j.val

private def chargeDecode (N : ℕ) (c : Charge N) : Fin N → ℕ :=
  decode N c.2.1.val c.1.val c.2.2.val

private theorem corner_finite (i j : ℕ) (h : i < j) : Finite (Corners i j) :=
  (Set.finite_of_encard_le_coe (corner_count i j h)).to_subtype

/-- The full native image bound, its exact golden-power inequality, and the real
interpretation of the nonnegative Fibonacci subtraction. -/
theorem native_history_image_bound (d N : ℕ) (hd : 2 ≤ d) :
    (Set.range (carryPrefix d N)).Finite ∧
    (Set.range (carryPrefix d N)).ncard ≤ 4 * (Nat.fib (N+5)-N-4) ∧
    (((4 * (Nat.fib (N+5)-N-4) : ℕ) : ℝ) ≤ 4*((1+Real.sqrt 5)/2)^(N+4)) ∧
    (((Nat.fib (N+5)-N-4 : ℕ) : ℝ) = (Nat.fib (N+5) : ℝ)-N-4) := by
  classical
  letI (j : Fin (N+2)) (i : Fin j.val) : Finite (Corners i.val j.val) :=
    corner_finite i.val j.val i.isLt
  letI : Finite (Charge N) := inferInstance
  have hr : Set.range (carryPrefix d N) ⊆ Set.range (chargeDecode N) := by
    rintro word ⟨a,rfl⟩
    obtain ⟨_,_,w,hwx,hwy,hw,heq⟩ := native_history_interior_realization d N hd a
    obtain ⟨i,j,hij,z,hz⟩ := native_corner_exists N w hwx hwy (fun m hm => (hw m hm).2)
    refine ⟨⟨j,⟨⟨i.val,hij⟩,z⟩⟩,?_⟩
    exact hz.symm.trans heq.symm
  have hc : Nat.card (Charge N) ≤ 2*layerPairCount N := by
    rw [Nat.card_sigma]
    calc
      _ = ∑ j : Fin (N+2), ∑ i : Fin j.val, Nat.card (Corners i.val j.val) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact Nat.card_sigma
      _ ≤ ∑ j : Fin (N+2), ∑ i : Fin j.val, 2*Nat.fib (j.val-i.val) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Nat.card_coe_set_eq] using
          (Set.encard_le_coe_iff_finite_ncard_le.mp (corner_count i.val j.val i.isLt)).2
      _ = 2*layerPairCount N := by
        simp only [← Finset.mul_sum]
        congr 1
        calc
          _ = ∑ j : Fin (N+2), layerPairRow j.val := by
            apply Finset.sum_congr rfl
            intro j hj
            exact Fin.sum_univ_eq_sum_range (fun i => Nat.fib (j.val-i)) j.val
          _ = layerPairCount N := Fin.sum_univ_eq_sum_range layerPairRow (N+2)
  have himage : (Set.range (carryPrefix d N)).ncard ≤ Nat.card (Charge N) := by
    calc
      _ ≤ (Set.range (chargeDecode N)).ncard := Set.ncard_le_ncard hr
      _ = (chargeDecode N '' Set.univ).ncard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set (Charge N)).ncard := Set.ncard_image_le Set.finite_univ
      _ = Nat.card (Charge N) := Set.ncard_univ _
  refine ⟨(Set.finite_range (chargeDecode N)).subset hr,?_,golden_bound N⟩
  rw [← pairs_formula]
  omega


end D5.S3.Quantum.Transport.FibonacciHistoryImage
