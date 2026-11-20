/- GID: D5/S1/Recurrence/Algebraic/MarkedAssemblyCoefficients
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/MarkedAssemblyCoefficients
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact signed decoration sums for ordered blocks with ambient markers. -/

import D5.S1.Recurrence.Algebraic.MarkedAssemblyFixedPoints
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Sylow
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.PowerSeries.Exp

/-! Ordered block decorations and their exact signed finite sums. -/

set_option autoImplicit false

open Finset PowerSeries
open scoped BigOperators

namespace D5.S1.Recurrence.Algebraic.MarkedAssemblyCoefficients

open MarkedAssemblyFixedPoints
noncomputable section

variable {d : ℕ}

variable {V C : Type} [Fintype V] [Fintype C] [decV : DecidableEq V]

/-- All orders of a prescribed vertex support. -/
abbrev Orders (U : Finset V) :=
  {l : {l : List V // l.Nodup} // l.val.toFinset = U}

private def ordersEquiv (U : Finset V) :
    Orders U ≃ {l : List V // l ∈ U.toList.permutations.toFinset} where
  toFun l := ⟨l.val.val, by
    rw [List.mem_toFinset, List.mem_permutations]
    apply List.perm_of_nodup_nodup_toFinset_eq l.val.property U.nodup_toList
    simpa using l.property⟩
  invFun l := by
    have hp : l.val.Perm U.toList := List.mem_permutations.mp (List.mem_toFinset.mp l.property)
    exact ⟨⟨l.val, hp.nodup_iff.mpr U.nodup_toList⟩,
      by simpa using List.toFinset_eq_of_perm _ _ hp⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem orders_card (U : Finset V) : Fintype.card (Orders U) = U.card.factorial := by
  rw [Fintype.card_congr (ordersEquiv U), Fintype.card_coe,
    List.toFinset_card_of_nodup (List.nodup_permutations _ U.nodup_toList),
    List.length_permutations, length_toList]

/-- The signed color multiplicity at a block size. -/
def colorSum (allowed : ℕ → C → Prop) (sign : C → ℤ) (j : ℕ) : ℤ :=
  by classical exact ∑ c : {c : C // allowed j c}, sign c.val

abbrev Supports (S : Finset V) (x : V) :=
  {U : Finset V // U ⊆ S ∧ x ∈ U}

omit [Fintype V] in
theorem order_length {U : Finset V} (l : Orders U) : l.val.val.length = U.card := by
  exact (List.toFinset_card_of_nodup l.val.property).symm.trans (congrArg Finset.card l.property)

private def supportsEquiv (S : Finset V) (x : V) (hx : x ∈ S) :
    Supports S x ≃ ↥((S.erase x).powerset) where
  toFun U := ⟨U.val.erase x, mem_powerset.mpr (by
    intro y hy
    exact mem_erase.mpr ⟨(mem_erase.mp hy).1, U.property.1 (mem_erase.mp hy).2⟩)⟩
  invFun R := ⟨insert x R.val, (by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact hx
    · exact (mem_erase.mp (mem_powerset.mp R.property hy)).2), mem_insert_self _ _⟩
  left_inv U := Subtype.ext (insert_erase U.property.2)
  right_inv R := Subtype.ext (erase_insert (by
    intro h
    exact (mem_erase.mp (mem_powerset.mp R.property h)).1 rfl))

theorem supports_sum (S : Finset V) (x : V) (hx : x ∈ S) (h : ℕ → ℚ) :
    (∑ U : Supports S x, h U.val.card) =
      ∑ k ∈ range S.card, ((S.card - 1).choose k : ℚ) * h (k + 1) := by
  classical
  calc
    _ = ∑ R : ↥((S.erase x).powerset), h (R.val.card + 1) := by
      apply Fintype.sum_equiv (supportsEquiv S x hx)
      intro U
      dsimp [supportsEquiv]
      rw [card_erase_of_mem U.property.2]
      have := card_pos.mpr ⟨x, U.property.2⟩
      congr 1
      omega
    _ = ∑ R ∈ (S.erase x).powerset, h (R.card + 1) := by
      exact sum_coe_sort _ (fun R : Finset V => h (R.card + 1))
    _ = _ := by
      rw [sum_powerset]
      simp_rw [sum_powersetCard _ _ (fun j => h (j + 1))]
      simp only [nsmul_eq_mul, card_erase_of_mem hx]
      have := card_pos.mpr ⟨x, hx⟩
      congr 2
      omega

/-- The formal exponent has ordinary signed color coefficients at positive degrees. -/
def colorSeries (allowed : ℕ → C → Prop) (sign : C → ℤ) : PowerSeries ℚ :=
  mk fun j => if j = 0 then 0 else (colorSum allowed sign j : ℚ)

theorem colorSeries_zero (allowed : ℕ → C → Prop) (sign : C → ℤ) :
    constantCoeff (colorSeries allowed sign) = 0 := by
  simp [colorSeries]

theorem choose_factorial (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℚ) * ((k + 1).factorial : ℚ) * ((n - k).factorial : ℚ) =
      (n.factorial : ℚ) * (k + 1 : ℚ) := by
  have he : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) =
      (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  linear_combination (k + 1 : ℚ) * he

private abbrev Decorations (allowed : ℕ → C → Prop) (T U : Finset V) :=
  Orders U × {c : C // allowed U.card c} × (Fin d → ↥T)

private def rootDecorationsEquiv (allowed : ℕ → C → Prop) (S T : Finset V) (x : V) :
    RootBlock (k := d) allowed S T x ≃ Σ U : Supports S x, Decorations (d := d) allowed T U.val where
  toFun b := by
    let U := (vertices b.val).toFinset
    have hU : U.card = (vertices b.val).length :=
      List.toFinset_card_of_nodup b.val.1.property
    exact ⟨⟨U, (by intro y hy; exact b.property.2.1 y (List.mem_toFinset.mp hy)),
      List.mem_toFinset.mpr b.property.1⟩,
      ⟨⟨b.val.1, rfl⟩, ⟨color b.val, hU.symm ▸ b.property.2.2.1⟩,
        fun i => ⟨markers b.val i, b.property.2.2.2 i⟩⟩⟩
  invFun e := by
    obtain ⟨U, l, c, m⟩ := e
    refine ⟨⟨l.val, c.val, fun i => (m i).val⟩, ?_, ?_, ?_, fun i => (m i).property⟩
    · apply List.mem_toFinset.mp
      change x ∈ l.val.val.toFinset
      rw [l.property]
      exact U.property.2
    · intro y hy
      apply U.property.1
      rw [← l.property]
      exact List.mem_toFinset.mpr hy
    · change allowed l.val.val.length c.val
      rw [order_length l]
      exact c.property
  left_inv _ := rfl
  right_inv e := by
    obtain ⟨⟨U, hU⟩, ⟨⟨l, hl⟩, hsupport⟩, c, m⟩ := e
    dsimp at hsupport
    subst U
    rfl

/-- Every actual root block is counted once. The factorial counts its orders,
the color sum retains signs, and the independent marker coordinates range over T. -/
private theorem root_block_weight_sum (allowed : ℕ → C → Prop) (S T : Finset V)
    (x : V) (sign : C → ℤ) (f : Finset V → ℤ) :
    (∑ b : RootBlock (k := d) allowed S T x, sign (color b.val) *
      f (S \ (vertices b.val).toFinset)) =
    ∑ U : {U : Finset V // U ⊆ S ∧ x ∈ U},
      (U.val.card.factorial : ℤ) * colorSum allowed sign U.val.card *
        (T.card : ℤ) ^ d * f (S \ U.val) := by
  classical
  calc
    _ = ∑ d : (Σ U : Supports S x, Decorations (d := d) allowed T U.val),
        sign d.2.2.1.val * f (S \ d.1.val) := by
      apply Fintype.sum_equiv (rootDecorationsEquiv allowed S T x)
      intro b
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply sum_congr rfl
      intro U _
      simp only [Decorations, Fintype.sum_prod_type]
      simp only [sum_const, card_univ, Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
        orders_card, ← mul_sum, ← sum_mul, colorSum, Nat.cast_pow]
      ring

omit [DecidableEq V] in
private theorem assembly_empty (allowed : ℕ → C → Prop) (T : Finset V) (sign : C → ℤ) :
    (∑ E : Assembly (k := d) allowed (∅ : Finset V) T, weight sign E.val) = 1 := by
  classical
  let e : Assembly (k := d) allowed (∅ : Finset V) T := ⟨∅, by
    constructor <;> intro b hb <;> exact False.elim (notMem_empty b hb)⟩
  have he (E : Assembly (k := d) allowed (∅ : Finset V) T) : E = e := by
    apply Subtype.ext
    apply eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (E.property.nonempty b hb)
    exact notMem_empty y (E.property.support b hb y hy)
  rw [sum_eq_single e]
  · exact prod_empty
  · intro E _ hne
    exact False.elim (hne (he E))
  · simp

omit [DecidableEq V] in
/-- The exact exponential formula, with ordinary exponent coefficients and the
original ambient marker domain, for every support and every signed color family. -/
theorem assembly_sum_coefficient (allowed : ℕ → C → Prop) (S T : Finset V)
    (sign : C → ℤ) :
    ((∑ E : Assembly (k := d) allowed S T, weight sign E.val : ℤ) : ℚ) =
      (S.card.factorial : ℚ) * coeff S.card
        ((exp ℚ).subst (PowerSeries.C ((T.card : ℚ) ^ d) * colorSeries allowed sign)) := by
  classical
  let P := colorSeries allowed sign
  let t : ℚ := (T.card : ℚ) ^ d
  let H := (exp ℚ).subst (PowerSeries.C t * P)
  have hP : constantCoeff P = 0 := colorSeries_zero allowed sign
  have harg : constantCoeff (PowerSeries.C t * P) = 0 := by simp [hP]
  have hH : constantCoeff H = 1 := by
    dsimp [H]
    change MvPowerSeries.constantCoeff _ = _
    rw [constantCoeff_subst_of_constantCoeff_zero harg]
    simp
  have hD : derivative (R := ℚ) H = PowerSeries.C t * derivative (R := ℚ) P * H := by
    dsimp [H]
    rw [derivative_subst (.of_constantCoeff_zero harg), derivative_exp]
    simp only [Derivation.leibniz, derivative_C, mul_zero, add_zero, smul_eq_mul]
    ring
  change _ = (S.card.factorial : ℚ) * coeff S.card H
  suffices ∀ m : ℕ, ∀ S : Finset V, S.card = m →
      ((∑ E : Assembly (k := d) allowed S T, weight sign E.val : ℤ) : ℚ) =
        (m.factorial : ℚ) * coeff m H by
    exact this S.card S rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro S hS
    cases m with
    | zero =>
      have he : S = ∅ := card_eq_zero.mp hS
      subst S
      rw [assembly_empty]
      simp [coeff_zero_eq_constantCoeff, hH]
    | succ n =>
      obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < S.card)
      have hsmall (U : Supports S x) :
          ((∑ E : Assembly (k := d) allowed (S \ U.val) T, weight sign E.val : ℤ) : ℚ) =
            ((S.card - U.val.card).factorial : ℚ) * coeff (S.card - U.val.card) H := by
        have hpos : 0 < U.val.card := card_pos.mpr ⟨x, U.property.2⟩
        have hlt : (S \ U.val).card < n + 1 := by
          rw [card_sdiff_of_subset U.property.1]
          omega
        simpa only [card_sdiff_of_subset U.property.1] using
          ih (S \ U.val).card hlt (S \ U.val) rfl
      have hrec := assembly_weight_point_recursion (k := d) allowed S T x hx sign
      rw [root_block_weight_sum allowed S T x sign
        (fun U => ∑ E : Assembly (k := d) allowed U T, weight sign E.val)] at hrec
      have hsum : ((∑ E : Assembly (k := d) allowed S T, weight sign E.val : ℤ) : ℚ) =
          ∑ U : Supports S x, (U.val.card.factorial : ℚ) *
            (colorSum allowed sign U.val.card : ℚ) * t *
            ((S.card - U.val.card).factorial : ℚ) * coeff (S.card - U.val.card) H := by
        rw [hrec]
        push_cast
        apply sum_congr rfl
        intro U _
        rw [← Int.cast_sum, hsmall U]
        dsimp [t]
        ring
      rw [hsum]
      have hs := supports_sum S x hx (fun j => (j.factorial : ℚ) *
        (colorSum allowed sign j : ℚ) * t *
        ((S.card - j).factorial : ℚ) * coeff (S.card - j) H)
      rw [hs]
      simp only [hS, Nat.succ_sub_one, Nat.add_sub_add_right]
      have hd := congrArg (coeff n) hD
      rw [coeff_derivative, mul_assoc, coeff_C_mul, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => coeff i (derivative (R := ℚ) P) * coeff j H) n] at hd
      simp only [coeff_derivative] at hd
      have hc (i : ℕ) : coeff (i + 1) P = (colorSum allowed sign (i + 1) : ℚ) := by
        simp [P, colorSeries]
      simp_rw [hc] at hd
      calc
        _ = (n.factorial : ℚ) * t *
            ∑ k ∈ range (n + 1), ((colorSum allowed sign (k + 1) : ℚ) * (k + 1 : ℚ)) *
              coeff (n - k) H := by
          rw [mul_sum]
          apply sum_congr rfl
          intro k hk
          have hf := choose_factorial n k (by have := mem_range.mp hk; omega)
          linear_combination ((colorSum allowed sign (k + 1) : ℚ) * t * coeff (n - k) H) * hf
        _ = ((n + 1).factorial : ℚ) * coeff (n + 1) H := by
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          linear_combination -(n.factorial : ℚ) * hd

variable [decC : DecidableEq C]
variable {allowed : ℕ → C → Prop}

/-- A finite signed palette for an arbitrary integer strict prefix. -/
abbrev PrefixColor (N : ℕ) (a : ℕ → ℤ) :=
  Σ j : Fin N, Fin (a j.val).toNat ⊕ Fin (-a j.val).toNat

/-- A color is available precisely at its own block size. -/
def prefixAllowed (N : ℕ) (a : ℕ → ℤ) (j : ℕ) (c : PrefixColor N a) : Prop :=
  c.1.val = j

/-- Positive and negative palette components carry unit signs. -/
def prefixSign (N : ℕ) (a : ℕ → ℤ) (c : PrefixColor N a) : ℤ :=
  c.2.elim (fun _ => 1) (fun _ => -1)

/-- The ordinary strict-prefix polynomial as a rational formal power series. -/
def prefixSeries (N : ℕ) (a : ℕ → ℤ) : PowerSeries ℚ :=
  mk fun j => if 0 < j ∧ j < N then (a j : ℚ) else 0

private def prefixColorEquiv (N : ℕ) (a : ℕ → ℤ) (j : ℕ) (hj : j < N) :
    {c : PrefixColor N a // prefixAllowed N a j c} ≃
      Fin (a j).toNat ⊕ Fin (-a j).toNat where
  toFun c := by
    obtain ⟨⟨⟨k, hk⟩, d⟩, he⟩ := c
    change k = j at he
    subst k
    exact d
  invFun d := ⟨⟨⟨j, hj⟩, d⟩, rfl⟩
  left_inv c := by
    obtain ⟨⟨⟨k, hk⟩, d⟩, he⟩ := c
    change k = j at he
    subst k
    rfl
  right_inv _ := rfl

private theorem prefix_color_sum (N : ℕ) (a : ℕ → ℤ) (j : ℕ) :
    colorSum (prefixAllowed N a) (prefixSign N a) j = if j < N then a j else 0 := by
  classical
  unfold colorSum
  by_cases hj : j < N
  · rw [ite_eq_left hj]
    calc
      _ = ∑ d : Fin (a j).toNat ⊕ Fin (-a j).toNat,
          d.elim (fun _ => (1 : ℤ)) (fun _ => -1) := by
        apply Fintype.sum_equiv (prefixColorEquiv N a j hj)
        intro c
        obtain ⟨⟨⟨k, hk⟩, d⟩, he⟩ := c
        change k = j at he
        subst k
        rfl
      _ = a j := by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, sum_const, card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one, mul_neg]
        simpa [sub_eq_add_neg] using (a j).toNat_sub_toNat_neg
  · rw [ite_eq_right hj]
    apply sum_eq_zero
    intro c _
    exact False.elim (hj (c.property ▸ c.val.1.isLt))

theorem prefix_series_eq (N : ℕ) (a : ℕ → ℤ) :
    colorSeries (prefixAllowed N a) (prefixSign N a) = prefixSeries N a := by
  ext j
  simp only [colorSeries, prefixSeries, coeff_mk, prefix_color_sum]
  by_cases hz : j = 0
  · simp [hz]
  · by_cases hj : j < N <;> simp [hz, hj, Nat.pos_of_ne_zero hz]

private theorem prefix_sign_unit (N : ℕ) (a : ℕ → ℤ) (c : PrefixColor N a) :
    prefixSign N a c = 1 ∨ prefixSign N a c = -1 := by
  rcases c with ⟨j, d | d⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem relabel_one (b : Block V C d) : relabel 1 b = b := by
  rcases b with ⟨⟨l, hl⟩, c, m⟩
  simp [relabel, color, markers]

private theorem relabel_mul (g h : Equiv.Perm V) (b : Block V C d) :
    relabel (g * h) b = relabel g (relabel h b) := by
  rcases b with ⟨⟨l, hl⟩, c, m⟩
  simp [relabel, color, markers, List.map_map, Function.comp_def]

private theorem relabel_injective (g : Equiv.Perm V) :
    Function.Injective (relabel g : Block V C d → Block V C d) := by
  intro a b h
  have := congrArg (relabel g⁻¹) h
  simpa only [← relabel_mul, inv_mul_cancel, relabel_one] using this

private theorem relabel_law (allowed : ℕ → C → Prop) (g : Equiv.Perm V)
    (E : Assembly (k := d) allowed (univ : Finset V) univ) :
    AssemblyLaw (k := d) allowed univ univ (E.val.image (relabel g)) := by
  constructor
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    simpa [vertices, relabel] using E.property.nonempty a ha
  · intro b hb x hx; exact mem_univ x
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    simpa [vertices, relabel, color] using E.property.admissible a ha
  · intro b hb i; exact mem_univ _
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := E.property.cover (g⁻¹ x) (mem_univ _)
    refine ⟨relabel g b, mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    change x ∈ (vertices b).map g
    simpa using List.mem_map_of_mem (f := g) hxb
  · intro b hb c hc x hxb hxc
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hc
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hxb
    obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hxc
    have hyz : y = z := g.injective (hyx.trans hzx.symm)
    subst z
    exact congrArg (relabel g) (E.property.separate a ha d hd y hy hz)

/-- Assemblies with every vertex and all markers in the full ambient type. -/
abbrev FullAssembly (allowed : ℕ → C → Prop) :=
  Assembly (k := d) allowed (univ : Finset V) univ

/-- The simultaneous permutation action on actual assemblies. -/
instance fullAssemblyMulAction (allowed : ℕ → C → Prop) :
    MulAction (Equiv.Perm V) (FullAssembly (d := d) (V := V) allowed) where
  smul g E := ⟨E.val.image (relabel g), relabel_law allowed g E⟩
  one_smul E := by
    apply Subtype.ext
    change E.val.image (relabel 1) = E.val
    rw [show (relabel (1 : Equiv.Perm V) : Block V C d → Block V C d) = id from
      funext relabel_one, image_id]
  mul_smul g h E := by
    apply Subtype.ext
    change E.val.image (relabel (g * h)) = (E.val.image (relabel h)).image (relabel g)
    rw [image_image]
    congr 1
    exact funext (relabel_mul g h)

private theorem action_weight (allowed : ℕ → C → Prop) (sign : C → ℤ)
    (g : Equiv.Perm V) (E : FullAssembly (d := d) (V := V) allowed) :
    weight sign (g • E).val = weight sign E.val := by
  change (∏ b ∈ E.val.image (relabel g), sign (color b)) = _
  rw [prod_image (fun a _ b _ h => relabel_injective g h)]
  rfl

private theorem stable_iff_image (g : Equiv.Perm V) (E : Finset (Block V C d)) :
    Stable g E ↔ E.image (relabel g) = E := by
  constructor
  · intro h
    apply eq_of_subset_of_card_le
    · exact image_subset_iff.mpr h
    · rw [card_image_of_injective _ (relabel_injective g)]
  · intro h b hb
    rw [← h]
    exact mem_image_of_mem _ hb

/-- The structural fixed assemblies are the fixed points of the actual action. -/
def fixedByAssemblyEquiv (allowed : ℕ → C → Prop) (g : Equiv.Perm V) :
    MulAction.fixedBy (FullAssembly (d := d) (V := V) allowed) g ≃
      FixedAssembly (k := d) allowed (univ : Finset V) univ g where
  toFun E := ⟨E.val.val, E.val.property,
    (stable_iff_image g E.val.val).mpr (congrArg Subtype.val E.property)⟩
  invFun E := ⟨⟨E.val, E.property.1⟩,
    Subtype.ext ((stable_iff_image g E.val).mp E.property.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance fixedByAssemblyFintype (allowed : ℕ → C → Prop) (g : Equiv.Perm V) :
    Fintype (MulAction.fixedBy (FullAssembly (d := d) (V := V) allowed) g) := Fintype.ofFinite _

/-- Relabeling preserves arbitrary signed weights, and its fixedBy sum is exactly
the structural invariant-assembly sum used by the coefficient factorization. -/
private theorem assembly_action_fixed_sum (allowed : ℕ → C → Prop) (sign : C → ℤ)
    (g : Equiv.Perm V) :
    (∀ E : FullAssembly (d := d) (V := V) allowed, weight sign (g • E).val = weight sign E.val) ∧
    (∑ E : MulAction.fixedBy (FullAssembly (d := d) (V := V) allowed) g, weight sign E.val.val) =
      ∑ E : FixedAssembly (k := d) allowed (univ : Finset V) univ g, weight sign E.val := by
  classical
  refine ⟨action_weight allowed sign g, ?_⟩
  exact Fintype.sum_equiv (fixedByAssemblyEquiv allowed g) _ _ (fun _ => rfl)

/-- A distinguished vertex, an independent marker family, and an assembly off the vertex.
The assembly marker domain still includes the distinguished vertex. -/
abbrev PointedAssembly (allowed : ℕ → C → Prop) :=
  {r : V × (Fin d → V) × Finset (Block V C d) //
    AssemblyLaw (k := d) allowed (univ.erase r.1) univ r.2.2}

instance pointedAssemblyFintype (allowed : ℕ → C → Prop) :
    Fintype (PointedAssembly (d := d) (V := V) allowed) := Fintype.ofFinite _

private theorem relabel_erase_law (allowed : ℕ → C → Prop) (g : Equiv.Perm V)
    (x : V) (E : Finset (Block V C d)) (hE : AssemblyLaw (k := d) allowed (univ.erase x) univ E) :
    AssemblyLaw (k := d) allowed (univ.erase (g x)) univ (E.image (relabel g)) := by
  constructor
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    simpa [vertices, relabel] using hE.nonempty a ha
  · intro b hb y hy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact mem_erase.mpr ⟨fun he => (mem_erase.mp (hE.support a ha z hz)).1
      (g.injective he), mem_univ _⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    simpa [vertices, relabel, color] using hE.admissible a ha
  · intro b hb i; exact mem_univ _
  · intro y hy
    have hxy : g⁻¹ y ≠ x := by
      intro he
      apply (mem_erase.mp hy).1
      simpa using congrArg g he
    obtain ⟨b, hb, hyb⟩ := hE.cover (g⁻¹ y) (mem_erase.mpr ⟨hxy, mem_univ _⟩)
    refine ⟨relabel g b, mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    change y ∈ (vertices b).map g
    simpa using List.mem_map_of_mem (f := g) hyb
  · intro b hb c hc y hyb hyc
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hc
    obtain ⟨z, hz, hzy⟩ := List.mem_map.mp hyb
    obtain ⟨w, hw, hwy⟩ := List.mem_map.mp hyc
    have hzw := g.injective (hzy.trans hwy.symm)
    subst w
    exact congrArg (relabel g) (hE.separate a ha d hd z hz hw)

/-- The root and every independent marker are simultaneously relabeled. -/
instance pointedAssemblyMulAction (allowed : ℕ → C → Prop) :
    MulAction (Equiv.Perm V) (PointedAssembly (d := d) (V := V) allowed) where
  smul g R := ⟨(g R.val.1, fun i => g (R.val.2.1 i),
    R.val.2.2.image (relabel g)), relabel_erase_law allowed g _ _ R.property⟩
  one_smul R := by
    apply Subtype.ext
    change (R.val.1, R.val.2.1,
      R.val.2.2.image (relabel (1 : Equiv.Perm V))) = R.val
    rw [show (relabel (1 : Equiv.Perm V) : Block V C d → Block V C d) = id from
      funext relabel_one, image_id]
  mul_smul g h R := by
    apply Subtype.ext
    change (g (h R.val.1), (fun i => g (h (R.val.2.1 i))),
      R.val.2.2.image (relabel (g * h))) =
      (g (h R.val.1), (fun i => g (h (R.val.2.1 i))),
        (R.val.2.2.image (relabel h)).image (relabel g))
    rw [image_image, show (relabel (g * h) : Block V C d → Block V C d) =
      relabel g ∘ relabel h from funext (relabel_mul g h)]

/-- Root markers have no effect on the color sign. -/
def pointedWeight (sign : C → ℤ) (R : PointedAssembly (d := d) (V := V) allowed) : ℤ :=
  weight sign R.val.2.2

instance pointedFixedByFintype (allowed : ℕ → C → Prop) (g : Equiv.Perm V) :
    Fintype (MulAction.fixedBy (PointedAssembly (d := d) (V := V) allowed) g) := Fintype.ofFinite _

/-- Fixed rooted objects have a fixed root and independently fixed marker coordinates. -/
def fixedByPointedEquiv (allowed : ℕ → C → Prop) (g : Equiv.Perm V) :
    MulAction.fixedBy (PointedAssembly (d := d) (V := V) allowed) g ≃
      Σ v : ↥(fixedVertices g (univ : Finset V)),
        (Fin d → ↥(fixedVertices g (univ : Finset V))) ×
          FixedAssembly (k := d) allowed (univ.erase v.val) univ g where
  toFun R := by
    have h : (g R.val.val.1, (fun i => g (R.val.val.2.1 i)),
        R.val.val.2.2.image (relabel g)) = R.val.val := congrArg Subtype.val R.property
    exact ⟨⟨R.val.val.1, mem_filter.mpr ⟨mem_univ _, congrArg Prod.fst h⟩⟩,
      (fun i => ⟨R.val.val.2.1 i,
        mem_filter.mpr ⟨mem_univ _, congrArg (fun r => r.2.1 i) h⟩⟩),
      ⟨R.val.val.2.2, R.val.property,
        (stable_iff_image g _).mpr (congrArg (fun r => r.2.2) h)⟩⟩
  invFun R := ⟨⟨(R.1.val, (fun i => (R.2.1 i).val), R.2.2.val), R.2.2.property.1⟩,
    Subtype.ext (Prod.ext (mem_filter.mp R.1.property).2
      (Prod.ext (funext (fun i => (mem_filter.mp (R.2.1 i).property).2))
        ((stable_iff_image g _).mp R.2.2.property.2)))⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem pointed_action_fixed_sum (allowed : ℕ → C → Prop) (sign : C → ℤ)
    (g : Equiv.Perm V) :
    (∀ R : PointedAssembly (d := d) (V := V) allowed,
      pointedWeight sign (g • R) = pointedWeight sign R) ∧
    (∑ R : MulAction.fixedBy (PointedAssembly (d := d) (V := V) allowed) g,
      pointedWeight sign R.val) =
      ∑ v : ↥(fixedVertices g (univ : Finset V)),
        ((fixedVertices g (univ : Finset V)).card : ℤ) ^ d *
          ∑ E : FixedAssembly (k := d) allowed (univ.erase v.val) univ g, weight sign E.val := by
  classical
  constructor
  · intro R
    change (∏ b ∈ R.val.2.2.image (relabel g), sign (color b)) = _
    rw [prod_image (fun a _ b _ h => relabel_injective g h)]
    rfl
  · calc
      _ = ∑ R : (Σ v : ↥(fixedVertices g (univ : Finset V)),
          (Fin d → ↥(fixedVertices g (univ : Finset V))) ×
            FixedAssembly (k := d) allowed (univ.erase v.val) univ g), weight sign R.2.2.val :=
        Fintype.sum_equiv (fixedByPointedEquiv allowed g) _ _ (fun _ => rfl)
      _ = _ := by
        rw [Fintype.sum_sigma]
        apply sum_congr rfl
        intro v _
        simp only [Fintype.sum_prod_type, sum_const, card_univ, Fintype.card_fun,
          Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul, Nat.cast_pow]

private def weightFiberAction {Γ X : Type} [Group Γ] [MulAction Γ X]
    (w : X → ℤ) (hw : ∀ (g : Γ) (x : X), w (g • x) = w x) (z : ℤ) :
    MulAction Γ {x : X // w x = z} where
  smul g x := ⟨g • x.val, (hw g x.val).trans x.property⟩
  one_smul x := Subtype.ext (one_smul _ x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

private def fiberFixedEquiv {Γ X : Type} [Group Γ] [MulAction Γ X]
    (w : X → ℤ) (hw : ∀ (g : Γ) (x : X), w (g • x) = w x) (z : ℤ) (g : Γ) :
    letI := weightFiberAction w hw z
    {x : MulAction.fixedBy X g // w x.val = z} ≃
      MulAction.fixedBy {x : X // w x = z} g := by
  letI := weightFiberAction w hw z
  exact
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, Subtype.ext x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, congrArg Subtype.val x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem signed_burnside {Γ X : Type} [Group Γ] [Fintype Γ] [Fintype X]
    [MulAction Γ X] (w : X → ℤ) (hw : ∀ (g : Γ) (x : X), w (g • x) = w x)
    (hs : ∀ x, w x = 1 ∨ w x = -1) :
    letI (g : Γ) : Fintype (MulAction.fixedBy X g) := Fintype.ofFinite _
    (Fintype.card Γ : ℤ) ∣ ∑ g : Γ, ∑ x : MulAction.fixedBy X g, w x.val := by
  classical
  letI (g : Γ) : Fintype (MulAction.fixedBy X g) := Fintype.ofFinite _
  let P := {x : X // w x = 1}
  let N := {x : X // w x = -1}
  letI : MulAction Γ P := weightFiberAction w hw 1
  letI : MulAction Γ N := weightFiberAction w hw (-1)
  letI (g : Γ) : Fintype (MulAction.fixedBy P g) := Fintype.ofFinite _
  letI (g : Γ) : Fintype (MulAction.fixedBy N g) := Fintype.ofFinite _
  letI : Fintype (MulAction.orbitRel.Quotient Γ P) := Fintype.ofFinite _
  letI : Fintype (MulAction.orbitRel.Quotient Γ N) := Fintype.ofFinite _
  have he (g : Γ) : (∑ x : MulAction.fixedBy X g, w x.val) =
      (Fintype.card (MulAction.fixedBy P g) : ℤ) -
        (Fintype.card (MulAction.fixedBy N g) : ℤ) := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun x : MulAction.fixedBy X g => w x.val = 1) (fun x => w x.val)
    have hp : (∑ x : {x : MulAction.fixedBy X g // w x.val = 1}, w x.val.val) =
        (Fintype.card (MulAction.fixedBy P g) : ℤ) := by
      simp_rw [show ∀ x : {x : MulAction.fixedBy X g // w x.val = 1},
        w x.val.val = 1 from fun x => x.property]
      simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
      exact_mod_cast Fintype.card_congr (fiberFixedEquiv w hw 1 g)
    let en : {x : MulAction.fixedBy X g // ¬w x.val = 1} ≃
        {x : MulAction.fixedBy X g // w x.val = -1} :=
      Equiv.subtypeEquivRight (fun x => by
        constructor
        · intro hx; exact (hs x.val).resolve_left hx
        · intro hx he; omega)
    have hn : (∑ x : {x : MulAction.fixedBy X g // ¬w x.val = 1}, w x.val.val) =
        -(Fintype.card (MulAction.fixedBy N g) : ℤ) := by
      calc
        _ = ∑ x : {x : MulAction.fixedBy X g // w x.val = -1}, w x.val.val :=
          Fintype.sum_equiv en _ _ (fun _ => rfl)
        _ = -(Fintype.card (MulAction.fixedBy N g) : ℤ) := by
          simp_rw [show ∀ x : {x : MulAction.fixedBy X g // w x.val = -1},
            w x.val.val = -1 from fun x => x.property]
          simp only [sum_const, card_univ, nsmul_eq_mul, mul_neg, mul_one]
          congr 1
          exact_mod_cast Fintype.card_congr (fiberFixedEquiv w hw (-1) g)
    rw [hp, hn] at hsplit
    exact hsplit.symm
  simp_rw [he]
  rw [sum_sub_distrib]
  have hp := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group Γ P
  have hn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group Γ N
  have hp' : (∑ g : Γ, (Fintype.card (MulAction.fixedBy P g) : ℤ)) =
      (Fintype.card (MulAction.orbitRel.Quotient Γ P) : ℤ) * (Fintype.card Γ : ℤ) := by
    exact_mod_cast hp
  have hn' : (∑ g : Γ, (Fintype.card (MulAction.fixedBy N g) : ℤ)) =
      (Fintype.card (MulAction.orbitRel.Quotient Γ N) : ℤ) * (Fintype.card Γ : ℤ) := by
    exact_mod_cast hn
  rw [hp', hn', ← sub_mul]
  exact dvd_mul_left _ _

private theorem weight_unit_sign (sign : C → ℤ) (hs : ∀ c, sign c = 1 ∨ sign c = -1)
    (E : Finset (Block V C d)) : weight sign E = 1 ∨ weight sign E = -1 := by
  induction E using Finset.induction_on with
  | empty => exact Or.inl rfl
  | @insert b E hb ih =>
    unfold weight at *
    rw [prod_insert hb]
    rcases hs (color b) with h | h <;> rcases ih with hi | hi <;>
      simp [h, hi]

/-- Signed Burnside for the actual assembly-minus-pointed-assembly subtraction.
The integer divisor is the order of any subgroup of the ambient symmetric group. -/
private theorem signed_assembly_burnside (allowed : ℕ → C → Prop) (sign : C → ℤ)
    (hs : ∀ c, sign c = 1 ∨ sign c = -1) (G : Subgroup (Equiv.Perm V)) :
    letI : Fintype G := Fintype.ofFinite _
    (Nat.card G : ℤ) ∣ ∑ g : G,
      ((∑ E : MulAction.fixedBy (FullAssembly (d := d) (V := V) allowed) g.val, weight sign E.val.val) -
        ∑ R : MulAction.fixedBy (PointedAssembly (d := d) (V := V) allowed) g.val,
          pointedWeight sign R.val) := by
  classical
  letI : Fintype G := Fintype.ofFinite _
  have hE := signed_burnside (Γ := G)
    (fun E : FullAssembly (d := d) (V := V) allowed => weight sign E.val)
    (fun g E => (assembly_action_fixed_sum allowed sign g.val).1 E)
    (fun E => weight_unit_sign sign hs E.val)
  have hR := signed_burnside (Γ := G)
    (fun R : PointedAssembly (d := d) (V := V) allowed => pointedWeight sign R)
    (fun g R => (pointed_action_fixed_sum allowed sign g.val).1 R)
    (fun R => weight_unit_sign sign hs R.val.2.2)
  rw [sum_sub_distrib, Nat.card_eq_fintype_card]
  exact dvd_sub hE hR


theorem fixed_erase (g : Equiv.Perm V)
    (v : ↥(fixedVertices g (univ : Finset V))) :
    fixedVertices g (univ.erase v.val) = (fixedVertices g univ).erase v.val := by
  ext x
  simp [fixedVertices, and_assoc, and_left_comm, and_comm]

theorem moved_erase (g : Equiv.Perm V)
    (v : ↥(fixedVertices g (univ : Finset V))) :
    movedVertices g (univ.erase v.val) = movedVertices g univ := by
  have hv : g v.val = v.val := (mem_filter.mp v.property).2
  ext x
  by_cases hx : x = v.val
  · subst x
    simp [movedVertices, hv]
  · simp [movedVertices, hx]

/-- The signed subtraction uses fixed points of the actual two permutation actions.
For positive fixed-vertex count, it is the lower source residual times the same
invariant moved-block sum and the fixed-vertex factorial. -/
private theorem fixed_point_subtraction_coefficient (allowed : ℕ → C → Prop) (sign : C → ℤ)
    (g : Equiv.Perm V) (hf : 1 ≤ (fixedVertices g (univ : Finset V)).card) :
    let F := fixedVertices g (univ : Finset V)
    let f := F.card
    let H := (exp ℚ).subst (PowerSeries.C ((f : ℚ) ^ d) * colorSeries allowed sign)
    let M := ∑ B : FixedAssembly (k := d) allowed (movedVertices g univ) univ g, weight sign B.val
    (((∑ E : MulAction.fixedBy (FullAssembly (d := d) (V := V) allowed) g, weight sign E.val.val) -
      (∑ R : MulAction.fixedBy (PointedAssembly (d := d) (V := V) allowed) g,
        pointedWeight sign R.val) : ℤ) : ℚ) =
      (M : ℚ) * (f.factorial : ℚ) * (coeff f H - (f : ℚ) ^ d * coeff (f - 1) H) := by
  classical
  dsimp only
  let F := fixedVertices g (univ : Finset V)
  let f := F.card
  let H := (exp ℚ).subst (PowerSeries.C ((f : ℚ) ^ d) * colorSeries allowed sign)
  let M := ∑ B : FixedAssembly (k := d) allowed (movedVertices g univ) univ g, weight sign B.val
  have hE : ((∑ E : MulAction.fixedBy (FullAssembly (d := d) (V := V) allowed) g,
      weight sign E.val.val : ℤ) : ℚ) = (f.factorial : ℚ) * coeff f H * (M : ℚ) := by
    rw [(assembly_action_fixed_sum allowed sign g).2,
      fixed_assembly_weight_factorization allowed univ univ g sign, Int.cast_mul,
      assembly_sum_coefficient]
  have hR : ((∑ R : MulAction.fixedBy (PointedAssembly (d := d) (V := V) allowed) g,
      pointedWeight sign R.val : ℤ) : ℚ) =
      (f : ℚ) ^ (d + 1) * ((f - 1).factorial : ℚ) * coeff (f - 1) H * (M : ℚ) := by
    rw [(pointed_action_fixed_sum allowed sign g).2, Int.cast_sum]
    have hterm (v : ↥F) :
        (((F.card : ℤ) ^ d *
          ∑ E : FixedAssembly (k := d) allowed (univ.erase v.val) univ g, weight sign E.val : ℤ) : ℚ) =
          (f : ℚ) ^ d * ((f - 1).factorial : ℚ) * coeff (f - 1) H * (M : ℚ) := by
      rw [fixed_assembly_weight_factorization allowed (univ.erase v.val) univ g sign,
        fixed_erase g v, moved_erase g v, Int.cast_mul, Int.cast_mul,
        assembly_sum_coefficient, card_erase_of_mem v.property]
      push_cast
      dsimp [M, H, f, F]
      push_cast
      ring
    have heq : (∑ v : ↥F, (((F.card : ℤ) ^ d *
        ∑ E : FixedAssembly (k := d) allowed (univ.erase v.val) univ g, weight sign E.val : ℤ) : ℚ)) =
        ∑ _v : ↥F,
          (f : ℚ) ^ d * ((f - 1).factorial : ℚ) * coeff (f - 1) H * (M : ℚ) := by
      apply sum_congr rfl
      intro v _
      exact hterm v
    rw [heq]
    simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
    change (f : ℚ) * _ = _
    rw [pow_succ]
    ring
  have hfac : (f.factorial : ℚ) = (f : ℚ) * ((f - 1).factorial : ℚ) := by
    have he : f = (f - 1) + 1 := (Nat.sub_add_cancel hf).symm
    have heN : f.factorial = f * (f - 1).factorial := by
      conv_lhs => rw [he, Nat.factorial_succ]
      rw [← he]
    exact_mod_cast heN
  rw [Int.cast_sub, hE, hR, hfac, pow_succ]
  ring

theorem sylow_fixed_card (p : ℕ) [Fact p.Prime]
    (P : Sylow p (Equiv.Perm V)) (g : P) (hpn : ¬p ∣ Fintype.card V) :
    1 ≤ (fixedVertices g.val (univ : Finset V)).card := by
  have hcyc := P.isPGroup'.to_subgroup (Subgroup.zpowers g)
  have hpn' : ¬p ∣ Nat.card V := by simpa only [Nat.card_eq_fintype_card] using hpn
  obtain ⟨x, hx⟩ := hcyc.nonempty_fixed_point_of_prime_not_dvd_card V hpn'
  have hfix : g.val x = x := hx ⟨g, Subgroup.mem_zpowers g⟩
  exact card_pos.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hfix⟩⟩

theorem proper_fixed_card (g : Equiv.Perm V) (hg : g ≠ 1) :
    (fixedVertices g (univ : Finset V)).card < Fintype.card V := by
  by_contra h
  have he : fixedVertices g (univ : Finset V) = univ :=
    eq_of_subset_of_card_le (subset_univ _) (by simpa using Nat.le_of_not_gt h)
  apply hg
  ext x
  change g x = x
  have hx : x ∈ fixedVertices g (univ : Finset V) := by rw [he]; exact mem_univ _
  exact (mem_filter.mp hx).2

/-- The actual signed Burnside subtraction is divisible by the full Sylow order.
Only the lower coefficient equations are premises; the action, fixed counts and
Sylow fixed-vertex bounds are proved, including every nonidentity group element. -/
private theorem sylow_subtraction_divisibility (allowed : ℕ → C → Prop) (sign : C → ℤ)
    (hs : ∀ c, sign c = 1 ∨ sign c = -1) (p : ℕ) (hp : p.Prime)
    (hpn : ¬p ∣ Fintype.card V)
    (hlower : ∀ f : ℕ, 1 ≤ f → f < Fintype.card V →
      let H := (exp ℚ).subst (PowerSeries.C ((f : ℚ) ^ d) * colorSeries allowed sign)
      coeff f H = (f : ℚ) ^ d * coeff (f - 1) H) :
    (p ^ (Fintype.card V).factorial.factorization p : ℤ) ∣
      ((∑ E : MulAction.fixedBy (FullAssembly (d := d) (V := V) allowed) (1 : Equiv.Perm V),
          weight sign E.val.val) -
        ∑ R : MulAction.fixedBy (PointedAssembly (d := d) (V := V) allowed) (1 : Equiv.Perm V),
          pointedWeight sign R.val) := by
  classical
  letI : DecidableEq V := decV
  letI : DecidableEq C := decC
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p (Equiv.Perm V) := Classical.choice inferInstance
  letI : Fintype P := Fintype.ofFinite _
  have hzero (g : P) (hg : g ≠ 1) :
      ((∑ E : MulAction.fixedBy (FullAssembly (d := d) (V := V) allowed) g.val,
          weight sign E.val.val) -
        ∑ R : MulAction.fixedBy (PointedAssembly (d := d) (V := V) allowed) g.val,
          pointedWeight sign R.val) = 0 := by
    have hne : g.val ≠ 1 := fun h => hg (Subtype.ext h)
    have hf := sylow_fixed_card p P g hpn
    have hlt := proper_fixed_card g.val hne
    have he := fixed_point_subtraction_coefficient (d := d) allowed sign g.val hf
    dsimp only at he
    rw [hlower _ hf hlt, sub_self, mul_zero] at he
    exact_mod_cast he
  have hb := signed_assembly_burnside (d := d) allowed sign hs P.toSubgroup
  rw [Finset.sum_eq_single 1] at hb
  · have hcard : Nat.card P = p ^ (Fintype.card V).factorial.factorization p := by
      rw [P.card_eq_multiplicity, Nat.card_eq_fintype_card, Fintype.card_perm]
    rw [hcard, Nat.cast_pow] at hb
    convert hb using 1 <;> congr 1
  · intro g _ hg
    exact hzero g hg
  · simp

private theorem moved_identity_sum (allowed : ℕ → C → Prop) (sign : C → ℤ) :
    (∑ B : FixedAssembly (k := d) allowed (movedVertices (1 : Equiv.Perm V) univ) univ 1,
      weight sign B.val) = 1 := by
  classical
  have hm : movedVertices (1 : Equiv.Perm V) (univ : Finset V) = ∅ := by
    ext x
    simp [movedVertices]
  rw [hm]
  let e : FixedAssembly (k := d) allowed (∅ : Finset V) univ 1 := ⟨∅, by
    constructor
    · constructor <;> intro b hb <;> exact False.elim (notMem_empty b hb)
    · intro b hb; exact False.elim (notMem_empty b hb)⟩
  have he (E : FixedAssembly (k := d) allowed (∅ : Finset V) univ 1) : E = e := by
    apply Subtype.ext
    apply eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (E.property.1.nonempty b hb)
    exact notMem_empty x (E.property.1.support b hb x hx)
  rw [sum_eq_single e]
  · exact prod_empty
  · intro E _ hne; exact False.elim (hne (he E))
  · simp

/-- Full factorial cancellation gives local integrality of the ordinary residual
at every prime coprime to the degree, for every finite unit-signed palette. -/
private theorem signed_residual_local_integral (allowed : ℕ → C → Prop) (sign : C → ℤ)
    (hs : ∀ c, sign c = 1 ∨ sign c = -1) (hn : 1 ≤ Fintype.card V)
    (p : ℕ) (hp : p.Prime) (hpn : ¬p ∣ Fintype.card V)
    (hlower : ∀ f : ℕ, 1 ≤ f → f < Fintype.card V →
      let H := (exp ℚ).subst (PowerSeries.C ((f : ℚ) ^ d) * colorSeries allowed sign)
      coeff f H = (f : ℚ) ^ d * coeff (f - 1) H) :
    let n := Fintype.card V
    let H := (exp ℚ).subst (PowerSeries.C ((n : ℚ) ^ d) * colorSeries allowed sign)
    0 ≤ padicValRat p
      (coeff n H - (n : ℚ) ^ d * coeff (n - 1) H) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let n := Fintype.card V
  let H := (exp ℚ).subst (PowerSeries.C ((n : ℚ) ^ d) * colorSeries allowed sign)
  let q := coeff n H - (n : ℚ) ^ d * coeff (n - 1) H
  let z : ℤ := (∑ E : MulAction.fixedBy (FullAssembly (d := d) (V := V) allowed) (1 : Equiv.Perm V),
      weight sign E.val.val) -
    ∑ R : MulAction.fixedBy (PointedAssembly (d := d) (V := V) allowed) (1 : Equiv.Perm V),
      pointedWeight sign R.val
  have hf : fixedVertices (1 : Equiv.Perm V) (univ : Finset V) = univ := by
    ext x
    simp [fixedVertices]
  have he : (z : ℚ) = (n.factorial : ℚ) * q := by
    have h := fixed_point_subtraction_coefficient (d := d) allowed sign (1 : Equiv.Perm V)
      (by simpa only [hf, card_univ] using hn)
    dsimp only at h
    rw [hf, card_univ, moved_identity_sum, Int.cast_one, one_mul] at h
    exact h
  have hd : (p : ℤ) ^ n.factorial.factorization p ∣ z :=
    sylow_subtraction_divisibility allowed sign hs p hp hpn hlower
  change 0 ≤ padicValRat p q
  by_cases hq : q = 0
  · simp [hq]
  have hnq : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hzq : (z : ℚ) ≠ 0 := by rw [he]; exact mul_ne_zero hnq hq
  have hz : z ≠ 0 := by exact_mod_cast hzq
  have hv := ((padicValInt_dvd_iff _ z).mp hd).resolve_left hz
  rw [Nat.factorization_def _ hp] at hv
  have hev := congrArg (padicValRat p) he
  rw [padicValRat.mul hnq hq, padicValRat.of_int, padicValRat.of_nat] at hev
  omega

/-- Every integral strict prefix has a locally integral residual at primes
coprime to its endpoint, provided its actual lower source equations hold. -/
theorem signed_prefix_residual_local_integral (d : ℕ) (N : ℕ) (a : ℕ → ℤ) (hN : 1 ≤ N)
    (p : ℕ) (hp : p.Prime) (hpn : ¬p ∣ N)
    (hlower : ∀ f : ℕ, 1 ≤ f → f < N →
      let H := (exp ℚ).subst (PowerSeries.C ((f : ℚ) ^ d) * prefixSeries N a)
      coeff f H = (f : ℚ) ^ d * coeff (f - 1) H) :
    let H := (exp ℚ).subst (PowerSeries.C ((N : ℚ) ^ d) * prefixSeries N a)
    0 ≤ padicValRat p
      (coeff N H - (N : ℚ) ^ d * coeff (N - 1) H) := by
  classical
  have he := signed_residual_local_integral (d := d) (V := Fin N) (prefixAllowed N a)
    (prefixSign N a) (prefix_sign_unit N a) (by simpa using hN) p hp (by simpa using hpn)
  simp only [Fintype.card_fin, prefix_series_eq] at he
  exact he hlower

end

end D5.S1.Recurrence.Algebraic.MarkedAssemblyCoefficients
