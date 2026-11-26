/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentStarProducts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentStarProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.BitVec]
   utility: none
   digest: The transverse Laurent gain forces the product of two three-cube stars and fixes its coordinatewise height. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
import D5.S3.Combinatorics.Graph.HypercubeSubQuorum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentTransverseFibers

/-! The transverse Laurent gain forces the product of two three-cube stars and fixes its coordinatewise height. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q6TwoBlockRigidity

open Finset
open BalancedCriticalSpectrum (Q)
open private cubeParity from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

/- The height contradiction used when two rows share two columns. -/
theorem row_eq_of_height
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (row : X → Finset Y) (height : X → Y → ℤ)
    (hcolumn : ∀ x x' y, height x y = height x' y)
    (hopposite : ∀ {x x' y z}, x ≠ x' →
      y ∈ row x → y ∈ row x' → z ∈ row x → z ∈ row x' →
      row x ≠ row x' →
      height x y - height x z = -(height x' y - height x' z))
    (hstep : ∀ {x y z}, y ∈ row x → z ∈ row x → y ≠ z →
      height x y - height x z ≠ 0)
    {x x' : X} (hinter : 2 ≤ (row x ∩ row x').card) :
    row x = row x' := by
  by_contra hrows
  have hxx' : x ≠ x' := by
    intro h
    apply hrows
    simpa [h]
  have hbig : 1 < (row x ∩ row x').card := by omega
  obtain ⟨y, hy, z, hz, hyz⟩ := one_lt_card.mp hbig
  have hsign := hopposite hxx' (mem_inter.mp hy).1 (mem_inter.mp hy).2
    (mem_inter.mp hz).1 (mem_inter.mp hz).2 hrows
  have hcancel : height x y - height x z =
      -(height x y - height x z) := by
    calc
      height x y - height x z = -(height x' y - height x' z) := hsign
      _ = -(height x y - height x z) := by
        rw [← hcolumn x x' y, ← hcolumn x x' z]
  have hzero : height x y - height x z = 0 := by omega
  exact hstep (mem_inter.mp hy).1 (mem_inter.mp hz).1 hyz hzero

/-!
If every active row and column has three points in a four-point side, and the
height argument makes overlapping rows agree, the incidence relation is a
three-by-three product.
-/
theorem three_by_three_product
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (B : Finset (X × Y)) (row : X → Finset Y) (col : Y → Finset X)
    (hcardX : Fintype.card X = 4) (hcardY : Fintype.card Y = 4)
    (hB : B.Nonempty)
    (hrow_mem : ∀ x y, (x, y) ∈ B ↔ y ∈ row x)
    (hcol_mem : ∀ x y, (x, y) ∈ B ↔ x ∈ col y)
    (hrow_card : ∀ {x}, (row x).Nonempty → (row x).card = 3)
    (hcol_card : ∀ {y}, (col y).Nonempty → (col y).card = 3)
    (hoverlap : ∀ {x x'}, 2 ≤ (row x ∩ row x').card → row x = row x') :
    ∃ A : Finset X, ∃ T : Finset Y,
      A.card = 3 ∧ T.card = 3 ∧ B = A.product T := by
  classical
  obtain ⟨p, hp⟩ := hB
  have hrow0 : (row p.1).Nonempty := by
    exact ⟨p.2, (hrow_mem p.1 p.2).mp hp⟩
  let T : Finset Y := row p.1
  have hTcard : T.card = 3 := hrow_card hrow0
  let A : Finset X := univ.filter (fun x => (row x).Nonempty)
  have hA_mem (x : X) : x ∈ A ↔ (row x).Nonempty := by
    simp [A]
  have hpA : p.1 ∈ A := (hA_mem p.1).2 hrow0
  have hrow_eq (x : X) (hx : x ∈ A) : row x = T := by
    change row x = row p.1
    apply hoverlap
    have hxcard : (row x).card = 3 := hrow_card ((hA_mem x).1 hx)
    have hunion : (row x ∪ T).card ≤ 4 := by
      have hle : (row x ∪ T).card ≤ Fintype.card Y := by
        simpa using (card_le_card (subset_univ (row x ∪ T)))
      simpa [hcardY] using hle
    have hsum := card_union_add_card_inter (row x) T
    rw [hxcard, hTcard] at hsum
    change 2 ≤ (row x ∩ T).card
    omega
  have hTnonempty : T.Nonempty := by
    rw [← card_pos]
    omega
  obtain ⟨y₀, hy₀⟩ := hTnonempty
  have hcol_eq : col y₀ = A := by
    ext x
    constructor
    · intro hxy
      have hBxy : (x, y₀) ∈ B := (hcol_mem x y₀).mpr hxy
      have hrowxy : y₀ ∈ row x := (hrow_mem x y₀).mp hBxy
      exact (hA_mem x).2 ⟨y₀, hrowxy⟩
    · intro hxA
      have hrowxy : y₀ ∈ row x := by
        rw [hrow_eq x hxA]
        exact hy₀
      have hBxy : (x, y₀) ∈ B := (hrow_mem x y₀).mpr hrowxy
      exact (hcol_mem x y₀).mp hBxy
  have hAcard : A.card = 3 := by
    have hycol : (col y₀).Nonempty := by
      rw [hcol_eq]
      exact ⟨p.1, (hA_mem p.1).2 hrow0⟩
    have := hcol_card hycol
    simpa [hcol_eq] using this
  refine ⟨A, T, hAcard, hTcard, ?_⟩
  ext p'
  rcases p' with ⟨x, y⟩
  rw [Finset.product_eq_sprod, Finset.mem_product]
  constructor
  · intro hp'
    have hrow_nonempty : (row x).Nonempty := by
      exact ⟨y, (hrow_mem x y).mp hp'⟩
    have hxA : x ∈ A := (hA_mem x).2 hrow_nonempty
    have hyT : y ∈ T := by
      rw [← hrow_eq x hxA]
      exact (hrow_mem x y).mp hp'
    exact ⟨hxA, hyT⟩
  · rintro ⟨hxA, hyT⟩
    exact (hrow_mem x y).mpr ((hrow_eq x hxA).symm ▸ hyT)

/- The product theorem with the one-sided Laurent height argument inlined. -/
theorem height_three_by_three_product
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (B : Finset (X × Y)) (row : X → Finset Y) (col : Y → Finset X)
    (height : X → Y → ℤ)
    (hcardX : Fintype.card X = 4) (hcardY : Fintype.card Y = 4)
    (hB : B.Nonempty)
    (hrow_mem : ∀ x y, (x, y) ∈ B ↔ y ∈ row x)
    (hcol_mem : ∀ x y, (x, y) ∈ B ↔ x ∈ col y)
    (hrow_card : ∀ {x}, (row x).Nonempty → (row x).card = 3)
    (hcol_card : ∀ {y}, (col y).Nonempty → (col y).card = 3)
    (hcolumn : ∀ x x' y, height x y = height x' y)
    (hopposite : ∀ {x x' y z}, x ≠ x' →
      y ∈ row x → y ∈ row x' → z ∈ row x → z ∈ row x' →
      row x ≠ row x' →
      height x y - height x z = -(height x' y - height x' z))
    (hstep : ∀ {x y z}, y ∈ row x → z ∈ row x → y ≠ z →
      height x y - height x z ≠ 0) :
    ∃ A : Finset X, ∃ T : Finset Y,
      A.card = 3 ∧ T.card = 3 ∧ B = A.product T := by
  apply three_by_three_product B row col hcardX hcardY hB hrow_mem hcol_mem
    hrow_card hcol_card
  intro x x' hinter
  exact row_eq_of_height row height hcolumn hopposite hstep hinter

/- The two parity classes of an actual Q3 are four-point sides. -/
abbrev Q3Side (b : Bool) := {x : Q 3 // cubeParity x = b}

theorem q3_side_card (b : Bool) : Fintype.card (Q3Side b) = 4 := by
  cases b <;> decide +kernel

/-!
This is the direct Q3 corollary.  The row and column hypotheses are the
three-point stars from the two complementary blocks, while `hopposite` and
`hstep` are the signed height and distinct-coordinate inputs.
-/
theorem q3_height_three_by_three_product
    {b₁ b₂ : Bool}
    (B : Finset (Q3Side b₁ × Q3Side b₂))
    (row : Q3Side b₁ → Finset (Q3Side b₂))
    (col : Q3Side b₂ → Finset (Q3Side b₁))
    (height : Q3Side b₁ → Q3Side b₂ → ℤ)
    (hB : B.Nonempty)
    (hrow_mem : ∀ x y, (x, y) ∈ B ↔ y ∈ row x)
    (hcol_mem : ∀ x y, (x, y) ∈ B ↔ x ∈ col y)
    (hrow_card : ∀ {x}, (row x).Nonempty → (row x).card = 3)
    (hcol_card : ∀ {y}, (col y).Nonempty → (col y).card = 3)
    (hcolumn : ∀ x x' y, height x y = height x' y)
    (hopposite : ∀ {x x' y z}, x ≠ x' →
      y ∈ row x → y ∈ row x' → z ∈ row x → z ∈ row x' →
      row x ≠ row x' →
      height x y - height x z = -(height x' y - height x' z))
    (hstep : ∀ {x y z}, y ∈ row x → z ∈ row x → y ≠ z →
      height x y - height x z ≠ 0) :
    ∃ A : Finset (Q3Side b₁), ∃ T : Finset (Q3Side b₂),
      A.card = 3 ∧ T.card = 3 ∧ B = A.product T := by
  exact height_three_by_three_product B row col height (q3_side_card b₁)
    (q3_side_card b₂) hB hrow_mem hcol_mem hrow_card hcol_card hcolumn hopposite hstep

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q6TwoBlockRigidity

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q3StarHeight

abbrev Point := BitVec 3

/-- A leaf is obtained from its center by one coordinate flip. -/
def isLeaf (center leaf : Point) : Bool :=
  (center ^^^ leaf).cpop == 1#3

/-- A fixed scalar projection of the height on three axes. -/
def leafHeight (center leaf : Point) : ℤ :=
  (center ^^^ leaf).toNat

private def leafCheck (c d y z : Fin 8) : Prop :=
    isLeaf (BitVec.ofFin c) (BitVec.ofFin y) = true →
    isLeaf (BitVec.ofFin c) (BitVec.ofFin z) = true → y ≠ z →
      (leafHeight (BitVec.ofFin c) (BitVec.ofFin y) ≠ leafHeight (BitVec.ofFin c) (BitVec.ofFin z) ∧
        (c ≠ d → isLeaf (BitVec.ofFin d) (BitVec.ofFin y) = true →
          isLeaf (BitVec.ofFin d) (BitVec.ofFin z) = true →
          leafHeight (BitVec.ofFin c) (BitVec.ofFin y) - leafHeight (BitVec.ofFin c) (BitVec.ofFin z) =
          -(leafHeight (BitVec.ofFin d) (BitVec.ofFin y) -
            leafHeight (BitVec.ofFin d) (BitVec.ofFin z))))

private instance (c d y z : Fin 8) : Decidable (leafCheck c d y z) := by
  unfold leafCheck
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
-- Check the relative heights on the eight three-cube points.
private theorem leaf_check_all :
    let pts := List.finRange 8
    pts.all (fun c => pts.all (fun d => pts.all (fun y => pts.all
      (fun z => decide (leafCheck c d y z))))) = true := by
  decide +kernel

private theorem leaf_checks (c d y z : Fin 8) : leafCheck c d y z := by
  have hc := List.all_eq_true.mp leaf_check_all c (List.mem_finRange c)
  have hd := List.all_eq_true.mp hc d (List.mem_finRange d)
  have hy := List.all_eq_true.mp hd y (List.mem_finRange y)
  exact of_decide_eq_true (List.all_eq_true.mp hy z (List.mem_finRange z))

/-- Three-leaf rows in a four-pattern block form one product under the
Laurent height. The scalar height uses distinct coefficients on the axes. -/
theorem product_of_star_rows {X Y : Type*} [Fintype X] [Fintype Y]
    (B : Finset (X × Y)) (row : X → Finset Y) (col : Y → Finset X)
    (hX : Fintype.card X = 4) (hY : Fintype.card Y = 4)
    (hB : B.Nonempty) (hrow : ∀ x y, (x, y) ∈ B ↔ y ∈ row x)
    (hcol : ∀ x y, (x, y) ∈ B ↔ x ∈ col y)
    (hrowCard : ∀ {x}, (row x).Nonempty → (row x).card = 3)
    (hcolCard : ∀ {y}, (col y).Nonempty → (col y).card = 3)
    (pattern : Y ↪ Point) (center : X → Point) (offset : X → ℤ) (height : Y → ℤ)
    (hleaf : ∀ {x}, (row x).Nonempty → ∀ y, y ∈ row x ↔
      isLeaf (center x) (pattern y) = true)
    (hheight : ∀ {x y}, y ∈ row x → height y = offset x + leafHeight (center x) (pattern y)) :
    ∃ A : Finset X, ∃ T : Finset Y, A.card = 3 ∧ T.card = 3 ∧ B = A.product T := by
  classical
  apply Q6TwoBlockRigidity.height_three_by_three_product B row col (fun _ => height)
    hX hY hB hrow hcol hrowCard hcolCard (fun _ _ _ => rfl)
  · intro x x' y z _ hy hy' hz hz' hr
    have hcenter : center x ≠ center x' := by
      intro h
      apply hr
      ext w
      rw [hleaf ⟨y, hy⟩ w, hleaf ⟨y, hy'⟩ w, h]
    by_cases heq : y = z
    · subst z
      simp
    have hn : (pattern y).toFin ≠ (pattern z).toFin := fun h =>
      heq (pattern.injective (BitVec.eq_of_toFin_eq h))
    have hd : (center x).toFin ≠ (center x').toFin := fun h =>
      hcenter (BitVec.eq_of_toFin_eq h)
    have hh := (leaf_checks (center x).toFin (center x').toFin (pattern y).toFin
      (pattern z).toFin ((hleaf ⟨y, hy⟩ y).mp hy) ((hleaf ⟨z, hz⟩ z).mp hz) hn).2 hd
      ((hleaf ⟨y, hy'⟩ y).mp hy') ((hleaf ⟨z, hz'⟩ z).mp hz')
    change leafHeight (center x) (pattern y) - leafHeight (center x) (pattern z) =
      -(leafHeight (center x') (pattern y) - leafHeight (center x') (pattern z)) at hh
    have h₁ := hheight hy
    have h₂ := hheight hz
    have h₃ := hheight hy'
    have h₄ := hheight hz'
    omega
  · intro x y z hy hz hyz
    have hn : (pattern y).toFin ≠ (pattern z).toFin := fun h =>
      hyz (pattern.injective (BitVec.eq_of_toFin_eq h))
    have hd := (leaf_checks (center x).toFin (center x).toFin (pattern y).toFin
      (pattern z).toFin ((hleaf ⟨y, hy⟩ y).mp hy) ((hleaf ⟨z, hz⟩ z).mp hz) hn).1
    change leafHeight (center x) (pattern y) ≠ leafHeight (center x) (pattern z) at hd
    have h₁ := hheight hy
    have h₂ := hheight hz
    omega

/-- Under the same height condition, a support whose occupied rows and
columns are cube stars is exactly the product of two stars. -/
theorem star_product_of_affine_rows {X Y : Type*} [Fintype X] [Fintype Y]
    (B : Finset (X × Y)) (row : X → Finset Y) (col : Y → Finset X)
    (hX : Fintype.card X = 4) (hY : Fintype.card Y = 4)
    (hB : B.Nonempty) (hrow : ∀ x y, (x, y) ∈ B ↔ y ∈ row x)
    (hcol : ∀ x y, (x, y) ∈ B ↔ x ∈ col y)
    (hrowCard : ∀ {x}, (row x).Nonempty → (row x).card = 3)
    (hcolCard : ∀ {y}, (col y).Nonempty → (col y).card = 3)
    (xPattern : X ↪ Point) (yPattern : Y ↪ Point)
    (xCenter : Y → Point) (yCenter : X → Point) (offset : X → ℤ) (height : Y → ℤ)
    (hrowLeaf : ∀ {x}, (row x).Nonempty → ∀ y, y ∈ row x ↔
      isLeaf (yCenter x) (yPattern y) = true)
    (hcolLeaf : ∀ {y}, (col y).Nonempty → ∀ x, x ∈ col y ↔
      isLeaf (xCenter y) (xPattern x) = true)
    (hheight : ∀ {x y}, y ∈ row x → height y = offset x + leafHeight (yCenter x) (yPattern y)) :
    ∃ c d : Point, ∀ x y, (x, y) ∈ B ↔
      isLeaf c (xPattern x) = true ∧ isLeaf d (yPattern y) = true := by
  classical
  obtain ⟨A, T, _, _, hprod⟩ := product_of_star_rows B row col hX hY hB hrow hcol
    hrowCard hcolCard yPattern yCenter offset height hrowLeaf hheight
  obtain ⟨⟨x₀, y₀⟩, h₀⟩ := hB
  have hm (x : X) (y : Y) : (x, y) ∈ B ↔ x ∈ A ∧ y ∈ T := by
    rw [hprod, Finset.product_eq_sprod, Finset.mem_product]
  obtain ⟨hx₀, hy₀⟩ := (hm x₀ y₀).mp h₀
  have hcol₀ : (col y₀).Nonempty := ⟨x₀, (hcol x₀ y₀).mp h₀⟩
  have hrow₀ : (row x₀).Nonempty := ⟨y₀, (hrow x₀ y₀).mp h₀⟩
  refine ⟨xCenter y₀, yCenter x₀, fun x y => ?_⟩
  rw [← hcolLeaf hcol₀, ← hrowLeaf hrow₀, ← hcol x y₀, ← hrow x₀ y, hm, hm, hm]
  simp [hx₀, hy₀]


end Q3StarHeight
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9TriplePartitions

open Finset
open BalancedCriticalSpectrum (Q)
local notation "cubeFlip" => BalancedCriticalSpectrum.flip
open Q9LaurentGainPartition (Side Exponent LaurentIdentity axis)
open Q9LaurentCommonTriple (Axes inside outside fiber star UniqueCommonNeighbor)
open Q3StarHeight (isLeaf leafHeight)
open private mem_star from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentCommonTriple

private theorem inside_flip (e : Axes) (x : Q 9) (j : Fin 3) :
    inside e (cubeFlip x (e (.inl j))) = cubeFlip (inside e x) j := by
  funext k
  by_cases h : k = j
  · subst k
    simp [inside, BalancedCriticalSpectrum.flip]
  · have h' : e (.inl k) ≠ e (.inl j) := fun he => h (Sum.inl.inj (e.injective he))
    simp [inside, BalancedCriticalSpectrum.flip, h, h']

private theorem bit_flip (x : BitVec 3) (j : Fin 3) :
    (cubeBitVec 3).symm (cubeFlip (cubeBitVec 3 x) j) = x ^^^ BitVec.ofNat 3 (2 ^ j.val) := by
  apply (cubeBitVec 3).injective
  rw [Equiv.apply_symm_apply, cubeBitVec_xor_single]
  rfl

private theorem leaf_cardinalities : ∀ j : Fin 3,
    (BitVec.ofNat 3 (2 ^ j.val)).cpop = 1#3 ∧ (BitVec.ofNat 3 (2 ^ j.val)).toNat = 2 ^ j.val := by
  decide +kernel

private theorem one_bit : ∀ d : Fin 8, (BitVec.ofFin d : BitVec 3).cpop = 1#3 →
    ∃ j : Fin 3, (BitVec.ofFin d : BitVec 3) = BitVec.ofNat 3 (2 ^ j.val) := by
  decide +kernel

private theorem flip_from_leaf {e : Axes} {c : Q 9} {p : BitVec 3}
    (h : isLeaf ((cubeBitVec 3).symm (inside e c)) p = true) :
    ∃ j : Fin 3, (cubeBitVec 3).symm (inside e (cubeFlip c (e (.inl j)))) = p := by
  let q := (cubeBitVec 3).symm (inside e c)
  have hcp : (q ^^^ p).cpop = 1#3 := beq_iff_eq.mp h
  obtain ⟨j, hj⟩ := one_bit (q ^^^ p).toFin hcp
  change q ^^^ p = BitVec.ofNat 3 (2 ^ j.val) at hj
  refine ⟨j, ?_⟩
  rw [inside_flip, ← show cubeBitVec 3 q = inside e c from Equiv.apply_symm_apply _ _, bit_flip,
    ← hj, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The scalar height on the triple assigns the distinct increments 1, 2, and 4. -/
def scalarHeight (e : Axes) (a : Exponent) : ℤ :=
  ∑ i : Fin 3, (2 : ℤ) ^ i.val * a (e (.inl i))

private theorem scalarHeight_add_axis (e : Axes) (k : Exponent) (j : Fin 3) :
    scalarHeight e (k + axis (e (.inl j))) = scalarHeight e k + (2 : ℤ) ^ j.val := by
  unfold scalarHeight
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  congr 1
  calc
    _ = (2 : ℤ) ^ j.val * axis (e (.inl j)) (e (.inl j)) := by
      refine Finset.sum_eq_single j ?_ (by simp)
      intro i _ hij
      have hne : e (.inl i) ≠ e (.inl j) := fun he => hij (Sum.inl.inj (e.injective he))
      simp [axis, hne]
    _ = _ := by simp [axis]

variable {C : Finset (Q 9)} {b : Bool} {S : Block} {root : Side C b}

/-- An occupied fiber of the selected transverse support projects bijectively
onto the leaves of a three-cube star. Its original exponent has the affine
height formula in the bit-vector chart. -/
theorem transverseFiber_bitStar {e : Axes} {a : Side C b → Exponent}
    (h : LaurentIdentity a) (hstar : UniqueCommonNeighbor (transverseSupport S root) b e)
    (x : Side (transverseSupport S root) b) :
    ∃ c : BitVec 3, ∃ k : ℤ,
      (∀ p : BitVec 3, isLeaf c p = true ↔ ∃ y : Side (transverseSupport S root) b,
        outside e y.val = outside e x.val ∧ (cubeBitVec 3).symm (inside e y.val) = p) ∧
      ∀ y : Side (transverseSupport S root) b, outside e y.val = outside e x.val →
        scalarHeight e (a (liftTransverse y)) =
          k + leafHeight c ((cubeBitVec 3).symm (inside e y.val)) := by
  classical
  obtain ⟨c, _, k, hF, hheight⟩ := transverseFiber_star_offset h hstar x
  let c' := (cubeBitVec 3).symm (inside e c)
  refine ⟨c', scalarHeight e k, ?_, ?_⟩
  · intro p
    constructor
    · intro hp
      obtain ⟨j, hj⟩ := flip_from_leaf (e := e) (c := c) hp
      let y := cubeFlip c (e (.inl j))
      have hy : y ∈ fiber (transverseSupport S root) b e (outside e x.val) := by
        rw [hF]
        exact mem_star.mpr ⟨j, rfl⟩
      obtain ⟨hmem, hpar, hout⟩ := mem_filter.mp hy
      exact ⟨⟨y, hmem, hpar⟩, hout, hj⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨j, hj, _⟩ := hheight y hy
      rw [← hj, inside_flip, ← show cubeBitVec 3 c' = inside e c from Equiv.apply_symm_apply _ _,
        bit_flip]
      unfold isLeaf
      rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, (leaf_cardinalities j).1]
      rfl
  · intro y hy
    obtain ⟨j, hj, hk⟩ := hheight y hy
    rw [hk, scalarHeight_add_axis, ← hj, inside_flip,
      ← show cubeBitVec 3 c' = inside e c from Equiv.apply_symm_apply _ _, bit_flip]
    unfold leafHeight
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, (leaf_cardinalities j).2]
    norm_cast

private theorem axis_bit : ∀ i j : Fin 3,
    (((BitVec.ofNat 3 (2 ^ i.val)).getLsbD j.val).toNat : ℤ) = if j = i then 1 else 0 := by
  decide +kernel

/-- The full vector height on a transverse fiber agrees with its three
flipped-bit indicators up to fixed offsets. -/
theorem transverseFiber_vectorHeight {e : Axes} {a : Side C b → Exponent}
    (h : LaurentIdentity a) (hstar : UniqueCommonNeighbor (transverseSupport S root) b e)
    (x : Side (transverseSupport S root) b) :
    ∃ c : BitVec 3, ∃ k : Fin 3 → ℤ,
      (∀ p : BitVec 3, isLeaf c p = true ↔ ∃ y : Side (transverseSupport S root) b,
        outside e y.val = outside e x.val ∧ (cubeBitVec 3).symm (inside e y.val) = p) ∧
      ∀ (y : Side (transverseSupport S root) b), outside e y.val = outside e x.val →
        ∀ j : Fin 3, a (liftTransverse y) (e (.inl j)) =
          k j + ((c ^^^ (cubeBitVec 3).symm (inside e y.val)).getLsbD j.val).toNat := by
  classical
  obtain ⟨c, _, k, hF, hheight⟩ := transverseFiber_star_offset h hstar x
  let c' := (cubeBitVec 3).symm (inside e c)
  refine ⟨c', fun j => k (e (.inl j)), ?_, ?_⟩
  · intro p
    constructor
    · intro hp
      obtain ⟨j, hj⟩ := flip_from_leaf (e := e) (c := c) hp
      let y := cubeFlip c (e (.inl j))
      have hy : y ∈ fiber (transverseSupport S root) b e (outside e x.val) := by
        rw [hF]
        exact mem_star.mpr ⟨j, rfl⟩
      obtain ⟨hmem, hpar, hout⟩ := mem_filter.mp hy
      exact ⟨⟨y, hmem, hpar⟩, hout, hj⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨j, hj, _⟩ := hheight y hy
      rw [← hj, inside_flip, ← show cubeBitVec 3 c' = inside e c from Equiv.apply_symm_apply _ _,
        bit_flip]
      unfold isLeaf
      rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, (leaf_cardinalities j).1]
      rfl
  · intro y hy j
    obtain ⟨i, hi, hk⟩ := hheight y hy
    rw [hk, ← hi, inside_flip,
      ← show cubeBitVec 3 c' = inside e c from Equiv.apply_symm_apply _ _, bit_flip,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, axis_bit]
    simp only [Pi.add_apply, axis, e.injective.eq_iff, Sum.inl.injEq]

/-- A star fiber can change its exponent only in the axes of the star. -/
theorem fiber_exponent_eq_of_axis_outside {e : Axes} {a : Side C b → Exponent}
    (h : LaurentIdentity a) (hstar : UniqueCommonNeighbor (transverseSupport S root) b e)
    (x y : Side (transverseSupport S root) b) (hout : outside e y.val = outside e x.val)
    (i : Fin 9) (hi : ∀ j : Fin 3, i ≠ e (.inl j)) :
    a (liftTransverse x) i = a (liftTransverse y) i := by
  obtain ⟨_, _, k, _, hk⟩ := transverseFiber_star_offset h hstar x
  obtain ⟨j, _, hx⟩ := hk x rfl
  obtain ⟨l, _, hy⟩ := hk y hout
  rw [hx, hy]
  simp [axis, hi j, hi l]


end Q9TriplePartitions
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9TriplePartitions

open Finset
open BalancedCriticalSpectrum (Q)
open Q9LaurentGainPartition (Side Exponent LaurentIdentity axis)
open Q9LaurentCommonTriple (Axes inside outside UniqueCommonNeighbor)
open Q6TwoBlockRigidity (Q3Side q3_side_card)
open Q3StarHeight (isLeaf leafHeight)
open private cubeParity from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private def sideBit (p : Bool) : Q3Side p ↪ BitVec 3 where
  toFun x := (cubeBitVec 3).symm x.val
  inj' := by
    intro x y h
    exact Subtype.ext ((cubeBitVec 3).symm.injective h)

private def allPoints : Finset (BitVec 3) := (univ : Finset (Fin 8)).image BitVec.ofFin

private theorem mem_allPoints (v : BitVec 3) : v ∈ allPoints :=
  mem_image.mpr ⟨v.toFin, mem_univ _, rfl⟩

private def leaves (c : BitVec 3) : Finset (BitVec 3) :=
  allPoints.filter (fun x => isLeaf c x = true)

private theorem leaves_card_check : ∀ c : Fin 8, (leaves (BitVec.ofFin c)).card = 3 := by
  decide +kernel

private theorem leaves_card (c : BitVec 3) : (leaves c).card = 3 := leaves_card_check c.toFin

private theorem scalarHeight_eq_of_outside {eL eR : Axes} {k : Exponent} {j : Fin 3}
    (hdisj : ∀ i : Fin 3, eR (.inl i) ≠ eL (.inl j)) :
    scalarHeight eR (k + axis (eL (.inl j))) = scalarHeight eR k := by
  unfold scalarHeight
  apply Finset.sum_congr rfl
  intro i _
  simp [axis, hdisj i]

variable {C : Finset (Q 9)} {b : Bool} {S : Block} {root : Side C b}
local notation "V" => Side (transverseSupport S root) b

set_option maxHeartbeats 2000000 in
-- Elaboration compares the distinct chart subtypes and their images.
/-- If both complementary triples have unique stars, the original Laurent
exponent forces their two sets of parity-compatible patterns to factor.
The chart assumptions express the fixed shared pattern and the disjoint cuts. -/
theorem actual_transverse_star_product {a : Side C b → Exponent} (h : LaurentIdentity a)
    (eL eR : Axes) (qL qR : Bool) (base : V)
    (hL : UniqueCommonNeighbor (transverseSupport S root) b eL)
    (hR : UniqueCommonNeighbor (transverseSupport S root) b eR)
    (hpL : ∀ x : V, cubeParity (inside eL x.val) = qL)
    (hpR : ∀ x : V, cubeParity (inside eR x.val) = qR)
    (hchartL : ∀ x y : V, outside eL x.val = outside eL y.val ↔
      inside eR x.val = inside eR y.val)
    (hchartR : ∀ x y : V, outside eR x.val = outside eR y.val ↔
      inside eL x.val = inside eL y.val)
    (hdisj : ∀ i j : Fin 3, eR (.inl i) ≠ eL (.inl j)) :
    ∃ c d : BitVec 3, ∀ u v : BitVec 3,
      (isLeaf c u = true ∧ isLeaf d v = true) ↔
      ∃ x : V, (cubeBitVec 3).symm (inside eL x.val) = u ∧
        (cubeBitVec 3).symm (inside eR x.val) = v := by
  classical
  let L (v : V) : Q3Side qL := ⟨inside eL v.val, hpL v⟩
  let R (v : V) : Q3Side qR := ⟨inside eR v.val, hpR v⟩
  let B : Finset (Q3Side qL × Q3Side qR) := univ.image (fun v : V => (L v, R v))
  let row (x : Q3Side qL) := univ.filter (fun y : Q3Side qR => (x, y) ∈ B)
  let col (y : Q3Side qR) := univ.filter (fun x : Q3Side qL => (x, y) ∈ B)
  have hB (x : Q3Side qL) (y : Q3Side qR) : (x, y) ∈ B ↔
      ∃ v : V, L v = x ∧ R v = y := by simp [B, Prod.mk.injEq]
  have hrow (x : Q3Side qL) (y : Q3Side qR) : (x, y) ∈ B ↔ y ∈ row x := by simp [row]
  have hcol (x : Q3Side qL) (y : Q3Side qR) : (x, y) ∈ B ↔ x ∈ col y := by simp [col]
  have hheightFactors : Function.FactorsThrough (fun v : V => scalarHeight eR (a (liftTransverse v))) R := by
    intro v w heq
    have hout := (hchartL w v).mpr (congrArg Subtype.val heq.symm)
    obtain ⟨_, _, k, _, hk⟩ := transverseFiber_star_offset h hL v
    obtain ⟨j, _, hv⟩ := hk v rfl
    obtain ⟨l, _, hw⟩ := hk w hout
    change scalarHeight eR (a (liftTransverse v)) = scalarHeight eR (a (liftTransverse w))
    rw [hv, hw, scalarHeight_eq_of_outside (hdisj · j), scalarHeight_eq_of_outside (hdisj · l)]
  obtain ⟨height, hHeight⟩ := (Function.factorsThrough_iff _).mp hheightFactors
  have hRight (x : Q3Side qL) (hx : (row x).Nonempty) : ∃ c : BitVec 3, ∃ k : ℤ,
      (∀ p : BitVec 3, isLeaf c p = true ↔ ∃ y ∈ row x, sideBit qR y = p) ∧
      ∀ y ∈ row x, height y = k + leafHeight c (sideBit qR y) := by
    obtain ⟨y, hy⟩ := hx
    obtain ⟨v, hv, _⟩ := (hB x y).mp ((hrow x y).mpr hy)
    obtain ⟨c, k, hc, hk⟩ := transverseFiber_bitStar h hR v
    refine ⟨c, k, ?_, ?_⟩
    · intro p
      rw [hc]
      constructor
      · rintro ⟨w, hout, hbit⟩
        have hw : L w = x := (Subtype.ext ((hchartR w v).mp hout)).trans hv
        exact ⟨R w, (hrow x (R w)).mp ((hB x (R w)).mpr ⟨w, hw, rfl⟩), hbit⟩
      · rintro ⟨z, hz, hbit⟩
        obtain ⟨w, hw, hrw⟩ := (hB x z).mp ((hrow x z).mpr hz)
        exact ⟨w, (hchartR w v).mpr (congrArg Subtype.val (hw.trans hv.symm)),
          (congrArg (sideBit qR) hrw).trans hbit⟩
    · intro z hz
      obtain ⟨w, hw, hrw⟩ := (hB x z).mp ((hrow x z).mpr hz)
      have hout := (hchartR w v).mpr (congrArg Subtype.val (hw.trans hv.symm))
      have he := congrFun hHeight w
      change scalarHeight eR (a (liftTransverse w)) = height (R w) at he
      have hh := hk w hout
      change scalarHeight eR (a (liftTransverse w)) = k + leafHeight c (sideBit qR (R w)) at hh
      have hz' := he.symm.trans hh
      rw [hrw] at hz'
      exact hz'
  have hLeft (y : Q3Side qR) (hy : (col y).Nonempty) : ∃ c : BitVec 3,
      ∀ p : BitVec 3, isLeaf c p = true ↔ ∃ x ∈ col y, sideBit qL x = p := by
    obtain ⟨x, hx⟩ := hy
    obtain ⟨v, _, hv⟩ := (hB x y).mp ((hcol x y).mpr hx)
    obtain ⟨c, _, hc, _⟩ := transverseFiber_bitStar h hL v
    refine ⟨c, fun p => ?_⟩
    rw [hc]
    constructor
    · rintro ⟨w, hout, hbit⟩
      have hw : R w = y := (Subtype.ext ((hchartL w v).mp hout)).trans hv
      exact ⟨L w, (hcol (L w) y).mp ((hB (L w) y).mpr ⟨w, rfl, hw⟩), hbit⟩
    · rintro ⟨z, hz, hbit⟩
      obtain ⟨w, hlw, hw⟩ := (hB z y).mp ((hcol z y).mpr hz)
      exact ⟨w, (hchartL w v).mpr (congrArg Subtype.val (hw.trans hv.symm)),
        (congrArg (sideBit qL) hlw).trans hbit⟩
  have image_leaves {p : Bool} {F : Finset (Q3Side p)} {c : BitVec 3}
      (hs : ∀ v, isLeaf c v = true ↔ ∃ x ∈ F, sideBit p x = v) :
      F.image (sideBit p) = leaves c := by
    ext v
    simpa only [leaves, mem_filter, mem_allPoints, true_and, mem_image] using (hs v).symm
  have card_of_leaves {p : Bool} {F : Finset (Q3Side p)} {c : BitVec 3}
      (hs : ∀ v, isLeaf c v = true ↔ ∃ x ∈ F, sideBit p x = v) : F.card = 3 := by
    rw [← card_image_of_injective F (sideBit p).injective, image_leaves hs, leaves_card]
  have mem_of_leaves {p : Bool} {F : Finset (Q3Side p)} {c : BitVec 3}
      (hs : ∀ v, isLeaf c v = true ↔ ∃ x ∈ F, sideBit p x = v) (x : Q3Side p) :
      x ∈ F ↔ isLeaf c (sideBit p x) = true := by
    constructor
    · intro hx
      exact (hs _).mpr ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨y, hy, he⟩ := (hs _).mp hx
      exact (sideBit p).injective he ▸ hy
  let yCenter (x : Q3Side qL) := if hx : (row x).Nonempty then (hRight x hx).choose else 0#3
  let offset (x : Q3Side qL) := if hx : (row x).Nonempty then
    (hRight x hx).choose_spec.choose else 0
  let xCenter (y : Q3Side qR) := if hy : (col y).Nonempty then (hLeft y hy).choose else 0#3
  have hr (x : Q3Side qL) (hx : (row x).Nonempty) := (hRight x hx).choose_spec.choose_spec
  have hl (y : Q3Side qR) (hy : (col y).Nonempty) := (hLeft y hy).choose_spec
  obtain ⟨c, d, hcd⟩ := Q3StarHeight.star_product_of_affine_rows B row col
    (q3_side_card qL) (q3_side_card qR) ⟨_, (hB (L base) (R base)).mpr ⟨base, rfl, rfl⟩⟩
    hrow hcol (fun {x} hx => card_of_leaves (hr x hx).1) (fun {y} hy => card_of_leaves (hl y hy))
    (sideBit qL) (sideBit qR) xCenter yCenter offset height
    (fun {x} hx y => by simpa only [yCenter, dite_eq_left hx] using mem_of_leaves (hr x hx).1 y)
    (fun {y} hy x => by simpa only [xCenter, dite_eq_left hy] using mem_of_leaves (hl y hy) x)
    (fun {x y} hy => by
      have hx : (row x).Nonempty := ⟨y, hy⟩
      simpa only [offset, yCenter, dite_eq_left hx] using (hr x hx).2 y hy)
  have hBase := (hcd (L base) (R base)).mp ((hB (L base) (R base)).mpr ⟨base, rfl, rfl⟩)
  have hc0 := hBase.1
  have hd0 := hBase.2
  refine ⟨c, d, fun u v => ?_⟩
  constructor
  · rintro ⟨hu, hv⟩
    have parityLeaves : ∀ c u v : Fin 8, isLeaf (BitVec.ofFin c) (BitVec.ofFin u) = true →
        isLeaf (BitVec.ofFin c) (BitVec.ofFin v) = true →
        cubeParity (cubeBitVec 3 (BitVec.ofFin u)) = cubeParity (cubeBitVec 3 (BitVec.ofFin v)) := by
      decide +kernel
    have hpu := parityLeaves c.toFin (sideBit qL (L base)).toFin u.toFin hc0 hu
    have hpv := parityLeaves d.toFin (sideBit qR (R base)).toFin v.toFin hd0 hv
    change cubeParity (cubeBitVec 3 ((cubeBitVec 3).symm (L base).val)) =
      cubeParity (cubeBitVec 3 u) at hpu
    change cubeParity (cubeBitVec 3 ((cubeBitVec 3).symm (R base).val)) =
      cubeParity (cubeBitVec 3 v) at hpv
    rw [Equiv.apply_symm_apply] at hpu hpv
    let x : Q3Side qL := ⟨cubeBitVec 3 u, hpu.symm.trans (L base).property⟩
    let y : Q3Side qR := ⟨cubeBitVec 3 v, hpv.symm.trans (R base).property⟩
    have hx : sideBit qL x = u := Equiv.symm_apply_apply _ _
    have hy : sideBit qR y = v := Equiv.symm_apply_apply _ _
    obtain ⟨w, hw, hwr⟩ := (hB x y).mp ((hcd x y).mpr ⟨hx.symm ▸ hu, hy.symm ▸ hv⟩)
    exact ⟨w, (congrArg (sideBit qL) hw).trans hx, (congrArg (sideBit qR) hwr).trans hy⟩
  · rintro ⟨w, rfl, rfl⟩
    exact (hcd (L w) (R w)).mp ((hB (L w) (R w)).mpr ⟨w, rfl, rfl⟩)


end Q9TriplePartitions
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9TriplePartitions

open BalancedCriticalSpectrum (Q)
open Q9LaurentGainPartition (Side Exponent LaurentIdentity)
open Q9LaurentCommonTriple (Axes inside outside UniqueCommonNeighbor)
open Q3StarHeight (isLeaf)

private theorem leaf_subset_check : ∀ c d : Fin 8,
    (∀ u : Fin 8, isLeaf (BitVec.ofFin c) (BitVec.ofFin u) = true →
      isLeaf (BitVec.ofFin d) (BitVec.ofFin u) = true) → c = d := by
  decide +kernel

private theorem center_of_leaf_subset (c d : BitVec 3)
    (h : ∀ u : BitVec 3, isLeaf c u = true → isLeaf d u = true) : c = d :=
  BitVec.eq_of_toFin_eq (leaf_subset_check c.toFin d.toFin fun u => h (BitVec.ofFin u))

variable {C : Finset (Q 9)} {b : Bool} {S : Block} {root : Side C b}
local notation "V" => Side (transverseSupport S root) b

/-- A transverse product of two stars has one vector offset on the right
block. Left-star moves preserve the right exponent, so one right-star row
determines the height formula on the whole product. -/
theorem right_height_on_transverse_product {a : Side C b → Exponent} (h : LaurentIdentity a)
    (eL eR : Axes) (base : V) (c d : BitVec 3)
    (hL : UniqueCommonNeighbor (transverseSupport S root) b eL)
    (hR : UniqueCommonNeighbor (transverseSupport S root) b eR)
    (hchartL : ∀ x y : V, outside eL x.val = outside eL y.val ↔
      inside eR x.val = inside eR y.val)
    (hchartR : ∀ x y : V, outside eR x.val = outside eR y.val ↔
      inside eL x.val = inside eL y.val)
    (hdisj : ∀ i j : Fin 3, eR (.inl i) ≠ eL (.inl j))
    (hprod : ∀ u v : BitVec 3,
      (isLeaf c u = true ∧ isLeaf d v = true) ↔
      ∃ x : V, (cubeBitVec 3).symm (inside eL x.val) = u ∧
        (cubeBitVec 3).symm (inside eR x.val) = v) :
    ∃ k : Fin 3 → ℤ, ∀ (x : V) (j : Fin 3),
      a (liftTransverse x) (eR (.inl j)) =
        k j + ((d ^^^ (cubeBitVec 3).symm (inside eR x.val)).getLsbD j.val).toNat := by
  let u := (cubeBitVec 3).symm (inside eL base.val)
  have hu : isLeaf c u = true := ((hprod _ _).mpr ⟨base, rfl, rfl⟩).1
  obtain ⟨d', k, hrow, hk⟩ := transverseFiber_vectorHeight h hR base
  have heq : d' = d := by
    apply center_of_leaf_subset
    intro v hv
    obtain ⟨y, _, hy⟩ := (hrow v).mp hv
    exact ((hprod _ v).mpr ⟨y, rfl, hy⟩).2
  subst d'
  refine ⟨k, ?_⟩
  intro x j
  let v := (cubeBitVec 3).symm (inside eR x.val)
  have hv : isLeaf d v = true := ((hprod _ _).mpr ⟨x, rfl, rfl⟩).2
  obtain ⟨y, hyu, hyv⟩ := (hprod u v).mp ⟨hu, hv⟩
  have hyL := (hchartL y x).mpr ((cubeBitVec 3).symm.injective hyv)
  have hyR := (hchartR y base).mpr ((cubeBitVec 3).symm.injective hyu)
  have hstay := fiber_exponent_eq_of_axis_outside h hL x y hyL (eR (.inl j)) (hdisj j)
  rw [hstay, hk y hyR, hyv]


end Q9TriplePartitions
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
