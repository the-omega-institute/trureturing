/- GID: D5/S3/Combinatorics/Geometry/MiuraFiberJoint
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraFiberJoint
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Entire two-axis indexed vectors are realized on one actual residual array. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraFiberReadback
import all D5.S3.Combinatorics.Geometry.MiuraCoreTranspose
import all D5.S3.Combinatorics.Geometry.MiuraCoreJoint
import all D5.S3.Combinatorics.Geometry.MiuraFiberIndexed

/-! Joint actual realization and exact extremum coordinates for both length vectors. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraFiberJoint
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreResidual
  MiuraCoreBoundary MiuraCoreFrozenSlope MiuraCoreNormal MiuraCoreJoint
  MiuraCoreTranspose MiuraSlabIncidence MiuraFiberIndexed MiuraFiberReadback
open private transpose_min_iff transpose_max_iff
  from D5.S3.Combinatorics.Geometry.MiuraCoreTranspose
open private column_chain_joint column_chain_transpose_joint joint_trans
  from D5.S3.Combinatorics.Geometry.MiuraCoreJoint
open private position_lt expansion_active from D5.S3.Combinatorics.Geometry.MiuraFiberIndexed
open scoped BigOperators
variable {m n M N : ℕ}

/-- Each actual minimum and maximum has both prescribed cumulative coordinates. -/
def JointExtremaExpansion (h : Cell m n → ℤ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (g : Cell M N → ℤ) : Prop :=
  (∀ q, IsStrictLocalMin g q ↔ ∃ p, IsStrictLocalMin h p ∧
    q.1.val = columnPosition r p.1 ∧ q.2.val = columnPosition c p.2) ∧
  (∀ q, IsStrictLocalMax g q ↔ ∃ p, IsStrictLocalMax h p ∧
    q.1.val = columnPosition r p.1 ∧ q.2.val = columnPosition c p.2)

private theorem column_expansion_row_active (h : Cell m n → ℤ) (c : Fin n → ℕ)
    (g : Cell m (n + ∑ j,c j) → ℤ) (he : ColumnExtremaExpansion h c g) (i : Fin m) :
    activeColumn (transposeHeight g) i ↔ activeColumn (transposeHeight h) i := by
  simp only [activeColumn,IsStrictLocalExtremum,transpose_min_iff,transpose_max_iff]
  constructor
  · rintro ⟨k,hk | hk⟩
    · obtain ⟨p,hp,heq,_⟩ := (he.2 (i,k)).mp hk
      exact ⟨p.2,Or.inl (by change i = p.1 at heq; rw [heq]; exact hp)⟩
    · obtain ⟨p,hp,heq,_⟩ := (he.1 (i,k)).mp hk
      exact ⟨p.2,Or.inr (by change i = p.1 at heq; rw [heq]; exact hp)⟩
  · rintro ⟨j,hj | hj⟩
    · exact ⟨⟨columnPosition c j,position_lt c j⟩,
        Or.inl ((he.2 _).mpr ⟨(i,j),hj,rfl,rfl⟩)⟩
    · exact ⟨⟨columnPosition c j,position_lt c j⟩,
        Or.inr ((he.1 _).mpr ⟨(i,j),hj,rfl,rfl⟩)⟩

/-- All coordinates on both axes are realized simultaneously, with the exact normalized
function class, legal reduction to the given core, and every individual extremum retained. -/
theorem indexed_joint_expansion (a b : ℕ) (h : Cell m n → ℤ)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hr : Residual a b h)
    (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrs : ∀ i, 0 < r i → frozenColumn (transposeHeight h) i)
    (hcs : ∀ j, 0 < c j → frozenColumn h j) :
    ∃ g : Cell (m + ∑ i,r i) (n + ∑ j,c j) → ℤ,
      Residual a b g ∧ JointReduction g h ∧ JointExtremaExpansion h r c g := by
  obtain ⟨f,hf,hfc,hec⟩ := indexed_column_expansion a b h (by omega) hr c hcs
  have hrs' : ∀ i, 0 < r i → frozenColumn (transposeHeight f) i := by
    intro i hi
    have hfi := hrs i hi
    apply (frozenColumn_iff_inactive _ (transpose_isHeight hf.1.1) i
      hfi.1 hfi.2.1 (by omega)).mpr
    intro ha
    exact frozenColumn_not_active _ i hfi ((column_expansion_row_active h c f hec i).mp ha)
  obtain ⟨t,ht,htr,her⟩ := indexed_column_expansion a b (transposeHeight f)
    (by omega) (transpose_residual a b f hf) r hrs'
  refine ⟨transposeHeight t,transpose_residual a b t ht,
    joint_trans (column_chain_transpose_joint htr) (column_chain_joint hfc),?_⟩
  constructor
  · intro q
    rw [transpose_min_iff,her.1]
    constructor
    · rintro ⟨p,hp,he1,he2⟩
      have hp' := (transpose_min_iff f p).mp hp
      obtain ⟨u,hu,he3,he4⟩ := (hec.1 (p.2,p.1)).mp hp'
      exact ⟨u,hu,he2.trans (congrArg (columnPosition r) he3),
        (congrArg Fin.val he1).trans he4⟩
    · rintro ⟨p,hp,he1,he2⟩
      let k : Fin (n+∑ j,c j) := ⟨columnPosition c p.2,position_lt c p.2⟩
      refine ⟨(k,p.1),?_,Fin.ext he2,he1⟩
      apply (transpose_min_iff f _).mpr
      exact (hec.1 _).mpr ⟨p,hp,rfl,rfl⟩
  · intro q
    rw [transpose_max_iff,her.2]
    constructor
    · rintro ⟨p,hp,he1,he2⟩
      have hp' := (transpose_max_iff f p).mp hp
      obtain ⟨u,hu,he3,he4⟩ := (hec.2 (p.2,p.1)).mp hp'
      exact ⟨u,hu,he2.trans (congrArg (columnPosition r) he3),
        (congrArg Fin.val he1).trans he4⟩
    · rintro ⟨p,hp,he1,he2⟩
      let k : Fin (n+∑ j,c j) := ⟨columnPosition c p.2,position_lt c p.2⟩
      refine ⟨(k,p.1),?_,Fin.ext he2,he1⟩
      apply (transpose_max_iff f _).mpr
      exact (hec.2 _).mpr ⟨p,hp,rfl,rfl⟩

private theorem joint_active_images (h : Cell m n → ℤ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (g : Cell M N → ℤ) (hM : M = m + ∑ i,r i) (hN : N = n + ∑ j,c j)
    (he : JointExtremaExpansion h r c g) :
    (∀ k, activeColumn g k ↔ ∃ j, activeColumn h j ∧ k.val = columnPosition c j) ∧
    (∀ k, activeColumn (transposeHeight g) k ↔
      ∃ i, activeColumn (transposeHeight h) i ∧ k.val = columnPosition r i) := by
  have hrow : ∀ i, columnPosition r i < M := by intro i; rw [hM]; exact position_lt r i
  have hcol : ∀ j, columnPosition c j < N := by intro j; rw [hN]; exact position_lt c j
  constructor
  · intro k
    constructor
    · rintro ⟨i,hi | hi⟩
      · obtain ⟨p,hp,_,heq⟩ := (he.2 (i,k)).mp hi
        exact ⟨p.2,⟨p.1,Or.inl hp⟩,heq⟩
      · obtain ⟨p,hp,_,heq⟩ := (he.1 (i,k)).mp hi
        exact ⟨p.2,⟨p.1,Or.inr hp⟩,heq⟩
    · rintro ⟨j,⟨i,hi | hi⟩,heq⟩
      · exact ⟨⟨columnPosition r i,hrow i⟩,Or.inl ((he.2 _).mpr ⟨(i,j),hi,rfl,heq⟩)⟩
      · exact ⟨⟨columnPosition r i,hrow i⟩,Or.inr ((he.1 _).mpr ⟨(i,j),hi,rfl,heq⟩)⟩
  · intro k
    simp only [activeColumn,IsStrictLocalExtremum,transpose_min_iff,transpose_max_iff]
    constructor
    · rintro ⟨j,hj | hj⟩
      · obtain ⟨p,hp,heq,_⟩ := (he.2 (k,j)).mp hj
        exact ⟨p.1,⟨p.2,Or.inl hp⟩,heq⟩
      · obtain ⟨p,hp,heq,_⟩ := (he.1 (k,j)).mp hj
        exact ⟨p.1,⟨p.2,Or.inr hp⟩,heq⟩
    · rintro ⟨i,⟨j,hj | hj⟩,heq⟩
      · exact ⟨⟨columnPosition c j,hcol j⟩,Or.inl ((he.2 _).mpr ⟨(i,j),hj,heq,rfl⟩)⟩
      · exact ⟨⟨columnPosition c j,hcol j⟩,Or.inr ((he.1 _).mpr ⟨(i,j),hj,heq,rfl⟩)⟩

/-- Equality of the actual output reads back both entire vectors on a reduced core. -/
theorem indexed_joint_weights_unique (h : Cell m n → ℤ) (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hrno : NoAdjacentFrozen (transposeHeight h)) (hcno : NoAdjacentFrozen h)
    (r r' : Fin m → ℕ) (c c' : Fin n → ℕ)
    (hrs : ∀ i, 0 < r i → frozenColumn (transposeHeight h) i)
    (hrs' : ∀ i, 0 < r' i → frozenColumn (transposeHeight h) i)
    (hcs : ∀ j, 0 < c j → frozenColumn h j)
    (hcs' : ∀ j, 0 < c' j → frozenColumn h j)
    (g : Cell M N → ℤ)
    (hM : M = m + ∑ i,r i) (hM' : M = m + ∑ i,r' i)
    (hN : N = n + ∑ j,c j) (hN' : N = n + ∑ j,c' j)
    (he : JointExtremaExpansion h r c g) (he' : JointExtremaExpansion h r' c' g) :
    r = r' ∧ c = c' := by
  have hi := joint_active_images h r c g hM hN he
  have hi' := joint_active_images h r' c' g hM' hN' he'
  exact ⟨indexed_column_weights_unique (transposeHeight h) (transpose_isHeight hh)
      (by omega) hm hrno r r' hrs hrs' (transposeHeight g) hM hM' hi.2 hi'.2,
    indexed_column_weights_unique h hh (by omega) hn hcno c c' hcs hcs' g hN hN' hi.1 hi'.1⟩

end D5.S3.Combinatorics.Geometry.MiuraFiberJoint
