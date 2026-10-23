/- GID: D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion
   generality: I
   mirror-B: D5/B/S3/Observer/Separation/FixedSkeletonWeightedInclusion
   mirror-E: none(waiver:symbolic-existence-and-bounds)
   anchors: []
   utility: none
   digest: The same actual Boolean addition family attains the least uniform exponent. -/

import D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.CutBounds

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion

open D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.RowCertificates
open D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.LabelledResponses
open D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.CutBounds
open scoped Classical

section WeightedBooleanSharpness
variable {A B Z : Type} [Fintype A] [Fintype B] [Fintype Z]
  [Nonempty A] [Nonempty B]
/-- Actual row membership, with the same complete selector suffix. -/
abbrev Row (φ : A → B → Z) (a : A) := {z // ∃ b, φ a b=z}
abbrev PositiveRow (φ : A → B → Z) (ell : Z → ℕ) (a : A) := {z : Row φ a // 0 < ell z.val}
abbrev Cell (m : ℕ) (ell : Z → ℕ) (z : Z) := ZMod (m^ell z)
abbrev Table (m : ℕ) (ell : Z → ℕ) := ∀ z,Cell m ell z
instance cellNeZero (m : ℕ) [NeZero m] (ell : Z → ℕ) (z : Z) : NeZero (m^ell z) :=
  ⟨pow_ne_zero _ (NeZero.ne m)⟩
noncomputable def zeroTest (φ : A → B → Z) (m : ℕ) (ell : Z → ℕ)
    (a b : Table m ell) (x : A) (y : B) : Bool := by
  classical
  exact decide (a (φ x y)+b (φ x y)=0)
/-- An exact common denominator from the pinned matrix-integer supplier.
No rationality or integer weight is supplied by the caller. -/
theorem integer_optimal_certificate (φ : A → B → Z) (hφ : ∀ z,∃ x y,φ x y=z) :
    ∃ (L : ℕ) (ell : Z → ℕ), 0 < L ∧
      ((∑ z,ell z : ℕ):ℝ)=(L:ℝ)*rowCoverNumber φ hφ ∧
      (∀ x, (∑ z : Row φ x,ell z.val) ≤ L) := by
  classical
  obtain ⟨w,hlam,hcover,hw,hrows,heq,_,_⟩ := optimal_row_cover_spec φ hφ
  let M : Matrix Z Unit ℚ := fun z _ => w z
  let L := M.den
  have hL : 0 < L := Nat.pos_of_ne_zero M.den_ne_zero
  have hden : (L:ℚ)≠0 := by exact_mod_cast hL.ne'
  have hnum (z : Z) : (M.num z () : ℚ)=(L:ℚ)*w z := by
    have h := (div_eq_iff hden).mp (M.num_div_den z ())
    simpa [M,L,mul_comm] using h
  have hn (z : Z) : 0 ≤ M.num z () := by
    have hwz := hw z
    have h : (0:ℚ) ≤ (M.num z () : ℚ) := by rw [hnum]; positivity
    exact_mod_cast h
  let ell : Z → ℕ := fun z => (M.num z ()).toNat
  have hell (z : Z) : (ell z : ℚ)=(L:ℚ)*w z := by
    have hc : ((ell z : ℕ):ℤ)=M.num z () := Int.toNat_of_nonneg (hn z)
    have hq : (ell z : ℚ)=(M.num z () : ℚ) := by exact_mod_cast hc
    exact hq.trans (hnum z)
  have htotal : ((∑ z,ell z : ℕ):ℚ)=(L:ℚ)*∑ z,w z := by
    rw [Nat.cast_sum,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => hell z)
  have hopt : ((∑ z,w z : ℚ):ℝ)=rowCoverNumber φ hφ := by
    rw [←heq,Rat.cast_sum]
    rfl
  refine ⟨L,ell,hL,?_,?_⟩
  · have hh : ((∑ z,ell z : ℕ):ℝ)=(L:ℝ)*((∑ z,w z : ℚ):ℝ) := by exact_mod_cast htotal
    rwa [hopt] at hh
  · intro x
    have hs : (∑ z : Row φ x,w z.val)=∑ z,if (∃ y,φ x y=z) then w z else 0 := by
      rw [←Finset.sum_filter]
      exact (Finset.sum_subtype (p := fun z => ∃ y,φ x y=z) (Finset.univ.filter (fun z => ∃ y,φ x y=z))
        (by intro z; simp [Row]) w).symm
    have hb : (∑ z : Row φ x,w z.val) ≤ 1 := by
      rw [hs]
      convert hrows x using 1
      apply Finset.sum_congr rfl
      intro z _
      by_cases h : ∃ y,φ x y=z <;> simp [h]
    have hscale : ((∑ z : Row φ x,ell z.val : ℕ):ℚ)=
        (L:ℚ)*∑ z : Row φ x,w z.val := by
      rw [Nat.cast_sum,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun z _ => hell z.val)
    have hq : ((∑ z : Row φ x,ell z.val : ℕ):ℚ) ≤ L := by
      rw [hscale]
      simpa using mul_le_mul_of_nonneg_left hb (by positivity : (0:ℚ) ≤ L)
    exact_mod_cast hq
private theorem table_card (m : ℕ) [NeZero m] (ell : Z → ℕ) :
    Nat.card (Table m ell)=m^(∑ z,ell z) := by
  classical
  simp only [Nat.card_eq_fintype_card,Fintype.card_pi,ZMod.card]
  exact Finset.prod_pow_eq_pow_sum Finset.univ ell m
private theorem row_table_card (φ : A → B → Z) (m : ℕ) [NeZero m] (ell : Z → ℕ) (x : A) :
    Nat.card (∀ z : Row φ x,Cell m ell z.val)=m^(∑ z : Row φ x,ell z.val) := by
  classical
  simp only [Nat.card_eq_fintype_card,Fintype.card_pi,ZMod.card]
  exact Finset.prod_pow_eq_pow_sum Finset.univ (fun z : Row φ x => ell z.val) m
/-- Only positive-weight coordinates can supply nonconstant zero flags. -/
private theorem positive_row_card (φ : A → B → Z) (ell : Z → ℕ) (x : A) :
    Nat.card (PositiveRow φ ell x) ≤ ∑ z : Row φ x,ell z.val := by
  classical
  let f : PositiveRow φ ell x → Σ z : Row φ x,Fin (ell z.val) :=
    fun z => ⟨z.val,⟨0,z.property⟩⟩
  have hf : Function.Injective f := by
    intro z z' h
    exact Subtype.ext (congrArg Sigma.fst h)
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_fin] using h
private theorem zero_weight_value (m : ℕ) (ell : Z → ℕ) (z : Z) (hz : ell z=0)
    (v : Cell m ell z) : v=0 := by
  have hmod : m^ell z=1 := by simp [hz]
  haveI : Subsingleton (ZMod (m^ell z)) := ZMod.subsingleton_iff.mpr hmod
  exact Subsingleton.elim _ _
/-- Signature of a real half-read addition prefix, tagged by its actual x. -/
abbrev MiddleSignature (φ : A → B → Z) (m : ℕ) (ell : Z → ℕ) :=
  Σ x : A,∀ z : Row φ x,Cell m ell z.val
noncomputable def middleSignature (φ : A → B → Z) (m : ℕ) (ell : Z → ℕ)
    (x : A) (a : Table m ell) : MiddleSignature φ m ell :=
  ⟨x,fun z => a z.val⟩
noncomputable def middleDecode (φ : A → B → Z) (m : ℕ) (ell : Z → ℕ)
    (v : MiddleSignature φ m ell) (b : Table m ell) (y : B) : Bool := by
  classical
  exact decide (v.2 ⟨φ v.1 y,⟨y,rfl⟩⟩+b (φ v.1 y)=0)
/-- Signature after addition has completed: raw observed y information is retained
by the caller's actual partial-coordinate extension; only positive row flags vary. -/
abbrev AfterSignature (φ : A → B → Z) (ell : Z → ℕ) :=
  Σ x : A,B × (PositiveRow φ ell x → Bool)
noncomputable def afterSignature (φ : A → B → Z) (m : ℕ) (ell : Z → ℕ)
    (x : A) (observedY : B) (a b : Table m ell) : AfterSignature φ ell := by
  classical
  exact ⟨x,observedY,fun z => decide (a z.val.val+b z.val.val=0)⟩
noncomputable def afterDecode (φ : A → B → Z) (ell : Z → ℕ)
    (v : AfterSignature φ ell) (joinY : B → B → B) (unreadY : B) : Bool := by
  classical
  let y := joinY v.2.1 unreadY
  let z : Row φ v.1 := ⟨φ v.1 y,⟨y,rfl⟩⟩
  exact if h : 0 < ell z.val then v.2.2 ⟨z,h⟩ else true
private theorem after_decode_actual (φ : A → B → Z) (m : ℕ) (ell : Z → ℕ)
    (x : A) (yp yq : B) (a b : Table m ell) (joinY : B → B → B) :
    afterDecode φ ell (afterSignature φ m ell x yp a b) joinY yq=
      zeroTest φ m ell a b x (joinY yp yq) := by
  classical
  let z := φ x (joinY yp yq)
  by_cases h : 0 < ell z
  · simp [afterDecode,afterSignature,zeroTest,z,h]
  · have hz : ell z=0 := by omega
    have ha := zero_weight_value m ell z hz (a z)
    have hb := zero_weight_value m ell z hz (b z)
    simp [afterDecode,afterSignature,zeroTest,z,h,ha,hb]
private theorem middle_signature_card_bound (φ : A → B → Z) (m L : ℕ) [NeZero m]
    (hm : 1 ≤ m) (ell : Z → ℕ) (hrow : ∀ x,(∑ z : Row φ x,ell z.val) ≤ L) :
    Nat.card (MiddleSignature φ m ell) ≤ Nat.card A*m^L := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  have h : (∑ x, Nat.card (∀ z : Row φ x,Cell m ell z.val)) ≤ ∑ _x : A,m^L := by
    apply Finset.sum_le_sum
    intro x _
    rw [row_table_card]
    exact Nat.pow_le_pow_right hm (hrow x)
  simpa only [Nat.card_eq_fintype_card,Finset.sum_const,Finset.card_univ,smul_eq_mul] using h
private theorem after_signature_card_bound (φ : A → B → Z) (m L : ℕ)
    (hm : 2 ≤ m) (ell : Z → ℕ) (hrow : ∀ x,(∑ z : Row φ x,ell z.val) ≤ L) :
    Nat.card (AfterSignature φ ell) ≤ Nat.card A*Nat.card B*m^L := by
  classical
  have hpos : ∀ x,Nat.card (PositiveRow φ ell x) ≤ L :=
    fun x => (positive_row_card φ ell x).trans (hrow x)
  have hflags : ∀ x,Nat.card (PositiveRow φ ell x → Bool) ≤ m^L := by
    intro x
    rw [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_bool]
    exact (Nat.pow_le_pow_right (by omega) (by simpa only [Nat.card_eq_fintype_card] using hpos x)).trans
      (Nat.pow_le_pow_left hm L)
  have hsum : (∑ x, Nat.card B*Nat.card (PositiveRow φ ell x → Bool)) ≤ ∑ _x : A,Nat.card B*m^L := by
    exact Finset.sum_le_sum (fun x _ => Nat.mul_le_mul_left _ (hflags x))
  simpa [AfterSignature,Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_prod,mul_assoc] using hsum
end WeightedBooleanSharpness
section WeightedBooleanSharpness
variable {R S : Type} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
  {X Y Z : R → Type} [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)] [∀ i,Fintype (Z i)]
  [∀ i,Nonempty (X i)] [∀ i,Nonempty (Y i)]
/-- The exact original strict containment neighborhood of an ordinary pair. -/
def N (s : Skeleton (R ⊕ S)) (k : S) (i : R) : Prop :=
  s.first (.inl i) < s.first (.inr k) ∧ s.first (.inr k) < s.second (.inr k) ∧
    s.second (.inr k) < s.second (.inl i)
abbrev XP (s : Skeleton (R ⊕ S)) (k : S) := ∀ i : {i // N s k i},X i.val
abbrev YP (s : Skeleton (R ⊕ S)) (k : S) := ∀ i : {i // N s k i},Y i.val
abbrev ZP (s : Skeleton (R ⊕ S)) (k : S) := ∀ i : {i // N s k i},Z i.val
def productMap (s : Skeleton (R ⊕ S)) (k : S) (φ : ∀ i,X i → Y i → Z i) :
    XP (X:=X) s k → YP (Y:=Y) s k → ZP (Z:=Z) s k := fun x y i => φ i.val (x i) (y i)
private theorem productMap_onto (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) :
    ∀ z,∃ x y,productMap s k φ x y=z := by
  intro z
  choose x y h using fun i : {i // N s k i} => hφ i.val (z i)
  exact ⟨x,y,funext h⟩
/-- Only k has a changing alphabet. Every other ordinary alphabet is Bool. -/
noncomputable def FamilyX (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) : R ⊕ S → Type _
  | .inl i => X i
  | .inr j => if j=k then Table m ell else Bool
noncomputable def FamilyY (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) : R ⊕ S → Type _
  | .inl i => Y i
  | .inr j => if j=k then Table m ell else Bool
noncomputable def FamilyZ (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) : R ⊕ S → Type _
  | .inl i => Z i
  | .inr j => if j=k then Table m ell else Bool
noncomputable instance familyXFintype (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) [NeZero m] (ell : ZP (Z:=Z) s k → ℕ)
    (i : R ⊕ S) : Fintype (FamilyX (X:=X) s k m ell i) := by
  classical
  cases i with
  | inl i => exact inferInstanceAs (Fintype (X i))
  | inr j => by_cases h:j=k <;> simp only [FamilyX,h,ite_true,ite_false] <;> infer_instance
noncomputable instance familyYFintype (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) [NeZero m] (ell : ZP (Z:=Z) s k → ℕ)
    (i : R ⊕ S) : Fintype (FamilyY (Y:=Y) s k m ell i) := by
  classical
  cases i with
  | inl i => exact inferInstanceAs (Fintype (Y i))
  | inr j => by_cases h:j=k <;> simp only [FamilyY,h,ite_true,ite_false] <;> infer_instance
noncomputable instance familyZFintype (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) [NeZero m] (ell : ZP (Z:=Z) s k → ℕ)
    (i : R ⊕ S) : Fintype (FamilyZ (Z:=Z) s k m ell i) := by
  classical
  cases i with
  | inl i => exact inferInstanceAs (Fintype (Z i))
  | inr j => by_cases h:j=k <;> simp only [FamilyZ,h,ite_true,ite_false] <;> infer_instance
noncomputable instance familyXNonempty (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ)
    (i : R ⊕ S) : Nonempty (FamilyX (X:=X) s k m ell i) := by
  classical
  cases i with
  | inl i => exact inferInstanceAs (Nonempty (X i))
  | inr j => by_cases h:j=k <;> simp only [FamilyX,h,ite_true,ite_false] <;> infer_instance
noncomputable instance familyYNonempty (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ)
    (i : R ⊕ S) : Nonempty (FamilyY (Y:=Y) s k m ell i) := by
  classical
  cases i with
  | inl i => exact inferInstanceAs (Nonempty (Y i))
  | inr j => by_cases h:j=k <;> simp only [FamilyY,h,ite_true,ite_false] <;> infer_instance
/- These equivalences are the only type transports at ordinary coordinates.
Their inverse maps construct actual endpoint values in the original alphabets. -/
noncomputable def selectedX (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (j : S) (h : j=k) :
    FamilyX (X:=X) s k m ell (.inr j) ≃ Table m ell := by
  classical
  exact Equiv.cast (by simp only [FamilyX,if_pos h])
noncomputable def selectedY (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (j : S) (h : j=k) :
    FamilyY (Y:=Y) s k m ell (.inr j) ≃ Table m ell := by
  classical
  exact Equiv.cast (by simp only [FamilyY,if_pos h])
noncomputable def selectedZ (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (j : S) (h : j=k) :
    FamilyZ (Z:=Z) s k m ell (.inr j) ≃ Table m ell := by
  classical
  exact Equiv.cast (by simp only [FamilyZ,if_pos h])
noncomputable def otherX (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (j : S) (h : j≠k) :
    FamilyX (X:=X) s k m ell (.inr j) ≃ Bool := by
  classical
  exact Equiv.cast (by simp only [FamilyX,if_neg h])
noncomputable def otherY (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (j : S) (h : j≠k) :
    FamilyY (Y:=Y) s k m ell (.inr j) ≃ Bool := by
  classical
  exact Equiv.cast (by simp only [FamilyY,if_neg h])
noncomputable def otherZ (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (j : S) (h : j≠k) :
    FamilyZ (Z:=Z) s k m ell (.inr j) ≃ Bool := by
  classical
  exact Equiv.cast (by simp only [FamilyZ,if_neg h])
private def transportBinary {A : Type} {B : Type} {C : Type} {A' : Type} {B' : Type} {C' : Type}
    (ea : A ≃ A') (eb : B ≃ B') (ec : C ≃ C')
    (f : A' → B' → C') (a : A) (b : B) : C :=
  ec.symm (f (ea a) (eb b))
private theorem transportBinary_decode {A : Type} {B : Type} {C : Type} {A' : Type} {B' : Type} {C' : Type}
    (ea : A ≃ A') (eb : B ≃ B') (ec : C ≃ C')
    (f : A' → B' → C') (a : A) (b : B) :
    ec (transportBinary ea eb ec f a b)=f (ea a) (eb b) :=
  ec.apply_symm_apply _
/-- Surjective slices survive independent equivalences of the three alphabets. -/
private theorem transportBinary_slices {A : Type} {B : Type} {C : Type} {A' : Type} {B' : Type} {C' : Type}
    (ea : A ≃ A') (eb : B ≃ B') (ec : C ≃ C') (f : A' → B' → C')
    (hf : (∃ a,Function.Surjective (f a)) ∧
      (∃ b,Function.Surjective (fun a => f a b))) :
    (∃ a,Function.Surjective (transportBinary ea eb ec f a)) ∧
      (∃ b,Function.Surjective (fun a => transportBinary ea eb ec f a b)) := by
  rcases hf with ⟨⟨a,ha⟩,⟨b,hb⟩⟩
  constructor
  · refine ⟨ea.symm a,?_⟩
    intro z
    obtain ⟨y,hy⟩ := ha (ec z)
    refine ⟨eb.symm y,?_⟩
    apply ec.injective
    rw [transportBinary_decode]
    simpa only [Equiv.apply_symm_apply] using hy
  · refine ⟨eb.symm b,?_⟩
    intro z
    obtain ⟨x,hx⟩ := hb (ec z)
    refine ⟨ea.symm x,?_⟩
    apply ec.injective
    rw [transportBinary_decode]
    simpa only [Equiv.apply_symm_apply] using hx
noncomputable def familyMap (s : Skeleton (R ⊕ S)) (k : S) (φ : ∀ i,X i → Y i → Z i)
    (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) :
    ∀ i,FamilyX (X:=X) s k m ell i → FamilyY (Y:=Y) s k m ell i → FamilyZ s k m ell i
  | .inl i => φ i
  | .inr j => by
    classical
    exact if h:j=k then
      transportBinary (selectedX (X:=X) s k m ell j h) (selectedY (Y:=Y) s k m ell j h)
        (selectedZ (Z:=Z) s k m ell j h) (fun a b : Table m ell => a+b)
    else
      transportBinary (otherX (X:=X) s k m ell j h) (otherY (Y:=Y) s k m ell j h)
        (otherZ (Z:=Z) s k m ell j h) Bool.xor
/-- Typed projection onto the designated selector tuple. -/
def designatedTuple (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (v : ∀ i,FamilyZ s k m ell i) : ZP (Z:=Z) s k :=
  fun i => v (.inl i.val)
/-- Typed projection onto the changing ordinary output. -/
noncomputable def selectedTable (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (v : ∀ i,FamilyZ s k m ell i) : Table m ell :=
  selectedZ (Z:=Z) s k m ell k rfl (v (.inr k))
noncomputable def familyOuter (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (v : ∀ i,FamilyZ s k m ell i) : Bool := by
  classical
  exact decide ((selectedTable s k m ell v) (designatedTuple s k m ell v)=0)
private theorem familyMap_selected_decode (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ)
    (a : FamilyX (X:=X) s k m ell (.inr k))
    (b : FamilyY (Y:=Y) s k m ell (.inr k)) :
    selectedZ (Z:=Z) s k m ell k rfl (familyMap s k φ m ell (.inr k) a b)=
      selectedX (X:=X) s k m ell k rfl a + selectedY (Y:=Y) s k m ell k rfl b := by
  classical
  simp [familyMap,transportBinary]
def FamilyAllowed (s : Skeleton (R ⊕ S)) (k : S) (φ : ∀ i,X i → Y i → Z i)
    (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) : Prop :=
    (∀ i,familyMap s k φ m ell (.inl i)=φ i) ∧
    (∀ j,
      (∃ a,Function.Surjective (familyMap s k φ m ell (.inr j) a)) ∧
      (∃ b,Function.Surjective (fun a => familyMap s k φ m ell (.inr j) a b))) ∧
    (∀ i z,∃ x y,familyMap s k φ m ell i x y=z)
/-- Actual surjective slices in the original conditional alphabets. -/
theorem family_allowed (s : Skeleton (R ⊕ S)) (k : S) (φ : ∀ i,X i → Y i → Z i)
    (hφ : ∀ i z,∃ x y,φ i x y=z) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) :
    FamilyAllowed s k φ m ell := by
  classical
  have ordinary (j : S) :
      (∃ a,Function.Surjective (familyMap s k φ m ell (.inr j) a)) ∧
      (∃ b,Function.Surjective (fun a => familyMap s k φ m ell (.inr j) a b)) := by
    by_cases h:j=k
    · simp only [familyMap,dif_pos h]
      apply transportBinary_slices
      exact ⟨⟨0,fun z => ⟨z,zero_add z⟩⟩,⟨0,fun z => ⟨z,add_zero z⟩⟩⟩
    · simp only [familyMap,dif_neg h]
      apply transportBinary_slices
      exact ⟨⟨false,fun z => ⟨z,by cases z <;> rfl⟩⟩,
        ⟨false,fun z => ⟨z,by cases z <;> rfl⟩⟩⟩
  refine ⟨fun i => rfl,ordinary,?_⟩
  intro i z
  cases i with
  | inl i => exact hφ i z
  | inr j => obtain ⟨a,ha⟩ := (ordinary j).1; obtain ⟨b,hb⟩ := ha z; exact ⟨a,b,hb⟩
section RawReadouts
variable (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ)
abbrev Prefix (l r : R ⊕ S → Prop) := Values (FamilyX (X:=X) s k m ell) (FamilyY (Y:=Y) s k m ell) l r
abbrev Suffix (l r : R ⊕ S → Prop) := Prefix (X:=X) (Y:=Y) s k m ell (fun i=>¬l i) (fun i=>¬r i)
noncomputable def preX (l r : R ⊕ S → Prop) (b : Prefix (X:=X) (Y:=Y) s k m ell l r) : XP (X:=X) s k := by
  classical
  exact fun i => if h:l (.inl i.val) then b.1 ⟨.inl i.val,h⟩ else Classical.choice inferInstance
noncomputable def sufX (l r : R ⊕ S → Prop) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) : XP (X:=X) s k := by
  classical
  exact fun i => if h:¬l (.inl i.val) then q.1 ⟨.inl i.val,h⟩ else Classical.choice inferInstance
noncomputable def preY (l r : R ⊕ S → Prop) (b : Prefix (X:=X) (Y:=Y) s k m ell l r) : YP (Y:=Y) s k := by
  classical
  exact fun i => if h:r (.inl i.val) then b.2 ⟨.inl i.val,h⟩ else Classical.choice inferInstance
noncomputable def sufY (l r : R ⊕ S → Prop) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) : YP (Y:=Y) s k := by
  classical
  exact fun i => if h:¬r (.inl i.val) then q.2 ⟨.inl i.val,h⟩ else Classical.choice inferInstance
noncomputable def joinX (l : R ⊕ S → Prop) (x x' : XP (X:=X) s k) : XP (X:=X) s k := by
  classical
  exact fun i => if l (.inl i.val) then x i else x' i
noncomputable def joinY (r : R ⊕ S → Prop) (y y' : YP (Y:=Y) s k) : YP (Y:=Y) s k := by
  classical
  exact fun i => if r (.inl i.val) then y i else y' i
noncomputable def preA (l r : R ⊕ S → Prop) (b : Prefix (X:=X) (Y:=Y) s k m ell l r) : Table m ell := by
  classical
  exact if h:l (.inr k) then selectedX (X:=X) s k m ell k rfl (b.1 ⟨.inr k,h⟩) else 0
noncomputable def sufA (l r : R ⊕ S → Prop) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) : Table m ell := by
  classical
  exact if h:¬l (.inr k) then selectedX (X:=X) s k m ell k rfl (q.1 ⟨.inr k,h⟩) else 0
noncomputable def preB (l r : R ⊕ S → Prop) (b : Prefix (X:=X) (Y:=Y) s k m ell l r) : Table m ell := by
  classical
  exact if h:r (.inr k) then selectedY (Y:=Y) s k m ell k rfl (b.2 ⟨.inr k,h⟩) else 0
noncomputable def sufB (l r : R ⊕ S → Prop) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) : Table m ell := by
  classical
  exact if h:¬r (.inr k) then selectedY (Y:=Y) s k m ell k rfl (q.2 ⟨.inr k,h⟩) else 0
/-- The partitioned endpoint is decoded once, with its other summand zero. -/
private theorem decode_partitioned_coordinate {I : Type} {A : Type} {V : I → Type}
    [AddMonoid A] (p : I → Prop) [DecidablePred p] (i : I) (e : V i ≃ A)
    (b : ∀ j : {j // p j},V j.val) (q : ∀ j : {j // ¬p j},V j.val) :
    e (if h:p i then b ⟨i,h⟩ else q ⟨i,h⟩)=
      (if h:p i then e (b ⟨i,h⟩) else 0) +
      (if h:¬p i then e (q ⟨i,h⟩) else 0) := by
  by_cases h:p i <;> simp [h]
/-- Equality of entire dependent selector tuples, before table evaluation. -/
private theorem designatedTuple_outputs (φ : ∀ i,X i → Y i → Z i) (l r : R ⊕ S → Prop)
    (b : Prefix (X:=X) (Y:=Y) s k m ell l r)
    (q : Suffix (X:=X) (Y:=Y) s k m ell l r) :
    designatedTuple s k m ell (outputs (familyMap s k φ m ell) l r b q)=
      productMap s k φ
        (joinX s k l (preX s k m ell l r b) (sufX s k m ell l r q))
        (joinY s k r (preY s k m ell l r b) (sufY s k m ell l r q)) := by
  classical
  funext i
  change φ i.val
      (if h:l (.inl i.val) then b.1 ⟨.inl i.val,h⟩ else q.1 ⟨.inl i.val,h⟩)
      (if h:r (.inl i.val) then b.2 ⟨.inl i.val,h⟩ else q.2 ⟨.inl i.val,h⟩)=
    φ i.val
      (joinX s k l (preX s k m ell l r b) (sufX s k m ell l r q) i)
      (joinY s k r (preY s k m ell l r b) (sufY s k m ell l r q) i)
  apply congrArg₂ (φ i.val)
  · by_cases h:l (.inl i.val) <;> simp [joinX,preX,sufX,h] <;> rfl
  · by_cases h:r (.inl i.val) <;> simp [joinY,preY,sufY,h] <;> rfl
/-- Equality of whole tables; the changing ordinary map is actual addition. -/
private theorem selectedTable_outputs (φ : ∀ i,X i → Y i → Z i) (l r : R ⊕ S → Prop)
    (b : Prefix (X:=X) (Y:=Y) s k m ell l r)
    (q : Suffix (X:=X) (Y:=Y) s k m ell l r) :
    selectedTable s k m ell (outputs (familyMap s k φ m ell) l r b q)=
      (preA s k m ell l r b+sufA s k m ell l r q)+
      (preB s k m ell l r b+sufB s k m ell l r q) := by
  classical
  change selectedZ (Z:=Z) s k m ell k rfl
    (familyMap s k φ m ell (.inr k)
      (if h:l (.inr k) then b.1 ⟨.inr k,h⟩ else q.1 ⟨.inr k,h⟩)
      (if h:r (.inr k) then b.2 ⟨.inr k,h⟩ else q.2 ⟨.inr k,h⟩))=_
  rw [familyMap_selected_decode]
  apply congrArg₂ (fun a b : Table m ell => a+b)
  · simpa only [preA,sufA] using
      decode_partitioned_coordinate l (.inr k) (selectedX (X:=X) s k m ell k rfl) b.1 q.1
  · simpa only [preB,sufB] using
      decode_partitioned_coordinate r (.inr k) (selectedY (Y:=Y) s k m ell k rfl) b.2 q.2
/-- Evaluation of the actual full task on this one original labelled suffix. -/
theorem sharp_response_formula (φ : ∀ i,X i → Y i → Z i) (l r : R ⊕ S → Prop)
    (b : Prefix (X:=X) (Y:=Y) s k m ell l r) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) :
    response (familyMap s k φ m ell) (familyOuter s k m ell) l r b q=
      zeroTest (productMap s k φ) m ell
        (preA s k m ell l r b+sufA s k m ell l r q)
        (preB s k m ell l r b+sufB s k m ell l r q)
        (joinX s k l (preX s k m ell l r b) (sufX s k m ell l r q))
        (joinY s k r (preY s k m ell l r b) (sufY s k m ell l r q)) := by
  classical
  change decide
    ((selectedTable s k m ell (outputs (familyMap s k φ m ell) l r b q))
      (designatedTuple s k m ell (outputs (familyMap s k φ m ell) l r b q))=0)=_
  rw [selectedTable_outputs,designatedTuple_outputs]
  rfl
end RawReadouts
private theorem response_le_signature {P Q V : Type} [Finite P] [Finite Q] [Finite V]
    (responseMap : P → Q) (signature : P → V)
    (h : ∀ p p',signature p=signature p' → responseMap p=responseMap p') :
    Nat.card (Set.range responseMap) ≤ Nat.card V :=
  (range_card_le_of_kernel signature responseMap h).trans
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)
set_option maxHeartbeats 1600000 in
/-- The three regimes cover every original endpoint layer, including interleaved
ignored coordinates, partial designated Y prefixes and the final layer. -/
theorem raw_layer_signature_bounds (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (m L : ℕ) [NeZero m] (hm : 2 ≤ m) (ell : ZP (Z:=Z) s k → ℕ)
    (hrow : ∀ x,(∑ z : Row (productMap s k φ) x,ell z.val) ≤ L) (t : ℕ) :
    let l := fun i => s.first i < t
    let r := fun i => s.second i < t
    let cap := cutCard (familyMap s k φ m ell) (familyOuter s k m ell) l r
    (t ≤ s.first (.inr k) → cap ≤ Nat.card (XP (X:=X) s k)) ∧
    (s.first (.inr k) < t → t ≤ s.second (.inr k) → cap ≤ Nat.card (XP (X:=X) s k)*m^L) ∧
    (s.second (.inr k) < t → cap ≤ Nat.card (XP (X:=X) s k)*Nat.card (YP (Y:=Y) s k)*m^L) := by
  let l := fun i => s.first i < t
  let r := fun i => s.second i < t
  let f := response (familyMap s k φ m ell) (familyOuter s k m ell) l r
  have hk := s.oriented (.inr k)
  change s.first (.inr k) < s.second (.inr k) at hk
  refine ⟨?_,?_,?_⟩
  · intro ht
    have ha : ¬l (.inr k) := by dsimp [l]; omega
    have hb : ¬r (.inr k) := by dsimp [r]; omega
    have hy : ∀ i : {i // N s k i},¬r (.inl i.val) := by
      intro i; have h:=i.property.2.2; dsimp [r]; omega
    apply response_le_signature f (preX s k m ell l r)
    intro b b' he
    funext q
    have hyjoin (b : Prefix (X:=X) (Y:=Y) s k m ell l r) : joinY s k r (preY s k m ell l r b) (sufY s k m ell l r q)=
        sufY s k m ell l r q := by funext i; simp [joinY,hy i]
    dsimp only [f]
    rw [sharp_response_formula,sharp_response_formula,hyjoin,hyjoin]
    simp [preA,preB,ha,hb,he]
  · intro hta htb
    have ha : l (.inr k) := hta
    have hb : ¬r (.inr k) := by dsimp [r]; omega
    have hx : ∀ i : {i // N s k i},l (.inl i.val) := by
      intro i; exact lt_trans i.property.1 hta
    have hy : ∀ i : {i // N s k i},¬r (.inl i.val) := by
      intro i; have h:=i.property.2.2; dsimp [r]; omega
    let sig := fun b : Prefix (X:=X) (Y:=Y) s k m ell l r =>
      middleSignature (productMap s k φ) m ell (preX s k m ell l r b) (preA s k m ell l r b)
    have factor (b : Prefix (X:=X) (Y:=Y) s k m ell l r) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) : f b q=middleDecode (productMap s k φ) m ell (sig b)
        (sufB s k m ell l r q) (sufY s k m ell l r q) := by
      have ex : joinX s k l (preX s k m ell l r b) (sufX s k m ell l r q)=preX s k m ell l r b := by
        funext i; simp [joinX,hx i]
      have ey : joinY s k r (preY s k m ell l r b) (sufY s k m ell l r q)=sufY s k m ell l r q := by
        funext i; simp [joinY,hy i]
      dsimp only [f]
      rw [sharp_response_formula,ex,ey]
      simp [sig,middleSignature,middleDecode,zeroTest,sufA,preB,ha,hb]
      congr 1
    have hbnd := response_le_signature f sig (by
      intro b b' he; funext q; rw [factor,factor,he])
    have hcard : Nat.card (MiddleSignature (productMap s k φ) m ell) ≤
        Nat.card (XP (X:=X) s k)*m^L := by
      apply middle_signature_card_bound (A:=XP (X:=X) s k) (B:=YP (Y:=Y) s k)
        (Z:=ZP (Z:=Z) s k) (productMap s k φ) m L (by omega) ell
      intro x
      apply le_trans ?_ (hrow x)
      apply le_of_eq
      apply Finset.sum_congr
      · ext z; simp
      · intro z hz; rfl
    exact Nat.le_trans hbnd hcard
  · intro htb
    have ha : l (.inr k) := lt_trans hk htb
    have hb : r (.inr k) := htb
    have hx : ∀ i : {i // N s k i},l (.inl i.val) := fun i => lt_trans i.property.1 ha
    let sig := fun b : Prefix (X:=X) (Y:=Y) s k m ell l r =>
      afterSignature (productMap s k φ) m ell (preX s k m ell l r b) (preY s k m ell l r b)
        (preA s k m ell l r b) (preB s k m ell l r b)
    have factor (b : Prefix (X:=X) (Y:=Y) s k m ell l r) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) : f b q=afterDecode (productMap s k φ) ell (sig b)
        (joinY s k r) (sufY s k m ell l r q) := by
      have ex : joinX s k l (preX s k m ell l r b) (sufX s k m ell l r q)=preX s k m ell l r b := by
        funext i; simp [joinX,hx i]
      dsimp only [f]
      rw [sharp_response_formula,ex]
      rw [show sig b=afterSignature _ _ _ _ _ _ _ from rfl,after_decode_actual]
      simp [sufA,sufB,ha,hb]
    have hbnd := response_le_signature f sig (by
      intro b b' he; funext q; rw [factor,factor,he])
    have hcard : Nat.card (AfterSignature (productMap s k φ) ell) ≤
        Nat.card (XP (X:=X) s k)*Nat.card (YP (Y:=Y) s k)*m^L := by
      apply after_signature_card_bound (A:=XP (X:=X) s k) (B:=YP (Y:=Y) s k)
        (Z:=ZP (Z:=Z) s k) (productMap s k φ) m L hm ell
      intro x
      apply le_trans ?_ (hrow x)
      apply le_of_eq
      apply Finset.sum_congr
      · ext z; simp
      · intro z hz; rfl
    exact Nat.le_trans hbnd hcard
/-- Uniform original-width bound with a fixed coefficient, independent of m. -/
theorem sharp_original_width_bound (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (m L : ℕ) [NeZero m] (hm : 2 ≤ m) (ell : ZP (Z:=Z) s k → ℕ)
    (hrow : ∀ x,(∑ z : Row (productMap s k φ) x,ell z.val) ≤ L) :
    1 ≤ width (familyMap s k φ m ell) (familyOuter s k m ell) s.position ∧
    width (familyMap s k φ m ell) (familyOuter s k m ell) s.position ≤ Nat.card (XP (X:=X) s k)*Nat.card (YP (Y:=Y) s k)*m^L := by
  have hx : 1 ≤ Nat.card (XP (X:=X) s k) := Nat.card_pos
  have hy : 1 ≤ Nat.card (YP (Y:=Y) s k) := Nat.card_pos
  have hp : 1 ≤ m^L := by
    have hpositive : 0 < m^L := pow_pos (by omega : 0 < m) L
    omega
  refine ⟨width_pos _ _ _,?_⟩
  apply Finset.sup_le
  intro t ht
  obtain ⟨hbefore,hbetween,hafter⟩ := raw_layer_signature_bounds s k φ m L hm ell hrow t
  by_cases ha : t ≤ s.first (.inr k)
  · exact (hbefore ha).trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (Nat.card (XP (X:=X) s k)) (Nat.mul_le_mul hy hp))
  · by_cases hb : t ≤ s.second (.inr k)
    · exact (hbetween (by omega) hb).trans (by simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left (Nat.card (XP (X:=X) s k)*m^L) hy)
    · exact hafter (by omega)
end WeightedBooleanSharpness
section WeightedBooleanSharpness
variable {R S : Type} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
  {X Y Z : R → Type} [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)] [∀ i,Fintype (Z i)]
  [∀ i,Nonempty (X i)] [∀ i,Nonempty (Y i)]
/-- Full original-coordinate inputs; omitted designated coordinates and ignored
ordinary blocks are assigned fixed values. No coordinate is removed. -/
noncomputable def inputX (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (a : Table m ell) (x : XP (X:=X) s k) :
    ∀ i,FamilyX (X:=X) s k m ell i
  | .inl i => by
    classical
    exact if h:N s k i then x ⟨i,h⟩ else Classical.choice inferInstance
  | .inr j => by
    classical
    exact if h:j=k then (selectedX (X:=X) s k m ell j h).symm a
      else (otherX (X:=X) s k m ell j h).symm false
noncomputable def inputY (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (b : Table m ell) (y : YP (Y:=Y) s k) :
    ∀ i,FamilyY (Y:=Y) s k m ell i
  | .inl i => by
    classical
    exact if h:N s k i then y ⟨i,h⟩ else Classical.choice inferInstance
  | .inr j => by
    classical
    exact if h:j=k then (selectedY (Y:=Y) s k m ell j h).symm b
      else (otherY (Y:=Y) s k m ell j h).symm false
private theorem inputX_selected (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (a : Table m ell) (x : XP (X:=X) s k) :
    selectedX (X:=X) s k m ell k rfl (inputX s k m ell a x (.inr k))=a := by
  classical
  simp [inputX]
private theorem inputY_selected (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (b : Table m ell) (y : YP (Y:=Y) s k) :
    selectedY (Y:=Y) s k m ell k rfl (inputY s k m ell b y (.inr k))=b := by
  classical
  simp [inputY]
noncomputable def lowerPrefix (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (a : Table m ell) :
    Prefix (X:=X) (Y:=Y) s k m ell
      (firstRead s (.pair (.inr k) false)) (secondRead s (.pair (.inr k) false)) :=
  (fun i => inputX s k m ell a (Classical.choice inferInstance) i.val,
   fun i => inputY s k m ell 0 (Classical.choice inferInstance) i.val)
noncomputable def lowerSuffix (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (b : Table m ell)
    (x : XP (X:=X) s k) (y : YP (Y:=Y) s k) :
    Suffix (X:=X) (Y:=Y) s k m ell
      (firstRead s (.pair (.inr k) false)) (secondRead s (.pair (.inr k) false)) :=
  (fun i => inputX s k m ell 0 x i.val,fun i => inputY s k m ell b y i.val)
/-- All selector inputs remain in the one common suffix at this normalized cut. -/
private theorem lower_response (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ)
    (a b : Table m ell) (x : XP (X:=X) s k) (y : YP (Y:=Y) s k) :
    response (familyMap s k φ m ell) (familyOuter s k m ell)
      (firstRead s (.pair (.inr k) false)) (secondRead s (.pair (.inr k) false))
      (lowerPrefix (X:=X) (Y:=Y) s k m ell a) (lowerSuffix (X:=X) (Y:=Y) s k m ell b x y)=
      zeroTest (productMap s k φ) m ell a b x y := by
  classical
  let l := firstRead s (.pair (.inr k) false)
  let r := secondRead s (.pair (.inr k) false)
  have hk1 : l (.inr k) := le_rfl
  have hk2 : ¬r (.inr k) := by simp [r,secondRead]
  have hx : ∀ i : {i // N s k i},¬l (.inl i.val) := by
    intro i; exact not_le.mpr i.property.2.2
  have hy : ∀ i : {i // N s k i},¬r (.inl i.val) := by
    intro i
    have h:=i.property.2.2
    simpa [r,secondRead] using
      (not_lt.mpr h.le : ¬s.second (.inl i.val) < s.second (.inr k))
  have ex : joinX s k l
      (preX s k m ell l r (lowerPrefix (X:=X) (Y:=Y) s k m ell a))
      (sufX s k m ell l r (lowerSuffix (X:=X) (Y:=Y) s k m ell b x y))=x := by
    funext i
    simp [joinX,sufX,lowerSuffix,inputX,hx i,i.property]
  have ey : joinY s k r
      (preY s k m ell l r (lowerPrefix (X:=X) (Y:=Y) s k m ell a))
      (sufY s k m ell l r (lowerSuffix (X:=X) (Y:=Y) s k m ell b x y))=y := by
    funext i
    simp [joinY,sufY,lowerSuffix,inputY,hy i,i.property]
  rw [sharp_response_formula]
  change zeroTest _ _ _ _ _
    (joinX s k l _ _) (joinY s k r _ _)=_
  rw [ex,ey]
  simp [preA,sufA,preB,sufB,lowerPrefix,lowerSuffix,
    hk1,hk2,inputX_selected,inputY_selected,firstRead,secondRead]
/-- Actual distinct response functions, witnessed on the same labelled suffix:
select a differing table coordinate z and use the second table -a. -/
theorem normalized_table_injection (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z)
    (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) :
    Function.Injective (fun a : Table m ell =>
      response (familyMap s k φ m ell) (familyOuter s k m ell)
        (firstRead s (.pair (.inr k) false)) (secondRead s (.pair (.inr k) false))
        (lowerPrefix (X:=X) (Y:=Y) s k m ell a)) := by
  classical
  intro a a' he
  funext z
  obtain ⟨x,y,hxy⟩ := productMap_onto s k φ hφ z
  subst z
  have h := congrFun he (lowerSuffix (X:=X) (Y:=Y) s k m ell (-a) x y)
  dsimp only at h
  rw [lower_response,lower_response] at h
  have hd : decide (a' (productMap s k φ x y)+-a (productMap s k φ x y)=0)=true := by
    simpa [zeroTest] using h.symm
  have hz : a' (productMap s k φ x y)+-a (productMap s k φ x y)=0 := of_decide_eq_true hd
  have heq : a' (productMap s k φ x y)=a (productMap s k φ x y) := eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hz)
  exact heq.symm
/-- Lower bound at the actual normalized layer immediately after k's first label. -/
theorem sharp_normalized_width_bound (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z)
    (m : ℕ) [NeZero m] (ell : ZP (Z:=Z) s k → ℕ) :
    m^(∑ z,ell z) ≤ width (familyMap s k φ m ell) (familyOuter s k m ell) s.completion := by
  classical
  let c : Cut (R ⊕ S) := .pair (.inr k) false
  let f := response (familyMap s k φ m ell) (familyOuter s k m ell)
    (firstRead s c) (secondRead s c)
  let emb : Table m ell → Set.range f := fun a =>
    ⟨f (lowerPrefix (X:=X) (Y:=Y) s k m ell a),Set.mem_range_self _⟩
  have hi : Function.Injective emb := by
    intro a a' h
    exact normalized_table_injection s k φ hφ m ell (congrArg Subtype.val h)
  have hc : m^(∑ z,ell z) ≤ cutCard (familyMap s k φ m ell)
      (familyOuter s k m ell) (firstRead s c) (secondRead s c) := by
    have h := Nat.card_le_card_of_injective emb hi
    rw [table_card] at h
    exact h
  obtain ⟨ht,h1,h2⟩ := completion_prefix s c
  have he1 : (fun i => (s.completion (i,false)).val < cutSize s c)=firstRead s c := by
    funext i; exact propext (h1 i)
  have he2 : (fun i => (s.completion (i,true)).val < cutSize s c)=secondRead s c := by
    funext i; exact propext (h2 i)
  have hw := width_contains (familyMap s k φ m ell) (familyOuter s k m ell)
    s.completion (cutSize s c) ht
  rw [he1,he2] at hw
  exact hc.trans hw
end WeightedBooleanSharpness
section WeightedBooleanSharpness
variable {R S : Type} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
  [Nonempty S] {X Y Z : R → Type}
  [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)] [∀ i,Fintype (Z i)]
  [∀ i,Nonempty (X i)] [∀ i,Nonempty (Y i)]
noncomputable def localExponent (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) (k : S) : ℝ := by
  classical
  exact ∏ i : {i // N s k i},rowCoverNumber (φ i.val) (hφ i.val)
noncomputable def Theta (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (localExponent s φ hφ)
private theorem localExponent_one_le (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) (k : S) :
    1 ≤ localExponent s φ hφ k := by
  classical
  apply Finset.one_le_prod₀
  intro i hi
  exact actualTau_one_le φ hφ i.val
set_option maxHeartbeats 1600000 in
/-- Finite maximization chooses k; no supplied maximum or sharpness hypothesis.
The returned integer certificate is the actual product-map dual certificate. -/
theorem attained_integer_certificate (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) :
    ∃ (k : S) (L : ℕ) (ell : ZP (Z:=Z) s k → ℕ),
      0 < L ∧ 1 ≤ Theta s φ hφ ∧ localExponent s φ hφ k=Theta s φ hφ ∧
      ((∑ z,ell z : ℕ):ℝ)=(L:ℝ)*Theta s φ hφ ∧
      (∀ x,(∑ z : Row (productMap s k φ) x,ell z.val) ≤ L) := by
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image Finset.univ
    (localExponent s φ hφ) Finset.univ_nonempty
  have he : localExponent s φ hφ k=Theta s φ hφ := by
    apply le_antisymm
    · exact Finset.le_sup' _ hk
    · exact Finset.sup'_le _ _ hmax
  have hT : 1 ≤ Theta s φ hφ := he ▸ localExponent_one_le s φ hφ k
  have hprod := productMap_onto s k φ hφ
  have hcover : rowCoverNumber (productMap s k φ) hprod=localExponent s φ hφ k := by
    exact product_cover_value (fun i : {i // N s k i} => φ i.val)
      (fun i => hφ i.val) hprod
  obtain ⟨L,ell,hL,htotal,hrow⟩ := integer_optimal_certificate (productMap s k φ) hprod
  rw [hcover,he] at htotal
  refine ⟨k,L,ell,hL,hT,he,htotal,?_⟩
  intro x
  apply le_trans ?_ (hrow x)
  apply le_of_eq
  apply Finset.sum_congr
  · ext z; simp
  · intro z hz; rfl
end WeightedBooleanSharpness
section WeightedBooleanSharpness
/-- A positive power eventually exceeds each fixed coefficient on integer moduli. -/
private theorem natural_rpow_unbounded (δ : ℝ) (hδ : 0 < δ) (K : ℝ) :
    ∃ m : ℕ,2 ≤ m ∧ K < (m:ℝ)^δ := by
  have hev : ∀ᶠ x : ℝ in Filter.atTop,K < x^δ :=
    (_root_.tendsto_rpow_atTop hδ).eventually (Filter.eventually_gt_atTop K)
  obtain ⟨b,hb⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨m,hm⟩ := exists_nat_gt (max b 2)
  have hmb : b ≤ (m:ℝ) := (le_max_left b 2).trans hm.le
  have hm2 : (2:ℝ) < m := (le_max_right b 2).trans_lt hm
  exact ⟨m,by exact_mod_cast hm2.le,hb m hmb⟩
/-- Both signs of alpha are covered. For alpha < 0, only Wpi≥1 is needed. -/
private theorem separating_modulus (L M : ℕ) (Θ α C c : ℝ)
    (hL : 0 < L) (hΘ : 1 ≤ Θ) (hM : (M:ℝ)=(L:ℝ)*Θ)
    (hα : α < Θ) (hC : 0 < C) (hc : 0 < c) :
    ∃ m : ℕ,2 ≤ m ∧ ∀ w : ℝ,1 ≤ w → w ≤ c*(m:ℝ)^L → C*w^α < (m:ℝ)^M := by
  have hLr : (0:ℝ) < L := by exact_mod_cast hL
  have hΘ0 : 0 < Θ := lt_of_lt_of_le zero_lt_one hΘ
  have hMr : (0:ℝ) < M := by rw [hM]; positivity
  by_cases hneg : α < 0
  · obtain ⟨m,hm,hgrow⟩ := natural_rpow_unbounded M hMr C
    refine ⟨m,hm,?_⟩
    intro w hw hwu
    have hpow : w^α ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1) hw hneg.le
    have hh := mul_le_mul_of_nonneg_left hpow hC.le
    have hsmall : C*w^α ≤ C := by simpa using hh
    exact hsmall.trans_lt (by simpa only [Real.rpow_natCast] using hgrow)
  · have hα0 : 0 ≤ α := le_of_not_gt hneg
    let δ := (M:ℝ)-(L:ℝ)*α
    have hδ : 0 < δ := by dsimp [δ]; rw [hM]; nlinarith
    obtain ⟨m,hm,hgrow⟩ := natural_rpow_unbounded δ hδ (C*c^α)
    have hmr : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hpowpos : 0 < (m:ℝ)^((L:ℝ)*α) := Real.rpow_pos_of_pos hmr _
    have hcalc : C*(c*(m:ℝ)^L)^α < (m:ℝ)^M := by
      calc
        C*(c*(m:ℝ)^L)^α = (C*c^α)*(m:ℝ)^((L:ℝ)*α) := by
          rw [Real.mul_rpow hc.le (by positivity),Real.rpow_mul hmr.le,Real.rpow_natCast]
          ring
        _ < (m:ℝ)^δ*(m:ℝ)^((L:ℝ)*α) := mul_lt_mul_of_pos_right hgrow hpowpos
        _ = (m:ℝ)^M := by
          rw [←Real.rpow_add hmr]
          have he : δ+(L:ℝ)*α=(M:ℝ) := by dsimp [δ]; ring
          rw [he,Real.rpow_natCast]
    refine ⟨m,hm,?_⟩
    intro w hw hwu
    have hmono := Real.rpow_le_rpow (by linarith : 0 ≤ w) hwu hα0
    exact (mul_le_mul_of_nonneg_left hmono hC.le).trans_lt hcalc
variable {R S : Type} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
  [Nonempty S] {X Y Z : R → Type}
  [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)] [∀ i,Fintype (Z i)]
  [∀ i,Nonempty (X i)] [∀ i,Nonempty (Y i)]
/-- One actual maximizing ordinary block defeats every smaller real exponent.
The fixed k, L and ell are chosen before alpha and C; only m and G then vary. -/
theorem scalar_boolean_subcritical_failure (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) :
    ∃ (k : S) (L : ℕ) (ell : ZP (Z:=Z) s k → ℕ),
      0 < L ∧ localExponent s φ hφ k=Theta s φ hφ ∧
      (∀ m : ℕ,FamilyAllowed s k φ m ell) ∧
      ∀ (α C : ℝ),α < Theta s φ hφ → 0 < C → ∃ (m : ℕ) (hm : 2 ≤ m),
          letI : NeZero m := ⟨by omega⟩
          C*(width (familyMap s k φ m ell) (familyOuter s k m ell) s.position : ℝ)^α < (width (familyMap s k φ m ell) (familyOuter s k m ell) s.completion : ℝ) := by
  obtain ⟨k,L,ell,hL,hΘ,he,htotal,hrow⟩ := attained_integer_certificate s φ hφ
  refine ⟨k,L,ell,hL,he,(fun m => family_allowed s k φ hφ m ell),?_⟩
  intro α C hα hC
  let c : ℝ := Nat.card (XP (X:=X) s k)*Nat.card (YP (Y:=Y) s k)
  have hx : 0 < Nat.card (XP (X:=X) s k) := Nat.card_pos
  have hy : 0 < Nat.card (YP (Y:=Y) s k) := Nat.card_pos
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨m,hm,hsep⟩ := separating_modulus L (∑ z,ell z)
    (Theta s φ hφ) α C c hL hΘ htotal hα hC hc
  refine ⟨m,hm,?_⟩
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨hpos,hub⟩ := sharp_original_width_bound s k φ m L hm ell hrow
  have hlow := sharp_normalized_width_bound s k φ hφ m ell
  have hp : (1:ℝ) ≤ width (familyMap s k φ m ell) (familyOuter s k m ell) s.position := by
    exact_mod_cast hpos
  have hu : (width (familyMap s k φ m ell) (familyOuter s k m ell) s.position : ℝ) ≤ c*(m:ℝ)^L := by
    dsimp [c]; exact_mod_cast hub
  have hl : (m:ℝ)^(∑ z,ell z) ≤ (width (familyMap s k φ m ell) (familyOuter s k m ell) s.completion : ℝ) := by
    exact_mod_cast hlow
  exact (hsep _ hp hu).trans_le hl
end WeightedBooleanSharpness
section WeightedBooleanSharpness
variable {R S : Type} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
  [Nonempty S]
def IsDesignated : R ⊕ S → Prop
  | .inl _ => True
  | .inr _ => False
section ThetaIdentity
variable {X Y Z : R → Type}
  [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)] [∀ i,Fintype (Z i)]
  [∀ i,Nonempty (X i)] [∀ i,Nonempty (Y i)]
/-- Only designated weights enter each strict containment neighborhood. -/
private theorem neighborhood_restriction (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z)
    (τ : R ⊕ S → ℝ) (hτ : ∀ i,τ (.inl i)=rowCoverNumber (φ i) (hφ i)) (k : S) :
    productOn (neighborhood s IsDesignated (.inr k)) τ=localExponent s φ hφ k := by
  classical
  calc
    productOn (neighborhood s IsDesignated (.inr k)) τ =
        ∏ i : R,if N s k i then τ (.inl i) else 1 := by
      simp [productOn,Fintype.prod_sum_type,neighborhood,IsDesignated,N]
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : N s k i <;> simp only [N] at h ⊢ <;> simp [h]
    _ = ∏ i : R,if N s k i then rowCoverNumber (φ i) (hφ i) else 1 := by
      simp only [hτ]
    _ = localExponent s φ hφ k := by
      exact (productOn_subtype (N s k) (fun i => rowCoverNumber (φ i) (hφ i))).symm
/-- The upper bridge's maximum equals the fixed designated-family maximum. -/
private theorem theta_restriction (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z)
    (τ : R ⊕ S → ℝ) (hτ : ∀ i,τ (.inl i)=rowCoverNumber (φ i) (hφ i))
    (ho : ∃ i : R ⊕ S,¬IsDesignated i) :
    theta s IsDesignated τ ho=Theta s φ hφ := by
  classical
  dsimp [theta,Theta]
  apply le_antisymm
  · refine Finset.sup'_le _ _ ?_
    intro j hj
    cases j with
    | inl i =>
      have hn := (Finset.mem_filter.mp hj).2
      exact (hn trivial).elim
    | inr k =>
      rw [neighborhood_restriction s φ hφ τ hτ]
      exact Finset.le_sup' _ (Finset.mem_univ k)
  · refine Finset.sup'_le _ _ ?_
    intro k hk
    rw [←neighborhood_restriction s φ hφ τ hτ k]
    exact neighborhood_le_theta s IsDesignated τ ho (.inr k) (by simp [IsDesignated])
end ThetaIdentity
section OriginalContract
variable [Nonempty R] {O : Type} [Fintype O] [Nonempty O]
  {U V W : R ⊕ S → Type}
  [∀ i,Fintype (U i)] [∀ i,Fintype (V i)] [∀ i,Fintype (W i)]
  [∀ i,Nonempty (U i)] [∀ i,Nonempty (V i)]
/-- Uniform upper bound for every allowed actual ordinary family, together with
one designated-family construction refuting every smaller exponent using Bool.
Constants in the upper bound involve only the fixed designated restriction.
-/
theorem original33_bound_and_boolean_obstruction
    (s : Skeleton (R ⊕ S)) (ψ : ∀ i,U i → V i → W i) (G : (∀ i,W i) → O)
    (hd : ∀ i : R,∀ z,∃ x y,ψ (.inl i) x y=z)
    (ho : ∀ j : S,
      (∃ a,Function.Surjective (ψ (.inr j) a)) ∧
      (∃ b,Function.Surjective (fun a => ψ (.inr j) a b))) :
    let φ := fun i : R => ψ (.inl i)
    let D : ℕ := ∏ i : R,Fintype.card (U (.inl i))*Fintype.card (V (.inl i))
    let T : ℝ := ∏ i : R,rowCoverNumber (φ i) (hd i)
    let old : ℝ := labelledWidth ψ G s.position
    (labelledWidth ψ G s.completion : ℝ) ≤ min (old^T) ((D:ℝ)*old^(Theta s φ hd)) ∧
    ∃ (k : S) (L : ℕ) (ell : ZP (Z:=fun i : R => W (.inl i)) s k → ℕ),
      0 < L ∧ localExponent s φ hd k=Theta s φ hd ∧
      (∀ m : ℕ,FamilyAllowed s k φ m ell) ∧
      ∀ (α C : ℝ),α < Theta s φ hd → 0 < C → ∃ (m : ℕ) (hm : 2 ≤ m),
          letI : NeZero m := ⟨by omega⟩
          C*(labelledWidth (familyMap s k φ m ell) (familyOuter s k m ell) s.position : ℝ)^α < (labelledWidth (familyMap s k φ m ell) (familyOuter s k m ell) s.completion : ℝ) := by
  let φ := fun i : R => ψ (.inl i)
  have hψ : ∀ i z,∃ x y,ψ i x y=z := by
    intro i z
    cases i with
    | inl i => exact hd i z
    | inr j =>
      obtain ⟨a,ha⟩ := (ho j).1
      obtain ⟨b,hb⟩ := ha z
      exact ⟨a,b,hb⟩
  have hord : ∀ i : R ⊕ S,¬IsDesignated i → (∃ a,Function.Surjective (ψ i a)) ∧
      (∃ b,Function.Surjective (fun a => ψ i a b)) := by
    intro i hi
    cases i with
    | inl i => exact (hi trivial).elim
    | inr j => exact ho j
  have hindex : ∃ i : R ⊕ S,¬IsDesignated i :=
    ⟨.inr (Classical.choice inferInstance),by simp [IsDesignated]⟩
  have hτ : ∀ i : R,actualTau ψ hψ (.inl i)=rowCoverNumber (φ i) (hd i) := by
    intro i; rfl
  have hΘ := theta_restriction s φ hd (actualTau ψ hψ) hτ hindex
  have hT : productOn IsDesignated (actualTau ψ hψ)=
      ∏ i : R,rowCoverNumber (φ i) (hd i) := by
    simp [productOn,Fintype.prod_sum_type,IsDesignated,hτ]
  have hD : (∏ i : {i : R ⊕ S // IsDesignated i},
      Fintype.card (U i.val)*Fintype.card (V i.val) : ℕ)=
      ∏ i : R,Fintype.card (U (.inl i))*Fintype.card (V (.inl i)) := by
    let e : {i : R ⊕ S // IsDesignated i} ≃ R :=
      { toFun := fun i => match i with
          | ⟨.inl j,_⟩ => j
          | ⟨.inr j,h⟩ => False.elim h
        invFun := fun j => ⟨.inl j,trivial⟩
        left_inv := by intro i; rcases i with ⟨i,h⟩; cases i with
          | inl j => rfl
          | inr j => exact False.elim h
        right_inv := by intro j; rfl }
    apply Fintype.prod_equiv e
    intro i
    rcases i with ⟨i,h⟩
    cases i with
    | inl j => rfl
    | inr j => exact False.elim h
  constructor
  · have hh := (original_labelled_upper_contract ψ G hψ s IsDesignated hindex hord).1
    rw [hT,hD,hΘ] at hh
    exact hh
  · obtain ⟨k,L,ell,hL,he,hfam,hfail⟩ := scalar_boolean_subcritical_failure s φ hd
    refine ⟨k,L,ell,hL,he,hfam,?_⟩
    intro α C hα hC
    obtain ⟨m,hm,h⟩ := hfail α C hα hC
    refine ⟨m,hm,?_⟩
    letI : NeZero m := ⟨by omega⟩
    simpa only [labelled_width_eq] using h
end OriginalContract
end WeightedBooleanSharpness

end D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion
