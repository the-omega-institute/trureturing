/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Strip
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Strip
   mirror-E: none(waiver:internal-strong-strip)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Strong shadow-charge invariants imply both literal first-ear prefix strips. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Source

/-! The old height is r-Q and the enlarged height after the first ear is h+r. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open SourceWidth PeriodicShortening RunFirstEarTransport

private def Strong (f q : ℕ→ℤ) (B h Q : ℤ) : List ℕ→Prop
  | [] => 0≤h ∧ h≤B-1 ∧ 0≤h+Q ∧ h+Q≤B
  | i::xs => 0≤h ∧ h≤B-1 ∧ 0≤h+Q ∧ h+Q≤B ∧
      Strong f q B (h+f i) (Q-q i) xs

/-- A common physical prefix satisfies both strips, including arbitrary prefix lengths. -/
private theorem strong_strips (f q : ℕ→ℤ) (B h Q : ℤ) (xs : List ℕ)
    (hs : Strong f q B h Q xs) :
    InStrip f (B-1) h xs ∧ InStrip (fun i => 2*f i-q i) (2*B-1) (2*h+Q) xs := by
  induction xs generalizing h Q with
  | nil =>
    dsimp [Strong] at hs
    exact ⟨⟨hs.1,hs.2.1⟩,⟨by omega,by omega⟩⟩
  | cons i xs ih =>
    obtain ⟨h0,hB,r0,rB,rest⟩ := hs
    obtain ⟨old,new⟩ := ih (h+f i) (Q-q i) rest
    constructor
    · exact ⟨h0,hB,old⟩
    · refine ⟨by omega,by omega,?_⟩
      convert new using 1 <;> ring

/-- At a proper prefix the remaining final-negative charge gives the strict old ceiling. -/
private theorem strong_of_shadow (B h Q : ℤ) (h0 : 0≤h) (hQ : 1≤Q)
    (hr : h+Q≤B) : 0≤h ∧ h≤B-1 ∧ 0≤h+Q ∧ h+Q≤B := by
  omega

/-- The lift preserves strong bounds when the actual remaining charge is unchanged. -/
private theorem lift_bounds (M B h Q : ℤ) (hM : 1≤M) (hB : 1≤B)
    (h0 : 0≤h) (hQ : 0≤Q) (hr : h+Q≤B)
    (hproper : 1≤Q ∨ h=0 ∧ Q=0) :
    let h' := M*h+(M-1)*Q
    0≤h' ∧ h'≤M*B-1 ∧ 0≤h'+Q ∧ h'+Q≤M*B := by
  dsimp only
  have hleft := mul_nonneg (show 0≤M by omega) h0
  have hright := mul_nonneg (show 0≤M-1 by omega) hQ
  have hmul := mul_le_mul_of_nonneg_left hr (show 0≤M by omega)
  have hMB : 1≤M*B := by nlinarith
  rcases hproper with hp|⟨rfl,rfl⟩ <;> constructor
  · nlinarith
  · refine ⟨?_,?_,?_⟩ <;> nlinarith
  · norm_num
  · norm_num at *
    omega


/-- With nonnegative charge, the old strict ceiling also covers the zero-charge case. -/
private theorem scaled_bounds (M B h Q : ℤ) (hM : 1≤M)
    (h0 : 0≤h) (hB : h≤B-1) (hQ : 0≤Q) (hr : h+Q≤B) :
    0≤M*h+(M-1)*Q ∧ M*h+(M-1)*Q≤M*B-1 ∧
      0≤M*h+(M-1)*Q+Q ∧ M*h+(M-1)*Q+Q≤M*B := by
  have hleft := mul_nonneg (show 0≤M by omega) h0
  have hright := mul_nonneg (show 0≤M-1 by omega) hQ
  have hmul := mul_le_mul_of_nonneg_left hr (show 0≤M by omega)
  refine ⟨by nlinarith,?_,by nlinarith,by nlinarith⟩
  by_cases hQ1 : 1≤Q
  · nlinarith
  · have hQ0 : Q=0 := by omega
    have hmul' := mul_le_mul_of_nonneg_left hB (show 0≤M by omega)
    rw [hQ0]
    nlinarith

/-- A positive block is controlled by its final shadow height and retained charge. -/
private theorem strong_positive_block (f q : ℕ→ℤ) (B h Q : ℤ) (xs : List ℕ)
    (hf : ∀ i∈xs, 0≤f i) (hq : ∀ i∈xs, q i=0)
    (h0 : 0≤h) (hQ : 1≤Q) (hend : h+Q+(xs.map f).sum≤B) :
    Strong f q B h Q xs := by
  induction xs generalizing h with
  | nil =>
    simp only [List.map_nil,List.sum_nil,add_zero] at hend
    exact strong_of_shadow B h Q h0 hQ hend
  | cons i xs ih =>
    have hfi:=hf i (by simp)
    have hqi:=hq i (by simp)
    have hf' : ∀ j∈xs, 0≤f j := by intro j hj; exact hf j (by simp [hj])
    have hsum : 0≤(xs.map f).sum :=
      List.sum_nonneg (by intro v hv; obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hv; exact hf' j hj)
    simp only [List.map_cons,List.sum_cons] at hend
    have hb:=strong_of_shadow B h Q h0 hQ (by linarith)
    refine ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,?_⟩
    rw [hqi,sub_zero]
    exact ih (h+f i) hf' (fun j hj => hq j (by simp [hj])) (by linarith) (by linarith)

private theorem strong_append (f q : ℕ→ℤ) (B h Q : ℤ) (xs ys : List ℕ)
    (hx : Strong f q B h Q xs)
    (hy : Strong f q B (h+(xs.map f).sum) (Q-(xs.map q).sum) ys) :
    Strong f q B h Q (xs++ys) := by
  induction xs generalizing h Q with
  | nil => simpa using hy
  | cons i xs ih =>
    obtain ⟨h0,hB,r0,rB,rest⟩:=hx
    refine ⟨h0,hB,r0,rB,?_⟩
    apply ih (h+f i) (Q-q i) rest
    convert hy using 1 <;> simp only [List.map_cons,List.sum_cons] <;> ring

/-- Whole-word lift transport, using actual per-label compatibility when instantiated. -/
private theorem strong_scaled (f q F G : ℕ→ℤ) (shift : ℕ→ℕ)
    (M B h Q : ℤ) (xs : List ℕ) (hM : 1≤M)
    (hs : Strong f q B h Q xs) (hq : ∀ i∈xs, 0≤q i)
    (hcharge : (xs.map q).sum≤Q)
    (hF : ∀ i∈xs, F (shift i)=M*f i-(M-1)*q i)
    (hG : ∀ i∈xs, G (shift i)=q i) :
    Strong F G (M*B) (M*h+(M-1)*Q) Q (xs.map shift) := by
  induction xs generalizing h Q with
  | nil =>
    simp only [List.map_nil,List.sum_nil] at hcharge
    exact scaled_bounds M B h Q hM hs.1 hs.2.1 hcharge hs.2.2.2
  | cons i xs ih =>
    obtain ⟨h0,hB,r0,rB,rest⟩:=hs
    have hsum : 0≤((i::xs).map q).sum :=
      List.sum_nonneg (by intro v hv; obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hv; exact hq j hj)
    have hb:=scaled_bounds M B h Q hM h0 hB (by omega) rB
    refine ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,?_⟩
    rw [hF i (by simp),hG i (by simp)]
    have he : M*h+(M-1)*Q+(M*f i-(M-1)*q i)=
        M*(h+f i)+(M-1)*(Q-q i) := by ring
    rw [he]
    apply ih (h+f i) (Q-q i) rest
    · intro j hj; exact hq j (by simp [hj])
    · simp only [List.map_cons,List.sum_cons] at hcharge
      linarith
    · intro j hj; exact hF j (by simp [hj])
    · intro j hj; exact hG j (by simp [hj])

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
