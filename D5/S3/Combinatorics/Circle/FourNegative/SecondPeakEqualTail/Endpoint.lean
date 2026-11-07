/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/Endpoint
   generality: I
   mirror-B: none(waiver:physical-source-family-registration)
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete original equal-tail joint lift with literal fresh insertion and repetitions. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Selection
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Physical

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
open SourceWidth PeriodicShortening RunFirstEarTransport
open private selector_exists selectorGates from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Selection
open private MaskBounds from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.SelectorMasks
open private dilation dilation_submask dilation_cap Submask from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Dilation
open private dilation_eq from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Dilation
open private scaledGates A B L K SU SV SW from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Algebra
open private physical_joint seamWindows oldSeams newSeams from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Physical
open private oldValue newValue sourceMod size base newBase charge from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private actual_nat_joint_iff from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private strip_of_prefix from
  D5.S3.Combinatorics.Circle.PeriodicShortening

private theorem repeated_prefixes {α : Type*} (f : α → ℤ) (B : ℤ) (word : List α)
    (hs : InStrip f B 0 word) (hz : (word.map f).sum=0) :
    (∀ m n : ℕ, 0 ≤ ((((List.replicate m word).flatten).take n).map f).sum ∧
      ((((List.replicate m word).flatten).take n).map f).sum ≤ B) ∧
    (∀ m : ℕ, (((List.replicate m word).flatten).map f).sum=0) := by
  have cycles (m : ℕ) : InStrip f B 0 (List.replicate m word).flatten ∧
      (((List.replicate m word).flatten).map f).sum=0 := by
    induction m with
    | zero =>
      constructor
      · simpa [InStrip] using inStrip_prefix hs 0
      · simp
    | succ m ih =>
      simp only [List.replicate_succ,List.flatten_cons]
      refine ⟨inStrip_append hs (by simpa only [hz,zero_add] using ih.1),?_⟩
      simp only [List.map_append,List.sum_append,hz,ih.2,add_zero]
  constructor
  · intro m n
    simpa only [zero_add] using inStrip_prefix (cycles m).1 n
  · intro m
    exact (cycles m).2

private theorem selector_windows (a b c alpha m0 v j0 : ℕ) (early : Bool)
    (r t : ℕ) (hc : c = a+r) (hb : b = c+t+1)
    (hg : ∀ i : Fin 12, 0 ≤ selectorGates a r t alpha m0 v j0 early i)
    (hM : (dilation t m0 : ℕ) = 2^t*(m0+1)-1)
    (hJ : (dilation t j0 : ℕ) = 2^t*(j0+1)-1) :
    seamWindows a b c alpha (dilation t m0) v (dilation t j0) early := by
  subst c
  subst b
  have basevec : base a (a+r+t+1) (a+r) (a+r) =
      ![A (2^a) (2^r) (2^t), B (2^a) (2^r) (2^t),
        L (2^a) (2^r), K (2^a) (2^r) (2^t)] := by
    funext i
    fin_cases i <;> dsimp [base,A,B,L,K] <;>
      simp [pow_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> ring
  have newvec : newBase a (a+r+t+1) (a+r) (a+r) =
      ![2*A (2^a) (2^r) (2^t), SU (2^a) (2^r) (2^t),
        SV (2^a) (2^r), SW (2^a) (2^r) (2^t)] := by
    funext i
    fin_cases i <;>
      simp [newBase,charge,basevec,SU,SV,SW] <;> ring
  have hMc : ((dilation t m0 : ℕ) : ℤ) + 1 =
      (2:ℤ)^t * ((m0:ℤ)+1) := by
    rw [hM]
    have hp : 1 ≤ 2^t*(m0+1) := by
      have ht : 1 ≤ 2^t := Nat.one_le_two_pow
      have hm : 1 ≤ m0+1 := by omega
      nlinarith
    rw [Nat.cast_sub hp]
    push_cast
    ring
  have hJc : ((dilation t j0 : ℕ) : ℤ) + 1 =
      (2:ℤ)^t * ((j0:ℤ)+1) := by
    rw [hJ]
    have hp : 1 ≤ 2^t*(j0+1) := by
      have ht : 1 ≤ 2^t := Nat.one_le_two_pow
      have hj : 1 ≤ j0+1 := by omega
      nlinarith
    rw [Nat.cast_sub hp]
    push_cast
    ring
  have hM4 : 2*(2:ℤ)^t*(4*(m0:ℤ)+4) =
      8*(((dilation t m0 : ℕ) : ℤ)+1) := by
    nlinarith only [hMc]
  have hJ4 : 2*(2:ℤ)^t*(4*(j0:ℤ)+4) =
      8*(((dilation t j0 : ℕ) : ℤ)+1) := by
    nlinarith only [hJc]
  dsimp [seamWindows,oldSeams,newSeams]
  rw [basevec,newvec]
  intro i
  fin_cases i
  · have h0 := hg 0
    have h1 := hg 1
    have h6 := hg 6
    have h7 := hg 7
    dsimp [selectorGates,scaledGates] at h0 h1 h6 h7 ⊢
    rw [hM4] at h0 h1 h6 h7
    have hearly :
        (8:ℤ) * (if early = true then 1 else 0) *
            A (2^a) (2^r) (2^t) =
          8 * (if early = true then A (2^a) (2^r) (2^t) else 0) := by
      cases early <;> simp
    rw [hearly] at h6 h7
    constructor
    · nlinarith only [h0,hMc]
    constructor
    · nlinarith only [h1,h0]
    constructor
    · nlinarith only [h6,hMc]
    · nlinarith only [h7,h6]
  · have h2 := hg 2
    have h3 := hg 3
    have h8 := hg 8
    have h9 := hg 9
    dsimp [selectorGates,scaledGates] at h2 h3 h8 h9 ⊢
    rw [hJ4] at h2 h3 h8 h9
    constructor
    · nlinarith only [h2,hJc]
    constructor
    · nlinarith only [h3,h2]
    constructor
    · nlinarith only [h8,hJc]
    · nlinarith only [h9,h8]
  · have h4 := hg 4
    have h5 := hg 5
    have h10 := hg 10
    have h11 := hg 11
    dsimp [selectorGates,scaledGates] at h4 h5 h10 h11 ⊢
    rw [hJ4] at h4 h5 h10 h11
    constructor
    · nlinarith only [h4,hJc]
    constructor
    · nlinarith only [h5,h4]
    constructor
    · nlinarith only [h10,hJc]
    · nlinarith only [h11,h10]

theorem actualSource_second_peak_equal_tail_joint_lift (a b c : ℕ)
    (ha : 2 ≤ a) (hac : a < c) (hcb : c < b) :
    ∃ sigma : List (Fin (a+b+c+c)), ∃ j : ℕ, j ≤ a+b+c+c ∧
      OriginalOrder (a+b+c+c) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+c+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+c) sigma j) ∧
      (∀ m n : ℕ,
        (((((List.replicate m sigma).flatten).take n).map
          (actualSource (a+b+c+c) (1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
            Set.Icc (0:ℤ) (modulus (a+b+c+c)/2)) ∧
      (∀ m n : ℕ,
        (((((List.replicate m (earWord (a+b+c+c) sigma j)).flatten).take n).map
          (actualSource (a+b+c+c+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))))).sum ∈
            Set.Icc (0:ℤ) (modulus (a+b+c+c))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+c) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+c) sigma j)).flatten).map
          (actualSource (a+b+c+c+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  let r := c-a
  let t := b-c-1
  have hr : 1 ≤ r := by dsimp [r]; omega
  obtain ⟨alpha,m0,v,j0,early,hmask,hg⟩ := selector_exists a r t ha hr
  let M := dilation t m0
  let J := dilation t j0
  rcases hmask with ⟨hAlpha,hM0,hV,hNested⟩
  have hb : 2 ≤ b := by omega
  have hc : 2 ≤ c := by omega
  have hMcap : M < 2^(b-1) := by
    have hh := dilation_cap t (a+r) m0 hM0
    dsimp [M]
    simpa only [show a+r+t=b-1 by omega] using hh
  have hVcap : v < 2^(c-1) := by
    simpa only [show a+r=c by dsimp [r]; omega] using hV
  have hJ : Submask J M := by
    exact dilation_submask t j0 m0 hNested
  have hw : seamWindows a b c alpha M v J early := by
    apply selector_windows a b c alpha m0 v j0 early r t
      (by dsimp [r]; omega) (by dsimp [r,t]; omega) hg
      (dilation_eq t m0) (dilation_eq t j0)
  obtain ⟨sigma,cut,hcut,ho,hn⟩ :=
    physical_joint a b c alpha M v J early ha hb hc hAlpha hMcap hVcap hJ hw
  have oldstrip : InStrip (actualSource (a+b+c+c)
      (1+2^a+2^(a+b)+2^(a+b+c)))
      (modulus (a+b+c+c)/2) 0 sigma := by
    apply strip_of_prefix
    intro n
    simpa only [zero_add,Set.mem_Icc] using ho.2.2 n
  have hhalf : modulus (a+b+c+c+1)/2=modulus (a+b+c+c) := by
    have hp : (2:ℤ)^(a+b+c+c+1)=2*(2:ℤ)^(a+b+c+c) := by
      rw [pow_succ]
      ring
    dsimp [modulus]
    rw [hp]
    omega
  have newstrip : InStrip (actualSource (a+b+c+c+1)
      (2*(1+2^a+2^(a+b)+2^(a+b+c))))
      (modulus (a+b+c+c+1)/2) 0 (earWord (a+b+c+c) sigma cut) := by
    apply strip_of_prefix
    intro n
    simpa only [zero_add,Set.mem_Icc] using hn.2.2 n
  obtain ⟨oldAll,oldZero⟩ := repeated_prefixes _ _ _ oldstrip ho.2.1
  obtain ⟨newAll,newZero⟩ := repeated_prefixes _ _ _ newstrip hn.2.1
  refine ⟨sigma,cut,hcut,ho,hn,?_,?_,?_⟩
  · intro m n
    simpa only [Set.mem_Icc] using oldAll m n
  · intro m n
    simpa only [hhalf,Set.mem_Icc] using newAll m n
  · intro m
    exact ⟨oldZero m,newZero m⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
