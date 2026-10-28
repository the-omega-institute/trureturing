import D5.S3.Combinatorics.Circle.TerminalSmallOwnership
set_option autoImplicit false
set_option relaxedAutoImplicit false
open D5.S3.Combinatorics.Circle
open SourceWidth ExpandingSourcePath MixedSuffixEnergy TwoOppositeLargeExchange
open ThreeLargePacketExchange TerminalSmallOwnership

example
    (k t : ℕ) (p y zpen z : Fin k) (A T0 T1 T2 E : List (Fin k))
    (H1 : 3 ≤ k)
    (H2 : 0 < s k t p)
    (H3 : Q k ≤ |s k t (hit k 1 p)|)
    (H4 : N k < 3 * |s k t p|)
    (H5 : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (H6 : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (H7 : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (H8 : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (H9 : Q k ≤ -s k t zpen)
    (H10 : Q k ≤ -s k t z)
    (H11 : s k t p < -s k t y)
    (H12 : ∀ V : List (Fin k), Legal k t V →
      J k t (oldWord p y zpen z A T0 T1 T2 E) ≤ J k t V) :
    let F := A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2
    let f := s k t
    let W := F ++ [z] ++ E
    let n := hit k 1 p
    let P := f p
    let D := |f n|
    let B := C k - P
    let d := P - D
    let u := mass f F
    let q := fun m : ℕ => mass f (F ++ [z] ++ E.take m)
    C k - d < u ∧
    (∀ m : ℕ, B < q m ∧ q m < D) ∧
    (∀ i : Fin k, |f i| < Q k → 0 ≤ f i → i ∈ W) ∧
    (∀ i : Fin k, i ∉ W → |f i| < Q k →
      let σ := -f i
      0 < σ ∧
      (∀ m : ℕ, q m < σ) ∧
      u - D < σ ∧
      f (hit k 1 i) = -(2 * σ) ∧
      Q k ≤ -f (hit k 1 i) ∧
      (hit k 1 i ∈ W ∨
        (u < 2 * σ ∧ hit k 2 i ∈ W ∧
          0 < f (hit k 2 i) ∧
          f (hit k 2 i) ≤ 2 * d - 3 ∧
          f (hit k 2 i) < Q k))) := by
  let F := A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2
  have hE : ∀ i ∈ E, |s k t i| < Q k := by
    intro i hi
    exact H8 i (List.mem_append_right _ hi)
  exact actualSource_terminal_small_ownership_transition k t H1 p z F E H2 H3 H4
    H5 H6 H7 hE H10 H12
