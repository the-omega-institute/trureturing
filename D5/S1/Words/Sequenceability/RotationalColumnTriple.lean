/- GID: D5/S1/Words/Sequenceability/RotationalColumnTriple
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/RotationalColumnTriple
   mirror-E: none(waiver:unbounded-symbolic-construction)
   anchors: []
   utility: none
   digest: Every prime at least seven has directed rotational columns with a consecutive additive triple. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! Walecki and four-block twizzler permutations, signed doubling and cyclic rotation.
The constructions follow Ollis--Willmott, On twizzler, zigzag and graceful terraces,
with the directed closing edge and the required additive triple proved separately. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.RotationalColumnTriple

private def Graceful (m : ℕ) (g : ℕ → ℕ) : Prop :=
  (∀ i < m, 1 ≤ g i ∧ g i ≤ m) ∧
  (∀ i < m, ∀ j < m, g i = g j → i = j) ∧
  (∀ i, i + 1 < m, 1 ≤ Nat.dist (g i) (g (i+1)) ∧
    Nat.dist (g i) (g (i+1)) < m) ∧
  (∀ i, i + 1 < m, ∀ j, j + 1 < m,
    Nat.dist (g i) (g (i+1)) = Nat.dist (g j) (g (j+1)) → i = j)

private def walecki (m i : ℕ) : ℕ :=
  if i % 2 = 0 then i / 2 + 1 else m - i / 2

private theorem walecki_graceful (m : ℕ) : Graceful m (walecki m) := by
  have hv : ∀ i < m, 1 ≤ walecki m i ∧ walecki m i ≤ m := by
    intro i hi
    dsimp [walecki]
    split_ifs <;> omega
  have he : ∀ i, i+1 < m,
      Nat.dist (walecki m i) (walecki m (i+1)) = m-1-i := by
    intro i hi
    simp only [walecki, Nat.dist]
    split_ifs <;> omega
  refine ⟨hv, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    simp only [walecki] at hij
    split_ifs at hij <;> omega
  · intro i hi
    rw [he i hi]
    omega
  · intro i hi j hj hij
    rw [he i hi, he j hj] at hij
    omega

/-- Reversal of every full Walecki block of four, followed by its exact tail. -/
private def twizzler (k R i : ℕ) : ℕ :=
  if i < 4*k then
    if i % 4 = 0 then 4*k+R-2*(i/4)-1
    else if i % 4 = 1 then 2*(i/4)+2
    else if i % 4 = 2 then 4*k+R-2*(i/4)
    else 2*(i/4)+1
  else
    let a := 2*k+1
    if R = 2 then a+(i-4*k)
    else if R = 3 then
      if i-4*k = 0 then a+1 else if i-4*k = 1 then a+2 else a
    else if i-4*k = 0 then a+3
    else if i-4*k = 1 then a+2
    else if i-4*k = 2 then a
    else if i-4*k = 3 then a+4
    else a+1

private theorem twizzler_bounds (k R : ℕ) (hk : 1 ≤ k)
    (hR : R = 0 ∨ R = 2 ∨ R = 3 ∨ R = 5) :
    ∀ i < 4*k+R, 1 ≤ twizzler k R i ∧ twizzler k R i ≤ 4*k+R := by
  intro i hi
  rcases hR with rfl | rfl | rfl | rfl <;>
    simp only [twizzler] <;> split_ifs <;> omega

private theorem twizzler_injective (k R : ℕ) (hk : 1 ≤ k)
    (hR : R = 0 ∨ R = 2 ∨ R = 3 ∨ R = 5) :
    ∀ i < 4*k+R, ∀ j < 4*k+R, twizzler k R i = twizzler k R j → i = j := by
  intro i hi j hj hij
  rcases hR with rfl | rfl | rfl | rfl <;>
    simp only [twizzler] at hij <;> split_ifs at hij <;> omega

private def twizzlerLength (k R i : ℕ) : ℕ :=
  if i < 4*k then
    4*k+R-4*(i/4)-(if i%4=0 then 3 else if i%4=1 then 2 else if i%4=2 then 1 else 4)
  else if i-4*k < 2 then i-4*k+1 else if i-4*k=2 then 4 else 3

private theorem twizzler_distance (k R : ℕ) (hk : 1 ≤ k)
    (hR : R = 0 ∨ R = 2 ∨ R = 3 ∨ R = 5) (i : ℕ) (hi : i+1 < 4*k+R) :
    Nat.dist (twizzler k R i) (twizzler k R (i+1)) = twizzlerLength k R i := by
  rcases hR with rfl | rfl | rfl | rfl <;>
    simp only [twizzler, twizzlerLength, Nat.dist] <;> split_ifs <;> omega

private theorem twizzler_graceful (k R : ℕ) (hk : 1 ≤ k)
    (hR : R = 0 ∨ R = 2 ∨ R = 3 ∨ R = 5) : Graceful (4*k+R) (twizzler k R) := by
  refine ⟨twizzler_bounds k R hk hR, twizzler_injective k R hk hR, ?_, ?_⟩
  · intro i hi
    rw [twizzler_distance k R hk hR i hi]
    rcases hR with rfl | rfl | rfl | rfl <;>
      simp only [twizzlerLength] <;> split_ifs <;> omega
  · intro i hi j hj hij
    rw [twizzler_distance k R hk hR i hi, twizzler_distance k R hk hR j hj] at hij
    rcases hR with rfl | rfl | rfl | rfl <;>
      simp only [twizzlerLength] at hij <;> split_ifs at hij <;> omega


private def HasTriple (m : ℕ) (g : ℕ → ℕ) : Prop :=
  ∃ i, i+2 < m ∧ (g i + g (i+2) = g (i+1) ∨
    g i + g (i+2) = g (i+1)+m+1)

private theorem walecki_triple (k : ℕ) (hk : 1 ≤ k) :
    HasTriple (3*k) (walecki (3*k)) := by
  refine ⟨2*k-2, by omega, Or.inl ?_⟩
  simp only [walecki]
  split_ifs <;> omega

private theorem twizzler_triple_even (k R h : ℕ) (hh : 1 ≤ h)
    (hR : R = 0 ∨ R = 2) (hm : 4*k+R = 6*h+2) :
    HasTriple (4*k+R) (twizzler k R) := by
  refine ⟨4*h-1, by omega, Or.inl ?_⟩
  rcases hR with rfl | rfl <;>
    simp only [twizzler] <;> split_ifs <;> omega

private theorem twizzler_triple_odd (k R h : ℕ) (hh : 1 ≤ h)
    (hR : R = 3 ∨ R = 5) (hm : 4*k+R = 6*h+5) :
    HasTriple (4*k+R) (twizzler k R) := by
  refine ⟨4*h+2, by omega, Or.inr ?_⟩
  rcases hR with rfl | rfl <;>
    simp only [twizzler] <;> split_ifs <;> omega

private theorem graceful_with_triple (m : ℕ) (hm : 3 ≤ m)
    (hc : m % 3 = 0 ∨ (m % 3 = 2 ∧ 8 ≤ m)) :
    ∃ g, Graceful m g ∧ HasTriple m g := by
  rcases hc with hc | ⟨hc,h8⟩
  · have he : m = 3*(m/3) := by omega
    rw [he]
    exact ⟨walecki _, walecki_graceful _, walecki_triple _ (by omega)⟩
  · have ht : ∀ k R, 1 ≤ k → (R=0 ∨ R=2 ∨ R=3 ∨ R=5) →
        m=4*k+R → ∃ g, Graceful m g ∧ HasTriple m g := by
      intro k R hk hR he
      have hx : HasTriple (4*k+R) (twizzler k R) := by
        by_cases h2 : m%6=2
        · apply twizzler_triple_even k R (m/6) (by omega) _ (by omega)
          omega
        · apply twizzler_triple_odd k R (m/6) (by omega) _ (by omega)
          omega
      refine ⟨twizzler k R, ?_, ?_⟩
      · simpa only [he] using twizzler_graceful k R hk hR
      · simpa only [he] using hx
    by_cases h0 : m%4=0
    · exact ht (m/4) 0 (by omega) (by omega) (by omega)
    by_cases h2 : m%4=2
    · exact ht (m/4) 2 (by omega) (by omega) (by omega)
    by_cases h3 : m%4=3
    · exact ht (m/4) 3 (by omega) (by omega) (by omega)
    · exact ht (m/4-1) 5 (by omega) (by omega) (by omega)


private theorem interval_surjective (n : ℕ) (f : ℕ → ℕ)
    (hb : ∀ i < n, 1 ≤ f i ∧ f i ≤ n)
    (hi : ∀ i < n, ∀ j < n, f i = f j → i = j) :
    ∀ x, 1 ≤ x → x ≤ n → ∃ i, i < n ∧ f i = x := by
  let F : Fin n → Fin n := fun i => ⟨f i-1, by have := hb i i.isLt; omega⟩
  have hF : Function.Injective F := by
    intro i j hij
    have hv := congrArg Fin.val hij
    have bi := hb i i.isLt
    have bj := hb j j.isLt
    apply Fin.ext
    exact hi i i.isLt j j.isLt (by change f i-1 = f j-1 at hv; omega)
  intro x hx hn
  obtain ⟨i,he⟩ := Finite.surjective_of_injective hF ⟨x-1, by omega⟩
  have hv := congrArg Fin.val he
  have bi := hb i i.isLt
  exact ⟨i,i.isLt,by change f i-1 = x-1 at hv; omega⟩

private def signedStep (g : ℕ → ℕ) (i : ℕ) : ℤ := (g (i+1) : ℤ) - g i

private def doubled (m : ℕ) (g : ℕ → ℕ) (i : ℕ) : ℤ :=
  if i < m then (g i : ℤ) else (g (2*m-1-i) : ℤ)+m

private def signedEdge (m : ℕ) (g : ℕ → ℕ) (i : ℕ) : ℤ :=
  if i+1 < m then signedStep g i
  else if i+1 = m then m
  else if i+1 < 2*m then -signedStep g (2*m-2-i)
  else -(m : ℤ)

private theorem signedEdge_spec (m : ℕ) (hm : 1 ≤ m) (g : ℕ → ℕ)
    (i : ℕ) (hi : i < 2*m) :
    signedEdge m g i = doubled m g (if i+1 < 2*m then i+1 else 0) - doubled m g i := by
  by_cases h1 : i+1 < m
  · simp only [signedEdge, if_pos h1, if_pos (show i+1 < 2*m by omega),
      doubled, if_pos (show i < m by omega), if_pos h1, signedStep]
  by_cases h2 : i+1 = m
  · have hr : 2*m-1-(i+1) = i := by omega
    simp only [signedEdge, if_neg h1, if_pos h2,
      if_pos (show i+1 < 2*m by omega), doubled, if_neg (show ¬ i+1 < m by omega),
      if_pos (show i < m by omega), hr]
    omega
  by_cases h3 : i+1 < 2*m
  · have ha : 2*m-1-(i+1) = 2*m-2-i := by omega
    have hb : 2*m-1-i = (2*m-2-i)+1 := by omega
    simp only [signedEdge, if_neg h1, if_neg h2, if_pos h3, doubled,
      if_neg (show ¬ i < m by omega), if_neg (show ¬ i+1 < m by omega), ha, hb,
      signedStep]
    ring
  · have he : 2*m-1-i = 0 := by omega
    simp only [signedEdge, if_neg h1, if_neg h2, if_neg h3, doubled,
      if_neg (show ¬ i < m by omega), if_pos (show 0 < m by omega), he]
    ring

private theorem signedStep_bounds (m : ℕ) (g : ℕ → ℕ) (hg : Graceful m g)
    (i : ℕ) (hi : i+1 < m) :
    -(m : ℤ) < signedStep g i ∧ signedStep g i < m ∧ signedStep g i ≠ 0 := by
  have hd := hg.2.2.1 i hi
  simp only [Nat.dist] at hd
  dsimp [signedStep]
  omega

private theorem signedEdge_bounds (m : ℕ) (hm : 1 ≤ m) (g : ℕ → ℕ)
    (hg : Graceful m g) (i : ℕ) (hi : i < 2*m) :
    -(m : ℤ) ≤ signedEdge m g i ∧ signedEdge m g i ≤ m ∧ signedEdge m g i ≠ 0 := by
  dsimp only [signedEdge]
  split_ifs with h1 h2 h3
  · have := signedStep_bounds m g hg i h1; omega
  · omega
  · have := signedStep_bounds m g hg (2*m-2-i) (by omega); omega
  · omega

private theorem signedEdge_pair (m : ℕ) (g : ℕ → ℕ) (i : ℕ) (hi : i+1 < m) :
    signedEdge m g i = signedStep g i ∧
    signedEdge m g (2*m-2-i) = -signedStep g i := by
  have hr : 2*m-2-(2*m-2-i) = i := by omega
  constructor
  · simp [signedEdge, hi]
  · simp [signedEdge, show ¬ (2*m-2-i)+1 < m by omega,
      show ¬ (2*m-2-i)+1 = m by omega,
      show (2*m-2-i)+1 < 2*m by omega, hr]

private theorem signedEdge_surjective (m : ℕ) (hm : 1 ≤ m) (g : ℕ → ℕ)
    (hg : Graceful m g) (x : ℕ) (hx : 1 ≤ x) (hxm : x ≤ m) :
    (∃ i, i < 2*m ∧ signedEdge m g i = (x : ℤ)) ∧
    (∃ i, i < 2*m ∧ signedEdge m g i = -(x : ℤ)) := by
  by_cases he : x=m
  · subst x
    constructor
    · exact ⟨m-1, by omega, by simp [signedEdge, show m-1+1=m by omega]⟩
    · exact ⟨2*m-1, by omega, by simp [signedEdge,
        show ¬ 2*m-1+1 < m by omega, show ¬ 2*m-1+1=m by omega,
        show ¬ 2*m-1+1 < 2*m by omega]⟩
  · obtain ⟨i,hi,hd⟩ := interval_surjective (m-1)
      (fun i => Nat.dist (g i) (g (i+1)))
      (by intro i hi; have := hg.2.2.1 i (by omega); omega)
      (by intro i hi j hj he; exact hg.2.2.2 i (by omega) j (by omega) he)
      x hx (by omega)
    have hip : i+1 < m := by omega
    have hp := signedEdge_pair m g i hip
    have hs : signedStep g i = (x : ℤ) ∨ signedStep g i = -(x : ℤ) := by
      simp only [Nat.dist] at hd
      dsimp [signedStep]
      omega
    rcases hs with hs | hs
    · exact ⟨⟨i,by omega,hp.1.trans hs⟩,
        ⟨2*m-2-i,by omega,by rw [hp.2,hs]⟩⟩
    · exact ⟨⟨2*m-2-i,by omega,by rw [hp.2,hs]; ring⟩,
        ⟨i,by omega,hp.1.trans hs⟩⟩

private theorem cast_nonzero (p : ℕ) (z : ℤ) (hl : -(p : ℤ) < z)
    (hu : z < p) (hn : z ≠ 0) : (z : ZMod p) ≠ 0 := by
  intro he
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp he
  by_cases hz : 0 ≤ z
  · exact hn (Int.eq_zero_of_dvd_of_nonneg_of_lt hz hu hd)
  · have he := Int.eq_zero_of_dvd_of_nonneg_of_lt (show 0 ≤ -z by omega)
      (show -z < p by omega) (dvd_neg.mpr hd)
    omega

private theorem nonzero_inventory (n p : ℕ) [NeZero n] [NeZero p]
    (hc : n = p-1) (f : ZMod n → ZMod p) (hn : ∀ i, f i ≠ 0)
    (hs : ∀ x, x ≠ 0 → ∃ i, f i = x) :
    Set.BijOn f Set.univ {x | x ≠ 0} := by
  let F : ZMod n → {x : ZMod p // x ≠ 0} := fun i => ⟨f i,hn i⟩
  have hsur : Function.Surjective F := by
    intro x
    obtain ⟨i,hi⟩ := hs x x.property
    exact ⟨i,Subtype.ext hi⟩
  have hcard : Fintype.card (ZMod n) = Fintype.card {x : ZMod p // x ≠ 0} := by
    simp [Fintype.card_subtype_compl, hc, ZMod.card]
  have hinj := ((Fintype.bijective_iff_surjective_and_card F).mpr ⟨hsur,hcard⟩).1
  refine ⟨fun i _ => hn i, ?_, fun x hx => ?_⟩
  · intro i _ j _ he
    exact hinj (Subtype.ext he)
  · obtain ⟨i,hi⟩ := hs x hx
    exact ⟨i,Set.mem_univ _,hi⟩


private theorem doubled_bounds (m : ℕ) (g : ℕ → ℕ) (hg : Graceful m g)
    (i : ℕ) (hi : i < 2*m) : 1 ≤ doubled m g i ∧ doubled m g i ≤ 2*m := by
  dsimp only [doubled]
  split_ifs with h
  · have := hg.1 i h; omega
  · have := hg.1 (2*m-1-i) (by omega); omega

private theorem doubled_surjective (m : ℕ) (g : ℕ → ℕ) (hg : Graceful m g)
    (x : ℕ) (hx : 1 ≤ x) (hxm : x ≤ 2*m) :
    ∃ i, i < 2*m ∧ doubled m g i = (x : ℤ) := by
  by_cases h : x ≤ m
  · obtain ⟨i,hi,he⟩ := interval_surjective m g hg.1 hg.2.1 x hx h
    exact ⟨i,by omega,by simp [doubled,hi,he]⟩
  · obtain ⟨i,hi,he⟩ := interval_surjective m g hg.1 hg.2.1 (x-m) (by omega) (by omega)
    refine ⟨2*m-1-i,by omega,?_⟩
    have hr : 2*m-1-(2*m-1-i) = i := by omega
    simp only [doubled, if_neg (show ¬ 2*m-1-i < m by omega), hr, he]
    omega

private theorem doubled_triple (m : ℕ) (g : ℕ → ℕ) (ht : HasTriple m g) :
    ∃ j, j+2 < 2*m ∧
      (doubled m g j + doubled m g (j+2) - doubled m g (j+1) = 0 ∨
       doubled m g j + doubled m g (j+2) - doubled m g (j+1) = ((2*m+1 : ℕ) : ℤ)) := by
  obtain ⟨i,hi,ht | ht⟩ := ht
  · refine ⟨i,by omega,Or.inl ?_⟩
    simp only [doubled, if_pos (show i < m by omega), if_pos hi,
      if_pos (show i+1 < m by omega)]
    omega
  · let j := 2*m-3-i
    have hj : j+2 < 2*m := by dsimp [j]; omega
    have h0 : 2*m-1-j = i+2 := by dsimp [j]; omega
    have h1 : 2*m-1-(j+1) = i+1 := by dsimp [j]; omega
    have h2 : 2*m-1-(j+2) = i := by dsimp [j]; omega
    refine ⟨j,hj,Or.inr ?_⟩
    simp only [doubled, if_neg (show ¬ j < m by dsimp [j]; omega),
      if_neg (show ¬ j+2 < m by dsimp [j]; omega),
      if_neg (show ¬ j+1 < m by dsimp [j]; omega), h0,h1,h2]
    omega

private theorem phase_successor (m : ℕ) (hm : 1 ≤ m) [NeZero (2*m)]
    (i : ZMod (2*m)) :
    (i+1).val = if i.val+1 < 2*m then i.val+1 else 0 := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < 2*m by omega)]
  have hi := i.val_lt
  split_ifs <;> omega

private def rawColumn (m : ℕ) (g : ℕ → ℕ) (i : ZMod (2*m)) : ZMod (2*m+1) :=
  (doubled m g i.val : ZMod (2*m+1))

private theorem rawColumn_edge (m : ℕ) (hm : 1 ≤ m) [NeZero (2*m)]
    (g : ℕ → ℕ) (i : ZMod (2*m)) :
    rawColumn m g (i+1) - rawColumn m g i = (signedEdge m g i.val : ZMod (2*m+1)) := by
  rw [signedEdge_spec m hm g i.val i.val_lt]
  simp only [rawColumn, phase_successor m hm, Int.cast_sub]

private theorem signed_representative (m : ℕ) (hm : 1 ≤ m)
    (x : ZMod (2*m+1)) (hx : x ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ (x = (k : ZMod (2*m+1)) ∨ x = -(k : ZMod (2*m+1))) := by
  have hval := x.val_lt
  have hpos : 1 ≤ x.val := by have := (ZMod.val_eq_zero x).not.mpr hx; omega
  by_cases he : x.val ≤ m
  · exact ⟨x.val,hpos,he,Or.inl (ZMod.natCast_zmod_val x).symm⟩
  · refine ⟨2*m+1-x.val,by omega,by omega,Or.inr ?_⟩
    have hv : (2*m+1-x.val) + x.val = 2*m+1 := by omega
    have heq := congrArg (fun n : ℕ => (n : ZMod (2*m+1))) hv
    simp only [Nat.cast_add, ZMod.natCast_self, ZMod.natCast_zmod_val] at heq
    exact (eq_neg_iff_add_eq_zero).mpr (by simpa [add_comm] using heq)

private theorem rawColumn_inventories (m : ℕ) (hm : 1 ≤ m) [NeZero (2*m)]
    (g : ℕ → ℕ) (hg : Graceful m g) :
    Set.BijOn (rawColumn m g) Set.univ {x | x ≠ 0} ∧
    Set.BijOn (fun i => rawColumn m g (i+1) - rawColumn m g i) Set.univ {x | x ≠ 0} := by
  constructor
  · apply nonzero_inventory (2*m) (2*m+1) (by omega)
    · intro i
      have hb := doubled_bounds m g hg i.val i.val_lt
      exact cast_nonzero _ _ (by omega) (by omega) (by omega)
    · intro x hx
      have hv := x.val_lt
      have hp : 1 ≤ x.val := by have := (ZMod.val_eq_zero x).not.mpr hx; omega
      obtain ⟨i,hi,he⟩ := doubled_surjective m g hg x.val hp (by omega)
      refine ⟨(i : ZMod (2*m)),?_⟩
      simp only [rawColumn, ZMod.val_natCast_of_lt hi, he, Int.cast_natCast,
        ZMod.natCast_zmod_val]
  · apply nonzero_inventory (2*m) (2*m+1) (by omega)
    · intro i
      rw [rawColumn_edge m hm]
      have hb := signedEdge_bounds m hm g hg i.val i.val_lt
      exact cast_nonzero _ _ (by omega) (by omega) hb.2.2
    · intro x hx
      obtain ⟨k,hk,hmk,he | he⟩ := signed_representative m hm x hx
      · obtain ⟨⟨i,hi,hiE⟩,_⟩ := signedEdge_surjective m hm g hg k hk hmk
        refine ⟨(i : ZMod (2*m)),?_⟩
        rw [rawColumn_edge m hm, ZMod.val_natCast_of_lt hi, hiE, Int.cast_natCast, ← he]
      · obtain ⟨_,⟨i,hi,hiE⟩⟩ := signedEdge_surjective m hm g hg k hk hmk
        refine ⟨(i : ZMod (2*m)),?_⟩
        rw [rawColumn_edge m hm, ZMod.val_natCast_of_lt hi, hiE, Int.cast_neg,
          Int.cast_natCast, ← he]

private theorem rotate_column (n p : ℕ) (D : ZMod n → ZMod p)
    (hv : Set.BijOn D Set.univ {x | x ≠ 0})
    (he : Set.BijOn (fun i => D (i+1)-D i) Set.univ {x | x ≠ 0})
    (j : ZMod n) (ht : D (j+1) = D j + D (j+2)) :
    ∃ d : ZMod n → ZMod p,
      Set.BijOn d Set.univ {x | x ≠ 0} ∧
      Set.BijOn (fun i => d (i+1)-d i) Set.univ {x | x ≠ 0} ∧
      d 1 = d 0 + d 2 := by
  have hshift : Set.BijOn (fun i : ZMod n => j+i) Set.univ Set.univ := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · intro a _ b _ hab; exact add_left_cancel hab
    · intro a _; exact ⟨a-j,Set.mem_univ _,by abel⟩
  refine ⟨fun i => D (j+i), hv.comp hshift, ?_, ?_⟩
  · simpa only [add_assoc] using he.comp hshift
  · simpa only [add_zero] using ht

private theorem column_from_graceful (m : ℕ) (hm : 1 ≤ m)
    (g : ℕ → ℕ) (hg : Graceful m g) (ht : HasTriple m g) :
    ∃ d : ZMod (2*m) → ZMod (2*m+1),
      Set.BijOn d Set.univ {x | x ≠ 0} ∧
      Set.BijOn (fun i => d (i+1)-d i) Set.univ {x | x ≠ 0} ∧
      d 1 = d 0 + d 2 := by
  letI : NeZero (2*m) := ⟨by omega⟩
  obtain ⟨hv,he⟩ := rawColumn_inventories m hm g hg
  obtain ⟨j,hj,ht⟩ := doubled_triple m g ht
  apply rotate_column (2*m) (2*m+1) (rawColumn m g) hv he (j : ZMod (2*m))
  have hj0 : j < 2*m := by omega
  have hj1 : j+1 < 2*m := by omega
  have hc1 : (j : ZMod (2*m))+1 = ((j+1 : ℕ) : ZMod (2*m)) := by simp
  have hc2 : (j : ZMod (2*m))+2 = ((j+2 : ℕ) : ZMod (2*m)) := by push_cast; rfl
  simp only [hc1,hc2,rawColumn,ZMod.val_natCast_of_lt hj0,
    ZMod.val_natCast_of_lt hj1,ZMod.val_natCast_of_lt hj]
  have hcast : ((doubled m g j + doubled m g (j+2) - doubled m g (j+1) : ℤ) :
      ZMod (2*m+1)) = 0 := by
    rcases ht with ht | ht <;> rw [ht] <;> simp
  push_cast at hcast
  linear_combination -hcast


/-- Every prime at least seven has a cyclic ordering of precisely the nonzero
residues, whose actual directed cyclic differences order the same set, and whose
first three consecutive entries satisfy the additive cut relation. -/
theorem exists_rotational_column_triple (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) :
    ∃ d : ZMod (p-1) → ZMod p,
      Set.BijOn d Set.univ {x | x ≠ 0} ∧
      Set.BijOn (fun i => d (i+1)-d i) Set.univ {x | x ≠ 0} ∧
      d 1 = d 0 + d 2 := by
  by_cases h11 : p=11
  · subst p
    refine ⟨fun i => (![1,3,2,7,4,8,6,9,10,5] : Fin 10 → ZMod 11) ⟨i.val,i.val_lt⟩, ?_⟩
    decide
  · have hodd := hp.eq_two_or_odd.resolve_left (by omega)
    have h3 : p%3 ≠ 0 := by
      intro he
      have hd := hp.eq_one_or_self_of_dvd 3 ((Nat.dvd_iff_mod_eq_zero).mpr he)
      omega
    let m := p/2
    have hpm : p=2*m+1 := by dsimp [m]; omega
    have hm : 3 ≤ m := by omega
    have hc : m%3=0 ∨ (m%3=2 ∧ 8 ≤ m) := by omega
    obtain ⟨g,hg,ht⟩ := graceful_with_triple m hm hc
    have H := column_from_graceful m (by omega) g hg ht
    simpa only [hpm, Nat.add_sub_cancel] using H

end D5.S1.Words.Sequenceability.RotationalColumnTriple
