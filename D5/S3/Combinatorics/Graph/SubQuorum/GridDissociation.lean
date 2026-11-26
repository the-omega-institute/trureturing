/- GID: D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/GridDissociation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual rectangular-grid row profiles and dissociation extrema. -/

import D5.S3.Combinatorics.Graph.SubQuorum.GridProfile
import D5.S3.Combinatorics.Graph.StarForming.SquareCapacity
import D5.S3.Combinatorics.Graph.StarForming.Isomorphism
import Mathlib.Data.Fin.VecNotation

/-! Actual grid semantics for GRID_PROFILE_PROOF, received from
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. The periodic lower construction is attributed there to Sahbi. The distinct coloring, representative and star-forming parameters are not
identified by this dissociation proof. -/

namespace D5.S3.Combinatorics.Graph.SubQuorum.GridDissociation
open StarFormingDissociationRefutation
open scoped BigOperators

/-- Cartesian product of the two actual finite paths. -/
def graph (m n : ℕ) : SimpleGraph (Fin m × Fin n) where
  Adj x y := (x.1=y.1 ∧ (SimpleGraph.pathGraph n).Adj x.2 y.2) ∨
    ((SimpleGraph.pathGraph m).Adj x.1 y.1 ∧ x.2=y.2)
  symm := ⟨by
    intro x y h
    rcases h with ⟨he,ha⟩ | ⟨ha,he⟩
    · exact Or.inl ⟨he.symm,ha.symm⟩
    · exact Or.inr ⟨ha.symm,he.symm⟩⟩
  loopless := ⟨by intro x h; rcases h with h | h <;> simp_all⟩

instance (m n : ℕ) : DecidableRel (graph m n).Adj := by
  intro x y
  unfold graph
  dsimp
  infer_instance

variable {m n : ℕ}

def row (D : Finset (Fin m × Fin n)) (i : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (i,j) ∈ D)

def rowCount (D : Finset (Fin m × Fin n)) (i : Fin m) : ℕ := (row D i).card

/-- Every vertex belongs to exactly one actual row. -/
theorem sum_rowCount (D : Finset (Fin m × Fin n)) : ∑ i, rowCount D i=D.card := by
  classical
  have he (i : Fin m) : D.filter (fun v => v.1=i) = (row D i).image (fun j => (i,j)) := by
    ext v
    rcases v with ⟨k,j⟩
    simp only [Finset.mem_filter,Finset.mem_image,row,Finset.mem_univ,true_and,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hm,rfl⟩
      exact ⟨j,hm,rfl,rfl⟩
    · rintro ⟨l,hm,he,hj⟩
      subst k
      subst l
      exact ⟨hm,rfl⟩
  have hc := Finset.card_eq_sum_card_fiberwise (f:=Prod.fst) (s:=D) (t:=Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  have hcard (i : Fin m) : ((row D i).image (fun j => (i,j))).card=(row D i).card :=
    Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
  simp_rw [he,hcard] at hc
  exact hc.symm

/-- Three consecutive selected row vertices contradict the actual dissociation predicate. -/
theorem row_three_free (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D)
    (i : Fin m) (j k l : Fin n) (hjk : j.val+1=k.val) (hkl : k.val+1=l.val) :
    ¬ (j ∈ row D i ∧ k ∈ row D i ∧ l ∈ row D i) := by
  rintro ⟨hj,hk,hl⟩
  have hd := (DoubleStarGrafting.independent_iff (graph m n) D).mp hD
  have he := hd (i,k) (Finset.mem_filter.mp hk).2
    (i,j) (Finset.mem_filter.mp hj).2 (i,l) (Finset.mem_filter.mp hl).2
    (Or.inl ⟨rfl,SimpleGraph.pathGraph_adj.mpr (Or.inr hjk)⟩)
    (Or.inl ⟨rfl,SimpleGraph.pathGraph_adj.mpr (Or.inl hkl)⟩)
  have hv := congrArg (fun v : Fin m × Fin n => v.2.val) he
  dsimp at hv
  omega

/-- The exact path bound applies to every row of every grid dissociation set. -/
theorem row_bound (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D)
    (i : Fin m) : rowCount D i ≤ n-n/3 := by
  let P := (row D i).image Fin.val
  have hb : P.card ≤ n-n/3 := by
    apply GridProfile.three_free_card n P
    · intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      exact k.isLt
    · rintro j ⟨h0,h1,h2⟩
      obtain ⟨k,hk,hek⟩ := Finset.mem_image.mp h0
      obtain ⟨l,hl,hel⟩ := Finset.mem_image.mp h1
      obtain ⟨p,hp,hep⟩ := Finset.mem_image.mp h2
      exact row_three_free D hD i k l p (by omega) (by omega) ⟨hk,hl,hp⟩
  simpa only [rowCount,P,Finset.card_image_of_injective _ Fin.val_injective] using hb

def bandCount (D : Finset (Fin m × Fin n)) (i k : Fin m) (j : Fin n) : ℕ :=
  (if (i,j) ∈ D then 1 else 0)+(if (k,j) ∈ D then 1 else 0)

private def square (i k : Fin m) (hik : (SimpleGraph.pathGraph m).Adj i k)
    (j l : Fin n) (hjl : (SimpleGraph.pathGraph n).Adj j l) :
    StarForming.SquareCapacity.Square (graph m n) where
  vertex := ![(i,j),(i,l),(k,l),(k,j)]
  injective := by
    have hi : i≠k := hik.ne
    have hj : j≠l := hjl.ne
    intro a b he
    fin_cases a <;> fin_cases b <;> simp_all
  edge01 := Or.inl ⟨rfl,hjl⟩
  edge12 := Or.inr ⟨hik,rfl⟩
  edge23 := Or.inl ⟨rfl,hjl.symm⟩
  edge30 := Or.inr ⟨hik.symm,rfl⟩

/-- Each actual two-by-two square contains at most two selected vertices. -/
theorem band_pair_bound (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D)
    (i k : Fin m) (hik : (SimpleGraph.pathGraph m).Adj i k)
    (j l : Fin n) (hjl : (SimpleGraph.pathGraph n).Adj j l) :
    bandCount D i k j+bandCount D i k l ≤ 2 := by
  classical
  let C := square i k hik j l hjl
  have hc := StarForming.SquareCapacity.intersection_cap (graph m n) D hD C
  have he : D ∩ C.carrier =
      (Finset.univ.filter (fun z : Fin 4 => C.vertex z ∈ D)).image C.vertex := by
    ext v
    simp only [Finset.mem_inter,StarForming.SquareCapacity.Square.carrier,Finset.mem_image,
      Finset.mem_univ,true_and,Finset.mem_filter]
    constructor
    · rintro ⟨hv,z,rfl⟩
      exact ⟨z,hv,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨hz,z,rfl⟩
  rw [he,Finset.card_image_of_injective _ C.injective,Finset.card_filter] at hc
  change (∑ z : Fin 4, if ![(i,j),(i,l),(k,l),(k,j)] z ∈ D then 1 else 0) ≤ 2 at hc
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Nat.add_zero] at hc
  dsimp [bandCount]
  by_cases h0 : (i,j) ∈ D <;> by_cases h1 : (i,l) ∈ D <;>
    by_cases h2 : (k,j) ∈ D <;> by_cases h3 : (k,l) ∈ D <;>
    simp_all only [ite_true,ite_false] <;> omega

/-- The column counts exactly sum the two row counts. -/
theorem sum_bandCount (D : Finset (Fin m × Fin n)) (i k : Fin m) :
    (∑ j, bandCount D i k j)=rowCount D i+rowCount D k := by
  simp only [bandCount,Finset.sum_add_distrib,rowCount,row,Finset.card_filter]

/-- A column of a two-row band contains at most its two actual vertices. -/
theorem bandCount_cap (D : Finset (Fin m × Fin n)) (i k : Fin m) (j : Fin n) :
    bandCount D i k j ≤ 2 := by
  unfold bandCount
  split_ifs <;> omega

/-- The even ladder bound holds on each pair of actual adjacent grid rows. -/
theorem even_band_bound (hn : n%2=0) (D : Finset (Fin m × Fin n))
    (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m)
    (hik : (SimpleGraph.pathGraph m).Adj i k) : rowCount D i+rowCount D k ≤ n := by
  have hb := GridProfile.even_adjacent_sum_bound hn
    (fun j => (bandCount D i k j : ℤ))
    (fun j l hjl => by exact_mod_cast band_pair_bound D hD i k hik j l hjl)
  rw [← Nat.cast_sum,sum_bandCount] at hb
  exact_mod_cast hb

/-- The odd ladder bound keeps the final full column, including width one. -/
theorem odd_band_bound (hn : n%2=1) (D : Finset (Fin m × Fin n))
    (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m)
    (hik : (SimpleGraph.pathGraph m).Adj i k) : rowCount D i+rowCount D k ≤ n+1 := by
  let j : Fin n := ⟨0,by omega⟩
  have hb := GridProfile.odd_adjacent_sum_bound hn
    (fun l => (bandCount D i k l : ℤ))
    (fun l p hlp => by exact_mod_cast band_pair_bound D hD i k hik l p hlp) j rfl
  rw [← Nat.cast_sum,sum_bandCount] at hb
  have hc := bandCount_cap D i k j
  omega

/-- Equality in an odd actual ladder has full even columns and empty odd columns. -/
theorem band_rigidity (hn : n%2=1) (D : Finset (Fin m × Fin n))
    (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m)
    (hik : (SimpleGraph.pathGraph m).Adj i k)
    (htotal : n+1 ≤ rowCount D i+rowCount D k) :
    ∀ j, bandCount D i k j=if j.val%2=0 then 2 else 0 := by
  apply GridProfile.odd_ladder_rigidity hn _ (bandCount_cap D i k)
    (fun j l hjl => band_pair_bound D hD i k hik j l hjl)
  rwa [sum_bandCount]

/-- The sole positive adjacent-row exception has equal row counts. -/
theorem odd_row_pair (hn : n%2=1) (D : Finset (Fin m × Fin n))
    (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m)
    (hik : (SimpleGraph.pathGraph m).Adj i k) :
    rowCount D i+rowCount D k ≤ n ∨
      (2*rowCount D i=n+1 ∧ 2*rowCount D k=n+1) := by
  by_cases hb : rowCount D i+rowCount D k ≤ n
  · exact Or.inl hb
  · have hc := odd_band_bound hn D hD i k hik
    have hr := band_rigidity hn D hD i k hik (by omega)
    have he : row D i=row D k := by
      ext j
      simp only [row,Finset.mem_filter,Finset.mem_univ,true_and]
      have hj := hr j
      dsimp [bandCount] at hj
      split_ifs at hj <;> simp_all
    have hec : rowCount D i=rowCount D k := congrArg Finset.card he
    exact Or.inr ⟨by omega,by omega⟩

/-- Actual selected neighbors prohibit three consecutive positive odd row deviations. -/
theorem row_profile_three_free (hn : n%2=1) (D : Finset (Fin m × Fin n))
    (hD : IsKIndependent (graph m n) 2 D) (i k l : Fin m)
    (hik : i.val+1=k.val) (hkl : k.val+1=l.val) :
    ¬ (0<2*(rowCount D i : ℤ)-n ∧ 0<2*(rowCount D k : ℤ)-n ∧
      0<2*(rowCount D l : ℤ)-n) := by
  rintro ⟨hi,hk,hl⟩
  have hr := band_rigidity hn D hD i k (SimpleGraph.pathGraph_adj.mpr (Or.inl hik))
    (by omega)
  have hs := band_rigidity hn D hD k l (SimpleGraph.pathGraph_adj.mpr (Or.inl hkl))
    (by omega)
  let j : Fin n := ⟨0,by omega⟩
  have h0 := hr j
  have h1 := hs j
  simp only [j,Fin.val_mk,Nat.zero_mod,ite_true] at h0 h1
  have hmem : (i,j) ∈ D ∧ (k,j) ∈ D ∧ (l,j) ∈ D := by
    dsimp [bandCount] at h0 h1
    dsimp [j]
    split_ifs at h0 h1 <;> simp_all
  have hd := (DoubleStarGrafting.independent_iff (graph m n) D).mp hD
  have he := hd (k,j) hmem.2.1 (i,j) hmem.1 (l,j) hmem.2.2
    (Or.inr ⟨SimpleGraph.pathGraph_adj.mpr (Or.inr hik),rfl⟩)
    (Or.inr ⟨SimpleGraph.pathGraph_adj.mpr (Or.inl hkl),rfl⟩)
  have hv := congrArg (fun v : Fin m × Fin n => v.1.val) he
  dsimp at hv
  omega

/-- Pair adjacent rows and retain exactly the unmatched final row. -/
private theorem paired_sum_bound (p q R : ℕ) (f : Fin p → ℕ)
    (hcap : ∀ i, f i ≤ R)
    (hpair : ∀ i j, (SimpleGraph.pathGraph p).Adj i j → f i+f j ≤ q) :
    (∑ i, f i) ≤ (p/2)*q+(p%2)*R := by
  induction p using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using hcap 0
  | more p ih _ =>
    have hb := ih (fun i => f i.succ.succ) (fun i => hcap i.succ.succ)
      (fun i j hij => hpair i.succ.succ j.succ.succ
        (SimpleGraph.pathGraph_adj.mpr (by
          rcases SimpleGraph.pathGraph_adj.mp hij with h | h <;>
            simp only [Fin.val_succ] <;> omega)))
    have hp := hpair 0 1 (SimpleGraph.pathGraph_adj.mpr (Or.inl rfl))
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    have hd : (p+2)/2=p/2+1 := by omega
    have hm : (p+2)%2=p%2 := by omega
    rw [hd,hm,Nat.add_mul]
    simpa only [Nat.one_mul,Fin.succ_zero_eq_one] using (by omega :
      f 0+(f 1+∑ i : Fin p, f i.succ.succ) ≤ (p/2)*q+1*q+(p%2)*R)

/-- Twice the ordinary path bound minus the path order. -/
def g (p : ℕ) : ℕ := p-2*(p/3)

/-- The first periodic row construction count. -/
def rowFormula (p q : ℕ) : ℕ := ((p+1)/2)*(q-q/3)+(p/2)*(q/3)

/-- The two independent construction directions remain a finite maximum. -/
def formula (p q : ℕ) : ℕ := max (rowFormula p q) (rowFormula q p)

private theorem twice_rowFormula (p q : ℕ) :
    2*rowFormula p q=p*q+(p%2)*g q := by
  have hp : 2*(p/2)+p%2=p := by omega
  have hp' : (p+1)/2=p/2+p%2 := by omega
  have hq : q/3 ≤ q := by omega
  have hq' : 2*(q/3) ≤ q := by omega
  unfold rowFormula g
  rw [hp']
  have h1 := congrArg (fun x : ℕ => (p/2)*x) (Nat.sub_add_cancel hq)
  have h2 := congrArg (fun x : ℕ => (p%2)*x)
    (show 2*(q-q/3)=q+(q-2*(q/3)) by omega)
  have h3 := congrArg (fun x : ℕ => x*q) hp
  nlinarith

private theorem twice_formula (p q : ℕ) :
    2*formula p q=p*q+max ((p%2)*g q) ((q%2)*g p) := by
  unfold formula
  rw [mul_max,twice_rowFormula,twice_rowFormula,Nat.mul_comm q p]
  omega

private theorem profile_sum (D : Finset (Fin m × Fin n)) :
    (∑ i, (2*(rowCount D i : ℤ)-(n : ℤ)))=2*D.card-(m : ℤ)*n := by
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Nat.cast_sum,sum_rowCount]
  simp

/-- The odd-width profile bound is extracted from actual row selections. -/
theorem odd_width_bound (hn : n%2=1) (D : Finset (Fin m × Fin n))
    (hD : IsKIndependent (graph m n) 2 D) : D.card ≤ formula m n := by
  let a : Fin m → ℤ := fun i => 2*(rowCount D i : ℤ)-n
  have ha : GridProfile.Compatible a := by
    intro i k hik
    rcases odd_row_pair hn D hD i k hik with h | ⟨hi,hk⟩
    · exact Or.inl (by dsimp [a]; omega)
    · exact Or.inr ⟨by dsimp [a]; omega,by dsimp [a]; omega⟩
  have hA : g n%2=1 := by dsimp [g]; omega
  have hu (i : Fin m) : a i ≤ g n := by
    have hb := row_bound D hD i
    dsimp [a,g]
    omega
  have hs := GridProfile.profile_bound a (g n) hA (fun i => by dsimp [a]; omega)
    hu ha (fun i j k hij hjk => row_profile_three_free hn D hD i j k hij hjk)
  change (∑ i, (2*(rowCount D i : ℤ)-(n : ℤ))) ≤ _ at hs
  rw [profile_sum] at hs
  have hf := twice_formula m n
  have hm : m%2=0 ∨ m%2=1 := by omega
  rcases hm with hm | hm
  · simp only [hm,ite_true] at hs
    simp only [hm,hn,Nat.zero_mul,Nat.one_mul,Nat.zero_max] at hf
    have hg : ((g m : ℕ) : ℤ)=(m : ℤ)-2*(m/3 : ℕ) := by
      dsimp [g]
      rw [Nat.cast_sub (by omega),Nat.cast_mul,Nat.cast_ofNat]
      norm_cast
    rw [← hg] at hs
    have hf' : 2*(formula m n : ℤ)=(m : ℤ)*n+g m := by exact_mod_cast hf
    omega
  · simp only [hm,show ¬ (1 : ℕ)=0 by decide,ite_false] at hs
    simp only [hm,hn,Nat.one_mul] at hf
    have hg : ((g m : ℕ) : ℤ)=(m : ℤ)-2*(m/3 : ℕ) := by
      dsimp [g]
      rw [Nat.cast_sub (by omega),Nat.cast_mul,Nat.cast_ofNat]
      norm_cast
    rw [← hg] at hs
    have hf' : 2*(formula m n : ℤ)=(m : ℤ)*n+max (g n : ℤ) (g m : ℤ) := by
      exact_mod_cast hf
    omega

/-- The complete upper bound includes empty dimensions and every parity case. -/
theorem selection_bound (D : Finset (Fin m × Fin n))
    (hD : IsKIndependent (graph m n) 2 D) : D.card ≤ formula m n := by
  by_cases hn : n%2=1
  · exact odd_width_bound hn D hD
  · have hne : n%2=0 := by omega
    have hb := paired_sum_bound m n (n-n/3) (rowCount D) (row_bound D hD)
      (fun i j hij => even_band_bound hne D hD i j hij)
    rw [sum_rowCount] at hb
    have hf := twice_formula m n
    have hg : g n+2*(n/3)=n := by dsimp [g]; omega
    have hm : 2*(m/2)+m%2=m := by omega
    have he : 2*((m/2)*n+(m%2)*(n-n/3))=m*n+(m%2)*g n := by
      have hh : (n-n/3)+n/3=n := by omega
      have h1 := congrArg (fun x : ℕ => (m/2)*x) (show n-n/3+n/3=n by omega)
      have h2 := congrArg (fun x : ℕ => (m%2)*x) (show 2*(n-n/3)=n+g n by omega)
      have h3 := congrArg (fun x : ℕ => x*n) hm
      nlinarith
    have hmax : (m%2)*g n ≤ max ((m%2)*g n) ((n%2)*g m) := le_max_left _ _
    omega

/-- This bounds the actual canonical finite maximum, not a conditional row count. -/
theorem beta_bound : beta (graph m n) 2 ≤ formula m n := by
  obtain ⟨D,hD,hc⟩ := StarForming.beta_attained (graph m n) 2
  rw [← hc]
  exact selection_bound D hD

/-- Sahbi's actual periodic selection, using zero-based column indices. -/
def chosen (p q : ℕ) : Finset (Fin p × Fin q) :=
  Finset.univ.filter (fun v => if v.1.val%2=0 then v.2.val%3≠2 else v.2.val%3=2)

private theorem chosen_horizontal {x y : Fin m × Fin n}
    (hx : x ∈ chosen m n) (hy : y ∈ chosen m n) (hxy : (graph m n).Adj x y) :
    x.1=y.1 ∧ (SimpleGraph.pathGraph n).Adj x.2 y.2 := by
  rcases hxy with h | ⟨hr,hc⟩
  · exact h
  · have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    have hv := congrArg Fin.val hc
    rcases SimpleGraph.pathGraph_adj.mp hr with hr | hr <;>
      dsimp at hx' hy' hv <;> split_ifs at hx' hy' <;> omega

/-- No selected vertical pair occurs, and no horizontal triple is selected. -/
theorem chosen_dissociation : IsKIndependent (graph m n) 2 (chosen m n) := by
  apply (DoubleStarGrafting.independent_iff (graph m n) (chosen m n)).mpr
  intro v hv x hx y hy hvx hvy
  have h0 := chosen_horizontal hv hx hvx
  have h1 := chosen_horizontal hv hy hvy
  have hp := (Finset.mem_filter.mp hv).2
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  rw [← h0.1] at hx'
  rw [← h1.1] at hy'
  apply Prod.ext (h0.1.symm.trans h1.1)
  apply Fin.ext
  rcases SimpleGraph.pathGraph_adj.mp h0.2 with h0 | h0 <;>
    rcases SimpleGraph.pathGraph_adj.mp h1.2 with h1 | h1 <;>
      split_ifs at hp hx' hy' <;> omega

private theorem count_residue (p : ℕ) :
    (∑ j : Fin p, if j.val%3=2 then (1 : ℕ) else 0)=p/3 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,ih]
    split_ifs <;> omega

private theorem count_other_residues (p : ℕ) :
    (∑ j : Fin p, if j.val%3≠2 then (1 : ℕ) else 0)=p-p/3 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,ih]
    split_ifs <;> omega

private theorem parity_weight_sum (p a b : ℕ) :
    (∑ i : Fin p, if i.val%2=0 then a else b)=((p+1)/2)*a+(p/2)*b := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,ih]
    by_cases hp : p%2=0
    · have h0 : (p+1+1)/2=(p+1)/2+1 := by omega
      have h1 : (p+1)/2=p/2 := by omega
      rw [ite_eq_left hp,h0,h1]
      ring
    · have h0 : (p+1+1)/2=(p+1)/2 := by omega
      have h1 : (p+1)/2=p/2+1 := by omega
      rw [ite_eq_right hp,h0,h1]
      ring

/-- The actual periodic witness has the first exact symbolic count. -/
theorem chosen_card : (chosen m n).card=rowFormula m n := by
  have hr (i : Fin m) : rowCount (chosen m n) i=
      if i.val%2=0 then n-n/3 else n/3 := by
    unfold rowCount row
    simp only [chosen,Finset.mem_filter,Finset.mem_univ,true_and,Finset.card_filter]
    by_cases hi : i.val%2=0
    · simpa only [hi,ite_true] using count_other_residues n
    · simpa only [hi,ite_false] using count_residue n
  rw [← sum_rowCount]
  simp_rw [hr]
  exact parity_weight_sum m (n-n/3) (n/3)

/-- Swapping the coordinates is an isomorphism of the actual grid graphs. -/
def transpose : graph m n ≃g graph n m where
  toEquiv := Equiv.prodComm _ _
  map_rel_iff' := by
    intro x y
    change ((x.2=y.2 ∧ (SimpleGraph.pathGraph m).Adj x.1 y.1) ∨
      ((SimpleGraph.pathGraph n).Adj x.2 y.2 ∧ x.1=y.1)) ↔
      ((x.1=y.1 ∧ (SimpleGraph.pathGraph n).Adj x.2 y.2) ∨
      ((SimpleGraph.pathGraph m).Adj x.1 y.1 ∧ x.2=y.2))
    tauto

/-- Both periodic orientations attain their symbolic counts in the actual finite maximum. -/
theorem formula_le_beta : formula m n ≤ beta (graph m n) 2 := by
  have hfirst (p q : ℕ) : rowFormula p q ≤ beta (graph p q) 2 := by
    rw [← chosen_card]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,chosen_dissociation⟩)
  have hi := (StarForming.Isomorphism.parameters (transpose (m:=m) (n:=n))).1
  have h0 := hfirst m n
  have h1 := hfirst n m
  rw [← hi] at h1
  exact max_le h0 h1

/-- The full all-size dissociation formula, proved without bounded grid enumeration. -/
theorem beta_exact : beta (graph m n) 2=formula m n :=
  le_antisymm beta_bound formula_le_beta

end D5.S3.Combinatorics.Graph.SubQuorum.GridDissociation
