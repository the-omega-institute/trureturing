/- GID: D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Connected twin-free theta graphs with short paths of length three. -/

/-
admission_basis: escape-witness
escape_witness: theta_connected
utility: none (unbounded theta-family statements and their consumed helpers).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23310
Frozen dependency declarations:
D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.distance_certificate @ sha256:2ed868feac517a64060ab1dc1f05d5c4edfaf7f3ee530ce3f1d4d0d67b9d7684
Declaration judgements (definitions carry no independent mathematical claim):
theta_adj | proof_shape: bind-only | escape_witness: none | consumer: da_adj
theta_reachable_zero | proof_shape: content | escape_witness: theta_reachable_zero | consumer: theta_connected
theta_connected | proof_shape: content | escape_witness: theta_reachable_zero | consumer: theta_metric_certificates
theta_no_single_distance | proof_shape: bind-only | escape_witness: none | consumer: theta_resolving_card_lower
theta_twin_free | proof_shape: bind-only | escape_witness: none | consumer: theta_metric_certificates
distance_certificate | proof_shape: bind-only | escape_witness: none | consumer: theta_dist_a
profile_injective | proof_shape: bind-only | escape_witness: none | consumer: theta_resolves
da_large | proof_shape: bind-only | escape_witness: none | consumer: da_descend
dz_large | proof_shape: bind-only | escape_witness: none | consumer: dz_descend
da_zero | proof_shape: bind-only | escape_witness: none | consumer: theta_dist_a
da_adj | proof_shape: bind-only | escape_witness: none | consumer: theta_dist_a
da_descend | proof_shape: bind-only | escape_witness: none | consumer: theta_dist_a
theta_dist_a | proof_shape: content | escape_witness: theta_reachable_zero | consumer: theta_resolves
dz_zero | proof_shape: bind-only | escape_witness: none | consumer: theta_dist_z
dz_adj | proof_shape: bind-only | escape_witness: none | consumer: theta_dist_z
dz_descend | proof_shape: bind-only | escape_witness: none | consumer: theta_dist_z
theta_dist_z | proof_shape: content | escape_witness: theta_reachable_zero | consumer: theta_resolves
theta_resolves | proof_shape: content | escape_witness: theta_reachable_zero | consumer: theta_metric_dimension
theta_resolving_card_lower | proof_shape: bind-only | escape_witness: none | consumer: theta_metric_dimension
theta_metric_dimension | proof_shape: content | escape_witness: theta_reachable_zero | consumer: theta_metric_certificates
theta_metric_certificates | proof_shape: content | escape_witness: theta_reachable_zero | consumer: result
distanceRepresentation | proof_shape: bind-only | escape_witness: none | consumer: ResolvingSet
ResolvingSet | proof_shape: bind-only | escape_witness: none | consumer: metricDimension
metricDimension | proof_shape: bind-only | escape_witness: none | consumer: theta_metric_certificates
Twins | proof_shape: bind-only | escape_witness: none | consumer: TwinFree
TwinFree | proof_shape: bind-only | escape_witness: none | consumer: theta_metric_certificates
multiplicity | proof_shape: bind-only | escape_witness: none | consumer: maximumMultiplicity
maximumMultiplicity | proof_shape: bind-only | escape_witness: none | consumer: mmL
mmL | proof_shape: bind-only | escape_witness: none | consumer: claim
signlessLaplacian | proof_shape: bind-only | escape_witness: none | consumer: mmQ
mmQ | proof_shape: bind-only | escape_witness: none | consumer: claim
thetaEdge | proof_shape: bind-only | escape_witness: none | consumer: theta_adj
thetaGraph | proof_shape: bind-only | escape_witness: none | consumer: theta_adj
da | proof_shape: bind-only | escape_witness: none | consumer: profile_injective
dz | proof_shape: bind-only | escape_witness: none | consumer: profile_injective
downA | proof_shape: bind-only | escape_witness: none | consumer: theta_dist_a
downZ | proof_shape: bind-only | escape_witness: none | consumer: theta_dist_z
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import D5.S3.Combinatorics.Graph.WellCoveredPowerCliqueProduct

set_option maxHeartbeats 800000

namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure

noncomputable section

/-- Shortest-path distances to the elements of the landmark set. -/
def distanceRepresentation {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (v : Fin n) : S → ℕ :=
  fun s => G.dist v s.val

/-- Distinct vertices have distinct distance representations. -/
def ResolvingSet {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v : Fin n, distanceRepresentation G S u = distanceRepresentation G S v → u = v

/-- The minimum cardinality of a resolving set; used on connected graphs. -/
def metricDimension {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset (Fin n), ResolvingSet G S ∧ S.card = m}

/-- The source excludes both adjacent and nonadjacent twins. -/
def Twins {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : Prop :=
  u ≠ v ∧ G.neighborSet u \ {v} = G.neighborSet v \ {u}

def TwinFree {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v : Fin n, ¬ Twins G u v

/-- Geometric multiplicity over the reals, as in the source. -/
def multiplicity {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (lambda : ℝ) : ℕ :=
  Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' M) lambda)

/-- Maximum multiplicity over all eigenvalues, not multiplicity at the largest eigenvalue. -/
def maximumMultiplicity {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  sSup {m : ℕ | ∃ lambda : ℝ,
    Module.End.HasEigenvalue (Matrix.toLin' M) lambda ∧ m = multiplicity M lambda}

def mmL {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact maximumMultiplicity (G.lapMatrix ℝ)

/-- The signless Laplacian is the sum of the degree and adjacency matrices. -/
def signlessLaplacian {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact G.degMatrix ℝ + G.adjMatrix ℝ

def mmQ {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  maximumMultiplicity (signlessLaplacian G)

end

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure

namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure

/-- Labels 0,1 are the terminals; 2,3 and 4,5 are the short paths;
labels 6 through r+4 are the r-1 interior vertices of the long path. -/
def thetaEdge (r x y : ℕ) : Prop :=
  (x=0 ∧ y=2) ∨ (x=2 ∧ y=3) ∨ (x=3 ∧ y=1) ∨
  (x=0 ∧ y=4) ∨ (x=4 ∧ y=5) ∨ (x=5 ∧ y=1) ∨
  (x=0 ∧ y=6) ∨ (x=r+4 ∧ y=1) ∨
  (6 ≤ x ∧ y=x+1)

def thetaGraph (r : ℕ) (hr : 2 ≤ r) : SimpleGraph (Fin (r+5)) where
  Adj x y := thetaEdge r x.val y.val ∨ thetaEdge r y.val x.val
  symm := ⟨by intro x y h; exact h.symm⟩
  loopless := ⟨by intro x; simp only [thetaEdge]; omega⟩

theorem theta_adj (r : ℕ) (hr : 2 ≤ r) (x y : Fin (r+5)) :
    (thetaGraph r hr).Adj x y ↔ thetaEdge r x.val y.val ∨ thetaEdge r y.val x.val := by exact Eq.to_iff rfl

private theorem theta_reachable_zero (r : ℕ) (hr : 2 ≤ r) (x : Fin (r+5)) :
    (thetaGraph r hr).Reachable x ⟨0, by omega⟩ := by
  have h02 : (thetaGraph r hr).Adj ⟨0,by omega⟩ ⟨2,by omega⟩ := by
    simp [theta_adj,thetaEdge]
  have h23 : (thetaGraph r hr).Adj ⟨2,by omega⟩ ⟨3,by omega⟩ := by
    simp [theta_adj,thetaEdge]
  have h31 : (thetaGraph r hr).Adj ⟨3,by omega⟩ ⟨1,by omega⟩ := by
    simp [theta_adj,thetaEdge]
  have h04 : (thetaGraph r hr).Adj ⟨0,by omega⟩ ⟨4,by omega⟩ := by
    simp [theta_adj,thetaEdge]
  have h45 : (thetaGraph r hr).Adj ⟨4,by omega⟩ ⟨5,by omega⟩ := by
    simp [theta_adj,thetaEdge]
  have h06 : (thetaGraph r hr).Adj ⟨0,by omega⟩ ⟨6,by omega⟩ := by
    simp [theta_adj,thetaEdge]
  have aux : ∀ n (hn : n < r+5),
      (thetaGraph r hr).Reachable ⟨n,hn⟩ ⟨0,by omega⟩ := by
    intro n
    induction n using Nat.strong_induction_on
    case h n ih =>
        intro hn
        by_cases hs : n < 7
        · interval_cases n
          · exact .rfl
          · exact h31.symm.reachable.trans (h23.symm.reachable.trans h02.symm.reachable)
          · exact h02.symm.reachable
          · exact h23.symm.reachable.trans h02.symm.reachable
          · exact h04.symm.reachable
          · exact h45.symm.reachable.trans h04.symm.reachable
          · exact h06.symm.reachable
        · let y : Fin (r+5) := ⟨n-1,by omega⟩
          have hadj : (thetaGraph r hr).Adj ⟨n,hn⟩ y := by
            dsimp [y]
            simp only [theta_adj,thetaEdge]
            omega
          exact hadj.reachable.trans (ih (n-1) (by omega) (by omega))
  exact aux x.val x.isLt

private theorem theta_connected (r : ℕ) (hr : 2 ≤ r) : (thetaGraph r hr).Connected := by
  refine { preconnected := ?_, nonempty := ⟨⟨0, by omega⟩⟩ }
  intro x y
  exact (theta_reachable_zero r hr x).trans (theta_reachable_zero r hr y).symm

private theorem theta_no_single_distance (r : ℕ) (hr : 2 ≤ r)
    (s : Fin (r+5)) : ¬ Function.Injective (fun x => (thetaGraph r hr).dist s x) := by
  intro hinj
  let u : Fin (r+5) := ⟨0,by omega⟩
  let a : Fin (r+5) := ⟨2,by omega⟩
  let c : Fin (r+5) := ⟨4,by omega⟩
  let z : Fin (r+5) := ⟨6,by omega⟩
  have h1 : (thetaGraph r hr).Adj u a := by simp [u,a,theta_adj,thetaEdge]
  have h2 : (thetaGraph r hr).Adj u c := by simp [u,c,theta_adj,thetaEdge]
  have h3 : (thetaGraph r hr).Adj u z := by simp [u,z,theta_adj,thetaEdge]
  have d1 := h1.diff_dist_adj (u:=s)
  have d2 := h2.diff_dist_adj (u:=s)
  have d3 := h3.diff_dist_adj (u:=s)
  have n1 : (thetaGraph r hr).dist s a ≠ (thetaGraph r hr).dist s u := by
    exact hinj.ne (Fin.ne_of_val_ne (by norm_num [a,u]))
  have n2 : (thetaGraph r hr).dist s c ≠ (thetaGraph r hr).dist s u := by
    exact hinj.ne (Fin.ne_of_val_ne (by norm_num [c,u]))
  have n3 : (thetaGraph r hr).dist s z ≠ (thetaGraph r hr).dist s u := by
    exact hinj.ne (Fin.ne_of_val_ne (by norm_num [z,u]))
  have n12 : (thetaGraph r hr).dist s a ≠ (thetaGraph r hr).dist s c := by
    exact hinj.ne (Fin.ne_of_val_ne (by norm_num [a,c]))
  have n13 : (thetaGraph r hr).dist s a ≠ (thetaGraph r hr).dist s z := by
    exact hinj.ne (Fin.ne_of_val_ne (by norm_num [a,z]))
  have n23 : (thetaGraph r hr).dist s c ≠ (thetaGraph r hr).dist s z := by
    exact hinj.ne (Fin.ne_of_val_ne (by norm_num [c,z]))
  omega

set_option maxHeartbeats 1800000 in
private theorem theta_twin_free (r : ℕ) (hr : 10 ≤ r)
    (x y : Fin (r+5)) :
    ¬ (x ≠ y ∧ (thetaGraph r (by omega)).neighborSet x \ {y} =
      (thetaGraph r (by omega)).neighborSet y \ {x}) := by
  rintro ⟨hne,ht⟩
  have hx := x.isLt
  have hy := y.isLt
  have hneval : x.val ≠ y.val := by exact Fin.val_ne_of_ne hne
  have H (w : ℕ) (hw : w<r+5) :
      ((thetaEdge r x.val w ∨ thetaEdge r w x.val) ∧ w ≠ y.val) ↔
      ((thetaEdge r y.val w ∨ thetaEdge r w y.val) ∧ w ≠ x.val) := by
    simpa only [Set.mem_sdiff,SimpleGraph.mem_neighborSet,Set.mem_singleton_iff,
      Fin.ext_iff,theta_adj] using Set.ext_iff.mp ht (⟨w,hw⟩ : Fin (r+5))
  have small_large (u v : ℕ) (hu : u<6) (hv : 6≤v)
      (hh : ∀ (w : ℕ) (_hw : w<r+5),
        ((thetaEdge r u w ∨ thetaEdge r w u) ∧ w ≠ v) ↔
        ((thetaEdge r v w ∨ thetaEdge r w v) ∧ w ≠ u)) : False := by
    interval_cases u
    · have h := (hh 2 (by omega)).mp ⟨by simp [thetaEdge], by omega⟩
      dsimp [thetaEdge] at h
      omega
    · have h := (hh 3 (by omega)).mp ⟨by simp [thetaEdge], by omega⟩
      dsimp [thetaEdge] at h
      omega
    · have h := (hh 3 (by omega)).mp ⟨by simp [thetaEdge], by omega⟩
      dsimp [thetaEdge] at h
      omega
    · have h := (hh 2 (by omega)).mp ⟨by simp [thetaEdge], by omega⟩
      dsimp [thetaEdge] at h
      omega
    · have h := (hh 5 (by omega)).mp ⟨by simp [thetaEdge], by omega⟩
      dsimp [thetaEdge] at h
      omega
    · have h := (hh 4 (by omega)).mp ⟨by simp [thetaEdge], by omega⟩
      dsimp [thetaEdge] at h
      omega
  by_cases hxs : x.val < 6
  · by_cases hys : y.val < 6
    · interval_cases hxv : x.val
      · interval_cases hyv : y.val
        · omega
        · have h := H 2 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 3 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 1 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 2 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 1 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
      · interval_cases hyv : y.val
        · have h := H 2 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · omega
        · have h := H 0 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 2 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 0 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 3 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
      · interval_cases hyv : y.val
        · have h := H 3 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 0 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · omega
        · have h := H 0 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 3 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 0 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
      · interval_cases hyv : y.val
        · have h := H 1 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 2 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 0 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · omega
        · have h := H 0 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 2 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
      · interval_cases hyv : y.val
        · have h := H 2 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 0 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 3 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 0 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · omega
        · have h := H 0 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
      · interval_cases hyv : y.val
        · have h := H 1 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 3 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 0 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 2 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · have h := H 0 (by omega)
          norm_num [hxv,hyv,thetaEdge] at h <;> omega
        · omega
    · exact small_large x.val y.val hxs (by omega) H
  · by_cases hys : y.val < 6
    · exact small_large y.val x.val hys (by omega) (fun w hw => (H w hw).symm)
    · by_cases hx6 : x.val=6
      · have h := (H 0 (by omega)).mp
          ⟨by simp [thetaEdge,hx6], by omega⟩
        dsimp [thetaEdge] at h
        omega
      by_cases hxl : x.val=r+4
      · have h := (H 1 (by omega)).mp
          ⟨by simp [thetaEdge,hxl], by omega⟩
        dsimp [thetaEdge] at h
        omega
      have hym : y.val ≤ x.val-1 := by
        by_cases heq : y.val=x.val-1
        · omega
        · have h := (H (x.val-1) (by omega)).mp
            ⟨by
              right
              simp only [thetaEdge]
              repeat' right
              exact ⟨by omega, by omega⟩, by omega⟩
          dsimp [thetaEdge] at h
          omega
      have h := (H (x.val+1) (by omega)).mp
        ⟨by
          left
          simp only [thetaEdge]
          repeat' right
          exact ⟨by omega, True.intro⟩, by omega⟩
      dsimp [thetaEdge] at h
      omega

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure


namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure

/-- A nonnegative integer labelling with legal one-step descent is the
shortest-path distance when every graph edge changes it by at most one. -/
private theorem distance_certificate {V : Type*} (G : SimpleGraph V)
    (hc : G.Connected) (s : V) (d : V → ℕ) (hz : ∀ x, d x = 0 ↔ x=s)
    (hedge : ∀ x y, G.Adj x y → d x ≤ d y + 1)
    (hdown : ∀ x, 0 < d x → ∃ y, G.Adj x y ∧ d y + 1 = d x)
    (x : V) : G.dist x s = d x := by
  classical
  letI : Nonempty V := hc.nonempty
  let m : V → V → ℕ := fun u v => if v=s then d u else G.dist u v
  have H := WellCoveredPowerCliqueProduct.distance_certificate G m
    (by
      intro u v
      by_cases hv : v=s
      · subst v; simpa [m] using hz u
      · simpa [m,hv] using (hc.dist_eq_zero_iff (u:=u) (v:=v)))
    (by
      intro u v w huv
      by_cases hw : w=s
      · simpa [m,hw] using hedge u v huv
      · have ht := hc.dist_triangle (u:=u) (v:=v) (w:=w)
        have he := SimpleGraph.dist_eq_one_iff_adj.mpr huv
        simpa [m,hw,he,Nat.add_comm] using ht)
    (by
      intro u v huv
      by_cases hv : v=s
      · subst v
        have hd : 0 < d u := by simpa [m] using Nat.pos_of_ne_zero huv
        obtain ⟨w,he,hd⟩ := hdown u hd
        exact ⟨w,he,by simpa [m] using hd⟩
      · obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
        cases p with
        | nil => simp_all [m]
        | @cons u w v he p =>
            refine ⟨w,he,?_⟩
            simp only [m,if_neg hv]
            have hl := G.dist_le p
            have ht := hc.dist_triangle (u:=u) (v:=w) (w:=v)
            have he1 := SimpleGraph.dist_eq_one_iff_adj.mpr he
            simp only [SimpleGraph.Walk.length_cons] at hp
            omega)
  simpa [m] using H.2 x s

/-- The proposed resolving-pair profiles in arithmetic labels. -/
private def da (r x : ℕ) : ℕ :=
  if x=0 then 1 else if x=1 then 2 else if x=2 then 0 else
  if x=3 then 1 else if x=4 then 2 else if x=5 then 3 else
  min (x-4) (r+7-x)

private def dz (r x : ℕ) : ℕ :=
  if x=0 then 1 else if x=1 then 4 else if x=2 then 2 else
  if x=3 then 3 else if x=4 then 2 else if x=5 then 3 else
  min (x-6) (r+9-x)

private theorem profile_injective (r : ℕ) (hr : 10 ≤ r)
    (x y : Fin (r+5))
    (ha : da r x.val = da r y.val) (hz : dz r x.val = dz r y.val) : x=y := by
  apply Fin.ext
  have hx := x.isLt
  have hy := y.isLt
  dsimp [da,dz] at ha hz
  split_ifs at ha hz <;> omega

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure

namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure

private def downA (r x : ℕ) : ℕ :=
  if x=0 then 2 else if x=1 then 3 else if x=2 then 2 else
  if x=3 then 2 else if x=4 then 0 else if x=5 then 4 else
  if x-4 ≤ r+7-x then (if x=6 then 0 else x-1)
  else (if x=r+4 then 1 else x+1)

private def downZ (r x : ℕ) : ℕ :=
  if x=0 then 6 else if x=1 then 3 else if x=2 then 0 else
  if x=3 then 2 else if x=4 then 0 else if x=5 then 4 else
  if x-6 ≤ r+9-x then x-1 else (if x=r+4 then 1 else x+1)

private theorem da_large (r x : ℕ) (hx : 6 ≤ x) :
    da r x = min (x-4) (r+7-x) := by
  simp [da,show x≠0 by omega,show x≠1 by omega,show x≠2 by omega,show x≠3 by omega,show x≠4 by omega,show x≠5 by omega]

private theorem dz_large (r x : ℕ) (hx : 6 ≤ x) :
    dz r x = min (x-6) (r+9-x) := by
  simp [dz,show x≠0 by omega,show x≠1 by omega,show x≠2 by omega,show x≠3 by omega,show x≠4 by omega,show x≠5 by omega]

private theorem da_zero (r : ℕ) (hr : 10 ≤ r) (x : Fin (r+5)) :
    da r x.val = 0 ↔ x = ⟨2,by omega⟩ := by
  have hx := x.isLt
  rw [Fin.ext_iff]
  change da r x.val=0 ↔ x.val=2
  constructor
  · intro h0
    dsimp [da] at h0
    split_ifs at h0 <;> omega
  · intro h0
    rw [h0]
    simp [da]

private theorem da_adj (r : ℕ) (hr : 10 ≤ r) (x y : Fin (r+5))
    (h : (thetaGraph r (by omega)).Adj x y) : da r x.val ≤ da r y.val + 1 := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [theta_adj,thetaEdge] at h
  dsimp [da]
  split_ifs <;> omega

private theorem da_descend (r x : ℕ) (hr : 10 ≤ r) (hx : x < r+5)
    (hpos : 0 < da r x) :
    downA r x < r+5 ∧
    (thetaEdge r x (downA r x) ∨ thetaEdge r (downA r x) x) ∧
    da r (downA r x) + 1 = da r x := by
  by_cases hs : x<6
  · interval_cases x <;> norm_num [downA,da,thetaEdge] at * <;> omega
  have hx6 : 6≤x := by exact Nat.le_of_not_lt hs
  by_cases he : x=6
  · subst x
    have hc : 6-4 ≤ r+7-6 := by omega
    have hd : downA r 6=0 := by simp [show r≠0 by omega,show r≠2 by omega,show ¬r≤3 by omega,downA,hc]
    rw [hd]
    refine ⟨by omega,by simp [thetaEdge],?_⟩
    rw [da_large r 6 (by omega)]
    norm_num [da]
    omega
  by_cases hl : x=r+4
  · subst x
    have hc : ¬((r+4)-4 ≤ r+7-(r+4)) := by omega
    have hd : downA r (r+4)=1 := by simp [show r≠0 by omega,show r≠2 by omega,show ¬r≤3 by omega,downA,show r+4≠0 by omega,show r+4≠1 by omega,show r+4≠2 by omega,show r+4≠3 by omega,show r+4≠4 by omega,show r+4≠5 by omega,hc]
    rw [hd]
    refine ⟨by omega,by simp [thetaEdge],?_⟩
    rw [da_large r (r+4) (by omega)]
    norm_num [da]
    omega
  by_cases hcmp : x-4 ≤ r+7-x
  · have hd : downA r x=x-1 := by simp [show r≠0 by omega,show r≠2 by omega,show ¬r≤3 by omega,downA,show x≠0 by omega,show x≠1 by omega,show x≠2 by omega,show x≠3 by omega,show x≠4 by omega,show x≠5 by omega,hcmp,he]
    rw [hd]
    refine ⟨by omega,?_,?_⟩
    · right
      unfold thetaEdge
      right; right; right; right; right; right; right; right
      exact ⟨by omega,by omega⟩
    · rw [da_large r (x-1) (by omega),da_large r x hx6]
      omega
  · have hd : downA r x=x+1 := by simp [show r≠0 by omega,show r≠2 by omega,show ¬r≤3 by omega,downA,show x≠0 by omega,show x≠1 by omega,show x≠2 by omega,show x≠3 by omega,show x≠4 by omega,show x≠5 by omega,hcmp,hl]
    rw [hd]
    refine ⟨by omega,?_,?_⟩
    · left
      unfold thetaEdge
      right; right; right; right; right; right; right; right
      exact ⟨by omega,rfl⟩
    · rw [da_large r (x+1) (by omega),da_large r x hx6]
      omega

private theorem theta_dist_a (r : ℕ) (hr : 10 ≤ r) (x : Fin (r+5)) :
    (thetaGraph r (by omega)).dist x ⟨2,by omega⟩ = da r x.val := by
  apply distance_certificate (thetaGraph r (by omega)) (theta_connected r (by omega)) _ (fun v => da r v.val)
  · exact da_zero r hr
  · exact fun u v h => da_adj r hr u v h
  · intro v hv
    obtain ⟨hb,he,hd⟩ := da_descend r v.val hr v.isLt hv
    exact ⟨⟨downA r v.val,hb⟩,he,hd⟩

private theorem dz_zero (r : ℕ) (hr : 10 ≤ r) (x : Fin (r+5)) :
    dz r x.val = 0 ↔ x = ⟨6,by omega⟩ := by
  have hx := x.isLt
  rw [Fin.ext_iff]
  change dz r x.val=0 ↔ x.val=6
  constructor
  · intro h0
    dsimp [dz] at h0
    split_ifs at h0 <;> omega
  · intro h0
    rw [h0]
    simp [dz]

private theorem dz_adj (r : ℕ) (hr : 10 ≤ r) (x y : Fin (r+5))
    (h : (thetaGraph r (by omega)).Adj x y) : dz r x.val ≤ dz r y.val + 1 := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [theta_adj,thetaEdge] at h
  dsimp [dz]
  split_ifs <;> omega

private theorem dz_descend (r x : ℕ) (hr : 10 ≤ r) (hx : x < r+5)
    (hpos : 0 < dz r x) :
    downZ r x < r+5 ∧
    (thetaEdge r x (downZ r x) ∨ thetaEdge r (downZ r x) x) ∧
    dz r (downZ r x) + 1 = dz r x := by
  by_cases hs : x<6
  · interval_cases x <;> norm_num [downZ,dz,thetaEdge] at * <;> omega
  have hx6 : 6≤x := by exact Nat.le_of_not_lt hs
  by_cases he : x=6
  · subst x
    have hz : dz r 6=0 := by exact Nat.eq_zero_of_add_eq_zero_left rfl
    rw [hz] at hpos
    omega
  by_cases hl : x=r+4
  · subst x
    have hc : ¬((r+4)-6 ≤ r+9-(r+4)) := by omega
    have hd : downZ r (r+4)=1 := by simp [show r≠0 by omega,show ¬r≤7 by omega,downZ,show r+4≠0 by omega,show r+4≠1 by omega,show r+4≠2 by omega,show r+4≠3 by omega,show r+4≠4 by omega,show r+4≠5 by omega,hc]
    rw [hd]
    refine ⟨by omega,by simp [thetaEdge],?_⟩
    rw [dz_large r (r+4) (by omega)]
    norm_num [dz]
    omega
  by_cases hcmp : x-6 ≤ r+9-x
  · have hd : downZ r x=x-1 := by simp [show r≠0 by omega,show ¬r≤7 by omega,downZ,show x≠0 by omega,show x≠1 by omega,show x≠2 by omega,show x≠3 by omega,show x≠4 by omega,show x≠5 by omega,hcmp,he]
    rw [hd]
    refine ⟨by omega,?_,?_⟩
    · right
      unfold thetaEdge
      right; right; right; right; right; right; right; right
      exact ⟨by omega,by omega⟩
    · rw [dz_large r (x-1) (by omega),dz_large r x hx6]
      omega
  · have hd : downZ r x=x+1 := by simp [show r≠0 by omega,show ¬r≤7 by omega,downZ,show x≠0 by omega,show x≠1 by omega,show x≠2 by omega,show x≠3 by omega,show x≠4 by omega,show x≠5 by omega,hcmp,hl]
    rw [hd]
    refine ⟨by omega,?_,?_⟩
    · left
      unfold thetaEdge
      right; right; right; right; right; right; right; right
      exact ⟨by omega,rfl⟩
    · rw [dz_large r (x+1) (by omega),dz_large r x hx6]
      omega

private theorem theta_dist_z (r : ℕ) (hr : 10 ≤ r) (x : Fin (r+5)) :
    (thetaGraph r (by omega)).dist x ⟨6,by omega⟩ = dz r x.val := by
  apply distance_certificate (thetaGraph r (by omega)) (theta_connected r (by omega)) _ (fun v => dz r v.val)
  · exact dz_zero r hr
  · exact fun u v h => dz_adj r hr u v h
  · intro v hv
    obtain ⟨hb,he,hd⟩ := dz_descend r v.val hr v.isLt hv
    exact ⟨⟨downZ r v.val,hb⟩,he,hd⟩

private theorem theta_resolves (r : ℕ) (hr : 10 ≤ r) :
    ResolvingSet (thetaGraph r (by omega))
      {⟨2,by omega⟩,⟨6,by omega⟩} := by
  classical
  intro x y h
  have ha := congrFun h ⟨⟨2,by omega⟩,by simp⟩
  have hz := congrFun h ⟨⟨6,by omega⟩,by simp⟩
  simp only [distanceRepresentation,theta_dist_a r hr] at ha
  simp only [distanceRepresentation,theta_dist_z r hr] at hz
  exact profile_injective r hr x y ha hz

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure
namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure

private theorem theta_resolving_card_lower (r : ℕ) (hr : 10 ≤ r)
    (S : Finset (Fin (r+5))) (hS : ResolvingSet (thetaGraph r (by omega)) S) :
    2 ≤ S.card := by
  classical
  by_contra hsmall
  have hcases : S.card=0 ∨ S.card=1 := by omega
  rcases hcases with hempty | hone
  · have he : S=∅ := Finset.card_eq_zero.mp hempty
    subst S
    have hc : (⟨0,by omega⟩ : Fin (r+5)) = ⟨1,by omega⟩ := by
      apply hS
      funext s
      exact False.elim (Finset.notMem_empty s.val s.property)
    have := congrArg Fin.val hc
    norm_num at this
  · obtain ⟨s,hs⟩ := Finset.card_eq_one.mp hone
    subst S
    apply theta_no_single_distance r (by omega) s
    intro x y hxy
    apply hS
    funext z
    have hz : z.val = s := Finset.mem_singleton.mp z.property
    change (thetaGraph r (by omega)).dist x z.val = (thetaGraph r (by omega)).dist y z.val
    rw [hz]
    exact (thetaGraph r (by omega)).dist_comm.trans
      (hxy.trans (thetaGraph r (by omega)).dist_comm)

private theorem theta_metric_dimension (r : ℕ) (hr : 10 ≤ r) :
    metricDimension (thetaGraph r (by omega)) = 2 := by
  classical
  let S : Finset (Fin (r+5)) := {⟨2,by omega⟩,⟨6,by omega⟩}
  have hS : ResolvingSet (thetaGraph r (by omega)) S := theta_resolves r hr
  have hcard : S.card = 2 := by exact Eq.symm (Nat.eq_of_beq_eq_true rfl)
  apply Nat.le_antisymm
  · exact Nat.sInf_le ⟨S,hS,hcard⟩
  · have hnon : {m : ℕ | ∃ S : Finset (Fin (r+5)),
        ResolvingSet (thetaGraph r (by omega)) S ∧ S.card=m}.Nonempty :=
      ⟨2,S,hS,hcard⟩
    obtain ⟨T,hT,hc⟩ := Nat.sInf_mem hnon
    have hl := theta_resolving_card_lower r hr T hT
    change 2 ≤ sInf _
    omega

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure

namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure

theorem theta_metric_certificates (k : ℕ) (hk : 1 ≤ k) :
    (thetaGraph (6*k+4) (by omega)).Connected ∧
    TwinFree (thetaGraph (6*k+4) (by omega)) ∧
    metricDimension (thetaGraph (6*k+4) (by omega)) = 2 :=
  ⟨theta_connected _ (by omega), theta_twin_free _ (by omega),
    theta_metric_dimension _ (by omega)⟩

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure
