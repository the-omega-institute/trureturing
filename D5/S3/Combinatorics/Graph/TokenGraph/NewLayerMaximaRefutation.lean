/- GID: D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.claim; result=D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.result; claim=D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.claim
   digest: Connected K1,3 refutes successive new Laplacian layer maxima monotonicity. -/

/-
proof_shape: all new theorems are bind-only; finite exact matrix identities,
complete-basis spectral identities, cardinal inequalities and multiset normalization.
escape_witness: none
admission_basis: open-problem-resolution (#23401, whole Conjecture 3.3 negation).
The designated result is the only new public theorem. Every private helper is
consumed by rho or result. The result is exempt from four-slot registration.
Direct frozen dependency: D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation,
statement_id sha256:9e929bc48169d56237071f7c9432d44bf6851b133bd4b0d7a715eaaded146144.
-/

import D5.S3.Combinatorics.Graph.TokenGraphLaplacianRadiusRefutation

/-! # Successive new Laplacian layers of token graphs

The actual connected star on four vertices violates Conjecture 3.3.
-/

set_option autoImplicit false

open Matrix Finset Polynomial
open D5.S3.Combinatorics.Graph.TokenGraphLaplacianRadiusRefutation (tokenGraph)

namespace D5.S3.Combinatorics.Graph.TokenGraph.NewLayerMaximaRefutation

/-- The entire ordinary real Laplacian spectrum, with algebraic multiplicities. -/
noncomputable def spectrum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Multiset ℝ :=
  Multiset.map (G.isHermitian_lapMatrix ℝ).eigenvalues Finset.univ.val

/-- Consecutive MULTISET subtraction, before taking any maximum. -/
noncomputable def layer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) : Multiset ℝ := by
  classical
  exact spectrum (tokenGraph G k) - spectrum (tokenGraph G (k - 1))

private lemma spectrum_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (spectrum G).card = Fintype.card V := by
  simp [spectrum]

private lemma layer_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n / 2) : (layer G k).toFinset.Nonempty := by
  classical
  apply Multiset.toFinset_nonempty.mpr
  intro hz
  have hs : spectrum (tokenGraph G k) ≤ spectrum (tokenGraph G (k - 1)) :=
    tsub_eq_zero_iff_le.mp hz
  have hc := Multiset.card_le_card hs
  simp only [spectrum_card] at hc
  have card_tokens (j : ℕ) : Fintype.card (Set.powersetCard (Fin n) j) = n.choose j := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      (Set.powersetCard.card (α := Fin n) (n := j))
  rw [card_tokens, card_tokens] at hc
  have he := Nat.choose_succ_right_eq n (k - 1)
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at he
  have hp : 0 < n.choose (k - 1) := Nat.choose_pos (by omega)
  have hlt : k < n - (k - 1) := by omega
  have hm := Nat.mul_lt_mul_of_pos_left hlt hp
  rw [← he] at hm
  have hn : n.choose (k - 1) < n.choose k := (Nat.mul_lt_mul_right (by omega)).mp hm
  omega

/-- Definition 3.1 on its whole source-admissible nonempty domain. -/
noncomputable def rho {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n / 2) : ℝ := by
  classical
  exact (layer G k).toFinset.max' (layer_nonempty G k hk hkn)

/-- The whole successive-comparison form of Conjecture 3.3, with no order cap. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    ∀ (k : ℕ) (hk : 1 ≤ k) (hkn : k < n / 2),
      rho G k hk (Nat.le_of_lt hkn) ≤
        rho G (k + 1) (by omega) (by omega)

private def connectedStar : {G : SimpleGraph (Fin 4) // G.Connected} :=
  ⟨SimpleGraph.starGraph 0, SimpleGraph.connected_starGraph 0⟩

private abbrev star := connectedStar.val

private instance : DecidableRel star.Adj := by
  change DecidableRel (SimpleGraph.starGraph (0 : Fin 4)).Adj
  infer_instance

private def subsets0 : Fin 1 → Set.powersetCard (Fin 4) 0 :=
  ![⟨∅, by change (∅ : Finset (Fin 4)).card = 0; decide⟩]

private def subsets1 : Fin 4 → Set.powersetCard (Fin 4) 1 :=
  ![⟨{0}, by change ({0} : Finset (Fin 4)).card = 1; decide⟩,
    ⟨{1}, by change ({1} : Finset (Fin 4)).card = 1; decide⟩,
    ⟨{2}, by change ({2} : Finset (Fin 4)).card = 1; decide⟩,
    ⟨{3}, by change ({3} : Finset (Fin 4)).card = 1; decide⟩]

/-- The actual two-subsets in six-cycle order 01,12,02,23,03,13. -/
private def subsets2 : Fin 6 → Set.powersetCard (Fin 4) 2 :=
  ![⟨{0,1}, by change ({0,1} : Finset (Fin 4)).card = 2; decide⟩,
    ⟨{1,2}, by change ({1,2} : Finset (Fin 4)).card = 2; decide⟩,
    ⟨{0,2}, by change ({0,2} : Finset (Fin 4)).card = 2; decide⟩,
    ⟨{2,3}, by change ({2,3} : Finset (Fin 4)).card = 2; decide⟩,
    ⟨{0,3}, by change ({0,3} : Finset (Fin 4)).card = 2; decide⟩,
    ⟨{1,3}, by change ({1,3} : Finset (Fin 4)).card = 2; decide⟩]

private noncomputable def e0 : Fin 1 ≃ Set.powersetCard (Fin 4) 0 :=
  Equiv.ofBijective subsets0 (by
    let : Fintype (Set.powersetCard (Fin 4) 0) :=
      inferInstanceAs (Fintype {s : Finset (Fin 4) // s.card = 0})
    decide)
private noncomputable def e1 : Fin 4 ≃ Set.powersetCard (Fin 4) 1 :=
  Equiv.ofBijective subsets1 (by
    let : Fintype (Set.powersetCard (Fin 4) 1) :=
      inferInstanceAs (Fintype {s : Finset (Fin 4) // s.card = 1})
    decide)
private noncomputable def e2 : Fin 6 ≃ Set.powersetCard (Fin 4) 2 :=
  Equiv.ofBijective subsets2 (by
    let : Fintype (Set.powersetCard (Fin 4) 2) :=
      inferInstanceAs (Fintype {s : Finset (Fin 4) // s.card = 2})
    decide)

private def L0 : Matrix (Fin 1) (Fin 1) ℤ := 0
private def L1 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![3,-1,-1,-1; -1,1,0,0; -1,0,1,0; -1,0,0,1]
private def L2 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2,-1,0,0,0,-1; -1,2,-1,0,0,0; 0,-1,2,-1,0,0;
     0,0,-1,2,-1,0; 0,0,0,-1,2,-1; -1,0,0,0,-1,2]

private lemma actual_lap0 : Matrix.reindex e0.symm e0.symm
    ((tokenGraph star 0).lapMatrix ℤ) = L0 := by
  let ft : Fintype (Set.powersetCard (Fin 4) 0) :=
    inferInstanceAs (Fintype {s : Finset (Fin 4) // s.card = 0})
  have hf : Set.powersetCard.instFintypeElemFinset (Fin 4) 0 = ft :=
    Subsingleton.elim _ _
  rw [hf]
  decide
private lemma actual_lap1 : Matrix.reindex e1.symm e1.symm
    ((tokenGraph star 1).lapMatrix ℤ) = L1 := by
  let ft : Fintype (Set.powersetCard (Fin 4) 1) :=
    inferInstanceAs (Fintype {s : Finset (Fin 4) // s.card = 1})
  have hf : Set.powersetCard.instFintypeElemFinset (Fin 4) 1 = ft :=
    Subsingleton.elim _ _
  rw [hf]
  decide
private lemma actual_lap2 : Matrix.reindex e2.symm e2.symm
    ((tokenGraph star 2).lapMatrix ℤ) = L2 := by
  let ft : Fintype (Set.powersetCard (Fin 4) 2) :=
    inferInstanceAs (Fintype {s : Finset (Fin 4) // s.card = 2})
  have hf : Set.powersetCard.instFintypeElemFinset (Fin 4) 2 = ft :=
    Subsingleton.elim _ _
  rw [hf]
  decide

private lemma spectrum_from_basis {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ} (e : Fin m ≃ V)
    (M : Matrix (Fin m) (Fin m) ℤ) (d : Fin m → ℝ)
    (hl : Matrix.reindex e.symm e.symm (G.lapMatrix ℤ) = M)
    (hc : (M.map (Int.castRingHom ℝ)).charpoly = ∏ i, (X - C (d i))) :
    spectrum G = Multiset.map d Finset.univ.val := by
  classical
  have hcast : G.lapMatrix ℝ = (G.lapMatrix ℤ).map (Int.castRingHom ℝ) := by
    ext s t
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      Matrix.sub_apply, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hre : Matrix.reindex e.symm e.symm (G.lapMatrix ℝ) =
      M.map (Int.castRingHom ℝ) := by
    ext i j
    have h := congrArg (fun A => (A : Matrix (Fin m) (Fin m) ℤ) i j) hl
    change G.lapMatrix ℤ (e i) (e j) = M i j at h
    change G.lapMatrix ℝ (e i) (e j) = (Int.castRingHom ℝ) (M i j)
    rw [hcast]
    exact congrArg (Int.castRingHom ℝ) h
  have hchar := Matrix.charpoly_reindex e.symm (G.lapMatrix ℝ)
  rw [hre, hc] at hchar
  have hr := (G.isHermitian_lapMatrix ℝ).roots_charpoly_eq_eigenvalues
  rw [← hchar, Polynomial.roots_prod] at hr
  · simpa [spectrum] using hr.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

private lemma charpoly_from_basis {m : ℕ} (M P Q : Matrix (Fin m) (Fin m) ℝ)
    (d : Fin m → ℝ) (hqp : Q * P = 1) (he : M * P = P * Matrix.diagonal d) :
    M.charpoly = ∏ i, (X - C (d i)) := by
  have hpq : P * Q = 1 := mul_eq_one_comm.mp hqp
  have hsim : M = (P * Matrix.diagonal d) * Q := by
    rw [← he, Matrix.mul_assoc, hpq, Matrix.mul_one]
  rw [hsim, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hqp,
    Matrix.one_mul, Matrix.charpoly_diagonal]

private lemma spectrum0 : spectrum (tokenGraph star 0) = {0} := by
  have hc : (L0.map (Int.castRingHom ℝ)).charpoly =
      ∏ i : Fin 1, (X - C ((![(0 : ℝ)]) i)) := by
    simp [L0]
  have h := spectrum_from_basis (tokenGraph star 0) e0 L0 ![0] actual_lap0 hc
  simpa [Fin.univ_val_map, List.ofFn_succ] using h

private lemma spectrum1 : spectrum (tokenGraph star 1) = {0, 1, 1, 4} := by
  change spectrum (tokenGraph star 1) = (([0, 1, 1, 4] : List ℝ) : Multiset ℝ)
  let P : Matrix (Fin 4) (Fin 4) ℝ :=
    !![1,0,0,3; 1,1,1,-1; 1,-1,1,-1; 1,0,-2,-1]
  let Q : Matrix (Fin 4) (Fin 4) ℝ :=
    !![1/4,1/4,1/4,1/4; 0,1/2,-1/2,0;
       0,1/6,1/6,-1/3; 1/4,-1/12,-1/12,-1/12]
  let d : Fin 4 → ℝ := ![0,1,1,4]
  have hqp : Q * P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, P, Q]
  have he : (L1.map (Int.castRingHom ℝ)) * P = P * Matrix.diagonal d := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, L1, P, d, Matrix.diagonal_apply]
  have h := spectrum_from_basis (tokenGraph star 1) e1 L1 d actual_lap1
    (charpoly_from_basis _ P Q d hqp he)
  simpa [d, Fin.univ_val_map, List.ofFn_succ] using h

private lemma spectrum2 : spectrum (tokenGraph star 2) = {0, 1, 1, 3, 3, 4} := by
  change spectrum (tokenGraph star 2) = (([0, 1, 1, 3, 3, 4] : List ℝ) : Multiset ℝ)
  let P : Matrix (Fin 6) (Fin 6) ℝ :=
    !![1,2,0,2,0,1; 1,1,1,-1,1,-1; 1,-1,1,-1,-1,1;
       1,-2,0,2,0,-1; 1,-1,-1,-1,1,1; 1,1,-1,-1,-1,-1]
  let Q : Matrix (Fin 6) (Fin 6) ℝ :=
    !![1/6,1/6,1/6,1/6,1/6,1/6;
       1/6,1/12,-1/12,-1/6,-1/12,1/12;
       0,1/4,1/4,0,-1/4,-1/4;
       1/6,-1/12,-1/12,1/6,-1/12,-1/12;
       0,1/4,-1/4,0,1/4,-1/4;
       1/6,-1/6,1/6,-1/6,1/6,-1/6]
  let d : Fin 6 → ℝ := ![0,1,1,3,3,4]
  have hqp : Q * P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, P, Q]
  have he : (L2.map (Int.castRingHom ℝ)) * P = P * Matrix.diagonal d := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, L2, P, d, Matrix.diagonal_apply]
  have h := spectrum_from_basis (tokenGraph star 2) e2 L2 d actual_lap2
    (charpoly_from_basis _ P Q d hqp he)
  simpa [d, Fin.univ_val_map, List.ofFn_succ] using h

/-- The connected K₁,₃ refutes the entire original Conjecture 3.3. -/
theorem result : ¬ claim := by
  classical
  have h1 : layer star 1 = {1, 1, 4} := by
    simp [layer, spectrum1, spectrum0]
  have h2 : layer star 2 = {3, 3} := by
    simp [layer, spectrum2, spectrum1]
  have r1 : rho star 1 (by omega) (by omega) = 4 := by
    unfold rho
    apply (Finset.max'_eq_iff _ _ _).mpr
    simp [h1]
  have r2 : rho star 2 (by omega) (by omega) = 3 := by
    unfold rho
    apply (Finset.max'_eq_iff _ _ _).mpr
    simp [h2]
  intro h
  have hc := h 4 star 1 (by omega) (by omega)
  rw [r1, r2] at hc
  norm_num at hc

end D5.S3.Combinatorics.Graph.TokenGraph.NewLayerMaximaRefutation
