/- GID: D5/S3/Quantum/Measurements/CliffordJointMeasurability/McNultyPathRobustness
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/CliffordJointMeasurability/McNultyPathRobustness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All realizations of three path and cycle families share one sharp threshold. -/
/-
proof_shape: result: content
escape_witness: path_dual_operator_certificate and cycle_majorana_parent on the result live path
admission_basis: open-problem-resolution (#13934; Proved)
Direct frozen dependencies: none on the baseline; supporting lane modules are first-freeze dependencies.
Information-escape registration is paused under CLAUDE.md section 3.9.
proof_shape: pathDualWeight_sum: bind-only; consumer: path_feasible_upper
proof_shape: path_feasible_upper: bind-only; consumer: odd_path_feasible_upper
proof_shape: JM_subfamily_of_trace_zero: bind-only; consumer: odd_path_feasible_upper
proof_shape: prefix_realization: bind-only; consumer: odd_path_feasible_upper
proof_shape: odd_path_feasible_upper: bind-only; consumer: result
proof_shape: cycle_feasible_upper: bind-only; consumer: result
proof_shape: natMajorana_anticommute: bind-only; consumer: odd_path_JM_threshold
proof_shape: odd_path_JM_threshold: bind-only; consumer: result
proof_shape: even_path_JM_threshold: bind-only; consumer: result
proof_shape: cycle_JM_threshold: bind-only; consumer: result
-/
import D5.S3.Quantum.Measurements.CliffordJointMeasurability.CentralCycleRealizations
import D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordBondParents
namespace D5.S3.Quantum.Measurements.CliffordJointMeasurability.McNultyPathRobustness
open D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations
open D5.S3.Quantum.Measurements.CliffordJointMeasurability.CentralCycleRealizations
open D5.S3.Quantum.Measurements.CliffordJointMeasurability.ShiftedFourierOperatorCertificate
open D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordBondParents
noncomputable section
noncomputable def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ d : ℕ, ∀ A : Fin (2 * n) → (Matrix (Fin d) (Fin d) ℂ),
      Realization (SimpleGraph.pathGraph (2 * n)) A → IsGreatest {η : ℝ | η ∈ Set.Icc 0 1 ∧ JM A η} (visibility n)) ∧
    (∀ d : ℕ, ∀ A : Fin (2 * n + 1) → (Matrix (Fin d) (Fin d) ℂ),
      Realization (SimpleGraph.pathGraph (2 * n + 1)) A → IsGreatest {η : ℝ | η ∈ Set.Icc 0 1 ∧ JM A η} (visibility n)) ∧
    (∀ d : ℕ, ∀ A : Fin (2 * n + 2) → (Matrix (Fin d) (Fin d) ℂ),
      Realization (SimpleGraph.cycleGraph (2 * n + 2)) A → IsGreatest {η : ℝ | η ∈ Set.Icc 0 1 ∧ JM A η} (visibility n))
end
noncomputable section
private lemma pathDualWeight_sum (n : ℕ) :
    (∑ k : Fin (2*n), pathDualWeight n k)=((n+1:ℕ):ℝ)*Real.cos (theta (n+1)) := by
  simp_rw [pathDualWeight,pathWeight_sine]
  have he : theta (n+1)=Real.pi/((2*n+2:ℕ):ℝ) := by unfold theta; push_cast; ring
  rw [he]
  have hh := sine_weights_path_sum (2*n)
  dsimp only at hh
  have hratio : ((2*n+2:ℕ):ℝ)/2=((n+1:ℕ):ℝ) := by push_cast; ring
  rw [hratio] at hh
  rw [← hh]
  change (∑ k : Fin (2*n), (fun k : ℕ => Real.sin (((k:ℝ)+1)*(Real.pi/((2*n+2:ℕ):ℝ)))*
    Real.sin (((k:ℝ)+1+1)*(Real.pi/((2*n+2:ℕ):ℝ)))) k)=_
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => Real.sin (((k:ℝ)+1)*(Real.pi/((2*n+2:ℕ):ℝ)))*
    Real.sin (((k:ℝ)+1+1)*(Real.pi/((2*n+2:ℕ):ℝ)))) (2*n)]
  congr 1
  ext k
  congr 2
  ring
private lemma path_feasible_upper {n d : ℕ} (hn : 1 ≤ n)
    (A : Fin (2*n) → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.pathGraph (2*n)) A)
    (t : ℝ) (ht : JM A t) : t ≤ visibility n := by
  have hw := weighted_trace_bound (by have := hR.dimension_pos; omega) A (pathDualWeight n) t
    (Real.cos (theta (n+1))/Real.sin (theta (n+1)))
    (path_realization_trace_zero (by omega) A hR) hR.square ht
    (by intro a; simpa only [Complex.ofReal_div] using path_dual_operator_certificate hn A hR a)
  rw [pathDualWeight_sum] at hw
  exact visibility_upper_of_weighted hn t hw
end
noncomputable section
private lemma JM_subfamily_of_trace_zero {m k d : ℕ} (A : Fin m → (Matrix (Fin d) (Fin d) ℂ))
    (htr : ∀ v, (A v).trace=0) (f : Fin k → Fin m) (t : ℝ) (h : JM A t) :
    JM (fun v => A (f v)) t := by
  obtain ⟨E,hE,hsum,hmarg⟩ := h
  apply labeled_parent_suffices (fun v => A (f v)) t (fun a v => a (f v)) E hE hsum
  intro v
  rw [noisy_eq_of_trace_zero _ (fun v => htr (f v))]
  exact parent_signed_marginal A t htr E hmarg (f v)
private lemma prefix_realization {m k d : ℕ} (hkm : k ≤ m) (G : SimpleGraph (Fin m))
    (A : Fin m → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization G A)
    (hadj : ∀ u v : Fin k, G.Adj (Fin.castLE hkm u) (Fin.castLE hkm v) ↔
      (SimpleGraph.pathGraph k).Adj u v) :
    Realization (SimpleGraph.pathGraph k) (fun v => A (Fin.castLE hkm v)) where
  dimension_pos := hR.dimension_pos
  hermitian v := hR.hermitian _
  square v := hR.square _
  adjacent u v hne ha := hR.adjacent _ _ (by simpa [Fin.ext_iff] using hne) ((hadj u v).mpr ha)
  nonadjacent u v hne ha := hR.nonadjacent _ _ (by simpa [Fin.ext_iff] using hne) (by rwa [hadj])
private lemma odd_path_feasible_upper {n d : ℕ} (hn : 1 ≤ n)
    (A : Fin (2*n+1) → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.pathGraph (2*n+1)) A)
    (t : ℝ) (ht : JM A t) : t ≤ visibility n := by
  let hkm : 2*n ≤ 2*n+1 := by omega
  let f : Fin (2*n) → Fin (2*n+1) := Fin.castLE hkm
  have hres := prefix_realization hkm _ A hR (by
    intro u v; simp only [SimpleGraph.pathGraph_adj,Fin.val_castLE])
  exact path_feasible_upper hn _ hres t (JM_subfamily_of_trace_zero A
    (path_realization_trace_zero (by omega) A hR) f t ht)
private lemma cycle_feasible_upper {n d : ℕ} (hn : 1 ≤ n)
    (A : Fin (2*n+2) → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.cycleGraph (2*n+2)) A)
    (t : ℝ) (ht : JM A t) : t ≤ visibility n := by
  let hkm : 2*n ≤ 2*n+2 := by omega
  let f : Fin (2*n) → Fin (2*n+2) := Fin.castLE hkm
  have hres := prefix_realization hkm _ A hR (by
    intro u v
    rw [natural_cycle_adj (by omega),SimpleGraph.pathGraph_adj]
    simp only [Fin.val_castLE]
    have := u.isLt; have := v.isLt
    omega)
  exact path_feasible_upper hn _ hres t (JM_subfamily_of_trace_zero A
    (cycle_realization_trace_zero (by omega) A hR) f t ht)
end
open  D5.S3.Quantum.FiniteDimensional
open scoped ComplexOrder Kronecker
noncomputable section
private lemma natMajorana_anticommute {R : Type*} [Ring R] (g : ℕ → R) (m : ℕ)
    (ha : ∀ j, j ≤ m → ∀ i, i < j → g i*g j=-(g j*g i)) :
    ∀ k l, k ≤ m → l ≤ m → k ≠ l → g k*g l=-(g l*g k) := by
  intro k l hk hl hkl
  by_cases hlt : k < l
  · exact ha l hl k hlt
  · have h := ha k hk l (by omega)
    simpa using congrArg Neg.neg h.symm
private lemma odd_path_JM_threshold {n d : ℕ} (hn : 1 ≤ n)
    (A : Fin (2*n+1) → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.pathGraph (2*n+1)) A) :
    JM A (visibility n) := by
  classical
  let g := pathMajorana (liftPath (totalPath A)) (liftSeed d)
  have hg := realization_majoranas A hR
  have hanti := natMajorana_anticommute g (2*n+1) hg.2.2.1
  let gf : Fin (2*(n+1)) → (Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) := fun v => g v.val
  let j : Fin (2*n+1) → Fin (2*(n+1)) := fun v => ⟨v.val,by have := v.isLt;omega⟩
  let k : Fin (2*n+1) → Fin (2*(n+1)) := fun v => ⟨v.val+1,by have := v.isLt;omega⟩
  obtain ⟨E,hE,hsum,hsigned⟩ := consecutive_majorana_parent hn gf
    (fun v => hg.1 v.val (by have := v.isLt;omega))
    (fun v => hg.2.1 v.val (by have := v.isLt;omega))
    (by
      intro v w hvw
      exact hanti v.val w.val (by have := v.isLt;omega)
        (by have := w.isLt;omega) (by simpa [Fin.ext_iff] using hvw)) j k (by intro v;rfl)
  apply compressed_parent A (fun v => Complex.I • (gf (j v)*gf (k v))) (visibility n)
    ((qubitV (ι := Fin d))) ((qubitV_isometry (ι := Fin d))) (path_realization_trace_zero (by omega) A hR) _ E hE hsum hsigned
  intro v
  change ((qubitV (ι := Fin d))).conjTranspose*(Complex.I • (g v.val*g (v.val+1)))*(qubitV (ι := Fin d))=A v
  rw [hg.2.2.2 v.val v.isLt]
  simp only [liftPath]
  split_ifs <;> rw [qubitV_compress] <;> simp [totalPath,v.isLt,qubitZ]
private lemma even_path_JM_threshold {n d : ℕ} (hn : 1 ≤ n)
    (A : Fin (2*n) → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.pathGraph (2*n)) A) :
    JM A (visibility n) := by
  classical
  let g := pathMajorana (liftPath (totalPath A)) (liftSeed d)
  have hg := realization_majoranas A hR
  have hanti := natMajorana_anticommute g (2*n) hg.2.2.1
  let pg : Fin (2*(n+1)) → Matrix ((Fin d × Fin 2) × Fin 2) ((Fin d × Fin 2) × Fin 2) ℂ := paddedMajoranas g
  have hp := paddedMajoranas_relations g hg.1 hg.2.1 hanti
  let j : Fin (2*n) → Fin (2*(n+1)) := fun v => ⟨v.val+1,by have := v.isLt;omega⟩
  let k : Fin (2*n) → Fin (2*(n+1)) := fun v => ⟨v.val+2,by have := v.isLt;omega⟩
  obtain ⟨E,hE,hsum,hsigned⟩ := consecutive_majorana_parent hn pg hp.1 hp.2.1 hp.2.2 j k (by intro v;rfl)
  apply compressed_parent A (fun v => Complex.I • (pg (j v)*pg (k v))) (visibility n)
    (padCompression d) (padCompression_isometry d) (path_realization_trace_zero (by omega) A hR) _ E hE hsum hsigned
  intro v
  have hpos : 0 < (j v).val := by simp [j]
  have hnext : (j v).val+1 < 2*n+2 := by have := v.isLt; dsimp [j]; omega
  have he : k v=⟨(j v).val+1,hnext⟩ := by apply Fin.ext;rfl
  rw [he]
  dsimp only [pg]
  rw [paddedMajoranas_bond g (j v) hpos hnext]
  have hidx : (j v).val-1=v.val := by simp [j]
  simp only [hidx,j,Fin.val_mk]
  rw [hg.2.2.2 v.val v.isLt,padCompression_compress]
  simp only [liftPath]
  split_ifs <;> rw [qubitV_compress] <;> simp [totalPath,v.isLt,qubitZ]
end
open  D5.S3.Quantum.FiniteDimensional
open scoped ComplexOrder Kronecker
noncomputable section
private lemma cycle_JM_threshold {n d : ℕ} (hn : 1 ≤ n)
    (A : Fin (2*n+2) → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.cycleGraph (2*n+2)) A) :
    JM A (visibility n) := by
  classical
  let v₀ : Fin (2*n+2) := ⟨2*n+1,by omega⟩
  let K := normalizedLoop n (cyclePrefix A) (A v₀)
  let B : Fin (2*n+2) → (Matrix (Fin d) (Fin d) ℂ) := fun v => if v=v₀ then K*A v else A v
  have hK := realization_cycle_loop hn A hR
  have hKherm : K.IsHermitian := hK.1
  have hKsq : K*K=1 := hK.2.1
  have hKcomm : ∀ v, K*A v=A v*K := hK.2.2.1
  have htrA := cycle_realization_trace_zero (by omega) A hR
  have htrB : ∀ v, (B v).trace=0 := by
    intro v
    dsimp only [B]
    split_ifs with hv
    · subst v
      let u : Fin (2*n+2) := ⟨0,by omega⟩
      have hne : v₀ ≠ u := by simp [v₀,u,Fin.ext_iff]
      have ha : (SimpleGraph.cycleGraph (2*n+2)).Adj v₀ u := by
        rw [natural_cycle_adj (by omega)]
        simp [v₀,u]
      have hab := hR.adjacent v₀ u hne ha
      apply anticommuting_trace_zero (K*A v₀) (A u) (hR.square u)
      calc
        K*A v₀*A u = K*(A v₀*A u) := Matrix.mul_assoc _ _ _
        _ = -(K*(A u*A v₀)) := by rw [hab,Matrix.mul_neg]
        _ = -(A u*(K*A v₀)) := by rw [← Matrix.mul_assoc,hKcomm u,Matrix.mul_assoc]
    · exact htrA v
  let g := pathMajorana (liftPath (cyclePrefix A)) (liftSeed d)
  have hg := cycle_majorana_extension hn A hR
  have hanti := natMajorana_anticommute g (2*n+1) hg.2.2.1
  let gf : Fin (2*(n+1)) → (Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) := fun v => g v.val
  obtain ⟨E,hE,hsum,hsigned⟩ := cycle_majorana_parent hn gf
    (fun v => hg.1 v.val (by have := v.isLt;omega))
    (fun v => hg.2.1 v.val (by have := v.isLt;omega))
    (by
      intro v w hvw
      exact hanti v.val w.val (by have := v.isLt;omega)
        (by have := w.isLt;omega) (by simpa [Fin.ext_iff] using hvw))
  have hrotate : ∀ v : Fin (2*(n+1)), finRotate (2*(n+1)) v =
      if hv : v.val+1 < 2*(n+1) then ⟨v.val+1,hv⟩ else ⟨0,by omega⟩ := by
    intro v
    change finRotate ((2*n+1)+1) v = _
    split_ifs with hv
    · exact finRotate_of_lt (by omega)
    · have he : v = Fin.last (2*n+1) := by
        apply Fin.ext
        simp only [Fin.val_last]
        have := v.isLt
        omega
      subst v
      exact finRotate_last'
  have hJM : JM B (visibility n) := by
    apply compressed_parent B (cycleMajoranaBond gf) (visibility n)
      ((qubitV (ι := Fin d))) ((qubitV_isometry (ι := Fin d))) htrB _ E hE hsum hsigned
    intro v
    by_cases hv : v=v₀
    · subst v
      have hlast : ¬(v₀.val+1 < 2*(n+1)) := by dsimp [v₀];omega
      simp only [cycleMajoranaBond,cycleCoeff,hrotate,hlast,↓reduceDIte]
      change ((qubitV (ι := Fin d))).conjTranspose*((-Complex.I) • (g (2*n+1)*g 0))*(qubitV (ι := Fin d))=B v₀
      rw [hg.2.2.2.2,qubitV_compress]
      simp [B,qubitZ,K,v₀]
    · have hk : v.val < 2*n+1 := by
        have hne : v.val ≠ 2*n+1 := by simpa [v₀,Fin.ext_iff] using hv
        have := v.isLt
        omega
      have hnext : v.val+1 < 2*(n+1) := by omega
      simp only [cycleMajoranaBond,cycleCoeff,hrotate,hnext,↓reduceDIte]
      change ((qubitV (ι := Fin d))).conjTranspose*(Complex.I • (g v.val*g (v.val+1)))*(qubitV (ι := Fin d))=B v
      rw [hg.2.2.2.1 v.val hk]
      simp only [liftPath]
      split_ifs <;> rw [qubitV_compress] <;>
        simp [B,hv,cyclePrefix,show v.val+1 < 2*n+2 by omega,qubitZ]
  apply central_relabel_parent A B (visibility n) v₀ K hKherm hKsq hKcomm _ htrA htrB hJM
  intro v
  rfl
end
noncomputable section
theorem result : claim := by
  intro n hn
  refine ⟨?_,?_,?_⟩
  · intro d A hR
    change IsGreatest {t : ℝ | t ∈ Set.Icc 0 1 ∧ JM A t} (visibility n)
    refine ⟨⟨visibility_Icc n hn,even_path_JM_threshold hn A hR⟩,?_⟩
    intro t ht
    exact path_feasible_upper hn A hR t ht.2
  · intro d A hR
    change IsGreatest {t : ℝ | t ∈ Set.Icc 0 1 ∧ JM A t} (visibility n)
    refine ⟨⟨visibility_Icc n hn,odd_path_JM_threshold hn A hR⟩,?_⟩
    intro t ht
    exact odd_path_feasible_upper hn A hR t ht.2
  · intro d A hR
    change IsGreatest {t : ℝ | t ∈ Set.Icc 0 1 ∧ JM A t} (visibility n)
    refine ⟨⟨visibility_Icc n hn,cycle_JM_threshold hn A hR⟩,?_⟩
    intro t ht
    exact cycle_feasible_upper hn A hR t ht.2
end
end D5.S3.Quantum.Measurements.CliffordJointMeasurability.McNultyPathRobustness
