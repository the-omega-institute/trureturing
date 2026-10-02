/- GID: D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ZeitlinSixJ/Inverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Racah finite sums and the Zeitlin six-j identities. -/

/-
inverse_moment_open:
  proof_shape: content
  escape_witness: physical_spectral_inverse: physicalSpectralInverse n j l = physicalG n j l for j<l<=n and j<=n. The full constructed inverse equality is used at its central diagonal before restoring the W support and j/l symmetry.
jacobi_eigencol_last_zero:
  proof_shape: content
  escape_witness: Local htail: forall i,k:Fin(m+1), i.val<=k.val -> Q k h=0, constructed by reverse induction from the last zero and the nonzero Jacobi edges. It is stronger than the requested final column-zero statement and remains live.
symmetric_jacobi_intertwiner_unique:
  proof_shape: content
  escape_witness: jacobi_eigencol_last_zero: an eigen-intertwining column with zero last entry vanishes identically. Its reverse-induction construction first propagates the last-column equality and then every column equality.
admission_basis: escape-witness
Direct frozen dependencies: none on the immutable origin/dev baseline.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Algebra.ZeitlinSixJ.SpectralInverse

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Algebra.ZeitlinSixJ.Inverse
open Finset Polynomial Matrix
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion
open D5.S3.Quantum.Algebra.ZeitlinSixJ.RawRecurrence
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Endpoint
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Orthogonality
open D5.S3.Quantum.Algebra.ZeitlinSixJ.SpectralInverse

theorem inverse_moment_open (N j l : ℕ) (hN : 2 ≤ N)
    (hj : 1 ≤ j ∧ j < N) (hl : 1 ≤ l ∧ l < N) (hjl : j ≠ l) :
    (∑ i ∈ range (N-1), (2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1) *
      W N (i+1) j l ^ 2) = 1/((N : ℝ)* |(j : ℝ)-l| *(j+l+1)) := by
  have sum_shifted_support (f : ℕ → ℝ) (n r d : ℕ) (hd : d≤r) (hr : r≤n)
      (hz : ∀ i, i < d ∨ r < i → f i=0) :
      (∑ t ∈ range (r-d+1),f (d+t))=∑ i ∈ range (n+1),f i := by
    have htrim : (∑ i ∈ range (r+1),f i)=∑ i ∈ range (n+1),f i := by
      apply sum_subset (range_mono (by omega))
      intro i _ hi
      apply hz
      have hi' : ¬i < r+1 := by simpa only [mem_range] using hi
      right
      omega
    have hlow : (∑ i ∈ range d,f i)=0 := by
      apply sum_eq_zero
      intro i hi
      exact hz i (Or.inl (mem_range.mp hi))
    rw [show r+1=d+(r-d+1) by omega,sum_range_add,hlow,zero_add] at htrim
    exact htrim
  have sixJ_cycle_columns (a b c d e f : ℕ) :
      sixJ a b c d e f = sixJ c a b f d e := by
    have triangle_cycle (a b c : ℕ) : triangle a b c ↔ triangle c a b := by
      unfold triangle
      omega
    have deltaSq_cycle (a b c : ℕ) : deltaSq a b c = deltaSq c a b := by
      unfold deltaSq
      rw [show c+a-b=a+c-b by omega, show c+b-a=b+c-a by omega,
        show a+b-c=a+b-c by rfl, show c+a+b=a+b+c by omega]
      ring
    have ha : admissible a b c d e f ↔ admissible c a b f d e := by
      unfold admissible
      rw [← triangle_cycle a b c, ← triangle_cycle d e c,
        ← triangle_cycle a e f, ← triangle_cycle d b f]
      tauto
    have hlo : lower a b c d e f = lower c a b f d e := by
      unfold lower
      rw [show c+a+b=a+b+c by omega, show c+d+e=d+e+c by omega,
        show f+a+e=a+e+f by omega, show f+d+b=d+b+f by omega]
      ac_rfl
    have hup : upper a b c d e f = upper c a b f d e := by
      unfold upper
      rw [show c+a+f+d=c+a+f+d by rfl, show a+b+d+e=a+b+d+e by rfl,
        show b+c+e+f=b+c+e+f by rfl]
      ac_rfl
    have ht (z : ℕ) : racahTerm a b c d e f z = racahTerm c a b f d e z := by
      unfold racahTerm
      rw [show c+a+b=a+b+c by omega, show c+d+e=d+e+c by omega,
        show f+a+e=a+e+f by omega, show f+d+b=d+b+f by omega]
      congr 1
      ring
    have hr : racahSum a b c d e f = racahSum c a b f d e := by
      simp only [racahSum, ← hlo, ← hup, ← ht]
    have hd : deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c =
        deltaSq c a b*deltaSq c d e*deltaSq f a e*deltaSq f d b := by
      rw [← deltaSq_cycle a b c, ← deltaSq_cycle d e c,
        ← deltaSq_cycle a e f, ← deltaSq_cycle d b f]
      ring
    simp only [sixJ, ← ha, ← hd, ← hr]
  have W_swap (N i j l : ℕ) : W N i j l=W N i l j := by
    have sixJ_swap_columns (a b c d e f : ℕ) :
        sixJ a b c d e f = sixJ b a c e d f := by
      have deltaSq_swap (a b c : ℕ) : deltaSq a b c = deltaSq b a c := by
        unfold deltaSq
        rw [show b+a-c=a+b-c by omega, show b+a+c=a+b+c by omega]
        ring
      have triangle_swap (a b c : ℕ) : triangle a b c ↔ triangle b a c := by
        unfold triangle
        omega
      have ha : admissible a b c d e f ↔ admissible b a c e d f := by
        unfold admissible
        rw [← triangle_swap b a c, ← triangle_swap b d f,
          ← triangle_swap e a f, ← triangle_swap e d c]
        tauto
      have hlo : lower a b c d e f = lower b a c e d f := by
        unfold lower
        rw [show b+a+c=a+b+c by omega, show e+a+f=a+e+f by omega,
          show e+d+c=d+e+c by omega, show b+d+f=d+b+f by omega]
        ac_rfl
      have hup : upper a b c d e f = upper b a c e d f := by
        unfold upper
        rw [show b+a+e+d=a+b+d+e by omega, show a+c+d+f=c+a+f+d by omega,
          show c+b+f+e=b+c+e+f by omega]
        ac_rfl
      have ht (z : ℕ) : racahTerm a b c d e f z = racahTerm b a c e d f z := by
        unfold racahTerm
        rw [show b+a+c=a+b+c by omega, show e+a+f=a+e+f by omega,
          show e+d+c=d+e+c by omega, show b+d+f=d+b+f by omega,
          show b+a+e+d=a+b+d+e by omega, show a+c+d+f=c+a+f+d by omega,
          show c+b+f+e=b+c+e+f by omega]
        congr 1
        ring
      have hr : racahSum a b c d e f = racahSum b a c e d f := by
        simp only [racahSum, ← hlo, ← hup, ← ht]
      have hd : deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c =
          deltaSq b a c*deltaSq b d f*deltaSq e a f*deltaSq e d c := by
        rw [← deltaSq_swap b a c, ← deltaSq_swap b d f,
          ← deltaSq_swap e a f, ← deltaSq_swap e d c]
        ring
      simp only [sixJ, ← ha, ← hd, ← hr]
    unfold W
    calc
      _ = sixJ (2*l) (2*i) (2*j) (N-1) (N-1) (N-1) := sixJ_cycle_columns _ _ _ _ _ _
      _ = _ := sixJ_swap_columns _ _ _ _ _ _
  have inverse_moment_ordered (N j l : ℕ) (hN : 2≤N)
      (hj : 1≤j ∧ j<N) (hl : 1≤l ∧ l<N) (hjl : j<l) :
      (∑ i ∈ range (N-1),(2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1)*W N (i+1) j l^2) =
        1/((N : ℝ)*|(j : ℝ)-l| *(j+l+1)) := by
    have central_inverse_moment (n j l : ℕ) (hn : 1≤n)
        (hj : j≤n) (hl : l≤n) (hjl : j<l) :
        ((n+1 : ℕ) : ℝ)*(∑ i ∈ range n,(2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1)*
          W (n+1) (i+1) j l^2) =
            1/(casimir l-casimir j) := by
      have central_symbol_is_W (N i j l : ℕ) :
          sixJ (N-1) (N-1) (2*i) (2*j) (2*l) (N-1) = W N i j l := by
        have sixJ_flip_pair (a b c d e f : ℕ) :
            sixJ a b c d e f = sixJ d e c a b f := by
          have ha : admissible a b c d e f ↔ admissible d e c a b f := by
            unfold admissible
            tauto
          have hlo : lower a b c d e f = lower d e c a b f := by
            unfold lower
            ac_rfl
          have hup : upper a b c d e f = upper d e c a b f := by
            unfold upper
            rw [show d+e+a+b=a+b+d+e by omega, show e+c+b+f=b+c+e+f by omega,
              show c+d+f+a=c+a+f+d by omega]
          have ht (z : ℕ) : racahTerm a b c d e f z = racahTerm d e c a b f z := by
            unfold racahTerm
            rw [show d+e+a+b=a+b+d+e by omega, show e+c+b+f=b+c+e+f by omega,
              show c+d+f+a=c+a+f+d by omega]
            congr 1
            ring
          have hr : racahSum a b c d e f = racahSum d e c a b f := by
            simp only [racahSum, ← hlo, ← hup, ← ht]
          have hd : deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c =
              deltaSq d e c*deltaSq d b f*deltaSq a e f*deltaSq a b c := by ring
          simp only [sixJ, ← ha, ← hd, ← hr]
        unfold W
        calc
          _ = sixJ (2*j) (2*l) (2*i) (N-1) (N-1) (N-1) := sixJ_flip_pair (N-1) (N-1) (2*i) (2*j) (2*l) (N-1)
          _ = sixJ (2*i) (2*j) (2*l) (N-1) (N-1) (N-1) := sixJ_cycle_columns (2*j) (2*l) (2*i) (N-1) (N-1) (N-1)
      have channel_center_label (n j l : ℕ) (hj : j ≤ n) (hl : l ≤ n)
          (hjl : j ≤ l) :
          ∃ t ≤ channelWidth n j l, channelLabel n j l t = n := by
        have hm : max n (j+l)+min n (j+l)=n+(j+l) := max_add_min _ _
        refine ⟨(n-channelBase n j l)/2, ?_, ?_⟩
        · unfold channelWidth channelBase
          omega
        · unfold channelLabel channelBase
          omega
      have greenColumn_diag (a e L R : ℕ → ℝ) (h : ℕ) :
          greenColumn a e L R h h=(L h+R h-a h)⁻¹ := by
        simp [greenColumn]
      have physical_gap (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j<l)
          (t : ℕ) (ht : t≤channelWidth n j l) :
          physicalLP n j l t+physicalRP n j l t-physicalA n j l t =
            ((n : ℝ)+1)*(casimir l-casimir j)/(2*(channelSpin n j l t : ℝ)+1) := by
        have pivot_gap (s j l k : ℚ) (hk : k ≠ 0) (hk1 : k+1 ≠ 0) (hk2 : 2*k+1 ≠ 0) :
            pivotLeft s j l k+pivotRight s j l k-rawDiagonal s s j l k =
              (2*s+1)*(spinCasimir l-spinCasimir j)/(2*k+1) := by
          have fourSpinDenominator_ne (y : ℚ) (hy : y ≠ 0)
              (hy1 : y+1 ≠ 0) (hy2 : 2*y+1 ≠ 0) : fourSpinDenominator y ≠ 0 := by
            unfold fourSpinDenominator
            exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) hy) hy1) hy2
          have rawDiagonal_scaled (a b c d u y : ℚ)
              (hy : y ≠ 0) (hy1 : y+1 ≠ 0) :
              fourSpinDenominator y*(rawDiagonal a b c d y-u*(u+1)) =
                (2*y+1)*(2*y*(y+1)*(a*(a+1)+b*(b+1)-u*(u+1))-
                  (y*(y+1)+a*(a+1)-d*(d+1))*(y*(y+1)+b*(b+1)-c*(c+1))) := by
            let v := (y*(y+1)+a*(a+1)-d*(d+1))*(y*(y+1)+b*(b+1)-c*(c+1))
            let w := a*(a+1)+b*(b+1)-u*(u+1)
            change fourSpinDenominator y*(a*(a+1)+b*(b+1)-v/(2*y*(y+1))-u*(u+1)) =
              (2*y+1)*(2*y*(y+1)*w-v)
            calc
              _ = (2*y+1)*(2*y*(y+1)*w-(2*y*(y+1))*(v/(2*y*(y+1)))) := by
                unfold fourSpinDenominator
                change _ = (2*y+1)*(2*y*(y+1)*(a*(a+1)+b*(b+1)-u*(u+1))-_)
                ring
              _ = _ := by rw [mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (by positivity) hy) hy1)]
          have pivotLeft_scaled (s j l k : ℚ) (hk1 : k+1 ≠ 0) (hk2 : 2*k+1 ≠ 0) :
              jacobiDenominator k*pivotLeft s j l k = k*pivotLeftNumerator s j l k := by
            unfold jacobiDenominator pivotLeft
            calc
              _ = k*((2*(k+1)*(2*k+1))*(pivotLeftNumerator s j l k/(2*(k+1)*(2*k+1)))) := by ring
              _ = _ := by rw [mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (by positivity) hk1) hk2)]
          have pivotRight_scaled (s j l k : ℚ) (hk : k ≠ 0) (hk2 : 2*k+1 ≠ 0) :
              jacobiDenominator k*pivotRight s j l k = (k+1)*pivotRightNumerator s j l k := by
            unfold jacobiDenominator pivotRight
            calc
              _ = (k+1)*((2*k*(2*k+1))*(pivotRightNumerator s j l k/(2*k*(2*k+1)))) := by ring
              _ = _ := by rw [mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (by positivity) hk) hk2)]
          have pivot_gap_polynomial (s j l k : ℚ) :
              k*pivotLeftNumerator s j l k+(k+1)*pivotRightNumerator s j l k -
                (2*k+1)*(4*k*(k+1)*spinCasimir s-
                  (k*(k+1)+spinCasimir s-spinCasimir j)*(k*(k+1)+spinCasimir s-spinCasimir l)) =
                2*k*(k+1)*(2*s+1)*(spinCasimir l-spinCasimir j) := by
            unfold pivotLeftNumerator pivotRightNumerator spinCasimir
            ring
          have hd : jacobiDenominator k ≠ 0 := fourSpinDenominator_ne k hk hk1 hk2
          have ha := rawDiagonal_scaled s s j l 0 k hk hk1
          simp only [zero_mul, zero_add, sub_zero] at ha
          have ha' : jacobiDenominator k*rawDiagonal s s j l k =
              (2*k+1)*(4*k*(k+1)*spinCasimir s-
                (k*(k+1)+spinCasimir s-spinCasimir j)*(k*(k+1)+spinCasimir s-spinCasimir l)) := by
            simpa only [jacobiDenominator, fourSpinDenominator, spinCasimir, mul_comm, mul_left_comm,
              mul_assoc, ← two_mul, mul_add, show (2 : ℚ)*2 = 4 by ring] using ha
          apply mul_left_cancel₀ hd
          conv_lhs => rw [mul_sub, mul_add]
          rw [pivotLeft_scaled s j l k hk1 hk2, pivotRight_scaled s j l k hk hk2, ha',
            pivot_gap_polynomial]
          unfold jacobiDenominator
          field_simp [hk2] <;> ring
        have channelSpin_bounds (n j l t : ℕ) (hj : j≤n) (hl : l≤n)
            (hjl : j<l) (ht : t≤channelWidth n j l) :
            0<channelSpin n j l t ∧ (n : ℚ)/2-j≤channelSpin n j l t ∧
              (l : ℚ)-(n : ℚ)/2≤channelSpin n j l t ∧ channelSpin n j l t≤(n : ℚ)/2+j := by
          have channel_admissible (n j l t u : ℕ) (hj : j ≤ n)
              (hl : l ≤ n) (hjl : j ≤ l) (ht : t ≤ channelWidth n j l)
              (hu : u ≤ channelWidth n j l) :
              admissible n n (2*(l-j+u)) (2*j) (2*l) (channelLabel n j l t) := by
            have hm : max n (j+l)+min n (j+l)=n+(j+l) := max_add_min _ _
            unfold channelWidth at ht hu
            unfold channelLabel channelBase admissible triangle
            omega
          have ha := channel_admissible n j l t 0 hj hl hjl.le ht (by omega)
          have h1 : (n : ℚ)≤2*j+channelLabel n j l t := by exact_mod_cast ha.2.2.1.2.1
          have h2 : (2*l : ℚ)≤n+channelLabel n j l t := by exact_mod_cast ha.2.1.2.1
          have h3 : (channelLabel n j l t : ℚ)≤2*j+n := by exact_mod_cast ha.2.2.1.2.2.1
          have hjlq : (j : ℚ)<l := by exact_mod_cast hjl
          unfold channelSpin
          constructor
          · linarith
          constructor
          · linarith
          constructor <;> linarith
        have physicalA_raw (n j l t : ℕ) (hp : 0<channelSpin n j l t) :
            physicalA n j l t=(rawDiagonal ((n : ℚ)/2) ((n : ℚ)/2) j l (channelSpin n j l t) : ℝ) := by
          have hz : channelLabel n j l t≠0 := by
            intro he
            simp [channelSpin,he] at hp
          simp only [physicalA,recurrenceDiagonalQ,if_neg hz,channelSpin]
          congr 1
          congr 1 <;> push_cast <;> ring
        have hb := channelSpin_bounds n j l t hj hl hjl ht
        rw [physicalA_raw _ _ _ _ hb.1]
        have h := pivot_gap ((n : ℚ)/2) j l (channelSpin n j l t)
          (ne_of_gt hb.1) (by linarith) (by linarith)
        unfold physicalLP physicalRP casimir
        unfold spinCasimir at h
        exact_mod_cast (by convert h using 1 <;> ring :
          pivotLeft ((n : ℚ)/2) j l (channelSpin n j l t)+pivotRight ((n : ℚ)/2) j l (channelSpin n j l t)-
            rawDiagonal ((n : ℚ)/2) ((n : ℚ)/2) j l (channelSpin n j l t) =
              ((n : ℚ)+1)*((l : ℚ)*(l+1)-(j : ℚ)*(j+1))/(2*channelSpin n j l t+1))
      rcases channel_center_label n j l hj hl hjl.le with ⟨t,ht,hlabel⟩
      let k : Fin (channelWidth n j l+1) := ⟨t,by omega⟩
      have hk : channelLabel n j l k.val=n := hlabel
      have hb : channelBase n j l+2*k.val=n := hk
      let f : ℕ → ℝ := fun i => (2*(i : ℝ)+1)/casimir i*sixJ n n (2*i) (2*j) (2*l) n^2
      have hfzero (i : ℕ) (hi : i < l-j ∨ min n (j+l) < i) : f i=0 := by
        have hnot : ¬admissible n n (2*i) (2*j) (2*l) n := by
          intro ha
          have h1 := ha.1
          have h4 := ha.2.2.2
          unfold triangle at h1 h4
          omega
        simp only [f,sixJ,if_neg hnot,zero_pow (by omega : (2 : ℕ)≠0),mul_zero]
      have hfsum : (∑ i : Fin (channelWidth n j l+1),f (l-j+i.val))=
          ∑ i ∈ range (n+1),f i := by
        unfold channelWidth
        rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => f (l-j+i))]
        apply sum_shifted_support f n (min n (j+l)) (l-j) (by omega) (by omega)
        exact hfzero
      have hsquare (i : Fin (channelWidth n j l+1)) :
          physicalU n j l k i^2=((n+1 : ℕ) : ℝ)*(2*((l-j+i.val : ℕ) : ℝ)+1)*
            sixJ n n (2*(l-j+i.val)) (2*j) (2*l) n^2 := by
        unfold physicalU
        rw [hk,mul_pow,Real.sq_sqrt (by positivity)]
        push_cast
        ring
      have hmatrix := physical_spectral_inverse n j l hj hl hjl
      have hm := congrArg (fun A => A k k) hmatrix
      change (physicalU n j l*diagonal (fun i : Fin (channelWidth n j l+1) =>
          (casimir (l-j+i.val))⁻¹)*(physicalU n j l)ᵀ) k k =
            greenColumn (physicalA n j l) (physicalE n j l) (physicalLP n j l) (physicalRP n j l) k.val k.val at hm
      rw [greenColumn_diag] at hm
      have hgap : physicalLP n j l k.val+physicalRP n j l k.val-physicalA n j l k.val=casimir l-casimir j := by
        rw [physical_gap n j l hj hl hjl k.val (by omega)]
        unfold channelSpin
        rw [hk]
        push_cast
        have hnp : (n : ℝ)+1≠0 := by positivity
        field_simp <;> ring
      rw [hgap,Matrix.mul_apply] at hm
      simp only [Matrix.mul_diagonal,Matrix.transpose_apply] at hm
      have hterm (i : Fin (channelWidth n j l+1)) :
          (physicalU n j l k i*(casimir (l-j+i.val))⁻¹)*physicalU n j l k i=
            ((n+1 : ℕ) : ℝ)*f (l-j+i.val) := by
        calc
          _ = (casimir (l-j+i.val))⁻¹*(physicalU n j l k i)^2 := by ring
          _ = _ := by rw [hsquare]; unfold f; simp only [div_eq_mul_inv]; ring
      simp_rw [hterm] at hm
      rw [←Finset.mul_sum,hfsum] at hm
      have hf0 : f 0=0 := by simp [f,casimir]
      rw [sum_range_succ',hf0,add_zero] at hm
      have hW (i : ℕ) : sixJ n n (2*i) (2*j) (2*l) n=W (n+1) i j l := by
        simpa only [Nat.add_sub_cancel_right] using central_symbol_is_W (n+1) i j l
      dsimp [f] at hm
      simp_rw [hW] at hm
      simpa only [one_div] using hm
    let n := N-1
    have hn : 1≤n := by dsimp [n]; omega
    have hjn : j≤n := by dsimp [n]; omega
    have hln : l≤n := by dsimp [n]; omega
    have hdimN : n+1=N := by dsimp [n]; omega
    have h := central_inverse_moment n j l hn hjn hln hjl
    rw [hdimN] at h
    have hNR : (N : ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
    have hjlR : (j : ℝ)<l := by exact_mod_cast hjl
    have habs : |(j : ℝ)-l|=(l : ℝ)-j := by rw [abs_of_neg (by linarith)]; ring
    rw [habs]
    have hdiff : casimir l-casimir j=((l : ℝ)-j)*((j : ℝ)+l+1) := by unfold casimir; ring
    rw [hdiff] at h
    dsimp [n] at h
    calc
      _ = (1/(((l : ℝ)-j)*((j : ℝ)+l+1)))/(N : ℝ) :=
        (eq_div_iff hNR).mpr (by simpa only [mul_comm] using h)
      _ = _ := by rw [div_div]; congr 1; ring
  by_cases horder : j<l
  · exact inverse_moment_ordered N j l hN hj hl horder
  · have h := inverse_moment_ordered N l j hN hl hj (by omega)
    have he : (∑ i ∈ range (N-1),(2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1)*W N (i+1) l j^2) =
        ∑ i ∈ range (N-1),(2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1)*W N (i+1) j l^2 := by
      apply sum_congr rfl
      intro i _
      rw [W_swap N (i+1) l j]
    rw [he,abs_sub_comm (l : ℝ) j] at h
    convert h using 1 <;> ring

noncomputable def indexParity (m b : ℕ) : Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
  diagonal (fun i => (-1 : ℝ)^(b+i.val))

private lemma jacobi_eigencol_last_zero (m : ℕ) (a e d : Fin (m+1) → ℝ)
    (Q : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (hedge : ∀ t : Fin m,e t.castSucc≠0)
    (hQ : jacobiMatrix m a e*Q=Q*diagonal d)
    (h : Fin (m+1)) (hzero : Q (Fin.last m) h=0) : ∀ k,Q k h=0 := by
  have upperBand_mul (m : ℕ) (e : Fin (m+1) → ℝ)
      (U : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (i : Fin (m+1)) (h : Fin (m+1)) :
      (upperBand m e*U) i h =
        if hi : i.val < m then e i*U ⟨i.val+1,by omega⟩ h else 0 := by
    classical
    simp only [Matrix.mul_apply,upperBand]
    by_cases hi : i.val < m
    · rw [dif_pos hi]
      rw [Finset.sum_eq_single (⟨i.val+1,by omega⟩ : Fin (m+1))]
      · simp
      · intro j _ hj
        have hn : i.val+1 ≠ j.val := by
          intro he
          apply hj
          apply Fin.ext
          exact he.symm
        simp only [if_neg hn,zero_mul]
      · simp
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro j _
      have hn : i.val+1 ≠ j.val := by omega
      simp only [if_neg hn,zero_mul]
  have lowerBand_mul (m : ℕ) (e : Fin (m+1) → ℝ)
      (U : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (i : Fin (m+1)) (h : Fin (m+1)) :
      ((upperBand m e)ᵀ*U) i h =
        if hi : 0 < i.val then
          e ⟨i.val-1,by omega⟩*U ⟨i.val-1,by omega⟩ h else 0 := by
    classical
    simp only [Matrix.mul_apply,Matrix.transpose_apply,upperBand]
    by_cases hi : 0 < i.val
    · rw [dif_pos hi]
      rw [Finset.sum_eq_single (⟨i.val-1,by omega⟩ : Fin (m+1))]
      · have he : i.val-1+1=i.val := by omega
        simp only [Fin.val_mk,if_pos he]
      · intro j _ hj
        have hn : j.val+1 ≠ i.val := by
          intro he
          apply hj
          apply Fin.ext
          change j.val=i.val-1
          omega
        simp only [if_neg hn,zero_mul]
      · simp
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro j _
      have hn : j.val+1 ≠ i.val := by omega
      simp only [if_neg hn,zero_mul]
  have jacobiMatrix_mul (m : ℕ) (a e : Fin (m+1) → ℝ)
      (U : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (i : Fin (m+1)) (h : Fin (m+1)) :
      (jacobiMatrix m a e*U) i h = a i*U i h +
        (if hi : i.val < m then e i*U ⟨i.val+1,by omega⟩ h else 0) +
        (if hi : 0 < i.val then e ⟨i.val-1,by omega⟩*U ⟨i.val-1,by omega⟩ h else 0) := by
    simp only [jacobiMatrix,Matrix.add_mul,Matrix.add_apply,Matrix.diagonal_mul,
      upperBand_mul,lowerBand_mul]
  have htail : ∀ i : Fin (m+1), ∀ k : Fin (m+1), i.val≤k.val → Q k h=0 := by
    intro i
    induction i using Fin.reverseInduction with
    | last =>
      intro k hk
      have he : k=Fin.last m := Fin.ext (by simp only [Fin.val_last] at hk ⊢; omega)
      rw [he]
      exact hzero
    | cast t ih =>
      intro k hk
      by_cases hn : t.succ.val≤k.val
      · exact ih k hn
      · have he : k=t.castSucc := Fin.ext (by simp only [Fin.val_succ,Fin.val_castSucc] at hk hn ⊢; omega)
        subst k
        have hr := congrArg (fun A => A t.succ h) hQ
        rw [jacobiMatrix_mul,Matrix.mul_diagonal] at hr
        have hdiag := ih t.succ le_rfl
        have hup : (if hp : t.succ.val<m then e t.succ*Q ⟨t.succ.val+1,by omega⟩ h else 0)=0 := by
          split_ifs with hp
          · rw [ih _ (by simp only [Fin.val_mk]; omega),mul_zero]
          · rfl
        have hp : 0<t.succ.val := by simp
        rw [hdiag,mul_zero,zero_mul,hup,add_zero,zero_add,dif_pos hp] at hr
        have heprev : (⟨t.succ.val-1,by omega⟩ : Fin (m+1))=t.castSucc := Fin.ext (by simp)
        rw [heprev] at hr
        exact (mul_eq_zero.mp hr).resolve_left (hedge t)
  intro k
  exact htail 0 k (by simp)

lemma symmetric_jacobi_intertwiner_unique (m : ℕ) (a e d : Fin (m+1) → ℝ)
    (X Z : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (hedge : ∀ t : Fin m,e t.castSucc≠0)
    (hX : jacobiMatrix m a e*X=X*diagonal d)
    (hZ : jacobiMatrix m a e*Z=Z*diagonal d)
    (hXs : Xᵀ=X) (hZs : Zᵀ=Z)
    (hend : X (Fin.last m) (Fin.last m)=Z (Fin.last m) (Fin.last m)) : X=Z := by
  have jacobi_eigencol_last_unique (m : ℕ) (a e d : Fin (m+1) → ℝ)
      (X Z : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
      (hedge : ∀ t : Fin m,e t.castSucc≠0)
      (hX : jacobiMatrix m a e*X=X*diagonal d)
      (hZ : jacobiMatrix m a e*Z=Z*diagonal d)
      (h : Fin (m+1)) (hlast : X (Fin.last m) h=Z (Fin.last m) h) : ∀ k,X k h=Z k h := by
    have hQ : jacobiMatrix m a e*(X-Z)=(X-Z)*diagonal d := by
      rw [Matrix.mul_sub,Matrix.sub_mul,hX,hZ]
    have hz : (X-Z) (Fin.last m) h=0 := sub_eq_zero.mpr hlast
    have h := jacobi_eigencol_last_zero m a e d (X-Z) hedge hQ h hz
    intro k
    exact sub_eq_zero.mp (h k)
  have hcol := jacobi_eigencol_last_unique m a e d X Z hedge hX hZ (Fin.last m) hend
  have hrow : ∀ h,X (Fin.last m) h=Z (Fin.last m) h := by
    intro h
    have hx := congrArg (fun A => A h (Fin.last m)) hXs
    have hz := congrArg (fun A => A h (Fin.last m)) hZs
    simp only [Matrix.transpose_apply] at hx hz
    exact hx.trans ((hcol h).trans hz.symm)
  ext k h
  exact jacobi_eigencol_last_unique m a e d X Z hedge hX hZ h (hrow h) k

noncomputable def physicalC0 (n j l : ℕ) : ℝ :=
  2*((n : ℝ)/2)*((n : ℝ)/2+1)+casimir j+casimir l

noncomputable def physicalX (n j l : ℕ) :
    Matrix (Fin (channelWidth n j l+1)) (Fin (channelWidth n j l+1)) ℝ :=
  physicalU n j l*indexParity (channelWidth n j l) (l-j)*(physicalU n j l)ᵀ

noncomputable def physicalM (n j l : ℕ) :
    Matrix (Fin (channelWidth n j l+1)) (Fin (channelWidth n j l+1)) ℝ :=
  physicalC0 n j l • 1-diagonal (physicalCasimir n j l)-physicalT n j l

noncomputable def physicalV (n j l : ℕ) :
    Matrix (Fin (channelWidth n j l+1)) (Fin (channelWidth n j l+1)) ℝ :=
  finiteSixJMatrix n (2*l) n (2*j) (channelBase n j l) (channelWidth n j l)
    (fun h : Fin (channelWidth n j l+1) => channelLabel n j l h.val)

noncomputable def physicalTprime (n j l : ℕ) :
    Matrix (Fin (channelWidth n j l+1)) (Fin (channelWidth n j l+1)) ℝ :=
  finiteSixJJacobi n (2*l) n (2*j) (channelBase n j l) (channelWidth n j l)

noncomputable def physicalZ (n j l : ℕ) :
    Matrix (Fin (channelWidth n j l+1)) (Fin (channelWidth n j l+1)) ℝ :=
  (-1 : ℝ)^(channelBase n j l) •
    (indexParity (channelWidth n j l) 0*physicalV n j l*indexParity (channelWidth n j l) 0)

end D5.S3.Quantum.Algebra.ZeitlinSixJ.Inverse
