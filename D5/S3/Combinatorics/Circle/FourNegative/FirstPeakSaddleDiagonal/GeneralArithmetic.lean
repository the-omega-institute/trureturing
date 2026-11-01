/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/GeneralArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:private-consumed-full-saddle-implementation)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Arbitrary-grain diagonal choice and general z>=4 rectangle-to-twelve proof. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal.Certificates

/-! SOURCE_ONLY_UNCOMPILED. All strict/equality diagonal selections are native.
rectangle_to_twelve is proved here for every z>=4; its proof uses positive
factored slacks and no restriction on the dyadic grain. The final consumer
converts these exact gate coordinates to the general physical JointChoice. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal
open private
  D A B L M Bn
  Ln Mn grain reserve C E0
  H0 pivot scaledMargin rectangleMargin boundaryMargin gateMargin
  chart_strict_neg1 chart_strict_negg chart_strict_pos11 chart_strict_pos1max
  chart_strict_posmax1 chart_strict_posmaxmax chart_strict_boundary chart_equality_Klarge_neg1 chart_equality_Klarge_pos11 chart_equality_Klarge_pos1max
  chart_equality_Klarge_posmax1 chart_equality_Klarge_posmaxmax chart_equality_Klarge_boundary chart_equality_Jlarge_neg1 chart_equality_Jlarge_pos11 chart_equality_Jlarge_pos1max
  chart_equality_Jlarge_posmax1 chart_equality_Jlarge_posmaxmax chart_equality_Jlarge_boundary
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal.Certificates

-- The only forbidden start is the unique gap of length m-1.
private theorem euclidean_gap_hit (g m b : ℤ) (hg : 4≤g) (hm : 2≤m)
    (hb : 0≤b ∧ b<g*m+1) (hne : b≠(g-1)*m+2) :
    ∃ δ i ε : ℤ, 0 ≤ δ ∧ δ ≤ m - 2 ∧ 0 ≤ i ∧ i < g ∧
      (ε = 0 ∨ ε = 1) ∧ ((g * m + 1) ∣ b + δ - (i * m + ε)) := by
  by_cases hlarge : (g-1)*m+2<b
  · refine ⟨g*m+1-b,0,0,?_,?_,by omega,by omega,Or.inl rfl,?_⟩
    · omega
    · nlinarith only [hlarge]
    · refine ⟨1,?_⟩; ring
  · have hsmall : b≤(g-1)*m+1 := by omega
    let i := b/m
    let u := b%m
    have hu : 0≤u ∧ u<m :=
      ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ (by omega)⟩
    have he : b=u+m*i := Int.emod_add_mul_ediv b m
    have hi : 0≤ i := by
      by_contra hn
      have hp := mul_le_mul_of_nonneg_left (show i≤-1 by omega) (show 0≤m by omega)
      nlinarith only [hp,he,hu.2,hb.1]
    by_cases hlow : u≤1
    · have hig : i<g := by
        by_contra hn
        have hh := mul_le_mul_of_nonneg_right (show g≤ i by omega) (show 0≤m by omega)
        nlinarith only [hh,he,hsmall,hu.1,hm]
      refine ⟨0,i,u,by omega,by omega,hi,hig,by omega,?_⟩
      refine ⟨0,?_⟩; nlinarith only [he]
    · have hig : i≤g-2 := by
        by_contra hn
        have hh := mul_le_mul_of_nonneg_right (show g-1≤ i by omega) (show 0≤m by omega)
        nlinarith only [hh,he,hsmall,show 2≤u by omega]
      refine ⟨m-u,i+1,0,by omega,by omega,by omega,by omega,Or.inl rfl,?_⟩
      refine ⟨0,?_⟩; nlinarith only [he]

-- General even grain g=2G. No topology, finite group enumeration or real rotations.
private theorem cyclic_cover (G m τ : ℤ) (hG : 2≤G) (hm : 2≤m)
    (hex : ¬(2*G*m+1)∣τ) :
    ∃ n l : ℤ, -(2*G)≤n ∧ n<2*G ∧ G*m-m≤l ∧ l≤G*m-2 ∧
      (2*G*m+1)∣(τ+G*m-1+n*m-l) := by
  let β := 2*G*m+1
  let a0 := τ+G*m-1
  let start := G*m-m
  let b := (start-a0)%β
  have hβ : 0<β := by dsimp [β]; nlinarith
  have hb : 0≤b ∧ b<2*G*m+1 :=
    ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ hβ⟩
  have hdb : β∣((start-a0)-b) := by
    refine ⟨(start-a0)/β,?_⟩
    have he := Int.emod_add_mul_ediv (start-a0) β
    dsimp [b]; linarith only [he]
  have hne : b≠(2*G-1)*m+2 := by
    intro he
    apply hex
    obtain ⟨w,hw⟩ := hdb
    refine ⟨-w-1,?_⟩
    rw [he] at hw
    dsimp [start,a0,β] at hw ⊢
    linear_combination -hw
  obtain ⟨δ,i,ε,hδ0,hδ1,hi0,hi1,hε,hd⟩ :=
    euclidean_gap_hit (2*G) m b (by omega) hm hb hne
  have choose (n : ℤ) (hn0 : -(2*G)≤n) (hn1 : n<2*G)
      (hs : β∣(n*m-(i*m+ε))) :
      ∃ n l : ℤ, -(2*G)≤n ∧ n<2*G ∧ G*m-m≤l ∧ l≤G*m-2 ∧
        β∣(τ+G*m-1+n*m-l) := by
    refine ⟨n,start+δ,hn0,hn1,by dsimp [start]; omega,
      by dsimp [start]; omega,?_⟩
    have hh := dvd_sub (dvd_sub hs hdb) hd
    convert hh using 1 <;> dsimp [a0,start] <;> ring
  rcases hε with rfl|rfl
  · apply choose i (by omega) hi1
    simp
  · apply choose (i-2*G) (by omega) (by omega)
    refine ⟨-1,?_⟩; dsimp [β]; ring

private theorem odd_successor_not_dvd_pow (c e : ℕ) (hc : 1≤c) :
    ¬((2:ℤ)^c+1)∣(2:ℤ)^e := by
  have hz : (2:ℕ)^c=2*2^(c-1) := by
    conv_lhs => rw [show c=(c-1)+1 by omega,pow_succ]
    ring
  have hc2 : Nat.Coprime (2^c+1) 2 := by
    apply Nat.coprime_two_right.mpr
    exact ⟨2^(c-1),by omega⟩
  intro hd
  have hd' : (2^c+1:ℕ)∣2^e := by exact_mod_cast hd
  have h1 := (hc2.pow_right e).eq_one_of_dvd hd'
  have hp : 1≤(2:ℕ)^c := Nat.one_le_two_pow
  omega

-- The shifted complete residue system [-1,g-1], including the wrap to -1.
private theorem equality_residue (g τ : ℤ) (hg : 1≤g) :
    ∃ n : ℤ, -1≤n ∧ n<g ∧ (g+1)∣(τ+1+n) := by
  refine ⟨(-τ)%(g+1)-1,?_,?_,?_⟩
  · have := Int.emod_nonneg (-τ) (by omega : g+1≠0); omega
  · have := Int.emod_lt_of_pos (-τ) (by omega : 0<g+1); omega
  · refine ⟨-((-τ)/(g+1)),?_⟩
    have := Int.emod_add_mul_ediv (-τ) (g+1)
    nlinarith only [this]

private theorem native_hr (K J n : ℤ) (hK : 1≤K) (hJ : 1≤J)
    (hn : -grain K J≤n ∧ n<grain K J) :
    ∃ h r : ℤ, 0≤h ∧ 1≤r ∧ r≤grain K J ∧ n=2*J*h-r ∧
      ((n<0 ∧ h=0 ∧ r=-n) ∨ (0≤n ∧ 1≤h ∧ h≤2*K ∧ r≤2*J)) := by
  by_cases hneg : n<0
  · exact ⟨0,-n,by omega,by omega,by omega,by ring,Or.inl ⟨hneg,rfl,rfl⟩⟩
  · let h := n/(2*J)+1
    let r := 2*J*h-n
    have hmod : 0≤n%(2*J) ∧ n%(2*J)<2*J :=
      ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ (by omega)⟩
    have he := Int.emod_add_mul_ediv n (2*J)
    have hq : 0≤n/(2*J) := by
      by_contra hnq
      have hp := mul_le_mul_of_nonneg_left (show n/(2*J)≤-1 by omega) (show 0≤2*J by omega)
      nlinarith only [hp,he,hmod.2,show 0≤n by omega]
    have hq1 : n/(2*J)<2*K := by
      by_contra hh
      have hp := mul_le_mul_of_nonneg_right (show 2*K≤n/(2*J) by omega)
        (show 0≤2*J by omega)
      dsimp [grain] at hn
      nlinarith only [hp,he,hmod.1,hn.2]
    have hr : 1 ≤ r ∧ r ≤ 2 * J := by
      dsimp [r, h]
      constructor <;> nlinarith only [he, hmod.1, hmod.2]
    have hrg : r≤grain K J := by
      have hp := mul_nonneg (show 0≤2*K-1 by omega) (show 0≤2*J by omega)
      dsimp [grain]; nlinarith only [hp,hr.2]
    exact ⟨h,r,by dsimp [h]; omega,hr.1,hrg,by dsimp [r]; ring,
      Or.inr ⟨by omega,by dsimp [h]; omega,by dsimp [h]; omega,hr.2⟩⟩

private theorem linear_interval (u v l r x : ℤ) (hx : l≤x ∧ x≤r)
    (hl : 0≤u+l*v) (hr : 0≤u+r*v) : 0≤u+x*v := by
  rcases le_total 0 v with hv|hv
  · have hp := mul_nonneg (show 0≤x-l by omega) hv
    nlinarith only [hp,hl]
  · have hp := mul_nonneg (show 0≤r-x by omega) (show 0≤-v by omega)
    nlinarith only [hp,hr]

private theorem scaled_affine (K J m t lo hi h r : ℤ) (i : Fin 4) :
    scaledMargin K J m t lo hi h r i =
      scaledMargin K J m t lo hi 0 0 i
      +h*(scaledMargin K J m t lo hi 1 0 i-scaledMargin K J m t lo hi 0 0 i)
      +r*(scaledMargin K J m t lo hi 0 1 i-scaledMargin K J m t lo hi 0 0 i) := by
  fin_cases i <;> dsimp [scaledMargin,E0,H0,pivot,grain,reserve,C,A,D,L,M,Ln,Mn] <;> ring

private theorem scaled_rectangle (K J m t lo hi h1 h2 r1 r2 h r : ℤ)
    (hh : h1≤h ∧ h≤h2) (hr : r1≤r ∧ r≤r2)
    (h11 : ∀ i,0≤scaledMargin K J m t lo hi h1 r1 i)
    (h12 : ∀ i,0≤scaledMargin K J m t lo hi h1 r2 i)
    (h21 : ∀ i,0≤scaledMargin K J m t lo hi h2 r1 i)
    (h22 : ∀ i,0≤scaledMargin K J m t lo hi h2 r2 i) :
    ∀ i,0≤scaledMargin K J m t lo hi h r i := by
  intro i
  let u := scaledMargin K J m t lo hi 0 0 i
  let v := scaledMargin K J m t lo hi 1 0 i-u
  let w := scaledMargin K J m t lo hi 0 1 i-u
  have hf (h r : ℤ) : scaledMargin K J m t lo hi h r i=u+h*v+r*w :=
    scaled_affine K J m t lo hi h r i
  have h1r : 0≤u+h1*v+r*w := linear_interval (u+h1*v) w r1 r2 r hr
    (by rw [←hf]; exact h11 i) (by rw [←hf]; exact h12 i)
  have h2r : 0≤u+h2*v+r*w := linear_interval (u+h2*v) w r1 r2 r hr
    (by rw [←hf]; exact h21 i) (by rw [←hf]; exact h22 i)
  have hhr := linear_interval (u+r*w) v h1 h2 h hh
    (by linarith only [h1r]) (by linarith only [h2r])
  rw [hf]; linarith only [hhr]

/- Exact symbolic corner proofs follow. Every variable is an unbounded integer.
The sparse coefficient lists are rendered in multivariate Horner form, so every
factor used by positivity is nonnegative. Each individual equality is a Lean
ring goal, rather than a certificate predicate or native_decide oracle. -/

private theorem corner_strict_neg1 (K J m t : ℤ)
    (hK : 1≤K) (hJ : 1≤J) (hm : 2≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J m t ((grain K J*m)-2*m+1) ((grain K J*m)-3) 0 (1) i := by
  have hc := chart_strict_neg1 (K-1) (J-1) (m-2) (t-4*grain K J*m)
    (by omega) (by omega) (by omega) (by omega)
  have eK : (1:ℤ)+(K-1)=K := by ring
  have eJ : (1:ℤ)+(J-1)=J := by ring
  have em : (2:ℤ)+(m-2)=m := by ring
  simp only [eK,eJ,em] at hc
  have et : 4*((4*K*J)*m)+(t-4*grain K J*m)=t := by dsimp [grain]; ring
  rw [et] at hc
  exact hc

private theorem corner_strict_negg (K J m t : ℤ)
    (hK : 1≤K) (hJ : 1≤J) (hm : 2≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J m t ((grain K J*m)-2*m+1) ((grain K J*m)-3) 0 (grain K J) i := by
  have hc := chart_strict_negg (K-1) (J-1) (m-2) (t-4*grain K J*m)
    (by omega) (by omega) (by omega) (by omega)
  have eK : (1:ℤ)+(K-1)=K := by ring
  have eJ : (1:ℤ)+(J-1)=J := by ring
  have em : (2:ℤ)+(m-2)=m := by ring
  simp only [eK,eJ,em] at hc
  have et : 4*((4*K*J)*m)+(t-4*grain K J*m)=t := by dsimp [grain]; ring
  rw [et] at hc
  exact hc

private theorem corner_strict_pos11 (K J m t : ℤ)
    (hK : 1≤K) (hJ : 1≤J) (hm : 2≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J m t ((grain K J*m)-2*m+1) ((grain K J*m)-3) 1 (1) i := by
  have hc := chart_strict_pos11 (K-1) (J-1) (m-2) (t-4*grain K J*m)
    (by omega) (by omega) (by omega) (by omega)
  have eK : (1:ℤ)+(K-1)=K := by ring
  have eJ : (1:ℤ)+(J-1)=J := by ring
  have em : (2:ℤ)+(m-2)=m := by ring
  simp only [eK,eJ,em] at hc
  have et : 4*((4*K*J)*m)+(t-4*grain K J*m)=t := by dsimp [grain]; ring
  rw [et] at hc
  exact hc

private theorem corner_strict_pos1max (K J m t : ℤ)
    (hK : 1≤K) (hJ : 1≤J) (hm : 2≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J m t ((grain K J*m)-2*m+1) ((grain K J*m)-3) 1 (2*J) i := by
  have hc := chart_strict_pos1max (K-1) (J-1) (m-2) (t-4*grain K J*m)
    (by omega) (by omega) (by omega) (by omega)
  have eK : (1:ℤ)+(K-1)=K := by ring
  have eJ : (1:ℤ)+(J-1)=J := by ring
  have em : (2:ℤ)+(m-2)=m := by ring
  simp only [eK,eJ,em] at hc
  have et : 4*((4*K*J)*m)+(t-4*grain K J*m)=t := by dsimp [grain]; ring
  rw [et] at hc
  exact hc

private theorem corner_strict_posmax1 (K J m t : ℤ)
    (hK : 1≤K) (hJ : 1≤J) (hm : 2≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J m t ((grain K J*m)-2*m+1) ((grain K J*m)-3) (2*K) (1) i := by
  have hc := chart_strict_posmax1 (K-1) (J-1) (m-2) (t-4*grain K J*m)
    (by omega) (by omega) (by omega) (by omega)
  have eK : (1:ℤ)+(K-1)=K := by ring
  have eJ : (1:ℤ)+(J-1)=J := by ring
  have em : (2:ℤ)+(m-2)=m := by ring
  simp only [eK,eJ,em] at hc
  have et : 4*((4*K*J)*m)+(t-4*grain K J*m)=t := by dsimp [grain]; ring
  rw [et] at hc
  exact hc

private theorem corner_strict_posmaxmax (K J m t : ℤ)
    (hK : 1≤K) (hJ : 1≤J) (hm : 2≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J m t ((grain K J*m)-2*m+1) ((grain K J*m)-3) (2*K) (2*J) i := by
  have hc := chart_strict_posmaxmax (K-1) (J-1) (m-2) (t-4*grain K J*m)
    (by omega) (by omega) (by omega) (by omega)
  have eK : (1:ℤ)+(K-1)=K := by ring
  have eJ : (1:ℤ)+(J-1)=J := by ring
  have em : (2:ℤ)+(m-2)=m := by ring
  simp only [eK,eJ,em] at hc
  have et : 4*((4*K*J)*m)+(t-4*grain K J*m)=t := by dsimp [grain]; ring
  rw [et] at hc
  exact hc

private theorem corner_strict_boundary (K J m t : ℤ)
    (hK : 1≤K) (hJ : 1≤J) (hm : 2≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤boundaryMargin K J m i := by
  have hc := chart_strict_boundary (K-1) (J-1) (m-2) (t-4*grain K J*m)
    (by omega) (by omega) (by omega) (by omega)
  have eK : (1:ℤ)+(K-1)=K := by ring
  have eJ : (1:ℤ)+(J-1)=J := by ring
  have em : (2:ℤ)+(m-2)=m := by ring
  simp only [eK,eJ,em] at hc
  exact hc

private theorem corner_equality_Klarge_neg1 (K J m t : ℤ)
    (hK : 2≤K) (hJ : 1≤J) (hm : 1≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J 1 t (grain K J-3) (grain K J-3) 0 (1) i := by
  have hc := chart_equality_Klarge_neg1 (K-2) (J-1) 0 (t-4*grain K J)
    (by omega) (by omega) (by omega) (by
      have hp := mul_nonneg (show 0≤grain K J by dsimp [grain]; positivity) (show 0≤m-1 by omega)
      nlinarith only [ht,hp])
  have eK : (2:ℤ)+(K-2)=K := by ring
  have eJ : (1:ℤ)+(J-1)=J := by ring
  simp only [eK,eJ] at hc
  have et : 4*((4*K*J)*1)+(t-4*grain K J)=t := by dsimp [grain]; ring
  rw [et] at hc
  simpa only [mul_one] using hc

private theorem corner_equality_Klarge_pos11 (K J m t : ℤ)
    (hK : 2≤K) (hJ : 1≤J) (hm : 1≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J 1 t (grain K J-3) (grain K J-3) 1 (1) i := by
  have hc := chart_equality_Klarge_pos11 (K-2) (J-1) 0 (t-4*grain K J)
    (by omega) (by omega) (by omega) (by
      have hp := mul_nonneg (show 0≤grain K J by dsimp [grain]; positivity) (show 0≤m-1 by omega)
      nlinarith only [ht,hp])
  have eK : (2:ℤ)+(K-2)=K := by ring
  have eJ : (1:ℤ)+(J-1)=J := by ring
  simp only [eK,eJ] at hc
  have et : 4*((4*K*J)*1)+(t-4*grain K J)=t := by dsimp [grain]; ring
  rw [et] at hc
  simpa only [mul_one] using hc

private theorem corner_equality_Klarge_pos1max (K J m t : ℤ)
    (hK : 2≤K) (hJ : 1≤J) (hm : 1≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J 1 t (grain K J-3) (grain K J-3) 1 (2*J) i := by
  have hc := chart_equality_Klarge_pos1max (K-2) (J-1) 0 (t-4*grain K J)
    (by omega) (by omega) (by omega) (by
      have hp := mul_nonneg (show 0≤grain K J by dsimp [grain]; positivity) (show 0≤m-1 by omega)
      nlinarith only [ht,hp])
  have eK : (2:ℤ)+(K-2)=K := by ring
  have eJ : (1:ℤ)+(J-1)=J := by ring
  simp only [eK,eJ] at hc
  have et : 4*((4*K*J)*1)+(t-4*grain K J)=t := by dsimp [grain]; ring
  rw [et] at hc
  simpa only [mul_one] using hc

private theorem corner_equality_Klarge_posmax1 (K J m t : ℤ)
    (hK : 2≤K) (hJ : 1≤J) (hm : 1≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J 1 t (grain K J-3) (grain K J-3) (2*K) (1) i := by
  have hc := chart_equality_Klarge_posmax1 (K-2) (J-1) 0 (t-4*grain K J)
    (by omega) (by omega) (by omega) (by
      have hp := mul_nonneg (show 0≤grain K J by dsimp [grain]; positivity) (show 0≤m-1 by omega)
      nlinarith only [ht,hp])
  have eK : (2:ℤ)+(K-2)=K := by ring
  have eJ : (1:ℤ)+(J-1)=J := by ring
  simp only [eK,eJ] at hc
  have et : 4*((4*K*J)*1)+(t-4*grain K J)=t := by dsimp [grain]; ring
  rw [et] at hc
  simpa only [mul_one] using hc

private theorem corner_equality_Klarge_posmaxmax (K J m t : ℤ)
    (hK : 2≤K) (hJ : 1≤J) (hm : 1≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J 1 t (grain K J-3) (grain K J-3) (2*K) (2*J) i := by
  have hc := chart_equality_Klarge_posmaxmax (K-2) (J-1) 0 (t-4*grain K J)
    (by omega) (by omega) (by omega) (by
      have hp := mul_nonneg (show 0≤grain K J by dsimp [grain]; positivity) (show 0≤m-1 by omega)
      nlinarith only [ht,hp])
  have eK : (2:ℤ)+(K-2)=K := by ring
  have eJ : (1:ℤ)+(J-1)=J := by ring
  simp only [eK,eJ] at hc
  have et : 4*((4*K*J)*1)+(t-4*grain K J)=t := by dsimp [grain]; ring
  rw [et] at hc
  simpa only [mul_one] using hc

private theorem corner_equality_Klarge_boundary (K J m t : ℤ)
    (hK : 2≤K) (hJ : 1≤J) (hm : 1≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤boundaryMargin K J 1 i := by
  have hc := chart_equality_Klarge_boundary (K-2) (J-1) 0 (t-4*grain K J)
    (by omega) (by omega) (by omega) (by
      have hp := mul_nonneg (show 0≤grain K J by dsimp [grain]; positivity) (show 0≤m-1 by omega)
      nlinarith only [ht,hp])
  have eK : (2:ℤ)+(K-2)=K := by ring
  have eJ : (1:ℤ)+(J-1)=J := by ring
  simp only [eK,eJ] at hc
  simpa only [mul_one] using hc

private theorem corner_equality_Jlarge_neg1 (K J m t : ℤ)
    (hK : 1≤K) (hJ : 2≤J) (hm : 1≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J 1 t (grain K J-3) (grain K J-3) 0 (1) i := by
  have hc := chart_equality_Jlarge_neg1 (K-1) (J-2) 0 (t-4*grain K J)
    (by omega) (by omega) (by omega) (by
      have hp := mul_nonneg (show 0≤grain K J by dsimp [grain]; positivity) (show 0≤m-1 by omega)
      nlinarith only [ht,hp])
  have eK : (1:ℤ)+(K-1)=K := by ring
  have eJ : (2:ℤ)+(J-2)=J := by ring
  simp only [eK,eJ] at hc
  have et : 4*((4*K*J)*1)+(t-4*grain K J)=t := by dsimp [grain]; ring
  rw [et] at hc
  simpa only [mul_one] using hc

private theorem corner_equality_Jlarge_pos11 (K J m t : ℤ)
    (hK : 1≤K) (hJ : 2≤J) (hm : 1≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J 1 t (grain K J-3) (grain K J-3) 1 (1) i := by
  have hc := chart_equality_Jlarge_pos11 (K-1) (J-2) 0 (t-4*grain K J)
    (by omega) (by omega) (by omega) (by
      have hp := mul_nonneg (show 0≤grain K J by dsimp [grain]; positivity) (show 0≤m-1 by omega)
      nlinarith only [ht,hp])
  have eK : (1:ℤ)+(K-1)=K := by ring
  have eJ : (2:ℤ)+(J-2)=J := by ring
  simp only [eK,eJ] at hc
  have et : 4*((4*K*J)*1)+(t-4*grain K J)=t := by dsimp [grain]; ring
  rw [et] at hc
  simpa only [mul_one] using hc

private theorem corner_equality_Jlarge_pos1max (K J m t : ℤ)
    (hK : 1≤K) (hJ : 2≤J) (hm : 1≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J 1 t (grain K J-3) (grain K J-3) 1 (2*J) i := by
  have hc := chart_equality_Jlarge_pos1max (K-1) (J-2) 0 (t-4*grain K J)
    (by omega) (by omega) (by omega) (by
      have hp := mul_nonneg (show 0≤grain K J by dsimp [grain]; positivity) (show 0≤m-1 by omega)
      nlinarith only [ht,hp])
  have eK : (1:ℤ)+(K-1)=K := by ring
  have eJ : (2:ℤ)+(J-2)=J := by ring
  simp only [eK,eJ] at hc
  have et : 4*((4*K*J)*1)+(t-4*grain K J)=t := by dsimp [grain]; ring
  rw [et] at hc
  simpa only [mul_one] using hc

private theorem corner_equality_Jlarge_posmax1 (K J m t : ℤ)
    (hK : 1≤K) (hJ : 2≤J) (hm : 1≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J 1 t (grain K J-3) (grain K J-3) (2*K) (1) i := by
  have hc := chart_equality_Jlarge_posmax1 (K-1) (J-2) 0 (t-4*grain K J)
    (by omega) (by omega) (by omega) (by
      have hp := mul_nonneg (show 0≤grain K J by dsimp [grain]; positivity) (show 0≤m-1 by omega)
      nlinarith only [ht,hp])
  have eK : (1:ℤ)+(K-1)=K := by ring
  have eJ : (2:ℤ)+(J-2)=J := by ring
  simp only [eK,eJ] at hc
  have et : 4*((4*K*J)*1)+(t-4*grain K J)=t := by dsimp [grain]; ring
  rw [et] at hc
  simpa only [mul_one] using hc

private theorem corner_equality_Jlarge_posmaxmax (K J m t : ℤ)
    (hK : 1≤K) (hJ : 2≤J) (hm : 1≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤scaledMargin K J 1 t (grain K J-3) (grain K J-3) (2*K) (2*J) i := by
  have hc := chart_equality_Jlarge_posmaxmax (K-1) (J-2) 0 (t-4*grain K J)
    (by omega) (by omega) (by omega) (by
      have hp := mul_nonneg (show 0≤grain K J by dsimp [grain]; positivity) (show 0≤m-1 by omega)
      nlinarith only [ht,hp])
  have eK : (1:ℤ)+(K-1)=K := by ring
  have eJ : (2:ℤ)+(J-2)=J := by ring
  simp only [eK,eJ] at hc
  have et : 4*((4*K*J)*1)+(t-4*grain K J)=t := by dsimp [grain]; ring
  rw [et] at hc
  simpa only [mul_one] using hc

private theorem corner_equality_Jlarge_boundary (K J m t : ℤ)
    (hK : 1≤K) (hJ : 2≤J) (hm : 1≤m)
    (ht : 4*grain K J*m≤t) :
    ∀ i : Fin 4, 0≤boundaryMargin K J 1 i := by
  have hc := chart_equality_Jlarge_boundary (K-1) (J-2) 0 (t-4*grain K J)
    (by omega) (by omega) (by omega) (by
      have hp := mul_nonneg (show 0≤grain K J by dsimp [grain]; positivity) (show 0≤m-1 by omega)
      nlinarith only [ht,hp])
  have eK : (1:ℤ)+(K-1)=K := by ring
  have eJ : (2:ℤ)+(J-2)=J := by ring
  simp only [eK,eJ] at hc
  simpa only [mul_one] using hc

private theorem strict_scaled (K J m t h r : ℤ) (hK : 1≤K) (hJ : 1≤J)
    (hm : 2≤m) (ht : 4*grain K J*m≤t)
    (hr : (h=0 ∧ 1≤r ∧ r≤grain K J) ∨
      (1≤h ∧ h≤2*K ∧ 1≤r ∧ r≤2*J)) :
    ∀ i,0≤scaledMargin K J m t (grain K J*m-2*m+1) (grain K J*m-3) h r i := by
  rcases hr with ⟨rfl,hr0,hr1⟩|⟨hh0,hh1,hr0,hr1⟩
  · exact scaled_rectangle K J m t _ _ 0 0 1 (grain K J) 0 r
      ⟨le_rfl,le_rfl⟩ ⟨hr0,hr1⟩
      (corner_strict_neg1 K J m t hK hJ hm ht)
      (corner_strict_negg K J m t hK hJ hm ht)
      (corner_strict_neg1 K J m t hK hJ hm ht)
      (corner_strict_negg K J m t hK hJ hm ht)
  · exact scaled_rectangle K J m t _ _ 1 (2*K) 1 (2*J) h r
      ⟨hh0,hh1⟩ ⟨hr0,hr1⟩
      (corner_strict_pos11 K J m t hK hJ hm ht)
      (corner_strict_pos1max K J m t hK hJ hm ht)
      (corner_strict_posmax1 K J m t hK hJ hm ht)
      (corner_strict_posmaxmax K J m t hK hJ hm ht)

private theorem equality_large_cases (K J : ℤ) (hK : 1≤K) (hJ : 1≤J)
    (hg : 8≤grain K J) : 2≤K ∨ 2≤J := by
  by_contra hh
  have hK1 : K=1 := by omega
  have hJ1 : J=1 := by omega
  simp [grain,hK1,hJ1] at hg

private theorem equality_scaled (K J t h r : ℤ) (hK : 1≤K) (hJ : 1≤J)
    (hg : 8≤grain K J) (ht : 4*grain K J≤t)
    (hr : (h=0 ∧ r=1) ∨ (1≤h ∧ h≤2*K ∧ 1≤r ∧ r≤2*J)) :
    ∀ i,0≤scaledMargin K J 1 t (grain K J-3) (grain K J-3) h r i := by
  rcases equality_large_cases K J hK hJ hg with hK2|hJ2
  · rcases hr with ⟨rfl,rfl⟩|⟨hh0,hh1,hr0,hr1⟩
    · exact corner_equality_Klarge_neg1 K J 1 t hK2 hJ (by omega) (by simpa using ht)
    · exact scaled_rectangle K J 1 t _ _ 1 (2*K) 1 (2*J) h r
        ⟨hh0,hh1⟩ ⟨hr0,hr1⟩
        (corner_equality_Klarge_pos11 K J 1 t hK2 hJ (by omega) (by simpa using ht))
        (corner_equality_Klarge_pos1max K J 1 t hK2 hJ (by omega) (by simpa using ht))
        (corner_equality_Klarge_posmax1 K J 1 t hK2 hJ (by omega) (by simpa using ht))
        (corner_equality_Klarge_posmaxmax K J 1 t hK2 hJ (by omega) (by simpa using ht))
  · rcases hr with ⟨rfl,rfl⟩|⟨hh0,hh1,hr0,hr1⟩
    · exact corner_equality_Jlarge_neg1 K J 1 t hK hJ2 (by omega) (by simpa using ht)
    · exact scaled_rectangle K J 1 t _ _ 1 (2*K) 1 (2*J) h r
        ⟨hh0,hh1⟩ ⟨hr0,hr1⟩
        (corner_equality_Jlarge_pos11 K J 1 t hK hJ2 (by omega) (by simpa using ht))
        (corner_equality_Jlarge_pos1max K J 1 t hK hJ2 (by omega) (by simpa using ht))
        (corner_equality_Jlarge_posmax1 K J 1 t hK hJ2 (by omega) (by simpa using ht))
        (corner_equality_Jlarge_posmaxmax K J 1 t hK hJ2 (by omega) (by simpa using ht))

private theorem equality_boundary (K J : ℤ) (hK : 1≤K) (hJ : 1≤J)
    (hg : 8≤grain K J) : ∀ i,0≤boundaryMargin K J 1 i := by
  rcases equality_large_cases K J hK hJ hg with hK2|hJ2
  · exact corner_equality_Klarge_boundary K J 1 (4*grain K J) hK2 hJ (by omega) (by simp)
  · exact corner_equality_Jlarge_boundary K J 1 (4*grain K J) hK hJ2 (by omega) (by simp)

private theorem positive_cancel (b x : ℤ) (hb : 0<b) (hx : 0≤b*x) : 0≤x := by
  by_contra hh
  have hn := mul_neg_of_pos_of_neg hb (show x<0 by omega)
  omega

-- Recover the four literal, unscaled inequalities from the selected native v.
private theorem scaled_to_rectangle (K J m t h r v j lo hi : ℤ)
    (hK : 1≤K) (hJ : 1≤J) (hm : 1≤m) (ht : 0≤t)
    (hj : lo≤j ∧ j≤hi)
    (hv : pivot K J m t h r-j=2*(grain K J*m+1)*v)
    (hc : ∀ i,0≤scaledMargin K J m t lo hi h r i) :
    ∀ i,0≤rectangleMargin (grain K J*t) (2*K*t) (grain K J*m) t
      (grain K J) (reserve K J t) (reserve K J t+r) r h v i := by
  let g := grain K J
  let z := g*m
  let aa := A (g*t) (2*K*t) z
  have hβ : 0<z+1 := by dsimp [z,g,grain]; positivity
  have hA : 0≤aa := by dsimp [aa,A,D,z,g,grain]; positivity
  have hlo := mul_nonneg hA (show 0≤j-lo by omega)
  have hhi := mul_nonneg hA (show 0≤hi-j by omega)
  have heq (i : Fin 4) :
      (z+1)*rectangleMargin (g*t) (2*K*t) z t g (reserve K J t)
        (reserve K J t+r) r h v i =
      scaledMargin K J m t lo hi h r i+
        if i=0 ∨ i=2 then aa*(j-lo) else aa*(hi-j) := by
    fin_cases i <;> simp [rectangleMargin,scaledMargin,E0,H0,pivot,z,g,aa,Mn,Ln]
    all_goals
      dsimp [pivot,grain] at hv
      first
      | linear_combination (A (grain K J*t) (2*K*t) (grain K J*m))*hv
      | linear_combination -(A (grain K J*t) (2*K*t) (grain K J*m))*hv
  intro i
  apply positive_cancel (z+1) _ hβ
  rw [heq]
  split_ifs <;> linarith only [hc i,hlo,hhi]

-- Integer divisibility produces an actual v, with no hidden rounding choice.
private theorem native_v (z t p j β : ℤ) (hz : 8≤z) (ht : 4*z≤t)
    (hβ : β=z+1) (hl : t-2*z+2≤p-j) (hu : p-j≤t+2*z)
    (hd : 2*β∣p-j) : ∃ v : ℤ, 0≤v ∧ 2*v≤t-2 ∧ p-j=2*β*v := by
  obtain ⟨v,hv⟩ := hd
  have hb : 0<β := by omega
  have cap : t+2*z≤β*(t-2) := by
    have hp := mul_nonneg (show 0≤z by omega) (show 0≤t-5 by omega)
    rw [hβ]; nlinarith only [hp,hz]
  have hv0 : 0≤v := by
    by_contra hh
    have hp := mul_neg_of_pos_of_neg (show 0<2*β by omega) (show v<0 by omega)
    nlinarith only [hp,hv,hl,ht,hz]
  have hv1 : 2*v≤t-2 := by
    by_contra hh
    have hp := mul_lt_mul_of_pos_left (show t-2<2*v by omega) hb
    nlinarith only [hp,hv,hu,cap]
  exact ⟨v,hv0,hv1,hv⟩

private theorem selected_rectangle (K J m t τ : ℤ)
    (hK : 1≤K) (hJ : 1≤J) (hm : 1≤m) (hz : 8≤grain K J*m)
    (ht : t=2*τ) (hcases : t=2*(grain K J*m) ∨ 4*(grain K J*m)≤t)
    (hregion : 2≤m ∨ (m=1 ∧ 8≤grain K J))
    (hex : ¬(grain K J*m+1)∣τ) :
    ∃ h r v : ℤ, 0≤h ∧ 1≤r ∧ r≤grain K J ∧ 0≤v ∧ 2*v≤t-2 ∧
      2*(grain K J*m)*(h+1)≤2*K*t ∧
      ∀ i,0≤rectangleMargin (grain K J*t) (2*K*t) (grain K J*m) t
        (grain K J) (reserve K J t) (reserve K J t+r) r h v i := by
  let g := grain K J
  let z := g*m
  have ez : z=g*m := rfl
  change 8≤z at hz
  have hg : 4≤g := by
    have hp := mul_nonneg (show 0≤K-1 by omega) (show 0≤J by omega)
    dsimp [g,grain]; nlinarith only [hp,hJ]
  rcases hcases with hb|ht4
  · change t=2*z at hb
    refine ⟨0,g,0,by omega,by omega,le_rfl,by omega,by omega,?_,?_⟩
    · dsimp [z,g] at *
      rw [hb]
      have hp := mul_nonneg (show 0≤grain K J*m by omega) (show 0≤2*K-1 by omega)
      nlinarith only [hp]
    · rw [hb]
      rcases hregion with hm2|⟨rfl,hg8⟩
      · exact corner_strict_boundary K J m (4*grain K J*m) hK hJ hm2 (by omega)
      · exact equality_boundary K J hK hJ hg8
  · change 4*z≤t at ht4
    have hτ : 0≤τ := by omega
    have choose_n : ∃ n j : ℤ, -g≤n ∧ n<g ∧
        (if m=1 then z-3 else z-2*m+1)≤j ∧ j≤z-3 ∧
        (2*(z+1))∣(t+z-1+2*m*n-j) ∧ (m=1 → -1≤n) := by
      rcases hregion with hm2|⟨hm1,hg8⟩
      · have hG : 2≤2*K*J := by dsimp [g,grain] at hg; nlinarith only [hg]
        obtain ⟨n,l,hn0,hn1,hl0,hl1,hd⟩ :=
          cyclic_cover (2*K*J) m τ hG hm2 (by
            have he : 2*(2*K*J)*m+1=grain K J*m+1 := by dsimp [grain]; ring
            rw [he]; exact hex)
        refine ⟨n,2*l+1,?_,?_,?_,?_,?_,by omega⟩
        · dsimp [g,grain]; nlinarith only [hn0]
        · dsimp [g,grain]; nlinarith only [hn1]
        · rw [if_neg (by omega : m≠1)]; dsimp [z,g,grain]; nlinarith only [hl0]
        · dsimp [z,g,grain]; nlinarith only [hl1]
        · obtain ⟨w,hw⟩ := hd
          refine ⟨w,?_⟩
          dsimp [z,g,grain] at *
          linear_combination 2*hw+ht
      · obtain ⟨n,hn0,hn1,hd⟩ := equality_residue g τ (by omega)
        refine ⟨n,z-3,by omega,hn1,by simp [hm1],le_rfl,?_,by omega⟩
        obtain ⟨w,hw⟩ := hd
        refine ⟨w,?_⟩
        dsimp [z] at *
        rw [hm1] at *
        linear_combination 2*hw+ht
    obtain ⟨n,j,hn0,hn1,hj0,hj1,hd,hneq⟩ := choose_n
    obtain ⟨h,r,hh0,hr0,hr1,hn,hhcase⟩ := native_hr K J n hK hJ ⟨hn0,hn1⟩
    have hh2 : h≤2*K := by
      rcases hhcase with ⟨_,he,_⟩|hh
      · rw [he]; omega
      · exact hh.2.2.1
    have hlow : t-2*z+2≤t+z-1+2*m*n-j := by
      have hp := mul_le_mul_of_nonneg_left hn0 (show 0≤2*m by omega)
      nlinarith only [hp,hj1,ez]
    have hupp : t+z-1+2*m*n-j≤t+2*z := by
      have hp := mul_le_mul_of_nonneg_left (show n≤g-1 by omega) (show 0≤2*m by omega)
      have hjlo : z-2*m-1≤j := by split_ifs at hj0 <;> omega
      by_cases hm1 : m=1
      · have hj : j=z-3 := by
          have hjlo : z-3≤j := by simpa [hm1] using hj0
          omega
        have ez1 : z=g := by rw [hm1,mul_one] at ez; exact ez
        rw [hm1] at hp ⊢
        nlinarith only [hp,hj,ez1]
      · have hjlo' : z-2*m+1≤j := by simpa [hm1] using hj0
        nlinarith only [hp,hjlo',ez]
    obtain ⟨v,hv0,hv1,hv⟩ := native_v z t (t+z-1+2*m*n) j (z+1) hz ht4 rfl hlow hupp hd
    have hcap : 2*z*(h+1)≤2*K*t := by
      have ha := mul_nonneg (show 0≤2*z by omega) (show 0≤2*K-h by omega)
      have hb := mul_nonneg (show 0≤2*z by omega) (show 0≤2*K-1 by omega)
      have hc := mul_nonneg (show 0≤2*K by omega) (show 0≤t-4*z by omega)
      nlinarith only [ha,hb,hc]
    refine ⟨h,r,v,hh0,hr0,hr1,hv0,hv1,hcap,?_⟩
    apply scaled_to_rectangle K J m t h r v j
      (if m=1 then z-3 else z-2*m+1) (z-3) hK hJ hm (by omega) ⟨hj0,hj1⟩
    · dsimp [pivot]; rw [←hn]; exact hv
    · by_cases hm1 : m=1
      · have ez1 : z=grain K J := by dsimp [z,g]; rw [hm1]; ring
        rw [hm1,if_pos rfl,ez1]
        apply equality_scaled K J t h r hK hJ (by simpa only [ez1] using hz) (by simpa only [ez1] using ht4)
        rcases hhcase with ⟨hnneg,rfl,hrr⟩|hh
        · exact Or.inl ⟨rfl,by have := hneq hm1; omega⟩
        · exact Or.inr ⟨hh.2.1,hh.2.2.1,hr0,hh.2.2.2⟩

      · rw [if_neg hm1]
        apply strict_scaled K J m t h r hK hJ (by rcases hregion with hh|hh; exact hh; omega) ht4
        rcases hhcase with ⟨_,rfl,_⟩|hh
        · exact Or.inl ⟨rfl,hr0,hr1⟩
        · exact Or.inr ⟨hh.2.1,hh.2.2.1,hr0,hh.2.2.2⟩

-- Pure arithmetic bridge; this is not the physical-prefix or inventory proof.
private theorem rectangle_to_twelve (x y z t g q s r h v : ℤ)
    (hz : 4≤z) (ht : 2*z≤t) (hy : 2*t≤y) (hx : 2*y≤x)
    (hq : 2*q=x-2*g) (hqr : s=q+r) (hq0 : 0≤q)
    (hr : 1≤r) (hs : 2*s≤x) (hh : 0≤h) (hcap : 2*z*(h+1)≤y)
    (hc : ∀ i,0≤rectangleMargin x y z t g q s r h v i) :
    ∀ i,0≤gateMargin x y z t s r h v i := by
  let aa := A x y z
  let dd := D y z
  let ll := L x z t
  let mm := M y z t
  let cc := C x y z t g
  let e := (t-2*v)*aa-2*s*mm+2*h*ll
  let κ := r*dd-h*(z+1)
  let τ := s*dd-h*(z+1)
  let gg := B x y t+ll-2*v*aa-2*r*mm+2*h*ll
  have hx0 : 0≤x := by omega
  have hy0 : 0≤y := by omega
  have ht0 : 0≤t := by omega
  have hz0 : 0≤z := by omega
  have hD : 0≤dd := by dsimp [dd,D]; positivity
  have hA : 1≤aa := by dsimp [aa,A]; have := mul_nonneg hx0 hD; omega
  have hL : 0≤ll := by dsimp [ll,L]; positivity
  have hyh : 1≤y-h := by
    have hp := mul_nonneg (show 0≤2*z-1 by omega) (show 0≤h+1 by omega)
    nlinarith only [hp,hcap]
  have hκ : z+2≤κ := by
    have hp := mul_nonneg (show 0≤r-1 by omega) hD
    have hp' := mul_nonneg (show 0≤y-h-1 by omega) (show 0≤z+1 by omega)
    have he : κ-(z+2)=(r-1)*dd+(y-h-1)*(z+1) := by dsimp [κ,dd,D]; ring
    linarith only [hp,hp',he]
  have hκτ : κ≤τ := by
    have hp := mul_nonneg (show 0≤s-r by omega) hD
    dsimp [κ,τ]; nlinarith only [hp]
  have hτ : 2*τ≤aa-1 := by
    have hp := mul_nonneg (show 0≤x-2*s by omega) hD
    have hp' := mul_nonneg hh (show 0≤z+1 by omega)
    dsimp [τ,aa,A,dd] at *
    nlinarith only [hp,hp']
  have htκ : τ=q*dd+κ := by dsimp [τ,κ]; rw [hqr]; ring
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have c3 := hc 3
  change 0≤e+cc at c0
  change 0≤aa-1-e at c1
  change 0≤e+κ-aa+q*dd at c2
  change 0≤ll-cc-(e+κ) at c3
  have he : aa-τ≤e := by linarith only [c2,htκ]
  have he0 : 0≤e := by omega
  have hgg : gg=e+cc := by
    dsimp [gg,e,cc,aa,ll,mm,C,A,B,D,L,M]
    rw [hqr]
    linear_combination (t*y*z+y*(z+1)+1)*hq
  have hg0 : 0≤gg := by rw [hgg]; exact c0
  have hg1 : gg≤ll-κ := by rw [hgg]; linarith only [c3]
  have f1 : 2*((t-1-2*v)*aa-s*Mn y z t+h*Ln x z t)=2*(e-aa+τ) := by
    dsimp [e,τ,Mn,Ln,mm,ll,dd]; ring
  have f2 : Bn x y t+Ln x z t-4*v*aa-2*r*Mn y z t+2*h*Ln x z t
      =2*gg+2*κ-z-2 := by
    dsimp [gg,κ,Bn,Ln,Mn,dd,ll]; ring
  have ht2 : 0≤t-2 := by omega
  have hz1 : 0≤z-1 := by omega
  have hLM : 0≤ll-mm := by
    have p0 := mul_nonneg (show 0≤x-2*y by omega) (show 0≤z*t by positivity)
    have p1 := mul_nonneg hy0 (show 0≤z*(t-2)+(z-1) by positivity)
    have hid : ll-mm=(x-2*y)*z*t+y*(z*(t-2)+(z-1))+z*t+z := by
      dsimp [ll,mm,L,M,D]; ring
    nlinarith only [p0,p1,hid,show 0≤z*t by positivity,hz0]
  have hnewLM : 0≤Ln x z t-Mn y z t := by
    have hp := mul_nonneg (show 0≤y-1 by omega) (show 0≤z+1 by omega)
    have hid : Ln x z t-Mn y z t=2*(ll-mm)+(y-1)*(z+1)+1 := by
      dsimp [Ln,Mn,ll,mm,D]; ring
    linarith only [hLM,hp,hid]
  have hLn : 0≤Ln x z t := by dsimp [Ln,L]; nlinarith only [hL,hz,show 0≤x*z*t by positivity,show 0≤z*t by positivity]
  have h3lo : 0≤2*(h+1)*ll-2*mm := by
    have hp := mul_nonneg hh hL
    nlinarith only [hp,hLM]
  have hn3lo : 0≤2*((h+1)*Ln x z t-Mn y z t) := by
    have hp := mul_nonneg hh hLn
    nlinarith only [hp,hnewLM]
  have pz1 : 0≤2*z-1 := by omega
  have pz2 : 0≤2*z^2+z-1 := by nlinarith only [sq_nonneg z,hz]
  have oldslack : 0≤z*(B x y t-1+2*mm)-y*ll := by
    have hid : z*(B x y t-1+2*mm)-y*ll=
        x*z*t+z*t+t*y*z*(2*z-1)+y*(2*z^2+z-1)+2*z := by
      dsimp [B,mm,ll,M,L,D]; ring
    rw [hid]; positivity
  have newslack : 0≤z*(Bn x y t-1+2*Mn y z t)-y*Ln x z t := by
    have hid : z*(Bn x y t-1+2*Mn y z t)-y*Ln x z t=
        2*x*z*t+2*z*t+2*t*y*z*(2*z-1)+y*(2*z^2+z-1)+2*z := by
      dsimp [Bn,B,Mn,Ln,M,L,D]; ring
    rw [hid]; positivity
  have h3hi : 0≤B x y t-1-(2*(h+1)*ll-2*mm) := by
    apply positive_cancel z _ (by omega)
    have hp := mul_nonneg (show 0≤y-2*z*(h+1) by omega) hL
    nlinarith only [oldslack,hp]
  have hn3hi : 0≤Bn x y t-1-2*((h+1)*Ln x z t-Mn y z t) := by
    apply positive_cancel z _ (by omega)
    have hp := mul_nonneg (show 0≤y-2*z*(h+1) by omega) hLn
    nlinarith only [newslack,hp]
  intro i
  fin_cases i
  · exact he0
  · exact c1
  · change 0≤2*((t-1-2*v)*aa-s*Mn y z t+h*Ln x z t)
    rw [f1]; omega
  · change 0≤aa-1-2*((t-1-2*v)*aa-s*Mn y z t+h*Ln x z t)
    rw [f1]; omega
  · exact hg0
  · change 0≤ll-1-gg; omega
  · change 0≤Bn x y t+Ln x z t-4*v*aa-2*r*Mn y z t+2*h*Ln x z t
    rw [f2]; omega
  · change 0≤Ln x z t-1-(Bn x y t+Ln x z t-4*v*aa-2*r*Mn y z t+2*h*Ln x z t)
    rw [f2]
    change 0≤(2*ll-z-1)-1-(2*gg+2*κ-z-2)
    omega
  · exact h3lo
  · exact h3hi
  · exact hn3lo
  · exact hn3hi

private theorem no_carry_submask (k q u : ℕ) (hq : 2^k∣q) (hu : u<2^k) :
    ∀ e : ℕ, u.testBit e=true → (q+u).testBit e=true := by
  have hm : (q+u)%2^k=u := by
    rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd hq,Nat.mod_eq_of_lt hu,zero_add,
      Nat.mod_eq_of_lt hu]
  intro e he
  by_cases hek : e<k
  · have hb := congrArg (fun n : ℕ => n.testBit e) hm
    simpa only [Nat.testBit_mod_two_pow,decide_eq_true hek,Bool.true_and,he] using hb
  · have hp : 2^k≤(2:ℕ)^e := Nat.pow_le_pow_right (by decide) (by omega)
    have hf := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hu hp)
    rw [hf] at he
    contradiction

private theorem dyadic_grain (a b d : ℕ) (hdb : d<b) (hba : b<a) :
    grain ((2:ℤ)^(b-d-1)) ((2:ℤ)^(a-b-1))=(2:ℤ)^(a-d) := by
  calc
    _ = (2:ℤ)^((b-d-1)+(a-b-1)+2) := by
      simp only [grain,pow_add]
      norm_num
      ring
    _ = _ := by congr 1; omega

private theorem dyadic_half (n : ℕ) (hn : 1≤n) :
    (2:ℤ)^n=2*(2:ℤ)^(n-1) := by
  conv_lhs => rw [show n=(n-1)+1 by omega,pow_succ]
  ring

private theorem dyadic_two_or_four (c d : ℕ) (hcd : c<d) :
    (2:ℤ)^d=2*(2:ℤ)^c ∨ 4*(2:ℤ)^c≤(2:ℤ)^d := by
  by_cases hd : d=c+1
  · left; rw [hd,pow_succ]; ring
  · right
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show c+2≤d by omega)
    have he : (2:ℤ)^(c+2)=4*(2:ℤ)^c := by rw [pow_add]; norm_num; ring
    rw [he] at hp
    exact hp

-- This private record is the complete arithmetic interface. No certificate,
-- feasibility predicate or physical endpoint is assumed in its constructor.
private structure ParameterChoice (a b c d : ℕ) where
  s : ℕ
  r : ℕ
  v : ℕ
  h : ℕ
  r_pos : 1≤r
  r_le_s : r≤s
  s_cap : s≤2^(a-1)
  v_cap : v<2^(d-1)
  h_cap : h<2^(b-c-1)
  submask : ∀ e : ℕ, (r-1).testBit e=true → (s-1).testBit e=true
  reserve_eq : (s:ℤ)=(2:ℤ)^(a-1)-(2:ℤ)^(a-d)+(r:ℤ)
  grain_cap : (r:ℤ)≤(2:ℤ)^(a-d)
  rectangle : ∀ i,0≤rectangleMargin ((2:ℤ)^a) ((2:ℤ)^b) ((2:ℤ)^c) ((2:ℤ)^d)
    ((2:ℤ)^(a-d)) ((2:ℤ)^(a-1)-(2:ℤ)^(a-d)) s r h v i
  gates : ∀ i,0≤gateMargin ((2:ℤ)^a) ((2:ℤ)^b) ((2:ℤ)^c) ((2:ℤ)^d) s r h v i

private theorem parameterChoice (a b c d : ℕ) (hc : 3≤c) (hcd : c<d)
    (hdb : d<b) (hba : b<a) (hdiag : a≤c+d) : Nonempty (ParameterChoice a b c d) := by
  let K : ℤ := 2^(b-d-1)
  let J : ℤ := 2^(a-b-1)
  let k := a-d
  let g := grain K J
  let m : ℤ := 2^(c-k)
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let t : ℤ := 2^d
  let τ : ℤ := 2^(d-1)
  have hK : 1≤K := by dsimp [K]; exact one_le_pow₀ (by norm_num)
  have hJ : 1≤J := by dsimp [J]; exact one_le_pow₀ (by norm_num)
  have hm : 1≤m := by dsimp [m]; exact one_le_pow₀ (by norm_num)
  have hk : 2≤k ∧ k≤c := by dsimp [k]; omega
  have hgpow : g=(2:ℤ)^k := dyadic_grain a b d hdb hba
  have hxt : x=g*t := by
    rw [hgpow]; dsimp [x,t,k]
    rw [←pow_add]; congr 1; omega
  have hyt : y=2*K*t := by
    calc
      y = (2:ℤ)^((b-d-1)+d+1) := by dsimp [y]; congr 1; omega
      _ = 2*K*t := by dsimp [K,t]; simp only [pow_add,pow_one]; ring
  have hzm : z=g*m := by
    rw [hgpow]; dsimp [z,m]
    rw [←pow_add]; congr 1; omega
  have hτ : t=2*τ := dyadic_half d (by omega)
  have hz8 : 8≤z := by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hc
    norm_num at hp
    exact hp
  have ht0 : 0≤t := by dsimp [t]; positivity
  have ht2 : 2*z≤t := by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show c+1≤d by omega)
    simpa [z,t,pow_succ,mul_comm] using hp
  have hy2 : 2*t≤y := by
    have hp := mul_nonneg (show 0≤2*t by positivity) (show 0≤K-1 by omega)
    rw [hyt]; nlinarith only [hp]
  have hx2 : 2*y≤x := by
    have hp := mul_nonneg (show 0≤4*K*t by positivity) (show 0≤J-1 by omega)
    rw [hxt,hyt]; dsimp [g,grain]; nlinarith only [hp]
  have hcases : t=2*(grain K J*m) ∨ 4*(grain K J*m)≤t := by
    rw [←hzm]
    exact dyadic_two_or_four c d hcd
  have hregion : 2≤m ∨ (m=1 ∧ 8≤grain K J) := by
    by_cases hkc : k=c
    · right
      have hm1 : m=1 := by simp [m,hkc]
      exact ⟨hm1,by rw [hm1,mul_one] at hzm; rw [←hzm]; exact hz8⟩
    · left
      have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤c-k by omega)
      norm_num at hp
      exact hp
  have hex : ¬(grain K J*m+1)∣τ := by
    rw [←hzm]
    exact odd_successor_not_dvd_pow c (d-1) (by omega)
  obtain ⟨h,r,v,hh0,hr0,hr1,hv0,hv1,hcap,hrect⟩ :=
    selected_rectangle K J m t τ hK hJ hm (by rw [←hzm]; exact hz8)
      hτ hcases hregion hex
  let qN : ℕ := 2^k*(2^(d-1)-1)
  let rN := r.toNat
  let vN := v.toNat
  let hN := h.toNat
  let sN := qN+rN
  have er : (rN:ℤ)=r := Int.toNat_of_nonneg (by omega)
  have ev : (vN:ℤ)=v := Int.toNat_of_nonneg hv0
  have eh : (hN:ℤ)=h := Int.toNat_of_nonneg hh0
  have eqN : (qN:ℤ)=reserve K J t := by
    dsimp [qN]
    rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    rw [←hgpow]
    dsimp [reserve]
    rw [hτ]
    dsimp [g,grain,τ]; ring
  have es : (sN:ℤ)=reserve K J t+r := by
    dsimp [sN]; push_cast; rw [eqN,er]
  have hqplus : qN+2^k=2^(a-1) := by
    calc
      qN+2^k = 2^k*((2^(d-1)-1)+1) := by dsimp [qN]; ring
      _ = 2^k*2^(d-1) := by rw [Nat.sub_add_cancel Nat.one_le_two_pow]
      _ = 2^(a-1) := by rw [←pow_add]; congr 1; dsimp [k]; omega
  have hqreal : reserve K J t=(2:ℤ)^(a-1)-g := by
    have heq : (qN:ℤ)+(2:ℤ)^k=(2:ℤ)^(a-1) := by exact_mod_cast hqplus
    rw [eqN,←hgpow] at heq
    linarith only [heq]
  have hrN0 : 1≤rN := by exact_mod_cast (show (1:ℤ)≤(rN:ℤ) by rw [er]; exact hr0)
  have hrNk : rN≤2^k := by
    have heq : (rN:ℤ)≤(2:ℤ)^k := by rw [er,←hgpow]; exact hr1
    exact_mod_cast heq
  have hsN : sN≤2^(a-1) := by dsimp [sN]; omega
  have hvs : vN<2^(d-1) := by
    have hvt : v<τ := by omega
    have heq : (vN:ℤ)<(2:ℤ)^(d-1) := by rw [ev]; exact hvt
    exact_mod_cast heq
  have hR : y=2*z*(2:ℤ)^(b-c-1) := by
    calc
      y = (2:ℤ)^(c+(b-c-1)+1) := by dsimp [y]; congr 1; omega
      _ = 2*z*(2:ℤ)^(b-c-1) := by dsimp [z]; simp only [pow_add,pow_one]; ring
  have hhs : hN<2^(b-c-1) := by
    have heq : h<(2:ℤ)^(b-c-1) := by
      by_contra hn
      have hp := mul_pos (show 0<2*z by omega)
        (show 0<h+1-(2:ℤ)^(b-c-1) by omega)
      rw [←hzm,←hyt] at hcap
      nlinarith only [hp,hcap,hR]
    exact_mod_cast (show (hN:ℤ)<(2:ℤ)^(b-c-1) by rw [eh]; exact heq)
  have hsub : ∀ e : ℕ, (rN-1).testBit e=true → (sN-1).testBit e=true := by
    have hsub' := no_carry_submask k qN (rN-1) ⟨2^(d-1)-1,rfl⟩ (by omega)
    have heq : sN-1=qN+(rN-1) := by dsimp [sN]; omega
    rw [heq]; exact hsub'
  have hrectN : ∀ i,0≤rectangleMargin x y z t g (reserve K J t) sN rN hN vN i := by
    rw [es,er,eh,ev,hxt,hyt,hzm]
    exact hrect
  have hq0 : 0≤reserve K J t := by rw [←eqN]; positivity
  have hq : 2*reserve K J t=x-2*g := by dsimp [reserve,g,grain]; rw [hxt]; dsimp [g,grain]; ring
  have hss : 2*(sN:ℤ)≤x := by
    have heq : (sN:ℤ)≤(2:ℤ)^(a-1) := by exact_mod_cast hsN
    have hh := dyadic_half a (by omega)
    dsimp [x]; omega
  have hgateN : ∀ i,0≤gateMargin x y z t sN rN hN vN i := by
    apply rectangle_to_twelve x y z t g (reserve K J t) sN rN hN vN
      (by omega) ht2 hy2 hx2 hq (by rw [es,er]) hq0
      (by rw [er]; exact hr0) hss (by rw [eh]; exact hh0)
      (by rw [eh,hzm,hyt]; exact hcap) hrectN
  refine ⟨{ s:=sN, r:=rN, v:=vN, h:=hN, r_pos:=hrN0,
    r_le_s:=by dsimp [sN]; omega, s_cap:=hsN, v_cap:=hvs, h_cap:=hhs,
    submask:=hsub, reserve_eq:=?_, grain_cap:=?_, rectangle:=?_, gates:=hgateN }⟩
  · rw [es,hqreal,er,hgpow]
  · rw [er,←hgpow]; exact hr1
  · rw [←hgpow,←hqreal]
    exact hrectN

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal
