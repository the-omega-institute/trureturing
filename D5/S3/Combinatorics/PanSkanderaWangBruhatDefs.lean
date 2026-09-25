/- GID: D5/S3/Combinatorics/PanSkanderaWangBruhatDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PanSkanderaWangBruhatDefs
   mirror-E: none(waiver:fixed-public-definitions-for-the-psw-bruhat-conjecture)
   anchors: [mathlib/module/Mathlib.Data.List.Range]
   utility: none
   digest: Defines the Pan-Skandera-Wang map and its Bruhat claim. -/

import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Range

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PanSkanderaWangBruhat

/-! Fixed public statement for Pan-Skandera-Wang Conjecture 7.8 (arXiv:2606.13162v1, Section 7).
    Permutations are lists in one-line notation, positions numbered from 1. -/

/-- `rank x p q = #{j <= p : x_j >= q}` (Bjorner-Brenti, Theorem 2.1.5 notation `x[p,q]`). -/
def rank (x : List ℕ) (p q : ℕ) : ℕ := ((x.take p).filter (fun v => decide (q ≤ v))).length

/-- `x` is a permutation of `[n] = {1, ..., n}` in one-line notation. -/
def IsPerm (n : ℕ) (x : List ℕ) : Prop := x.Perm (List.range' 1 n)

/-- Strong Bruhat order on `S_n`, by the rank (Ehresmann tableau) criterion
    (Bjorner-Brenti, *Combinatorics of Coxeter Groups*, Theorem 2.1.5). -/
def BruhatLE (n : ℕ) (x y : List ℕ) : Prop :=
  IsPerm n x ∧ IsPerm n y ∧ ∀ p q : ℕ, rank x p q ≤ rank y p q

/-- `A_n` (7.3): `w_1 ... w_t` permutes `[t]`, `t = floor(n/2)`. -/
def A (n : ℕ) (w : List ℕ) : Prop :=
  IsPerm n w ∧ (w.take (n / 2)).Perm (List.range' 1 (n / 2))

/-- `w ↦ w^{RU}`: reverse, then complement `v ↦ n + 1 - v`. -/
def RU (n : ℕ) (w : List ℕ) : List ℕ := w.reverse.map (fun v => n + 1 - v)

/-- `[a, b, c, d, ...] ↦ [b, a, d, c, ...]`. -/
def swapPairs : List ℕ → List ℕ
  | a :: b :: t => b :: a :: swapPairs t
  | t => t

/-- `inss_q : S_n → S_{n+1}`,
    `w ↦ w_1 ... w_{q-1} (n+1) w_{q+1} w_q w_{q+3} w_{q+2} ... w_n w_{n-1}`. -/
def inss (q : ℕ) (w : List ℕ) : List ℕ :=
  w.take (q - 1) ++ (w.length + 1) :: swapPairs (w.drop (q - 1))

/-- The base map (7.7). -/
def f4 (w : List ℕ) : List ℕ :=
  if w = [1, 2, 3, 4] then [1, 2, 3, 4]
  else if w = [1, 2, 4, 3] then [1, 4, 3, 2]
  else if w = [2, 1, 3, 4] then [3, 2, 1, 4]
  else if w = [2, 1, 4, 3] then [3, 4, 1, 2]
  else w

/-- Algorithm 7.5. For `w in A_{m+1}`, `w = ins_p(a)` exactly when `p` is the position
    of the maximum `m + 1` in `w` and `a` is `w` with that entry erased.
    Odd `m + 1` (`m = 2k`): `f_{m+1}(w) = inss_{2(p-k)-1}(f_m(a))`.
    Even `m + 1` (`m = 2k+1`): `f_{m+1}(u) = inss_{2(q-k-1)}(f_tilde_m(w_tilde))`,
    `f_tilde_m(w_tilde) = (f_m(w_tilde^{RU}))^{RU}` (7.6). -/
def f : ℕ → List ℕ → List ℕ
  | 0 => id
  | m + 1 => fun w =>
      if m + 1 ≤ 4 then f4 w
      else
        let p := w.idxOf (m + 1) + 1
        let a := w.eraseIdx (p - 1)
        if m % 2 = 0 then inss (2 * (p - m / 2) - 1) (f m a)
        else inss (2 * (p - m / 2 - 1)) (RU m (f m (RU m a)))

/-- Conjecture 7.8: for all `n` (Algorithm 7.5 defines `f_n` for `n >= 4`) and all
    `w in A_n`, `w <= f_n(w)` in the Bruhat order. -/
def claim : Prop := ∀ n : ℕ, 4 ≤ n → ∀ w : List ℕ, A n w → BruhatLE n w (f n w)

end D5.S3.Combinatorics.PanSkanderaWangBruhat
