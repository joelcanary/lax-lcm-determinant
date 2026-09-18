import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
---
title: The determinant of the least-common-multiple matrix
type: theorem
---
Smith (1875) evaluated the determinant of the $N \times N$ matrix with entries
$\gcd(i, j)$, and more generally of $f(\gcd(i,j))$ when $f = g * 1$ is a
Dirichlet convolution: it equals $\prod_{k \le N} g(k)$. The matrix of least
common multiples is not of that form, but $\mathrm{lcm}(i,j)\gcd(i,j) = ij$
writes it as $D\,S\,D$ with $D = \mathrm{diag}(1, \dots, N)$ and
$S_{ij} = 1/\gcd(i,j)$, and $1/m$ is a Dirichlet convolution $g * 1$ with
$g = \mu * (1/\cdot)$ by Möbius inversion. Hence

$$\det\big(\mathrm{lcm}(i,j)\big)_{i,j \le N} = (N!)^2 \prod_{k \le N} g(k),
\qquad g(n) = \sum_{ab = n} \frac{\mu(a)}{b} = \frac{1}{n}\prod_{p \mid n}(1 - p),$$

so that the determinant is $N! \prod_{k \le N} \prod_{p \mid k} (1 - p)$. The
three statements are the determinant in terms of $g$, the closed form of $g$,
and the closed form of the determinant.
-/

namespace Lax426240.LcmDeterminant

open Finset
open scoped ArithmeticFunction.Moebius

/-- The `N × N` matrix with entries `lcm(i, j)` for `1 ≤ i, j ≤ N`, over `ℚ`. -/
def lcmMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => (Nat.lcm ((i : ℕ) + 1) ((j : ℕ) + 1) : ℚ)

/-- The Dirichlet inverse-image of `1/n` under convolution with `1`:
`g(n) = ∑_{ab = n} μ(a) / b`. -/
noncomputable def g (n : ℕ) : ℚ :=
  ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℚ) * (1 / x.2)

/-- `det (lcm(i,j)) = (N!)² ∏_{k ≤ N} g(k)`. -/
axiom det_lcmMatrix (N : ℕ) :
    (lcmMatrix N).det
      = (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * ∏ i : Fin N, g ((i : ℕ) + 1)

/-- `g(n) = (1/n) ∏_{p ∣ n} (1 − p)` for `n ≠ 0`. -/
axiom g_eq (n : ℕ) (hn : n ≠ 0) :
    g n = (1 / (n : ℚ)) * ∏ p ∈ n.primeFactors, (1 - (p : ℚ))

/-- `det (lcm(i,j)) = N! ∏_{k ≤ N} ∏_{p ∣ k} (1 − p)`. -/
axiom det_lcmMatrix_closed (N : ℕ) :
    (lcmMatrix N).det
      = (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * ∏ i : Fin N, ∏ p ∈ ((i : ℕ) + 1).primeFactors, (1 - (p : ℚ))

end Lax426240.LcmDeterminant
