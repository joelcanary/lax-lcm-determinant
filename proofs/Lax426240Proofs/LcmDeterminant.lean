import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.Radical.NatInt
import Lax426240.LcmDeterminant

/-!
Helpers: Smith's factorisation `f(gcd(i,j)) = Zᵀ D Z` over a commutative ring,
the Möbius sum `∑_{d ∣ n} μ(d) f(d) = ∏_{p ∣ n} (1 − f p)` for every `n ≠ 0`, and
the reduction of the lcm matrix to Smith's. None of these is archive content
here; only the three lcm statements of the concept are.
-/

open Matrix Finset ArithmeticFunction UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius

namespace Lax426240Proofs.LcmDeterminant

open Lax426240.LcmDeterminant

section Smith

variable {R : Type*} [CommRing R]

/-! ## 1. La maquinaria de Smith sobre un anillo conmutativo cualquiera -/

def zetaR (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  fun i j => if (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0

theorem zetaR_blockTriangular (N : ℕ) : (zetaR (R := R) N).BlockTriangular id := by
  intro i j hij
  simp only [zetaR]
  rw [if_neg]
  intro hd
  have := Nat.le_of_dvd (by omega) hd
  simp only [id] at hij
  omega

theorem det_zetaR (N : ℕ) : (zetaR (R := R) N).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (zetaR_blockTriangular N)]
  simp [zetaR]

def smithR (N : ℕ) (f : ℕ → R) : Matrix (Fin N) (Fin N) R :=
  fun i j => f (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1))

def diagR (N : ℕ) (g : ℕ → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.diagonal (fun i => g ((i : ℕ) + 1))

theorem diagR_mul_zetaR (N : ℕ) (g : ℕ → R) (d j : Fin N) :
    (diagR N g * zetaR (R := R) N) d j
      = if (d : ℕ) + 1 ∣ (j : ℕ) + 1 then g ((d : ℕ) + 1) else 0 := by
  simp only [Matrix.mul_apply, diagR, Matrix.diagonal_apply, zetaR]
  have step : (∑ x : Fin N, (if d = x then g ((d : ℕ) + 1) else 0)
        * (if (x : ℕ) + 1 ∣ (j : ℕ) + 1 then (1 : R) else 0))
      = ∑ x : Fin N, (if x = d then
          (if (x : ℕ) + 1 ∣ (j : ℕ) + 1 then g ((d : ℕ) + 1) else 0) else 0) := by
    apply Finset.sum_congr rfl; intro x _
    by_cases h : x = d
    · simp [h]
    · rw [if_neg h, if_neg (fun hh => h hh.symm), zero_mul]
  rw [step, Finset.sum_ite_eq' Finset.univ d]
  simp

theorem fin_sum_eq_divisors_sum (N m : ℕ) (g : ℕ → R) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    (∑ x : Fin N, if (x : ℕ) + 1 ∣ m then g ((x : ℕ) + 1) else 0)
      = ∑ d ∈ Nat.divisors m, g d := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if x + 1 ∣ m then g (x + 1) else 0)]
  rw [← Finset.sum_filter]
  have hset : (Finset.range N).filter (fun i => i + 1 ∣ m) = (Nat.divisors m).image (· - 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨hiN, hdvd⟩
      refine ⟨i + 1, ⟨hdvd, by omega⟩, by omega⟩
    · rintro ⟨d, ⟨hdvd, hmne⟩, hd⟩
      have hdle : d ≤ m := Nat.le_of_dvd (by omega) hdvd
      have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      refine ⟨by omega, ?_⟩
      have heq1 : i = d - 1 := hd.symm
      rw [heq1]
      have heq2 : d - 1 + 1 = d := by omega
      rw [heq2]; exact hdvd
  rw [hset, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hde : d - 1 + 1 = d := by omega
    rw [hde]
  · intro a ha b hb hab
    simp only at hab
    have hapos : 1 ≤ a := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 (by omega)
    have hbpos : 1 ≤ b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 (by omega)
    omega

theorem entrada_factorizacion_R (N : ℕ) (f g : ℕ → R)
    (hyp : ∀ m, 1 ≤ m → f m = ∑ d ∈ Nat.divisors m, g d) (i j : Fin N) :
    ((zetaR (R := R) N)ᵀ * (diagR N g * zetaR (R := R) N)) i j = smithR N f i j := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply, diagR_mul_zetaR N g, zetaR]
  have key : (∑ x : Fin N, (if (x : ℕ) + 1 ∣ (i : ℕ) + 1 then (1 : R) else 0)
        * (if (x : ℕ) + 1 ∣ (j : ℕ) + 1 then g ((x : ℕ) + 1) else 0))
      = ∑ x : Fin N,
          (if (x : ℕ) + 1 ∣ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) then g ((x : ℕ) + 1) else 0) := by
    apply Finset.sum_congr rfl; intro x _
    by_cases h1 : (x : ℕ) + 1 ∣ (i : ℕ) + 1 <;> by_cases h2 : (x : ℕ) + 1 ∣ (j : ℕ) + 1 <;>
      simp [h1, h2, Nat.dvd_gcd_iff]
  rw [key]
  have hgcdpos : 1 ≤ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgcdle : Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) ≤ N := by
    have := Nat.gcd_le_left (m := (i : ℕ) + 1) ((j : ℕ) + 1) (by omega)
    have hi := i.isLt
    omega
  rw [fin_sum_eq_divisors_sum N _ g hgcdpos hgcdle]
  exact (hyp _ hgcdpos).symm

theorem smithR_eq_factorizacion (N : ℕ) (f g : ℕ → R)
    (hyp : ∀ m, 1 ≤ m → f m = ∑ d ∈ Nat.divisors m, g d) :
    smithR N f = (zetaR (R := R) N)ᵀ * (diagR N g * zetaR (R := R) N) := by
  ext i j
  exact (entrada_factorizacion_R N f g hyp i j).symm

theorem det_diagR (N : ℕ) (g : ℕ → R) :
    (diagR N g).det = ∏ i : Fin N, g ((i : ℕ) + 1) := by
  simp [diagR, Matrix.det_diagonal]

theorem smithR_determinant (N : ℕ) (f g : ℕ → R)
    (hyp : ∀ m, 1 ≤ m → f m = ∑ d ∈ Nat.divisors m, g d) :
    (smithR N f).det = ∏ i : Fin N, g ((i : ℕ) + 1) := by
  rw [smithR_eq_factorizacion N f g hyp, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, det_zetaR, det_diagR]
  ring

end Smith

section MoebiusSum

variable {R : Type*} [CommRing R]

theorem dvd_radical_of_squarefree {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) (hsq : Squarefree d) :
    d ∣ radical n := by
  rw [Nat.radical_eq_prod_primeFactors]
  have : d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
  rw [this]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono hd hn)

theorem sum_moebius_mul_eq_prod_one_sub (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (μ d : R) * f d = ∏ p ∈ n.primeFactors, (1 - f p) := by
  have hrad : radical n ≠ 0 := (Nat.radical_pos n).ne'
  have paso : ∑ d ∈ n.divisors, (μ d : R) * f d
      = ∑ d ∈ (radical n).divisors, (μ d : R) * f d := by
    refine (Finset.sum_subset ?_ ?_).symm
    · exact Nat.divisors_subset_of_dvd hn radical_dvd_self
    · intro d hd hno
      have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
      have : ¬ Squarefree d := by
        intro hsq
        exact hno (Nat.mem_divisors.mpr ⟨dvd_radical_of_squarefree hn hdn hsq, hrad⟩)
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree this]
      simp
  rw [paso, ← hf.prodPrimeFactors_one_sub_of_squarefree f squarefree_radical,
      Nat.primeFactors_radical]

theorem sum_moebius_mul_id {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (μ d : ℚ) * (d : ℚ)
      = ∏ p ∈ n.primeFactors, (1 - (p : ℚ)) := by
  have := sum_moebius_mul_eq_prod_one_sub
    (R := ℚ) ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℚ)
    ArithmeticFunction.isMultiplicative_id.natCast hn
  simpa using this

end MoebiusSum

section Lcm

def diagId (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.diagonal (fun i => (((i : ℕ) + 1 : ℕ) : ℚ))

theorem lcmMat_eq (N : ℕ) :
    lcmMatrix N = diagId N * smithR N (fun m => (1 : ℚ) / m) * diagId N := by
  ext i j
  simp only [diagId, Matrix.mul_diagonal, Matrix.diagonal_mul, smithR, lcmMatrix]
  have hgpos : 0 < Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) :=
    Nat.gcd_pos_of_pos_left _ (by omega)
  have hgQ : ((Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hgpos.ne'
  have hmulQ : ((Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) : ℕ) : ℚ)
        * ((Nat.lcm ((i : ℕ) + 1) ((j : ℕ) + 1) : ℕ) : ℚ)
      = (((i : ℕ) + 1 : ℕ) : ℚ) * (((j : ℕ) + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.gcd_mul_lcm ((i : ℕ) + 1) ((j : ℕ) + 1)
  field_simp
  linear_combination hmulQ

theorem det_diagId (N : ℕ) :
    (diagId N).det = ∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ) := by
  simp [diagId, Matrix.det_diagonal]

theorem det_lcmMat (N : ℕ) (g : ℕ → ℚ)
    (hyp : ∀ m, 1 ≤ m → (1 : ℚ) / m = ∑ d ∈ Nat.divisors m, g d) :
    (lcmMatrix N).det
      = (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * ∏ i : Fin N, g ((i : ℕ) + 1) := by
  rw [lcmMat_eq N, Matrix.det_mul, Matrix.det_mul, det_diagId,
      smithR_determinant N (fun m => (1 : ℚ) / m) g hyp]
  ring

theorem g_spec (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℚ) / m = ∑ d ∈ Nat.divisors m, g d := by
  have h : ∀ n, 0 < n →
      ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℚ) * (1 / x.2) = g n :=
    fun _ _ => rfl
  exact ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℚ)
    (f := g) (g := fun n => (1 : ℚ) / n)).mpr h m (by omega)).symm

/--
---
conclusion: Lax426240.LcmDeterminant.det_lcmMatrix
---
`lcm(i,j) = i · (1/gcd(i,j)) · j` factors the matrix as `D S D`; Smith's
determinant for `S` with `1/m = ∑_{d ∣ m} g(d)` (Möbius inversion) gives the
product.
-/
theorem det_lcmMatrix (N : ℕ) :
    (lcmMatrix N).det
      = (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * ∏ i : Fin N, g ((i : ℕ) + 1) :=
  det_lcmMat N g (fun m hm => g_spec m hm)

/--
---
conclusion: Lax426240.LcmDeterminant.g_eq
---
Reindex the antidiagonal sum by the divisor `a`: `1/(n/a) = a/n`, so
`g(n) = (1/n) ∑_{a ∣ n} μ(a) a = (1/n) ∏_{p ∣ n} (1 − p)`.
-/
theorem g_eq (n : ℕ) (hn : n ≠ 0) :
    g n = (1 / (n : ℚ)) * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)) := by
  rw [← sum_moebius_mul_id hn, Finset.mul_sum]
  unfold g
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (μ a : ℚ) * (1 / (b : ℚ)))]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hdvd : a ∣ n := Nat.dvd_of_mem_divisors ha
  have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast Nat.pos_of_mem_divisors ha |>.ne'
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [Nat.cast_div hdvd ha0]
  field_simp

/--
---
conclusion: Lax426240.LcmDeterminant.det_lcmMatrix_closed
---
-/
theorem det_lcmMatrix_closed (N : ℕ) :
    (lcmMatrix N).det
      = (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * ∏ i : Fin N, ∏ p ∈ ((i : ℕ) + 1).primeFactors, (1 - (p : ℚ)) := by
  rw [det_lcmMatrix]
  have hg : ∀ i : Fin N, g ((i : ℕ) + 1)
      = (1 / ((((i : ℕ) + 1 : ℕ) : ℚ))) * ∏ p ∈ ((i : ℕ) + 1).primeFactors, (1 - (p : ℚ)) :=
    fun i => by rw [g_eq _ (by omega)]
  simp_rw [hg]
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_const_one]
  have hne : (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
  field_simp
  try ring

end Lcm

end Lax426240Proofs.LcmDeterminant
