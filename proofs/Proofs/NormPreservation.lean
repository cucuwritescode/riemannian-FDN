/-
structured riemannian pruning of feedback delay networks
formal proofs for beng thesis

author: facundo franchino

this module proves that orthogonal matrices preserve euclidean norms,
which is the foundational energy argument for lossless fdns.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace FDNProofs

open Matrix BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

--the core theorem: orthogonal matrices preserve the euclidean norm
--this is why lossless fdns require orthogonal feedback matrices:
--energy in = energy out, no unbounded growth or decay

theorem orthogonal_preserves_norm
    (A : Matrix n n ℝ)
    (hA : Aᵀ * A = 1)
    (x : n → ℝ) :
    ‖A.mulVec x‖ = ‖x‖ := by
  --we show ‖Ax‖² = ‖x‖², then take square roots
  --the key is that ‖Ax‖² = xᵀAᵀAx = xᵀIx = ‖x‖²
  have h : ‖A.mulVec x‖^2 = ‖x‖^2 := by
    --rewrite norms as inner products
    rw [sq_norm_eq_inner (𝕜 := ℝ), sq_norm_eq_inner (𝕜 := ℝ)]
    --unfold the inner product on the transformed vector
    simp only [EuclideanSpace.inner_piLp_equiv_symm, Fintype.inner_apply]
    --the matrix multiplication satisfies ⟨Ax, Ax⟩ = ⟨x, AᵀAx⟩ = ⟨x, x⟩
    conv_lhs =>
      arg 1
      ext i
      rw [Matrix.mulVec, Matrix.dotProduct, Matrix.mulVec, Matrix.dotProduct]
    --use the orthogonality condition AᵀA = I
    simp only [hA, Matrix.one_mulVec]
  --extract the result from squared norms
  exact sq_eq_sq' (norm_nonneg _).le (norm_nonneg _).le |>.mp h

--corollary: orthogonal transformations preserve energy (squared norm)
--this is the physical interpretation for audio signals

theorem orthogonal_preserves_energy
    (A : Matrix n n ℝ)
    (hA : Aᵀ * A = 1)
    (x : n → ℝ) :
    ‖A.mulVec x‖^2 = ‖x‖^2 := by
  rw [orthogonal_preserves_norm A hA x]

--immediate consequence: if feedback matrix is orthogonal,
--the fdn cannot have unbounded energy growth

theorem lossless_implies_bounded
    (A : Matrix n n ℝ)
    (hA : Aᵀ * A = 1)
    (x : n → ℝ)
    (bound : ℝ)
    (hx : ‖x‖ ≤ bound) :
    ‖A.mulVec x‖ ≤ bound := by
  rw [orthogonal_preserves_norm A hA x]
  exact hx

end FDNProofs
