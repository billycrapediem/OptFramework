
import Optlib.Function.Lsmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- A monotone operator from E to subsets of E -/
structure MonotoneOperator (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  T : E → Set E
  /-- Monotonicity condition: ⟨x - y, v - w⟩ ≥ 0 for all (x,v), (y,w) in the graph -/
  monotone : ∀ x y v w : E, v ∈ T x → w ∈ T y → inner (x - y) (v - w) ≥ (0 : ℝ)


class GeneralizedProximalPoint
  (T : MonotoneOperator E)
  (x : ℕ → E)
  (lam : ℕ → ℝ) where
  /-- Stepsize is positive -/
  stepsize_pos : ∀ k : ℕ, k ≥ 1 → lam k > 0
  /-- Main iteration condition: (x_{k-1} - xₖ)/λₖ ∈ T(xₖ) for k ≥ 1 -/
  iteration_condition : ∀ k : ℕ, k ≥ 1 →
    ((lam k)⁻¹ • (x (k - 1) - x k)) ∈ T.T (x k)

namespace GeneralizedProximalPoint

variable {T : MonotoneOperator E} {x : ℕ → E} {lam : ℕ → ℝ}
variable [GeneralizedProximalPoint T x lam]

/-- Define vₖ = (x_{k-1} - xₖ)/λₖ -/
noncomputable def v {x : ℕ → E} {lam : ℕ → ℝ} (k : ℕ) : E := (lam k)⁻¹ • (x (k - 1) - x k)
