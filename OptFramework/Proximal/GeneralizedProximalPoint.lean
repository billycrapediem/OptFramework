
import Optlib.Function.Lsmooth
import OptFramework.Proximal.GeneralizedInexactProximalPoint
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- A monotone operator from E to subsets of E -/


class GeneralizedProximalPoint
  (T : MonotoneOperator E)
  (x : ℕ → E)
  (lam : ℕ → ℝ) where
  /-- Stepsize is positive -/
  stepsize_pos : ∀ k : ℕ, k ≥ 1 → lam k > 0
  iteration_condition : ∀ k : ℕ, k ≥ 1 →
    ((lam k)⁻¹ • (x (k - 1) - x k)) ∈ T.Operator (x k)

namespace GeneralizedProximalPoint

variable {T : MonotoneOperator E} {x : ℕ → E} {lam : ℕ → ℝ}
variable [GeneralizedProximalPoint T x lam]



/-- Define vₖ = (x_{k-1} - xₖ)/λₖ -/
noncomputable def v {x : ℕ → E} {lam : ℕ → ℝ} (k : ℕ) : E := (lam k)⁻¹ • (x (k - 1) - x k)
