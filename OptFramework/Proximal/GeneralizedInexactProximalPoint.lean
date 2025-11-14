import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open Set InnerProductSpace

structure MonotoneOperator (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  Operator : E → Set E
  /-- Monotonicity condition: ⟨x - y, v - w⟩ ≥ 0 for all v ∈ T(x), w ∈ T(y) -/
  monotone : ∀ x y v w : E, v ∈ Operator x → w ∈ Operator y →
    inner (x - y) (v - w) ≥ (0 : ℝ)

/-- Definition 4: The ε-enlargement of a monotone operator T
    T^ε(x̃) = {ṽ : ⟨x̃ - x, ṽ - v⟩ ≥ -ε, ∀x ∈ E, ∀v ∈ T(x)}
    This relaxes the monotonicity condition by allowing an error of -ε. -/
def EpsEnlargement (T : MonotoneOperator E) (ε : ℝ) (x_tilde : E) : Set E :=
  {v_tilde | ∀ x v, v ∈ T.Operator x → inner (x_tilde - x) (v_tilde - v) ≥ -ε}



class GeneralizedInexactProximalPoint (T : MonotoneOperator E) (σ : ℝ) (x₀ : E) where
  /-- The iterate sequence xₖ -/
  x : ℕ → E
  /-- The approximate point x̃ₖ -/
  x_tilde : ℕ → E
  /-- The stepsize sequence λₖ -/
  lam : ℕ → ℝ
  /-- The error sequence δₖ -/
  delta : ℕ → ℝ
  /-- The tolerance sequence εₖ -/
  eps : ℕ → ℝ
  /-- σ is in (0,1) -/
  σ_bound : 0 < σ ∧ σ < 1
  /-- Initial condition x₀ -/
  x_init : x 0 = x₀
  /-- Stepsizes are positive -/
  lam_pos : ∀ k : ℕ, k > 0 → 0 < lam k
  /-- Errors are non-negative -/
  delta_nonneg : ∀ k : ℕ, k > 0 → 0 ≤ delta k
  /-- Tolerances are non-negative -/
  eps_nonneg : ∀ k : ℕ, k > 0 → 0 ≤ eps k
  /-- Condition: (xₖ₋₁ - xₖ)/λₖ ∈ T^εₖ(x̃ₖ)
      This means vₖ is in the ε-enlargement of T at x̃ₖ,
      where vₖ = (xₖ₋₁ - xₖ)/λₖ -/
  eps_enlargement_cond : ∀ k : ℕ, k > 0 →
    (1 / lam k) • (x (k - 1) - x k) ∈ EpsEnlargement T (eps k) (x_tilde k)
  /-- Proximal condition: ‖xₖ - x̃ₖ‖² + 2λₖεₖ ≤ σ‖x̃ₖ - xₖ₋₁‖² + δₖ
      This bounds how far x̃ₖ can deviate from xₖ in terms of the previous step. -/
  prox_cond : ∀ k : ℕ, k > 0 →
    ‖x k - x_tilde k‖^2 + 2 * lam k * eps k ≤
    σ * ‖x_tilde k - x (k - 1)‖^2 + delta k

/-- lemma5  vₖ = (xₖ₋₁ - xₖ)/λₖ
     -/
noncomputable def v_general {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀) (k : ℕ) : E :=
  (gipp.lam k)⁻¹ • (gipp.x (k - 1) - gipp.x k)

/-- lemma5 -/
noncomputable def Gamma_general {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀) (k : ℕ) (x : E) : ℝ :=
  inner (v_general gipp k) (x - gipp.x_tilde k) - gipp.eps k


omit [CompleteSpace E] in
/-- Lemma 5(a): For all x, we have Γₖ(x) provides a lower bound based on the ε-enlargement.
    This follows directly from the definition of ε-enlargement. -/
lemma gamma_lower_bound {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀) (k : ℕ) (hk : k > 0) (x : E) (v : E)
    (hv : v ∈ T.Operator x) :
    Gamma_general gipp k x ≤ inner (v_general gipp k) (x - gipp.x_tilde k) := by
  unfold Gamma_general
  have h := gipp.eps_enlargement_cond k hk
  unfold EpsEnlargement at h
  simp at h
  have := h x v hv
  have eps_nn := gipp.eps_nonneg k hk
  linarith

/-- Theorem parameter θₖ = max{2λₖεₖ/σ, λₖ²‖vₖ‖²/(1+√σ)²}

  min_{1≤i≤k} θᵢ ≤ ‖x₀ - x*‖²/((1-σ)k) -/
noncomputable def theta {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀) (k : ℕ) : ℝ :=
  max (2 * gipp.lam k * gipp.eps k / σ)
      ((gipp.lam k)^2 * ‖v_general gipp k‖^2 / (1 + Real.sqrt σ)^2)


/-- Lemma 6: For every k ≥ 1, we have
    -λₖΓₖ(x*) + (1-σ)/2 ‖x̃ₖ - xₖ₋₁‖² ≤ δₖ + ½‖x* - xₖ₋₁‖² - ½‖x* - xₖ‖²

    This is a key descent lemma showing that the algorithm makes progress
    toward any solution x* ∈ T⁻¹(0).

    Proof structure:
    1. Start with: λₖΓₖ(x) + ½‖x - xₖ₋₁‖² = min{...} + ½‖x - xₖ‖²
    2. Use Lemma 5(c): min{...} ≥ (1-σ)/2 ‖x̃ₖ - xₖ₋₁‖² - δₖ
    3. Combine: λₖΓₖ(x) + ½‖x - xₖ₋₁‖² ≥ (1-σ)/2 ‖x̃ₖ - xₖ₋₁‖² - δₖ + ½‖x - xₖ‖²
    4. Take x = x* and rearrange -/
lemma lemma6 {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀)
    (k : ℕ) (hk : k > 0) (x_star : E) (hx : 0 ∈ T.Operator x_star) :
    -gipp.lam k * Gamma_general gipp k x_star +
    (1 - σ) / 2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 ≤
    gipp.delta k + 1/2 * ‖x_star - gipp.x (k - 1)‖^2 -
    1/2 * ‖x_star - gipp.x k‖^2 := by

  -- Step 1: The auxiliary function at x is split into minimum plus distance to xₖ
  -- λₖΓₖ(x) + ½‖x - xₖ₋₁‖² = [λₖΓₖ(xₖ) + ½‖xₖ - xₖ₋₁‖²] + ½‖x - xₖ‖²
  -- This holds because xₖ minimizes λₖΓₖ(·) + ½‖· - xₖ₋₁‖²

  have key_decomp : ∀ x : E,
    gipp.lam k * Gamma_general gipp k x + 1/2 * ‖x - gipp.x (k - 1)‖^2 =
    gipp.lam k * Gamma_general gipp k (gipp.x k) +
    1/2 * ‖gipp.x k - gipp.x (k - 1)‖^2 +
    1/2 * ‖x - gipp.x k‖^2 := by
    intro x
    -- This follows from the three-point identity
    sorry


  -- Step 2: Use Lemma 5(c) to bound the minimum
  have min_bound :
    gipp.lam k * Gamma_general gipp k (gipp.x k) +
    1/2 * ‖gipp.x k - gipp.x (k - 1)‖^2 ≥
    (1 - σ) / 2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 - gipp.delta k := by
    -- From evaluating at x̃ₖ and using proximal condition
    sorry

  -- Step 3: Combine the decomposition and the bound
  have key_ineq : ∀ x : E,
    gipp.lam k * Gamma_general gipp k x + 1/2 * ‖x - gipp.x (k - 1)‖^2 ≥
    (1 - σ) / 2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 - gipp.delta k +
    1/2 * ‖x - gipp.x k‖^2 := by
    intro x
    rw [key_decomp x]
    linarith [min_bound]

  -- Step 4: Take x = x* and rearrange
  have at_xstar := key_ineq x_star

  -- Final rearrangement
  have rearrange :
    gipp.lam k * Gamma_general gipp k x_star + 1/2 * ‖x_star - gipp.x (k - 1)‖^2 ≥
    (1 - σ) / 2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 - gipp.delta k +
    1/2 * ‖x_star - gipp.x k‖^2 := at_xstar

  linarith [rearrange]


/-- Lemma 7: θₖ ≤ ‖x̃ₖ - xₖ₋₁‖²
    This relates the convergence parameter to the actual step size. -/
lemma theta_bound {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀) (k : ℕ) (hk : k > 0) :
    theta gipp k ≤ ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 := by
  sorry
