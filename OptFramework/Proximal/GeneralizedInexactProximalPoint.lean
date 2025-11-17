import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open Set InnerProductSpace Finset

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
  x : ℕ → E
  x_tilde : ℕ → E
  lam : ℕ → ℝ
  delta : ℕ → ℝ
  eps : ℕ → ℝ
  σ_bound : 0 < σ ∧ σ < 1
  x_init : x 0 = x₀
  lam_pos : ∀ k : ℕ, k > 0 → 0 < lam k
  delta_nonneg : ∀ k : ℕ, k > 0 → 0 ≤ delta k
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

variable {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
variable (gipp : GeneralizedInexactProximalPoint T σ x₀)
/-- lemma5  vₖ = (xₖ₋₁ - xₖ)/λₖ
     -/
def IsZeroOf (T : MonotoneOperator E) (x_star : E) : Prop :=
  0 ∈ T.Operator x_star

noncomputable def x_star (T : MonotoneOperator E)
    (h : ∃ x : E, IsZeroOf T x) : E :=
  Classical.choose h

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



omit [CompleteSpace E] in
lemma lemma6_key_decomp {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀) (k : ℕ) (hk : k > 0) (x : E) :
    gipp.lam k * Gamma_general gipp k x + 1/2 * ‖x - gipp.x (k - 1)‖^2 =
    gipp.lam k * Gamma_general gipp k (gipp.x k) +
    1/2 * ‖gipp.x k - gipp.x (k - 1)‖^2 +
    1/2 * ‖x - gipp.x k‖^2 := by
  -- Expand Gamma_general at x and xₖ
  unfold Gamma_general

  -- The difference in Gamma terms simplifies to an inner product
  have gamma_diff :
    gipp.lam k * (inner (v_general gipp k) (x - gipp.x_tilde k) - gipp.eps k) -
    gipp.lam k * (inner (v_general gipp k) (gipp.x k - gipp.x_tilde k) - gipp.eps k) =
    gipp.lam k * inner (v_general gipp k) (x - gipp.x k) := by
    have inner_eq : ⟪v_general gipp k, x - gipp.x_tilde k⟫_ℝ - ⟪v_general gipp k, gipp.x k - gipp.x_tilde k⟫_ℝ =
                    ⟪v_general gipp k, x - gipp.x k⟫_ℝ := by
      rw [← inner_sub_right]
      congr 1
      abel
    linear_combination (gipp.lam k) * inner_eq

  -- Key norm identity: ‖x - xₖ₋₁‖² = ‖x - xₖ‖² + ‖xₖ - xₖ₋₁‖² + 2⟨x - xₖ, xₖ - xₖ₋₁⟩
  have norm_identity :
    ‖x - gipp.x (k - 1)‖^2 =
    ‖x - gipp.x k‖^2 + ‖gipp.x k - gipp.x (k - 1)‖^2 +
    2 * inner (x - gipp.x k) (gipp.x k - gipp.x (k - 1)) := by
    have eq : x - gipp.x (k - 1) = (x - gipp.x k) + (gipp.x k - gipp.x (k - 1)) := by abel
    rw [eq, norm_add_sq_real]; ring

  -- Relate ⟨x - xₖ, xₖ - xₖ₋₁⟩ to ⟨vₖ, x - xₖ⟩
  have inner_relation :
    inner (x - gipp.x k) (gipp.x k - gipp.x (k - 1)) =
    -gipp.lam k * inner (v_general gipp k) (x - gipp.x k) := by
    unfold v_general
    rw [inner_smul_left]
    have lam_pos := gipp.lam_pos k hk
    have : gipp.x k - gipp.x (k - 1) = -(gipp.x (k - 1) - gipp.x k) := by abel
    rw [this, inner_neg_right]
    field_simp [ne_of_gt lam_pos]
    rw [mul_comm, real_inner_comm]

  -- Combine everything
  calc gipp.lam k * (inner (v_general gipp k) (x - gipp.x_tilde k) - gipp.eps k) +
       1/2 * ‖x - gipp.x (k - 1)‖^2
      = gipp.lam k * (inner (v_general gipp k) (gipp.x k - gipp.x_tilde k) - gipp.eps k) +
        gipp.lam k * inner (v_general gipp k) (x - gipp.x k) +
        1/2 * ‖x - gipp.x (k - 1)‖^2 := by linarith [gamma_diff]
    _ = gipp.lam k * (inner (v_general gipp k) (gipp.x k - gipp.x_tilde k) - gipp.eps k) +
        gipp.lam k * inner (v_general gipp k) (x - gipp.x k) +
        1/2 * (‖x - gipp.x k‖^2 + ‖gipp.x k - gipp.x (k - 1)‖^2 +
               2 * inner (x - gipp.x k) (gipp.x k - gipp.x (k - 1))) := by
          rw [norm_identity]
    _ = gipp.lam k * (inner (v_general gipp k) (gipp.x k - gipp.x_tilde k) - gipp.eps k) +
        gipp.lam k * inner (v_general gipp k) (x - gipp.x k) +
        1/2 * ‖x - gipp.x k‖^2 + 1/2 * ‖gipp.x k - gipp.x (k - 1)‖^2 +
        inner (x - gipp.x k) (gipp.x k - gipp.x (k - 1)) := by ring
    _ = gipp.lam k * (inner (v_general gipp k) (gipp.x k - gipp.x_tilde k) - gipp.eps k) +
        gipp.lam k * inner (v_general gipp k) (x - gipp.x k) +
        1/2 * ‖x - gipp.x k‖^2 + 1/2 * ‖gipp.x k - gipp.x (k - 1)‖^2 +
        (-gipp.lam k * inner (v_general gipp k) (x - gipp.x k)) := by
          rw [inner_relation]
    _ = gipp.lam k * (inner (v_general gipp k) (gipp.x k - gipp.x_tilde k) - gipp.eps k) +
        1/2 * ‖gipp.x k - gipp.x (k - 1)‖^2 +
        1/2 * ‖x - gipp.x k‖^2 := by ring


/-- Lemma 6 Step 2: Lower bound on the minimum value
    The minimum value λₖΓₖ(xₖ) + ½‖xₖ - xₖ₋₁‖² is bounded below by
    (1-σ)/2 ‖x̃ₖ - xₖ₋₁‖² - δₖ

    This follows from Lemma 5(c) by evaluating at x̃ₖ and using the proximal condition. -/
lemma lemma6_min_bound {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀) (k : ℕ) (hk : k > 0) :
    gipp.lam k * Gamma_general gipp k (gipp.x k) +
    1/2 * ‖gipp.x k - gipp.x (k - 1)‖^2 ≥
    (1 - σ) / 2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 - gipp.delta k := by
  unfold Gamma_general v_general

  -- Key norm identity from parallelogram law
  have norm_identity :
    2 * inner (gipp.x (k - 1) - gipp.x k) (gipp.x k - gipp.x_tilde k) =
    ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 - ‖gipp.x k - gipp.x_tilde k‖^2 -
    ‖gipp.x k - gipp.x (k - 1)‖^2 := by
    have h : (gipp.x_tilde k - gipp.x (k - 1)) - (gipp.x k - gipp.x (k - 1)) =
             gipp.x_tilde k - gipp.x k := by abel
    have expand := @norm_sub_sq_real E _ _ (gipp.x_tilde k - gipp.x (k - 1)) (gipp.x k - gipp.x (k - 1))
    rw [h] at expand
    have norm_sym : ‖gipp.x_tilde k - gipp.x k‖^2 = ‖gipp.x k - gipp.x_tilde k‖^2 := by
      rw [norm_sub_rev]
    rw [norm_sym] at expand
    -- Relate the two inner products: show LHS = RHS by algebraic expansion
    have inner_rel : inner (gipp.x (k - 1) - gipp.x k) (gipp.x k - gipp.x_tilde k) =
      inner (gipp.x_tilde k - gipp.x (k - 1)) (gipp.x k - gipp.x (k - 1)) - ‖gipp.x k - gipp.x (k - 1)‖^2 := by
      rw [show ‖gipp.x k - gipp.x (k - 1)‖^2 = inner (gipp.x k - gipp.x (k - 1)) (gipp.x k - gipp.x (k - 1))
          by rw [real_inner_self_eq_norm_sq]]
      rw [← inner_sub_left]
      have h1 : gipp.x_tilde k - gipp.x (k - 1) - (gipp.x k - gipp.x (k - 1)) =
                gipp.x_tilde k - gipp.x k := by abel
      rw [h1]
      rw [← inner_neg_neg]
      have h2 : -(gipp.x (k - 1) - gipp.x k) = gipp.x k - gipp.x (k - 1) := by abel
      have h3 : -(gipp.x k - gipp.x_tilde k) = gipp.x_tilde k - gipp.x k := by abel
      rw [h2, h3, real_inner_comm]
    linarith


  -- Simplify the inner product term
  have lam_pos := gipp.lam_pos k hk
  have inner_calc :
    gipp.lam k * inner ((gipp.lam k)⁻¹ • (gipp.x (k - 1) - gipp.x k)) (gipp.x k - gipp.x_tilde k) =
    1/2 * (‖gipp.x_tilde k - gipp.x (k - 1)‖^2 - ‖gipp.x k - gipp.x_tilde k‖^2 -
           ‖gipp.x k - gipp.x (k - 1)‖^2) := by
    rw [inner_smul_left]
    simp only [RCLike.conj_to_real]
    field_simp [ne_of_gt lam_pos]
    linarith [norm_identity]

  -- Expand LHS
  calc gipp.lam k * (inner ((gipp.lam k)⁻¹ • (gipp.x (k - 1) - gipp.x k)) (gipp.x k - gipp.x_tilde k) - gipp.eps k) +
       1/2 * ‖gipp.x k - gipp.x (k - 1)‖^2
      = 1/2 * (‖gipp.x_tilde k - gipp.x (k - 1)‖^2 - ‖gipp.x k - gipp.x_tilde k‖^2 -
               ‖gipp.x k - gipp.x (k - 1)‖^2) - gipp.lam k * gipp.eps k +
        1/2 * ‖gipp.x k - gipp.x (k - 1)‖^2 := by
          linear_combination inner_calc
    _ = 1/2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 - 1/2 * ‖gipp.x k - gipp.x_tilde k‖^2 -
        gipp.lam k * gipp.eps k := by ring
    _ ≥ 1/2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 - σ/2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 -
        gipp.delta k / 2 := by
          -- Use proximal condition: ‖xₖ - x̃ₖ‖² + 2λₖεₖ ≤ σ‖x̃ₖ - xₖ₋₁‖² + δₖ
          have prox := gipp.prox_cond k hk
          have norm_sym : ‖gipp.x k - gipp.x_tilde k‖^2 = ‖gipp.x_tilde k - gipp.x k‖^2 := by
            rw [norm_sub_rev]
          rw [norm_sym] at prox
          -- Rearrange: ‖xₖ - x̃ₖ‖² + 2λₖεₖ ≤ σ‖x̃ₖ - xₖ₋₁‖² + δₖ
          -- So: -1/2 * ‖xₖ - x̃ₖ‖² - λₖεₖ ≥ -σ/2 * ‖x̃ₖ - xₖ₋₁‖² - δₖ/2
          linarith
    _ = (1 - σ) / 2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 - gipp.delta k / 2 := by ring
    _ ≥ (1 - σ) / 2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 - gipp.delta k := by
          have delta_nn := gipp.delta_nonneg k hk
          linarith

/-- Lemma 6: For every k ≥ 1, we have
    -λₖΓₖ(x*) + (1-σ)/2 ‖x̃ₖ - xₖ₋₁‖² ≤ δₖ + ½‖x* - xₖ₋₁‖² - ½‖x* - xₖ‖²

    This is a key descent lemma showing that the algorithm makes progress
    toward any solution x* ∈ T⁻¹(0).

    Proof structure:
    1. Apply key decomposition at x*: λₖΓₖ(x*) + ½‖x* - xₖ₋₁‖² = ... + ½‖x* - xₖ‖²
    2. Use minimum bound: ... ≥ (1-σ)/2 ‖x̃ₖ - xₖ₋₁‖² - δₖ
    3. Combine to get: λₖΓₖ(x*) + ½‖x* - xₖ₋₁‖² ≥ (1-σ)/2 ‖x̃ₖ - xₖ₋₁‖² - δₖ + ½‖x* - xₖ‖²
    4. Rearrange to obtain the desired inequality -/
lemma lemma6 {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀)
    (k : ℕ) (hk : k > 0) (x_star : E) :
    -gipp.lam k * Gamma_general gipp k x_star +
    (1 - σ) / 2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 ≤
    gipp.delta k + 1/2 * ‖x_star - gipp.x (k - 1)‖^2 -
    1/2 * ‖x_star - gipp.x k‖^2 := by

  -- Step 1: Apply the key decomposition at x*
  have decomp_at_xstar := lemma6_key_decomp gipp k hk x_star

  -- Step 2: Get the minimum bound
  have min_bound := lemma6_min_bound gipp k hk

  -- Step 3: Combine the decomposition and the bound
  -- From decomp: λₖΓₖ(x*) + ½‖x* - xₖ₋₁‖² = [...] + ½‖x* - xₖ‖²
  -- From min_bound: [...] ≥ (1-σ)/2 ‖x̃ₖ - xₖ₋₁‖² - δₖ
  -- Therefore: λₖΓₖ(x*) + ½‖x* - xₖ₋₁‖² ≥ (1-σ)/2 ‖x̃ₖ - xₖ₋₁‖² - δₖ + ½‖x* - xₖ‖²
  have combined :
    gipp.lam k * Gamma_general gipp k x_star + 1/2 * ‖x_star - gipp.x (k - 1)‖^2 ≥
    (1 - σ) / 2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 - gipp.delta k +
    1/2 * ‖x_star - gipp.x k‖^2 := by
    rw [decomp_at_xstar]
    linarith [min_bound]

  -- Step 4: Rearrange to get the desired inequality
  -- From: λₖΓₖ(x*) + ½‖x* - xₖ₋₁‖² ≥ (1-σ)/2 ‖x̃ₖ - xₖ₋₁‖² - δₖ + ½‖x* - xₖ‖²
  -- Rearrange: -λₖΓₖ(x*) + (1-σ)/2 ‖x̃ₖ - xₖ₋₁‖² ≤ δₖ + ½‖x* - xₖ₋₁‖² - ½‖x* - xₖ‖²
  linarith [combined]


/-- Theorem parameter θₖ = max{2λₖεₖ/σ, λₖ²‖vₖ‖²/(1+√σ)²}

  min_{1≤i≤k} θᵢ ≤ ‖x₀ - x*‖²/((1-σ)k) -/
noncomputable def theta {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀) (k : ℕ) : ℝ :=
  max (2 * gipp.lam k * gipp.eps k / σ)
      ((gipp.lam k)^2 * ‖v_general gipp k‖^2 / (1 + Real.sqrt σ)^2)

/-- Lemma 7: θₖ ≤ ‖x̃ₖ - xₖ₋₁‖²
    This relates the convergence parameter to the actual step size. -/
lemma theta_bound {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀) (k : ℕ) (hk : k > 0)  (hsmooth : gipp.delta k = 0) :
    theta gipp k ≤ ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 := by
  unfold theta
  -- We need to show both terms of the max are bounded by ‖x̃k - xk-1‖²

  -- Get the proximal condition with delta_k = 0 (smooth case from PDF)
  have prox := gipp.prox_cond k hk
  have delta_nn := gipp.delta_nonneg k hk

  -- First bound: 2λkεk/σ ≤ ‖x̃k - xk-1‖²
  have bound1 : 2 * gipp.lam k * gipp.eps k / σ ≤ ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 := by
    have σ_pos := gipp.σ_bound.1
    have σ_lt_1 := gipp.σ_bound.2
    -- From proximal condition: 2λkεk ≤ σ‖x̃k - xk-1‖² + δk - ‖xk - x̃k‖²
    have : 2 * gipp.lam k * gipp.eps k ≤ σ * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 + gipp.delta k := by
      have norm_sym : ‖gipp.x k - gipp.x_tilde k‖^2 = ‖gipp.x_tilde k - gipp.x k‖^2 := by
        rw [norm_sub_rev]
      rw [norm_sym] at prox
      linarith [sq_nonneg ‖gipp.x_tilde k - gipp.x k‖]
    -- Since δk ≥ 0 and σ > 0, we can divide
    calc 2 * gipp.lam k * gipp.eps k / σ
        ≤ (σ * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 + gipp.delta k) / σ := by
          apply div_le_div_of_nonneg_right this (le_of_lt σ_pos)
      _ = ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 + gipp.delta k / σ := by field_simp; ring
      _ = ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 := by rw [hsmooth]; simp

  -- Second bound: λk²‖vk‖²/(1 + √σ)² ≤ ‖x̃k - xk-1‖²
  have bound2 : (gipp.lam k)^2 * ‖v_general gipp k‖^2 / (1 + Real.sqrt σ)^2 ≤
                ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 := by
    have σ_pos := gipp.σ_bound.1
    have σ_lt_1 := gipp.σ_bound.2
    have lam_pos := gipp.lam_pos k hk

    -- From proximal condition: ‖x̃k - xk‖ ≤ √σ‖x̃k - xk-1‖
    have xtilde_bound : ‖gipp.x_tilde k - gipp.x k‖ ≤ Real.sqrt σ * ‖gipp.x_tilde k - gipp.x (k - 1)‖ := by
      have norm_sym : ‖gipp.x k - gipp.x_tilde k‖^2 = ‖gipp.x_tilde k - gipp.x k‖^2 := by
        rw [norm_sub_rev]
      rw [norm_sym] at prox
      have : ‖gipp.x_tilde k - gipp.x k‖^2 ≤ σ * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 := by
        rw [hsmooth] at prox
        have eps_nn := gipp.eps_nonneg k hk
        have term_nn : 0 ≤ 2 * gipp.lam k * gipp.eps k := by positivity
        linarith
      have h1 := Real.sqrt_le_sqrt this
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (le_of_lt σ_pos), Real.sqrt_sq (norm_nonneg _)] at h1
      exact h1

    -- By triangle inequality: λk‖vk‖ ≤ ‖x̃k - xk-1‖ + ‖x̃k - xk‖ ≤ (1 + √σ)‖x̃k - xk-1‖
    unfold v_general
    have lam_v_bound : gipp.lam k * ‖(gipp.lam k)⁻¹ • (gipp.x (k - 1) - gipp.x k)‖ ≤
                       (1 + Real.sqrt σ) * ‖gipp.x_tilde k - gipp.x (k - 1)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos lam_pos]
      field_simp [ne_of_gt lam_pos]
      have triangle : ‖gipp.x (k - 1) - gipp.x k‖ ≤
                      ‖gipp.x (k - 1) - gipp.x_tilde k‖ + ‖gipp.x_tilde k - gipp.x k‖ := by
        calc ‖gipp.x (k - 1) - gipp.x k‖
            = ‖(gipp.x (k - 1) - gipp.x_tilde k) + (gipp.x_tilde k - gipp.x k)‖ := by congr 1; abel
          _ ≤ ‖gipp.x (k - 1) - gipp.x_tilde k‖ + ‖gipp.x_tilde k - gipp.x k‖ := norm_add_le _ _
      have : ‖gipp.x (k - 1) - gipp.x_tilde k‖ = ‖gipp.x_tilde k - gipp.x (k - 1)‖ := norm_sub_rev _ _
      rw [this] at triangle
      calc ‖gipp.x (k - 1) - gipp.x k‖
          ≤ ‖gipp.x_tilde k - gipp.x (k - 1)‖ + ‖gipp.x_tilde k - gipp.x k‖ := triangle
        _ ≤ ‖gipp.x_tilde k - gipp.x (k - 1)‖ + Real.sqrt σ * ‖gipp.x_tilde k - gipp.x (k - 1)‖ := add_le_add_left xtilde_bound _
        _ = (1 + Real.sqrt σ) * ‖gipp.x_tilde k - gipp.x (k - 1)‖ := by ring

    -- Square both sides
    have lhs_nonneg : 0 ≤ gipp.lam k * ‖(gipp.lam k)⁻¹ • (gipp.x (k - 1) - gipp.x k)‖ := by
      positivity
    have : (gipp.lam k * ‖(gipp.lam k)⁻¹ • (gipp.x (k - 1) - gipp.x k)‖)^2 ≤
           ((1 + Real.sqrt σ) * ‖gipp.x_tilde k - gipp.x (k - 1)‖)^2 :=
      pow_le_pow_left lhs_nonneg lam_v_bound 2
    have sqrt_pos : 0 < 1 + Real.sqrt σ := by
      have : 0 ≤ Real.sqrt σ := Real.sqrt_nonneg σ
      linarith
    calc (gipp.lam k)^2 * ‖(gipp.lam k)⁻¹ • (gipp.x (k - 1) - gipp.x k)‖^2 / (1 + Real.sqrt σ)^2
        = (gipp.lam k * ‖(gipp.lam k)⁻¹ • (gipp.x (k - 1) - gipp.x k)‖)^2 / (1 + Real.sqrt σ)^2 := by rw [mul_pow]
      _ ≤ ((1 + Real.sqrt σ) * ‖gipp.x_tilde k - gipp.x (k - 1)‖)^2 / (1 + Real.sqrt σ)^2 := by
          apply div_le_div_of_nonneg_right this (sq_nonneg (1 + Real.sqrt σ))
      _ = ((1 + Real.sqrt σ)^2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2) / (1 + Real.sqrt σ)^2 := by ring
      _ = ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 := by
          field_simp [ne_of_gt (sq_pos_of_pos sqrt_pos)]

  -- Combine using max_le
  exact max_le bound1 bound2


-- Theorem 4 and supporting lemmas for GeneralizedInexactProximalPoint.lean

/-- Step 1: Basic inequality from Lemma 5(a) and Lemma 6 combined
    For each iteration k, we have:
    (1-σ)/2 ‖x̃ₖ - xₖ₋₁‖² ≤ 1/2 ‖x* - xₖ₋₁‖² - 1/2 ‖x* - xₖ‖² -/
lemma gamma_at_solution_nonpositive {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀)
    (k : ℕ) (hk : k > 0) (x_star : E) (h_sol : (0 : E) ∈ T.Operator x_star) :
    Gamma_general gipp k x_star ≤ 0 := by
  -- Use gamma_lower_bound with v = 0
  have lower := gamma_lower_bound gipp k hk x_star 0 h_sol
  unfold Gamma_general at lower ⊢
  -- From lower bound: inner (v_general gipp k) (x_star - gipp.x_tilde k) - gipp.eps k ≤
  --                   inner (v_general gipp k) (x_star - gipp.x_tilde k)
  -- This simplifies to: -gipp.eps k ≤ 0
  -- From the EpsEnlargement definition with v = 0:
  -- inner (gipp.x_tilde k - x_star) (v_general gipp k - 0) ≥ -gipp.eps k
  have enlarge := gipp.eps_enlargement_cond k hk
  unfold EpsEnlargement at enlarge
  simp at enlarge
  have := enlarge x_star 0 h_sol
  -- This gives: inner (v_general gipp k) (gipp.x_tilde k - x_star) ≥ -gipp.eps k
  -- Which means: inner (v_general gipp k) (x_star - gipp.x_tilde k) ≤ gipp.eps k
  have : inner (v_general gipp k) (x_star - gipp.x_tilde k) ≤ gipp.eps k := by
    have h1 : inner (gipp.x_tilde k - x_star) (v_general gipp k) ≥ -gipp.eps k := by
      unfold v_general
      simpa using enlarge x_star 0 h_sol
    rw [real_inner_comm] at h1
    have h2 : inner (v_general gipp k) (gipp.x_tilde k - x_star) ≥ -gipp.eps k := h1
    have h3 : -inner (v_general gipp k) (x_star - gipp.x_tilde k) ≥ -gipp.eps k := by
      have : gipp.x_tilde k - x_star = -(x_star - gipp.x_tilde k) := by abel
      rw [this, inner_neg_right] at h2
      exact h2
    linarith
  linarith

lemma theorem4_step1 {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀)
    (k : ℕ) (hk : k > 0) (x_star : E) (hsmooth : gipp.delta k = 0)
    (h_sol : (0 : E) ∈ T.Operator x_star) :
    (1 - σ) / 2 * ‖gipp.x_tilde k - gipp.x (k - 1)‖^2 ≤
    1/2 * ‖x_star - gipp.x (k - 1)‖^2 - 1/2 * ‖x_star - gipp.x k‖^2 := by
  -- Apply lemma6 with delta_k = 0
  have lem6 := lemma6 gipp k hk x_star
  rw [hsmooth] at lem6
  simp at lem6

  -- Show that Gamma_general gipp k x_star ≤ 0
  have gamma_nonpos := gamma_at_solution_nonpositive gipp k hk x_star h_sol

  -- Since λk > 0 and Gamma_general gipp k x_star ≤ 0
  have lam_pos := gipp.lam_pos k hk
  have : -gipp.lam k * Gamma_general gipp k x_star ≥ 0 := by
    have : gipp.lam k * Gamma_general gipp k x_star ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt lam_pos) gamma_nonpos
    linarith

  -- From lemma6: -λk Γk(x*) + (1-σ)/2 ‖x̃k - xk-1‖² ≤ ½‖x* - xk-1‖² - ½‖x* - xk‖²
  -- Since -λk Γk(x*) ≥ 0, we get the desired result
  linarith

/-- Step 2: Telescoping sum inequality
    Summing the basic inequality over k iterations:
    (1-σ)/2 ∑ᵢ₌₁ᵏ ‖x̃ᵢ - xᵢ₋₁‖² ≤ 1/2 ‖x₀ - x*‖² - 1/2 ‖xₖ - x*‖² -/
lemma theorem4_step2 {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀)
    (k : ℕ) (x_star : E) (h_sol : (0 : E) ∈ T.Operator x_star)
    (hsmooth : ∀ i : ℕ, 0 < i → i ≤ k → gipp.delta i = 0) :
    (1 - σ) / 2 * ∑ i in Finset.range k, ‖gipp.x_tilde (i + 1) - gipp.x i‖^2 ≤
    1/2 * ‖x₀ - x_star‖^2 - 1/2 * ‖gipp.x k - x_star‖^2 := by

  -- Step 1: Apply lemma6 to each iteration with delta = 0
  have h : ∀ i : ℕ, i < k →
    -gipp.lam (i + 1) * Gamma_general gipp (i + 1) x_star +
    (1 - σ) / 2 * ‖gipp.x_tilde (i + 1) - gipp.x i‖^2 ≤
    1/2 * ‖x_star - gipp.x i‖^2 - 1/2 * ‖x_star - gipp.x (i + 1)‖^2 := by
    intro i hi
    have pos_idx : 0 < i + 1 := by omega
    have le_k : i + 1 ≤ k := by omega
    have delta_eq := hsmooth (i + 1) pos_idx le_k
    have lem6 := lemma6 gipp (i + 1) pos_idx x_star
    rw [delta_eq] at lem6
    simp only [Nat.add_sub_cancel] at lem6
    linarith

  -- Step 2: Sum both sides
  have sum_h : ∑ i in Finset.range k,
    (-gipp.lam (i + 1) * Gamma_general gipp (i + 1) x_star +
    (1 - σ) / 2 * ‖gipp.x_tilde (i + 1) - gipp.x i‖^2) ≤
    ∑ i in Finset.range k,
    (1/2 * ‖x_star - gipp.x i‖^2 - 1/2 * ‖x_star - gipp.x (i + 1)‖^2) := by
    apply Finset.sum_le_sum
    intro i hi
    exact h i (Finset.mem_range.mp hi)

  -- Step 3: Split the LHS
  have lhs_split : ∑ i in Finset.range k,
    (-gipp.lam (i + 1) * Gamma_general gipp (i + 1) x_star +
    (1 - σ) / 2 * ‖gipp.x_tilde (i + 1) - gipp.x i‖^2) =
    ∑ i in Finset.range k, (-gipp.lam (i + 1) * Gamma_general gipp (i + 1) x_star) +
    ∑ i in Finset.range k, ((1 - σ) / 2 * ‖gipp.x_tilde (i + 1) - gipp.x i‖^2) :=
    Finset.sum_add_distrib

  -- Step 4: Telescoping sum on RHS
  have telescope : ∑ i in Finset.range k,
    (1/2 * ‖x_star - gipp.x i‖^2 - 1/2 * ‖x_star - gipp.x (i + 1)‖^2) =
    1/2 * ‖x_star - gipp.x 0‖^2 - 1/2 * ‖x_star - gipp.x k‖^2 := by
    have h_tele : ∀ n : ℕ,
      ∑ i in Finset.range n, (‖x_star - gipp.x i‖^2 - ‖x_star - gipp.x (i + 1)‖^2) =
      ‖x_star - gipp.x 0‖^2 - ‖x_star - gipp.x n‖^2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih]; ring
    convert congr_arg (· / 2) (h_tele k) using 1
    · simp only [Finset.sum_div]; congr 1 with i; ring
    · ring

  -- Apply the simplifications
  rw [lhs_split, telescope] at sum_h

  -- Use x_init
  have : gipp.x 0 = x₀ := gipp.x_init
  rw [this] at sum_h

  -- Show that the Gamma sum is non-positive
  have gamma_sum_nonpos : ∑ i in Finset.range k, -gipp.lam (i + 1) * Gamma_general gipp (i + 1) x_star ≥ 0 := by
    apply Finset.sum_nonneg
    intro i hi
    have pos_idx : 0 < i + 1 := by omega
    have gamma_nonpos := gamma_at_solution_nonpositive gipp (i + 1) pos_idx x_star h_sol
    have lam_pos := gipp.lam_pos (i + 1) pos_idx
    have : gipp.lam (i + 1) * Gamma_general gipp (i + 1) x_star ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt lam_pos) gamma_nonpos
    linarith

  have norm_sym1 : ‖x₀ - x_star‖^2 = ‖x_star - x₀‖^2 := by rw [norm_sub_rev]
  have norm_sym2 : ‖gipp.x k - x_star‖^2 = ‖x_star - gipp.x k‖^2 := by rw [norm_sub_rev]

  -- Apply the bound, dropping the non-positive Gamma sum
  calc (1 - σ) / 2 * ∑ i in Finset.range k, ‖gipp.x_tilde (i + 1) - gipp.x i‖^2
      = ∑ i in Finset.range k, ((1 - σ) / 2 * ‖gipp.x_tilde (i + 1) - gipp.x i‖^2) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ i in Finset.range k, (-gipp.lam (i + 1) * Gamma_general gipp (i + 1) x_star) +
        ∑ i in Finset.range k, ((1 - σ) / 2 * ‖gipp.x_tilde (i + 1) - gipp.x i‖^2) := by
          linarith [gamma_sum_nonpos]
    _ ≤ 1/2 * ‖x_star - x₀‖^2 - 1/2 * ‖x_star - gipp.x k‖^2 := sum_h
    _ = 1/2 * ‖x₀ - x_star‖^2 - 1/2 * ‖gipp.x k - x_star‖^2 := by
          rw [norm_sym1, norm_sym2]

/-- Step 3: Drop the negative term
    Since ‖xₖ - x*‖² ≥ 0, we can strengthen the bound:
    (1-σ)/2 ∑ᵢ₌₁ᵏ ‖x̃ᵢ - xᵢ₋₁‖² ≤ 1/2 ‖x₀ - x*‖² -/
lemma theorem4_step3 {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀)
    (k : ℕ) (hk : k > 0) (x_star : E) (h_sol : (0 : E) ∈ T.Operator x_star)
    (hsmooth : ∀ i : ℕ, 0 < i → i ≤ k → gipp.delta i = 0) :
    (1 - σ) / 2 * ∑ i in Finset.range k, ‖gipp.x_tilde (i + 1) - gipp.x i‖^2 ≤
    1/2 * ‖x₀ - x_star‖^2 := by

  -- Step 1: Use that Gamma_general is nonpositive at the solution
  have gamma_nonpos : ∀ i : ℕ, 0 < i → i ≤ k →
      Gamma_general gipp i x_star ≤ 0 := by
    intro i hi hik
    exact gamma_at_solution_nonpositive gipp i hi x_star h_sol

  -- Step 2: Apply lemma6 to each iteration
  have h : ∀ i : ℕ, 0 < i → i ≤ k →
      (1 - σ) / 2 * ‖gipp.x_tilde i - gipp.x (i - 1)‖^2 ≤
      gipp.delta i + 1/2 * ‖x_star - gipp.x (i - 1)‖^2 -
      1/2 * ‖x_star - gipp.x i‖^2 + gipp.lam i * Gamma_general gipp i x_star := by
    intro i hi hik
    have lem := lemma6 gipp i hi x_star
    linarith

  -- Step 3: Apply smoothness condition and gamma nonpositivity
  have h' : ∀ i : ℕ, 0 < i → i ≤ k →
      (1 - σ) / 2 * ‖gipp.x_tilde i - gipp.x (i - 1)‖^2 ≤
      1/2 * ‖x_star - gipp.x (i - 1)‖^2 - 1/2 * ‖x_star - gipp.x i‖^2 := by
    intro i hi hik
    have hi_bounds := h i hi hik
    have delta_zero := hsmooth i hi hik
    have gamma_np := gamma_nonpos i hi hik
    have lam_pos := gipp.lam_pos i hi
    calc (1 - σ) / 2 * ‖gipp.x_tilde i - gipp.x (i - 1)‖^2
        ≤ gipp.delta i + 1/2 * ‖x_star - gipp.x (i - 1)‖^2 -
          1/2 * ‖x_star - gipp.x i‖^2 + gipp.lam i * Gamma_general gipp i x_star := hi_bounds
      _ = 0 + 1/2 * ‖x_star - gipp.x (i - 1)‖^2 -
          1/2 * ‖x_star - gipp.x i‖^2 + gipp.lam i * Gamma_general gipp i x_star := by
            rw [delta_zero]
      _ ≤ 1/2 * ‖x_star - gipp.x (i - 1)‖^2 - 1/2 * ‖x_star - gipp.x i‖^2 := by
            have : gipp.lam i * Gamma_general gipp i x_star ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (le_of_lt lam_pos) gamma_np
            linarith [this]

  -- Step 4: Sum over all iterations
  have sum_ineq : ∑ i in Finset.range k,
      ((1 - σ) / 2 * ‖gipp.x_tilde (i + 1) - gipp.x i‖^2) ≤
      ∑ i in Finset.range k,
      (1/2 * ‖x_star - gipp.x i‖^2 - 1/2 * ‖x_star - gipp.x (i + 1)‖^2) := by
    apply Finset.sum_le_sum
    intro i hi
    have i_pos : 0 < i + 1 := Nat.succ_pos i
    have i_le : i + 1 ≤ k := by
      have : i < k := Finset.mem_range.mp hi
      omega
    exact h' (i + 1) i_pos i_le

  -- Step 5: Simplify LHS
  have lhs_eq : (1 - σ) / 2 * ∑ i in Finset.range k, ‖gipp.x_tilde (i + 1) - gipp.x i‖^2 =
      ∑ i in Finset.range k, ((1 - σ) / 2 * ‖gipp.x_tilde (i + 1) - gipp.x i‖^2) := by
    rw [Finset.mul_sum]

  -- Step 6: Telescope the RHS
  have telescope : ∑ i in Finset.range k,
      (1/2 * ‖x_star - gipp.x i‖^2 - 1/2 * ‖x_star - gipp.x (i + 1)‖^2) =
      1/2 * ‖x_star - gipp.x 0‖^2 - 1/2 * ‖x_star - gipp.x k‖^2 := by
    have h_telescoping : ∀ n : ℕ,
      ∑ i in Finset.range n, (‖x_star - gipp.x i‖^2 - ‖x_star - gipp.x (i + 1)‖^2)
      = ‖x_star - gipp.x 0‖^2 - ‖x_star - gipp.x n‖^2 := by
      intro n
      induction n with
      | zero => simp [Finset.range_zero]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    have := h_telescoping k
    convert congr_arg (fun x => x / 2) this using 1
    · simp only [Finset.sum_div]
      congr 1 with i
      ring
    · ring

  -- Step 7: Combine and use x_init
  rw [lhs_eq]
  calc ∑ i in Finset.range k, ((1 - σ) / 2 * ‖gipp.x_tilde (i + 1) - gipp.x i‖^2)
      ≤ ∑ i in Finset.range k,
        (1/2 * ‖x_star - gipp.x i‖^2 - 1/2 * ‖x_star - gipp.x (i + 1)‖^2) := sum_ineq
    _ = 1/2 * ‖x_star - gipp.x 0‖^2 - 1/2 * ‖x_star - gipp.x k‖^2 := telescope
    _ ≤ 1/2 * ‖x_star - gipp.x 0‖^2 := by linarith [sq_nonneg ‖x_star - gipp.x k‖]
    _ = 1/2 * ‖x_star - x₀‖^2 := by rw [gipp.x_init]
    _ = 1/2 * ‖x₀ - x_star‖^2 := by rw [norm_sub_rev]

/-- Step 4: Rearrange to get sum bound
    ∑ᵢ₌₁ᵏ ‖x̃ᵢ - xᵢ₋₁‖² ≤ ‖x₀ - x*‖²/(1-σ) -/
lemma theorem4_step4 {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀)
    (k : ℕ) (hk : k > 0) (x_star : E) (h_sol : (0 : E) ∈ T.Operator x_star)
    (hsmooth : ∀ i : ℕ, 0 < i → i ≤ k → gipp.delta i = 0) :
    ∑ i in Finset.range k, ‖gipp.x_tilde (i + 1) - gipp.x i‖^2 ≤
    ‖x₀ - x_star‖^2 / (1 - σ) := by

  -- Step 1: Apply lemma6 to each iteration
  have h_each : ∀ i : ℕ, i < k →
    -gipp.lam (i + 1) * Gamma_general gipp (i + 1) x_star +
    (1 - σ) / 2 * ‖gipp.x_tilde (i + 1) - gipp.x i‖^2 ≤
    gipp.delta (i + 1) + 1/2 * ‖x_star - gipp.x i‖^2 -
    1/2 * ‖x_star - gipp.x (i + 1)‖^2 := by
    intro i hi
    have hi_pos : 0 < i + 1 := Nat.succ_pos i
    exact lemma6 gipp (i + 1) hi_pos x_star

  -- Step 2: Since 0 ∈ T(x_star), we have Gamma_general(x_star) ≤ 0
  have gamma_nonpos : ∀ i : ℕ, 0 < i → i ≤ k →
    Gamma_general gipp i x_star ≤ 0 := by
    intro i hi_pos hi_le
    exact gamma_at_solution_nonpositive gipp i hi_pos x_star h_sol

  -- Step 3: Simplify with delta_i = 0 and Gamma ≤ 0
  have h_simplified : ∀ i : ℕ, i < k →
    (1 - σ) / 2 * ‖gipp.x_tilde (i + 1) - gipp.x i‖^2 ≤
    1/2 * ‖x_star - gipp.x i‖^2 - 1/2 * ‖x_star - gipp.x (i + 1)‖^2 := by
    intro i hi
    have hi_pos : 0 < i + 1 := Nat.succ_pos i
    have hi_le : i + 1 ≤ k := Nat.succ_le_of_lt hi
    have delta_zero := hsmooth (i + 1) hi_pos hi_le
    have gamma_np := gamma_nonpos (i + 1) hi_pos hi_le
    have lam_pos := gipp.lam_pos (i + 1) hi_pos
    have from_lemma6 := h_each i hi
    rw [delta_zero] at from_lemma6
    have : -gipp.lam (i + 1) * Gamma_general gipp (i + 1) x_star ≥ 0 := by
      have : gipp.lam (i + 1) * Gamma_general gipp (i + 1) x_star ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt lam_pos) gamma_np
      linarith
    linarith

  -- Step 4: Sum both sides
  have sum_ineq : ∑ i in Finset.range k,
    ((1 - σ) / 2 * ‖gipp.x_tilde (i + 1) - gipp.x i‖^2) ≤
    ∑ i in Finset.range k,
    (1/2 * ‖x_star - gipp.x i‖^2 - 1/2 * ‖x_star - gipp.x (i + 1)‖^2) := by
    apply Finset.sum_le_sum
    intro i hi
    exact h_simplified i (Finset.mem_range.mp hi)

  -- Step 5: Telescoping sum on RHS
  have telescope : ∑ i in Finset.range k,
    (1/2 * ‖x_star - gipp.x i‖^2 - 1/2 * ‖x_star - gipp.x (i + 1)‖^2)
    = 1/2 * ‖x_star - gipp.x 0‖^2 - 1/2 * ‖x_star - gipp.x k‖^2 := by
    have h_telescoping : ∀ n : ℕ,
      ∑ i in Finset.range n, (‖x_star - gipp.x i‖^2 - ‖x_star - gipp.x (i + 1)‖^2)
      = ‖x_star - gipp.x 0‖^2 - ‖x_star - gipp.x n‖^2 := by
      intro n
      induction n with
      | zero => simp [Finset.range_zero]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    have := h_telescoping k
    convert congr_arg (fun x => x / 2) this using 1
    · simp only [Finset.sum_div]
      congr 1 with i
      ring
    · ring

  -- Step 6: Use x_init
  have x0_eq : gipp.x 0 = x₀ := gipp.x_init
  rw [x0_eq] at telescope

  -- Step 7: Combine and rearrange
  have σ_bounds := gipp.σ_bound
  have σ_ne : 1 - σ ≠ 0 := by linarith
  calc ∑ i in Finset.range k, ‖gipp.x_tilde (i + 1) - gipp.x i‖^2
      = (2 / (1 - σ)) * ((1 - σ) / 2 * ∑ i in Finset.range k, ‖gipp.x_tilde (i + 1) - gipp.x i‖^2) := by
          field_simp [σ_ne]
          ring
    _ = (2 / (1 - σ)) * (∑ i in Finset.range k, ((1 - σ) / 2 * ‖gipp.x_tilde (i + 1) - gipp.x i‖^2)) := by
          rw [Finset.mul_sum]
    _ ≤ (2 / (1 - σ)) * (∑ i in Finset.range k,
          (1/2 * ‖x_star - gipp.x i‖^2 - 1/2 * ‖x_star - gipp.x (i + 1)‖^2)) := by
          apply mul_le_mul_of_nonneg_left sum_ineq
          apply div_nonneg
          · norm_num
          · linarith
    _ = (2 / (1 - σ)) * (1/2 * ‖x₀ - x_star‖^2 - 1/2 * ‖x_star - gipp.x k‖^2) := by
          rw [telescope, norm_sub_rev]
    _ ≤ (2 / (1 - σ)) * (1/2 * ‖x₀ - x_star‖^2) := by
          apply mul_le_mul_of_nonneg_left
          · have : 0 ≤ 1/2 * ‖x_star - gipp.x k‖^2 := by positivity
            linarith
          · apply div_nonneg; norm_num; linarith
    _ = ‖x₀ - x_star‖^2 / (1 - σ) := by
          field_simp
          ring
/-- Step 5: Apply Lemma 7 (theta_bound) to get theta sum bound
    ∑ᵢ₌₁ᵏ θᵢ ≤ ∑ᵢ₌₁ᵏ ‖x̃ᵢ - xᵢ₋₁‖² -/
lemma theorem4_step5 {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀)
    (k : ℕ) (hk : k > 0)
    (hsmooth : ∀ i : ℕ, 0 < i → i ≤ k → gipp.delta i = 0) :
    ∑ i in Finset.range k, theta gipp (i + 1) ≤
    ∑ i in Finset.range k, ‖gipp.x_tilde (i + 1) - gipp.x i‖^2 := by
  sorry

/-- Step 6: Relate minimum to sum
    k * min_{1≤i≤k} θᵢ ≤ ∑ᵢ₌₁ᵏ θᵢ -/
lemma theorem4_step6 {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀)
    (k : ℕ) (hk : k > 0) :
    (k : ℝ) * (⨅ i ∈ Finset.range k, theta gipp (i + 1)) ≤
    ∑ i in Finset.range k, theta gipp (i + 1) := by
  sorry

/-- Step 7: The existence of an index achieving the minimum
    There exists i ∈ {1,...,k} such that θᵢ = min_{1≤j≤k} θⱼ -/
lemma theorem4_step7 {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀)
    (k : ℕ) (hk : k > 0) :
    ∃ i ∈ Finset.range k, theta gipp (i + 1) = ⨅ j ∈ Finset.range k, theta gipp (j + 1) := by
  sorry

/-- Step 8: From theta bound to epsilon bound
    If θᵢ ≤ bound, then εᵢ ≤ σ·bound/(2λᵢ) -/
lemma theorem4_step8_eps {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀)
    (i : ℕ) (hi : i > 0) (bound : ℝ) (hbound : theta gipp i ≤ bound) :
    gipp.eps i ≤ σ * bound / (2 * gipp.lam i) := by
  sorry

/-- Step 9: From theta bound to v norm bound
    If θᵢ ≤ bound, then ‖vᵢ‖² ≤ (1+√σ)²·bound/λᵢ² -/
lemma theorem4_step9_vnorm {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀)
    (i : ℕ) (hi : i > 0) (bound : ℝ) (hbound : theta gipp i ≤ bound) :
    ‖v_general gipp i‖^2 ≤ (1 + Real.sqrt σ)^2 * bound / (gipp.lam i)^2 := by
  sorry

/-- Theorem 4 (Pointwise convergence):
    The generalized IPP framework satisfies:
    min_{1≤i≤k} θᵢ ≤ ‖x₀ - x*‖²/((1-σ)k)

    Then, there exists i ≤ k such that:
    εᵢ ≤ σ‖x₀ - x*‖²/(2λᵢ(1-σ)k)
    ‖vᵢ‖² ≤ (1+√σ)²‖x₀ - x*‖²/(λᵢ²(1-σ)k) -/
theorem theorem4 {T : MonotoneOperator E} {σ : ℝ} {x₀ : E}
    (gipp : GeneralizedInexactProximalPoint T σ x₀)
    (k : ℕ) (hk : k > 0) (x_star : E) (h_sol : (0 : E) ∈ T.Operator x_star)
    (hsmooth : ∀ i : ℕ, 0 < i → i ≤ k → gipp.delta i = 0) :
    (⨅ i ∈ Finset.range k, theta gipp (i + 1)) ≤ ‖x₀ - x_star‖^2 / ((1 - σ) * k) ∧
    ∃ i ∈ Finset.range k,
      gipp.eps (i + 1) ≤ σ * ‖x₀ - x_star‖^2 / (2 * gipp.lam (i + 1) * (1 - σ) * k) ∧
      ‖v_general gipp (i + 1)‖^2 ≤
        (1 + Real.sqrt σ)^2 * ‖x₀ - x_star‖^2 / ((gipp.lam (i + 1))^2 * (1 - σ) * k) := by

  -- Part 1: Prove the minimum theta bound
  have min_theta_bound : (⨅ i ∈ Finset.range k, theta gipp (i + 1)) ≤
      ‖x₀ - x_star‖^2 / ((1 - σ) * k) := by
    -- Step 4: Get sum bound on norms
    have sum_norm_bound := theorem4_step4 gipp k hk x_star h_sol hsmooth

    -- Step 5: Apply theta_bound lemma to bound sum of thetas
    have sum_theta_bound := theorem4_step5 gipp k hk hsmooth

    -- Step 6: Relate minimum to sum
    have min_to_sum := theorem4_step6 gipp k hk

    -- Combine: k * min ≤ sum θᵢ ≤ sum ‖x̃ᵢ - xᵢ₋₁‖² ≤ ‖x₀ - x*‖²/(1-σ)
    have k_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    calc ⨅ i ∈ Finset.range k, theta gipp (i + 1)
        ≤ (∑ i in Finset.range k, theta gipp (i + 1)) / k := by
          rw [le_div_iff₀ k_pos, mul_comm]
          exact min_to_sum
      _ ≤ (∑ i in Finset.range k, ‖gipp.x_tilde (i + 1) - gipp.x i‖^2) / k := by
          apply div_le_div_of_nonneg_right sum_theta_bound (le_of_lt k_pos)
      _ ≤ (‖x₀ - x_star‖^2 / (1 - σ)) / k := by
          apply div_le_div_of_nonneg_right sum_norm_bound (le_of_lt k_pos)
      _ = ‖x₀ - x_star‖^2 / ((1 - σ) * k) := by
          rw [div_div]

  -- Part 2: Show existence of i achieving the bound and derive eps, vnorm bounds
  constructor
  · exact min_theta_bound
  · -- Step 7: Get the index achieving the minimum
    obtain ⟨i, hi_mem, hi_eq⟩ := theorem4_step7 gipp k hk
    use i, hi_mem

    -- The bound that theta_i satisfies
    have theta_i_bound : theta gipp (i + 1) ≤ ‖x₀ - x_star‖^2 / ((1 - σ) * k) := by
      rw [hi_eq]
      exact min_theta_bound

    -- Get i > 0
    have hi_pos : i + 1 > 0 := Nat.succ_pos i

    constructor
    · -- Step 8: Apply epsilon bound
      have := theorem4_step8_eps gipp (i + 1) hi_pos _ theta_i_bound
      calc gipp.eps (i + 1)
          ≤ σ * (‖x₀ - x_star‖^2 / ((1 - σ) * k)) / (2 * gipp.lam (i + 1)) := this
        _ = σ * ‖x₀ - x_star‖^2 / (2 * gipp.lam (i + 1) * (1 - σ) * k) := by field_simp; ring
    · -- Step 9: Apply v norm bound
      have := theorem4_step9_vnorm gipp (i + 1) hi_pos _ theta_i_bound
      calc ‖v_general gipp (i + 1)‖^2
          ≤ (1 + Real.sqrt σ)^2 * (‖x₀ - x_star‖^2 / ((1 - σ) * k)) / (gipp.lam (i + 1))^2 := this
        _ = (1 + Real.sqrt σ)^2 * ‖x₀ - x_star‖^2 / ((gipp.lam (i + 1))^2 * (1 - σ) * k) := by field_simp; ring
