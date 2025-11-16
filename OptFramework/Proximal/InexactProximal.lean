import Optlib.Function.Lsmooth

namespace InexactProximal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x₀ xm : E} {f : E → ℝ} {f' : E → E} {σ : ℝ}

open Set Finset

noncomputable def x_star (f : E → ℝ) (h : ∃ x : E, IsMinOn f univ x) : E :=
  Classical.choose h


def EpsSubderivAt (f : E → ℝ) (x : E) (ε : ℝ) : Set E :=
  {g | ∀ y, f y ≥ f x + inner g (y - x) - ε}

class InexactProximalPoint (f : E → ℝ) (f' : E → E) (σ : ℝ) (x₀ : E) where
  x : ℕ → E
  x_tilde : ℕ → E
  lam : ℕ → ℝ
  delta : ℕ → ℝ
  eps : ℕ → ℝ
  σ_bound : 0 < σ ∧ σ ≤ 1
  x_init : x 0 = x₀
  fc: ConvexOn ℝ univ f
  lam_pos : ∀ k : ℕ, k > 0 → 0 < lam k
  delta_nonneg : ∀ k : ℕ, k > 0 → 0 ≤ delta k
  subgrad_cond : ∀ k : ℕ, k > 0 →
    (1 / lam k) • (x (k - 1) - x k) ∈ EpsSubderivAt f (x_tilde k) (eps k)
  prox_cond : ∀ k : ℕ, k > 0 →
    ‖x k - x_tilde k‖^2 + 2 * lam k * eps k ≤
    σ * ‖x_tilde k - x (k - 1)‖^2 + 2 * delta k

noncomputable def v (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) : E :=
  (ippm.lam k)⁻¹ • (ippm.x (k - 1) - ippm.x k)

noncomputable def Gamma (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (x : E) : ℝ :=
  f (ippm.x_tilde k) + inner (v ippm k) (x - ippm.x_tilde k) - ippm.eps k
noncomputable def objective (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (x : E) : ℝ :=
  ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2
-- Now Lemma 1(a) is provable
omit [CompleteSpace E] in
lemma inexact_proximal_lower_bound (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (hk : k > 0) :
    ∀ x : E, Gamma ippm k x ≤ f x := by
  intro x
  unfold Gamma v
  have h := ippm.subgrad_cond k hk
  unfold EpsSubderivAt at h
  simp at h
  specialize h x
  linarith
omit [CompleteSpace E] in
lemma eps_subgrad_at_xk (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (hk : k > 0) :
    f (ippm.x k) ≥ f (ippm.x_tilde k) +
    inner (v ippm k) (ippm.x k - ippm.x_tilde k) - ippm.eps k := by
  have h := ippm.subgrad_cond k hk
  simp [EpsSubderivAt] at h
  simpa [v] using h (ippm.x k)

omit [CompleteSpace E] in
-- Helper Lemma 2: Rearrange to get the gap
lemma gap_from_subgrad (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (hk : k > 0) :
    f (ippm.x_tilde k) - f (ippm.x k) ≤
    -inner (v ippm k) (ippm.x k - ippm.x_tilde k) + ippm.eps k := by
  have h := eps_subgrad_at_xk ippm k hk
  linarith

omit [CompleteSpace E] in
-- Helper Lemma 3: Simplify the inner product term
lemma inner_product_expansion (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) :
    -inner (v ippm k) (ippm.x k - ippm.x_tilde k) =
    (1 / ippm.lam k) * inner (ippm.x (k-1) - ippm.x k) (ippm.x_tilde k - ippm.x k) := by
  unfold v
  rw [inner_smul_left]
  simp [real_inner_smul_left]
  have h : ippm.x k - ippm.x_tilde k = -(ippm.x_tilde k - ippm.x k) := by abel
  rw [h, inner_neg_right]
  simp [mul_neg, neg_neg]

omit [CompleteSpace E] in
-- Helper Lemma 4: Key norm identity
lemma norm_identity_for_three_points (a b c : E) :
    2 * inner (a - b) (c - b) = ‖a - b‖^2 + ‖c - b‖^2 - ‖a - c‖^2 := by
  have h : a - c = (a - b) - (c - b) := by abel
  have expand : ‖(a - b) - (c - b)‖^2 =
      ‖a - b‖^2 - 2 * inner (a - b) (c - b) + ‖c - b‖^2 := by
    apply norm_sub_sq_real
  rw [← h] at expand
  linarith

omit [CompleteSpace E] in
-- Helper Lemma 5: Express as sum of norms
lemma inner_as_norm_difference (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (_hk : k > 0) :
    (1 / ippm.lam k) * inner (ippm.x (k-1) - ippm.x k) (ippm.x_tilde k - ippm.x k) =
    (1 / (2 * ippm.lam k)) * (‖ippm.x (k-1) - ippm.x k‖^2 +
                               ‖ippm.x_tilde k - ippm.x k‖^2 -
                               ‖ippm.x (k-1) - ippm.x_tilde k‖^2) := by
  have h := norm_identity_for_three_points (ippm.x (k-1)) (ippm.x k) (ippm.x_tilde k)
  -- Divide both sides of the identity by (2 * lam k)
  have h' := congrArg (fun t : ℝ => t / (2 * ippm.lam k)) h
  -- Turn divisions into multiplications by inverses
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'

omit [CompleteSpace E] in
-- Helper Lemma 6: Combine with added terms
lemma combine_norm_terms (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (hk : k > 0) :
    (1 / ippm.lam k) * inner (ippm.x (k-1) - ippm.x k) (ippm.x_tilde k - ippm.x k) +
    (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k-1)‖^2 -
    (1 / (2 * ippm.lam k)) * ‖ippm.x k - ippm.x (k-1)‖^2 =
    (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x k‖^2 := by
  rw [inner_as_norm_difference ippm k hk]
  have h1 : ‖ippm.x_tilde k - ippm.x (k-1)‖^2 = ‖ippm.x (k-1) - ippm.x_tilde k‖^2 := by
    rw [norm_sub_rev]
  have h2 : ‖ippm.x k - ippm.x (k-1)‖^2 = ‖ippm.x (k-1) - ippm.x k‖^2 := by
    rw [norm_sub_rev]
  rw [h1, h2]
  field_simp
  ring

omit [CompleteSpace E] in
-- Helper Lemma 7: Apply the proximal condition to get final bound
lemma apply_prox_condition (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (hk : k > 0) :
    (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x k‖^2 + ippm.eps k ≤
    (σ / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k-1)‖^2 + ippm.delta k / ippm.lam k := by
  have prox := ippm.prox_cond k hk
  have h : ‖ippm.x k - ippm.x_tilde k‖^2 = ‖ippm.x_tilde k - ippm.x k‖^2 := by
    rw [norm_sub_rev]
  rw [h] at prox
  have lam_pos := ippm.lam_pos k hk
  calc
    (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x k‖^2 + ippm.eps k
        = (‖ippm.x_tilde k - ippm.x k‖^2 + 2 * ippm.lam k * ippm.eps k) / (2 * ippm.lam k) := by
          field_simp; ring
      _ ≤ (σ * ‖ippm.x_tilde k - ippm.x (k-1)‖^2 + 2 * ippm.delta k) / (2 * ippm.lam k) := by
          gcongr
      _ = (σ / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k-1)‖^2 + ippm.delta k / ippm.lam k := by
          field_simp; ring

omit [CompleteSpace E] in
-- Main Lemma 1(b): Putting it all together
lemma inexact_proximal_optimality_gap_bound (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    f (ippm.x_tilde k) + (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2
      - f (ippm.x k) - (1 / (2 * ippm.lam k)) * ‖ippm.x k - ippm.x (k - 1)‖^2
    ≤ (σ / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 + ippm.delta k / ippm.lam k := by
  -- Start with the gap from subgradient
  have gap := gap_from_subgrad ippm k hk

  -- Express inner product in a useful form
  have inner_expand := inner_product_expansion ippm k
  rw [inner_expand] at gap

  -- Main calculation
  calc f (ippm.x_tilde k) + (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2
      - f (ippm.x k) - (1 / (2 * ippm.lam k)) * ‖ippm.x k - ippm.x (k - 1)‖^2
        = (f (ippm.x_tilde k) - f (ippm.x k)) +
          (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
          (1 / (2 * ippm.lam k)) * ‖ippm.x k - ippm.x (k - 1)‖^2 := by ring
      _ ≤ ((1 / ippm.lam k) * inner (ippm.x (k-1) - ippm.x k) (ippm.x_tilde k - ippm.x k) + ippm.eps k) +
          (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
          (1 / (2 * ippm.lam k)) * ‖ippm.x k - ippm.x (k - 1)‖^2 := by linarith [gap]
      _ = (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x k‖^2 + ippm.eps k := by
          rw [← combine_norm_terms ippm k hk]; ring
      _ ≤ (σ / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 + ippm.delta k / ippm.lam k :=
          apply_prox_condition ippm k hk

omit [CompleteSpace E] in
lemma gradient_zero_at_iterate (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    ippm.lam k • v ippm k + (ippm.x k - ippm.x (k - 1)) = 0 := by
  unfold v
  have lam_ne_zero : ippm.lam k ≠ 0 := ne_of_gt (ippm.lam_pos k hk)
  rw [smul_smul, mul_inv_cancel₀ lam_ne_zero, one_smul]
  abel

omit [CompleteSpace E] in
lemma inexact_proximal_minimizer (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    IsMinOn (objective ippm k) univ (ippm.x k) := by
  rw [isMinOn_univ_iff]
  intro y
  unfold objective Gamma

  -- Use the gradient zero condition
  have grad_zero := gradient_zero_at_iterate ippm k hk
  unfold v at grad_zero

  -- Key: rewrite using three-point identity
  suffices h : ippm.lam k * inner (v ippm k) (y - ippm.x_tilde k) + 1/2 * ‖y - ippm.x (k - 1)‖^2 ≥
               ippm.lam k * inner (v ippm k) (ippm.x k - ippm.x_tilde k) + 1/2 * ‖ippm.x k - ippm.x (k - 1)‖^2 by
    linarith

  -- Expand the inner products
  have inner_diff : ippm.lam k * inner (v ippm k) (y - ippm.x_tilde k) -
                    ippm.lam k * inner (v ippm k) (ippm.x k - ippm.x_tilde k) =
                    ippm.lam k * inner (v ippm k) (y - ippm.x k) := by
    rw [← mul_sub, ← inner_sub_right]
    congr 2
    abel

  -- Three-point norm identity
  have norm_expand : ‖y - ippm.x (k - 1)‖^2 - ‖ippm.x k - ippm.x (k - 1)‖^2 =
                     ‖y - ippm.x k‖^2 + 2 * inner (y - ippm.x k) (ippm.x k - ippm.x (k - 1)) := by
    have h : y - ippm.x (k - 1) = (y - ippm.x k) + (ippm.x k - ippm.x (k - 1)) := by abel
    have expand : ‖(y - ippm.x k) + (ippm.x k - ippm.x (k - 1))‖^2 =
        ‖y - ippm.x k‖^2 + 2 * inner (y - ippm.x k) (ippm.x k - ippm.x (k - 1)) +
        ‖ippm.x k - ippm.x (k - 1)‖^2 := by
      apply norm_add_sq_real
    rw [← h] at expand
    linarith

  -- Combine using grad_zero
  have key : ippm.lam k * inner (v ippm k) (y - ippm.x k) +
             inner (y - ippm.x k) (ippm.x k - ippm.x (k - 1)) = 0 := by
    calc ippm.lam k * inner (v ippm k) (y - ippm.x k) + inner (y - ippm.x k) (ippm.x k - ippm.x (k - 1))
        = inner (ippm.lam k • v ippm k) (y - ippm.x k) + inner (y - ippm.x k) (ippm.x k - ippm.x (k - 1)) := by
          simp [inner_smul_left]
      _ = inner (ippm.lam k • v ippm k) (y - ippm.x k) + inner (ippm.x k - ippm.x (k - 1)) (y - ippm.x k) := by
          simp [real_inner_comm]
      _ = inner (ippm.lam k • v ippm k + (ippm.x k - ippm.x (k - 1))) (y - ippm.x k) := by
          rw [← inner_add_left]
      _ = inner 0 (y - ippm.x k) := by
          unfold v; rw [grad_zero]
      _ = 0 := by rw [inner_zero_left]

  -- Now prove the suffices goal
  calc ippm.lam k * inner (v ippm k) (y - ippm.x_tilde k) + 1/2 * ‖y - ippm.x (k - 1)‖^2
      = ippm.lam k * inner (v ippm k) (ippm.x k - ippm.x_tilde k) +
        ippm.lam k * inner (v ippm k) (y - ippm.x k) +
        1/2 * ‖ippm.x k - ippm.x (k - 1)‖^2 +
        1/2 * (‖y - ippm.x k‖^2 + 2 * inner (y - ippm.x k) (ippm.x k - ippm.x (k - 1))) := by
          rw [← inner_diff, ← norm_expand]; ring
    _ = ippm.lam k * inner (v ippm k) (ippm.x k - ippm.x_tilde k) +
        1/2 * ‖ippm.x k - ippm.x (k - 1)‖^2 +
        1/2 * ‖y - ippm.x k‖^2 +
        (ippm.lam k * inner (v ippm k) (y - ippm.x k) + inner (y - ippm.x k) (ippm.x k - ippm.x (k - 1))) := by
          ring
    _ = ippm.lam k * inner (v ippm k) (ippm.x k - ippm.x_tilde k) +
        1/2 * ‖ippm.x k - ippm.x (k - 1)‖^2 +
        1/2 * ‖y - ippm.x k‖^2 := by
          rw [key]; ring
    _ ≥ ippm.lam k * inner (v ippm k) (ippm.x k - ippm.x_tilde k) +
        1/2 * ‖ippm.x k - ippm.x (k - 1)‖^2 := by
          linarith [sq_nonneg ‖y - ippm.x k‖]

omit [CompleteSpace E] in
-- Lemma: The infimum of the objective equals its value at xk
lemma objective_infimum_at_iterate (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    sInf ((objective ippm k) '' univ) = objective ippm k (ippm.x k) := by
  have min_at_xk := inexact_proximal_minimizer ippm k hk
  rw [isMinOn_univ_iff] at min_at_xk
  -- Show that objective ippm k (ippm.x k) is the infimum
  apply le_antisymm
  · -- sInf ((objective ippm k) '' univ) ≤ objective ippm k (ippm.x k)
    apply csInf_le
    · -- Bounded below
      use objective ippm k (ippm.x k)
      intros y hy
      obtain ⟨x, _, rfl⟩ := hy
      exact min_at_xk x
    · -- objective ippm k (ippm.x k) is in the image
      use ippm.x k
      simp
  · -- objective ippm k (ippm.x k) ≤ sInf ((objective ippm k) '' univ)
    apply le_csInf
    · -- The image is nonempty
      use objective ippm k (ippm.x k)
      use ippm.x k
      simp
    · -- objective ippm k (ippm.x k) is a lower bound
      intros y hy
      obtain ⟨x, _, rfl⟩ := hy
      exact min_at_xk x


omit [CompleteSpace E] in
-- Lemma: Identity relating objective at xk to objective at any point x
lemma objective_identity_with_norm (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) (x : E) :
    objective ippm k (ippm.x k) =
    objective ippm k x - 1/2 * ‖x - ippm.x k‖^2 := by
  unfold objective
  -- Gamma linearity
  have gamma_diff : Gamma ippm k x - Gamma ippm k (ippm.x k) = inner (v ippm k) (x - ippm.x k) := by
    unfold Gamma
    simp [inner_sub_right]


  -- Three-point identity
  have three_point : ‖x - ippm.x (k - 1)‖^2 - ‖ippm.x k - ippm.x (k - 1)‖^2 =
      ‖x - ippm.x k‖^2 + 2 * inner (x - ippm.x k) (ippm.x k - ippm.x (k - 1)) := by
    have h : x - ippm.x (k - 1) = (x - ippm.x k) + (ippm.x k - ippm.x (k - 1)) := by abel
    have expand : ‖(x - ippm.x k) + (ippm.x k - ippm.x (k - 1))‖^2 =
        ‖x - ippm.x k‖^2 + 2 * inner (x - ippm.x k) (ippm.x k - ippm.x (k - 1)) +
        ‖ippm.x k - ippm.x (k - 1)‖^2 := by
      apply norm_add_sq_real
    rw [← h] at expand
    linarith

  -- Use gradient zero condition
  have grad_zero := gradient_zero_at_iterate ippm k hk

  calc ippm.lam k * Gamma ippm k (ippm.x k) + 1/2 * ‖ippm.x k - ippm.x (k - 1)‖^2
      = ippm.lam k * Gamma ippm k x - ippm.lam k * inner (v ippm k) (x - ippm.x k) +
        1/2 * ‖ippm.x k - ippm.x (k - 1)‖^2 := by
          rw [← gamma_diff]; ring
    _ = ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2 -
        1/2 * (‖x - ippm.x (k - 1)‖^2 - ‖ippm.x k - ippm.x (k - 1)‖^2) -
        ippm.lam k * inner (v ippm k) (x - ippm.x k) := by ring
    _ = ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2 -
        1/2 * ‖x - ippm.x k‖^2 - inner (x - ippm.x k) (ippm.x k - ippm.x (k - 1)) -
        ippm.lam k * inner (v ippm k) (x - ippm.x k) := by
          rw [three_point]; ring
    _ = ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2 - 1/2 * ‖x - ippm.x k‖^2 -
        inner (x - ippm.x k) (ippm.lam k • v ippm k + (ippm.x k - ippm.x (k - 1))) := by
          rw [inner_add_right, inner_smul_right]
          rw [real_inner_comm (x - ippm.x k) (v ippm k)]
          ring_nf
    _ = ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2 - 1/2 * ‖x - ippm.x k‖^2 := by
          rw [grad_zero, inner_zero_right]
          ring

omit [CompleteSpace E] in
-- Lemma: Gamma evaluated at x_tilde k simplifies
lemma gamma_at_x_tilde (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) :
    Gamma ippm k (ippm.x_tilde k) = f (ippm.x_tilde k) - ippm.eps k := by
  unfold Gamma v
  simp [inner_zero_right, sub_self]

omit [CompleteSpace E] in
-- Lemma: Algebraic rearrangement for the objective terms
lemma objective_rearrangement (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) :
    ippm.lam k * (f (ippm.x_tilde k) - ippm.eps k) +
    1/2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
    1/2 * ‖ippm.x_tilde k - ippm.x k‖^2 =
    ippm.lam k * f (ippm.x_tilde k) +
    1/2 * (‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
           ‖ippm.x_tilde k - ippm.x k‖^2 -
           2 * ippm.lam k * ippm.eps k) := by
  ring

omit [CompleteSpace E] in
-- Lemma: Lower bound from proximal condition
lemma lower_bound_from_prox_condition (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
    ‖ippm.x_tilde k - ippm.x k‖^2 -
    2 * ippm.lam k * ippm.eps k
    ≥ (1 - σ) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 - 2 * ippm.delta k := by
  have prox := ippm.prox_cond k hk
  have norm_sym : ‖ippm.x k - ippm.x_tilde k‖^2 = ‖ippm.x_tilde k - ippm.x k‖^2 := by
    rw [norm_sub_rev]
  rw [norm_sym] at prox

  calc ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 - ‖ippm.x_tilde k - ippm.x k‖^2 - 2 * ippm.lam k * ippm.eps k
      = ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 - (‖ippm.x_tilde k - ippm.x k‖^2 + 2 * ippm.lam k * ippm.eps k) := by ring
    _ ≥ ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 - (σ * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 + 2 * ippm.delta k) := by linarith [prox]
    _ = (1 - σ) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 - 2 * ippm.delta k := by ring

omit [CompleteSpace E] in
lemma strengthen_lower_bound (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    ippm.lam k * f (ippm.x_tilde k) +
    (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
    ippm.delta k / 2
    ≥ ippm.lam k * f (ippm.x_tilde k) +
    (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
    ippm.delta k := by
  have delta_nonneg := ippm.delta_nonneg k hk
  linarith

omit [CompleteSpace E] in
theorem inexact_proximal_minimum_lower_bound (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    sInf ((objective ippm k) '' univ)
    ≥ ippm.lam k * f (ippm.x_tilde k) + (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2
      - ippm.delta k := by
  -- Step 1: The infimum equals the objective at xk
  rw [objective_infimum_at_iterate ippm k hk]

  -- Step 2: Use the identity to relate it to x_tilde k
  rw [objective_identity_with_norm ippm k hk (ippm.x_tilde k)]
  unfold objective

  -- Step 3: Simplify Gamma at x_tilde k
  rw [gamma_at_x_tilde ippm k]

  -- Step 4: Algebraic rearrangement
  rw [objective_rearrangement ippm k]

  -- Step 5: Apply lower bound from proximal condition
  have bound := lower_bound_from_prox_condition ippm k hk

  calc ippm.lam k * f (ippm.x_tilde k) +
       1/2 * (‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
              ‖ippm.x_tilde k - ippm.x k‖^2 -
              2 * ippm.lam k * ippm.eps k)
      ≥ ippm.lam k * f (ippm.x_tilde k) +
        1/2 * ((1 - σ) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 - 2 * ippm.delta k) := by
          linarith [bound]
    _ = ippm.lam k * f (ippm.x_tilde k) +
        (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
        ippm.delta k := by ring
    _ ≥ ippm.lam k * f (ippm.x_tilde k) +
        (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
        ippm.delta k := by linarith

omit [CompleteSpace E] in
lemma objective_lower_bound_via_gamma (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) (x : E) :
    ippm.lam k * f x + 1/2 * ‖x - ippm.x (k - 1)‖^2 ≥
    ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2 := by
  have gamma_bound := inexact_proximal_lower_bound ippm k hk x
  have lam_pos := ippm.lam_pos k hk
  have h : ippm.lam k * Gamma ippm k x ≤ ippm.lam k * f x :=
    mul_le_mul_of_nonneg_left gamma_bound (le_of_lt lam_pos)
  linarith

-- Helper Lemma: Identity relating objective at x to minimum plus distance to xk
omit [CompleteSpace E] in
lemma objective_decomposition (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) (x : E) :
    ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2 =
    sInf ((objective ippm k) '' univ) + 1/2 * ‖x - ippm.x k‖^2 := by
  rw [objective_infimum_at_iterate ippm k hk]
  have h := objective_identity_with_norm ippm k hk x
  unfold objective at h ⊢
  linarith

-- Main three-point inequality combining everything
omit [CompleteSpace E] in
lemma three_point_inequality_with_minimum (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) (x : E) :
    ippm.lam k * f x + 1/2 * ‖x - ippm.x (k - 1)‖^2 ≥
    ippm.lam k * f (ippm.x_tilde k) + (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
    ippm.delta k + 1/2 * ‖x - ippm.x k‖^2 := by
  calc ippm.lam k * f x + 1/2 * ‖x - ippm.x (k - 1)‖^2
      ≥ ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2 :=
        objective_lower_bound_via_gamma ippm k hk x
    _ = sInf ((objective ippm k) '' univ) + 1/2 * ‖x - ippm.x k‖^2 :=
        objective_decomposition ippm k hk x
    _ ≥ ippm.lam k * f (ippm.x_tilde k) + (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
        ippm.delta k + 1/2 * ‖x - ippm.x k‖^2 := by
          have bound := inexact_proximal_minimum_lower_bound ippm k hk
          linarith

omit [CompleteSpace E] in
theorem inexact_proximal_lemma2 (ippm : InexactProximalPoint f f' σ x₀)
    (f_min_exists : ∃ x_star : E, IsMinOn f univ x_star)
    (k : ℕ) (hk : k > 0) :
    ippm.lam k * (f (ippm.x_tilde k) - f (InexactProximal.x_star f f_min_exists)) +
    (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2
    ≤ ippm.delta k + 1/2 * ‖ippm.x (k - 1) - InexactProximal.x_star f f_min_exists‖^2 -
      1/2 * ‖ippm.x k - InexactProximal.x_star f f_min_exists‖^2 := by
  let xstar := InexactProximal.x_star f f_min_exists

  have three_pt := three_point_inequality_with_minimum ippm k hk xstar
  calc ippm.lam k * (f (ippm.x_tilde k) - f xstar) +
       (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2
      = ippm.lam k * f (ippm.x_tilde k) + (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
        ippm.lam k * f xstar := by ring
    _ ≤ ippm.lam k * f xstar + 1/2 * ‖xstar - ippm.x (k - 1)‖^2 -
        1/2 * ‖xstar - ippm.x k‖^2 -
        ippm.lam k * f xstar + ippm.delta k := by linarith [three_pt]
    _ = 1/2 * ‖xstar - ippm.x (k - 1)‖^2 - 1/2 * ‖xstar - ippm.x k‖^2 + ippm.delta k := by ring
    _ = ippm.delta k + 1/2 * ‖ippm.x (k - 1) - xstar‖^2 - 1/2 * ‖ippm.x k - xstar‖^2 := by
        rw [norm_sub_rev (ippm.x (k - 1)) xstar, norm_sub_rev (ippm.x k) xstar]
        ring

-- Step 1: Sum the key inequality over all iterations
omit [CompleteSpace E] in
lemma inexact_proximal_sum_lemma2 (ippm : InexactProximalPoint f f' σ x₀)
    (f_min_exists : ∃ x_star : E, IsMinOn f univ x_star)
    (k : ℕ+) :
    let xstar := InexactProximal.x_star f f_min_exists
    ∑ i in Finset.range k, ippm.lam (i + 1) * (f (ippm.x_tilde (i + 1)) - f xstar) +
    ∑ i in Finset.range k, ((1 - σ) / 2 * ‖ippm.x_tilde (i + 1) - ippm.x i‖^2)
    ≤ ∑ i in Finset.range k, ippm.delta (i + 1) +
      1/2 * ‖x₀ - xstar‖^2 - 1/2 * ‖ippm.x k - xstar‖^2 := by
  let xstar := InexactProximal.x_star f f_min_exists

  -- Step 1: Apply lemma2 to each term
  have h : ∀ i : ℕ, i < k →
    ippm.lam (i + 1) * (f (ippm.x_tilde (i + 1)) - f xstar) +
    (1 - σ) / 2 * ‖ippm.x_tilde (i + 1) - ippm.x i‖^2
    ≤ ippm.delta (i + 1) + 1/2 * ‖ippm.x i - xstar‖^2 - 1/2 * ‖ippm.x (i + 1) - xstar‖^2 := by
    intro i _
    have pos_idx : 0 < i + 1 := by omega
    exact inexact_proximal_lemma2 ippm f_min_exists (i + 1) pos_idx

  -- Step 2: Sum both sides of th e inequality
  have sum_h : ∑ i in Finset.range k,
    (ippm.lam (i + 1) * (f (ippm.x_tilde (i + 1)) - f xstar) +
    (1 - σ) / 2 * ‖ippm.x_tilde (i + 1) - ippm.x i‖^2)
    ≤ ∑ i in Finset.range k,
    (ippm.delta (i + 1) + 1/2 * ‖ippm.x i - xstar‖^2 - 1/2 * ‖ippm.x (i + 1) - xstar‖^2) := by
    apply Finset.sum_le_sum
    intro i hi
    exact h i (Finset.mem_range.mp hi)

  -- Step 3: Rearrange LHS - split the sum
  have lhs_eq : ∑ i in Finset.range k,
    (ippm.lam (i + 1) * (f (ippm.x_tilde (i + 1)) - f xstar) +
    (1 - σ) / 2 * ‖ippm.x_tilde (i + 1) - ippm.x i‖^2)
    = ∑ i in Finset.range k, ippm.lam (i + 1) * (f (ippm.x_tilde (i + 1)) - f xstar) +
      ∑ i in Finset.range k, ((1 - σ) / 2 * ‖ippm.x_tilde (i + 1) - ippm.x i‖^2) := by
    exact Finset.sum_add_distrib

  -- Step 4: Handle telescoping on RHS
  have telescope_sum : ∑ i in Finset.range k,
    (1/2 * ‖ippm.x i - xstar‖^2 - 1/2 * ‖ippm.x (i + 1) - xstar‖^2)
    = 1/2 * ‖ippm.x 0 - xstar‖^2 - 1/2 * ‖ippm.x k - xstar‖^2 := by
    -- Prove by induction
    have h_telescoping : ∀ n : ℕ,
      ∑ i in Finset.range n, (‖ippm.x i - xstar‖^2 - ‖ippm.x (i + 1) - xstar‖^2)
      = ‖ippm.x 0 - xstar‖^2 - ‖ippm.x n - xstar‖^2 := by
      intro n
      induction n with
      | zero =>
        simp [Finset.range_zero]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    have := h_telescoping k
    convert congr_arg (fun x => x / 2) this using 1
    · simp only [Finset.sum_div]
      congr 1 with i
      ring
    · ring

  -- Step 5: Rearrange RHS using telescoping
  have rhs_eq : ∑ i in Finset.range k,
    (ippm.delta (i + 1) + 1/2 * ‖ippm.x i - xstar‖^2 - 1/2 * ‖ippm.x (i + 1) - xstar‖^2)
    = ∑ i in Finset.range k, ippm.delta (i + 1) +
      (1/2 * ‖ippm.x 0 - xstar‖^2 - 1/2 * ‖ippm.x k - xstar‖^2) := by
    simp_rw [add_sub_assoc]
    rw [Finset.sum_add_distrib, telescope_sum]

  -- Step 6: Apply the rearrangements
  rw [lhs_eq, rhs_eq] at sum_h

  -- Step 7: Use x_init to substitute x₀ for ippm.x 0
  have x0_eq : ippm.x 0 = x₀ := ippm.x_init
  rw [x0_eq] at sum_h

  linarith


omit [CompleteSpace E] in
-- Step 2: Drop the non-negative term and simplify
lemma inexact_proximal_sum_bound (ippm : InexactProximalPoint f f' σ x₀)
    (f_min_exists : ∃ x_star : E, IsMinOn f univ x_star)
    (k : ℕ+) :
    let xstar := InexactProximal.x_star f f_min_exists
    ∑ i in Finset.range k, ippm.lam (i + 1) * (f (ippm.x_tilde (i + 1)) - f xstar)
    ≤ ∑ i in Finset.range k, ippm.delta (i + 1) + 1/2 * ‖x₀ - xstar‖^2 := by
  intro xstar
  have h := inexact_proximal_sum_lemma2 ippm f_min_exists k
  simp only [xstar] at h

  -- Drop the non-negative second term and the negative term
  have drop_nonneg : ∑ i in Finset.range k, ((1 - σ) / 2 * ‖ippm.x_tilde (i + 1) - ippm.x i‖^2) ≥ 0 := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg
    · apply div_nonneg
      · have σ_bound := ippm.σ_bound
        linarith [σ_bound.1, σ_bound.2]
      · norm_num
    · exact sq_nonneg _

  have drop_negative : 1/2 * ‖x₀ - xstar‖^2 - 1/2 * ‖ippm.x k - xstar‖^2 ≤
                       1/2 * ‖x₀ - xstar‖^2 := by
    have : 0 ≤ 1/2 * ‖ippm.x k - xstar‖^2 := by
      apply mul_nonneg
      · norm_num
      · exact sq_nonneg _
    linarith

  linarith [h, drop_nonneg, drop_negative]



omit [CompleteSpace E] in
lemma convex_weighted_average (ippm : InexactProximalPoint f f' σ x₀)
    (f_min_exists : ∃ x_star : E, IsMinOn f univ x_star)
    (k : ℕ+) :
    let Λ := ∑ i in Finset.range k, ippm.lam (i + 1)
    let x_hat := Λ⁻¹ • (∑ i in Finset.range k, ippm.lam (i + 1) • ippm.x_tilde (i + 1))
    let xstar := InexactProximal.x_star f f_min_exists
    f x_hat - f xstar ≤
    (∑ i in Finset.range k, ippm.lam (i + 1) * (f (ippm.x_tilde (i + 1)) - f xstar)) / Λ := by
  intro Λ x_hat xstar

  -- First establish that Λ > 0
  have hΛ_pos : 0 < Λ := by
    apply Finset.sum_pos
    · intros i _
      exact ippm.lam_pos (i + 1) (Nat.succ_pos i)
    · use 0; simp [k.pos]

  -- Rewrite division inequality as multiplication
  rw [le_div_iff₀ hΛ_pos]

  -- Expand: (f x_hat - f xstar) * Λ ≤ ∑ i, lam(i+1) * (f(x_tilde(i+1)) - f xstar)
  rw [sub_mul]

  -- Suffices to show: f x_hat * Λ ≤ ∑ i, lam(i+1) * f(x_tilde(i+1))
  suffices f x_hat * Λ ≤ ∑ i in Finset.range k, ippm.lam (i + 1) * f (ippm.x_tilde (i + 1)) by
    calc f x_hat * Λ - f xstar * Λ
        ≤ ∑ i in Finset.range k, ippm.lam (i + 1) * f (ippm.x_tilde (i + 1)) - f xstar * Λ := by linarith [this]
      _ = ∑ i in Finset.range k, ippm.lam (i + 1) * f (ippm.x_tilde (i + 1)) -
          ∑ i in Finset.range k, ippm.lam (i + 1) * f xstar := by
            rw [← Finset.sum_mul, mul_comm];
      _ = ∑ i in Finset.range k, (ippm.lam (i + 1) * f (ippm.x_tilde (i + 1)) - ippm.lam (i + 1) * f xstar) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ i in Finset.range k, ippm.lam (i + 1) * (f (ippm.x_tilde (i + 1)) - f xstar) := by
            congr 1; ext i; ring

  -- Use convexity: f is convex
  have h_convex : ConvexOn ℝ univ f := ippm.fc

  -- Apply Jensen's inequality for weighted averages
  have h_jensen := ConvexOn.map_centerMass_le h_convex
    (p := fun i => ippm.x_tilde (i + 1))
    (fun i _ => le_of_lt (ippm.lam_pos (i + 1) (Nat.succ_pos i)))
    hΛ_pos
    (fun i _ => mem_univ _)

  -- Simplify: centerMass is exactly x_hat, and extract the inequality we need
  simp only [Finset.centerMass] at h_jensen

  -- Multiply both sides by Λ and simplify
  have key : Λ * f (Λ⁻¹ • ∑ i in Finset.range k, ippm.lam (i + 1) • ippm.x_tilde (i + 1)) ≤
             ∑ i in Finset.range k, ippm.lam (i + 1) * f (ippm.x_tilde (i + 1)) := by
    have h := mul_le_mul_of_nonneg_left h_jensen (le_of_lt hΛ_pos)
    calc Λ * f (Λ⁻¹ • ∑ i in Finset.range k, ippm.lam (i + 1) • ippm.x_tilde (i + 1))
        ≤ Λ * (Λ⁻¹ • ∑ i in Finset.range k, ippm.lam (i + 1) • (f (ippm.x_tilde (i + 1)))) := h
      _ = Λ • (Λ⁻¹ • ∑ i in Finset.range k, ippm.lam (i + 1) • (f (ippm.x_tilde (i + 1)))) := by
            simp [smul_eq_mul]
      _ = (Λ * Λ⁻¹) • ∑ i in Finset.range k, ippm.lam (i + 1) • (f (ippm.x_tilde (i + 1))) := by
            rw [smul_smul]
      _ = ∑ i in Finset.range k, ippm.lam (i + 1) • (f (ippm.x_tilde (i + 1))) := by
            rw [mul_inv_cancel₀ (ne_of_gt hΛ_pos), one_smul]
      _ = ∑ i in Finset.range k, ippm.lam (i + 1) * f (ippm.x_tilde (i + 1)) := by
            simp only [smul_eq_mul]

  -- Rewrite to match goal: f x_hat * Λ = Λ * f x_hat
  rw [mul_comm]
  exact key


-- theorem 2.2
omit [CompleteSpace E] in
theorem inexact_proximal_convergence_rate (ippm : InexactProximalPoint f f' σ x₀)
    (f_min_exists : ∃ x_star : E, IsMinOn f univ x_star) : ∀ (k : ℕ+),
    f ((∑ i in Finset.range k, ippm.lam (i + 1))⁻¹ • (∑ i in Finset.range k, ippm.lam (i + 1) • ippm.x_tilde (i + 1)))
      - f (InexactProximal.x_star f f_min_exists) ≤
    (∑ i in Finset.range k, ippm.delta (i + 1)) / (∑ i in Finset.range k, ippm.lam (i + 1)) +
    ‖x₀ - InexactProximal.x_star f f_min_exists‖^2 / (2 * (∑ i in Finset.range k, ippm.lam (i + 1))) := by
  intro k
  let Λ := ∑ i in Finset.range k, ippm.lam (i + 1)
  let x_hat := Λ⁻¹ • (∑ i in Finset.range k, ippm.lam (i + 1) • ippm.x_tilde (i + 1))
  let xstar := InexactProximal.x_star f f_min_exists

  -- Get bound on weighted average of function values
  have step1 := convex_weighted_average ippm f_min_exists k
  simp only [Λ, x_hat, xstar] at step1

  -- Get bound on sum of function values
  have step2 := inexact_proximal_sum_bound ippm f_min_exists k
  simp only [Λ, xstar] at step2

  -- Λ is positive
  have Λ_pos : Λ > 0 := by
    simp only [Λ]
    apply Finset.sum_pos
    · intro i _
      have hi : i + 1 > 0 := Nat.succ_pos i
      exact ippm.lam_pos (i + 1) hi
    · use 0
      simp [k.pos]

  -- Combine the inequalities
  calc f x_hat - f xstar
      ≤ (∑ i in Finset.range k, ippm.lam (i + 1) * (f (ippm.x_tilde (i + 1)) - f xstar)) / Λ := step1
    _ ≤ (∑ i in Finset.range k, ippm.delta (i + 1) + 1/2 * ‖x₀ - xstar‖^2) / Λ := by
          apply div_le_div_of_nonneg_right step2
          exact le_of_lt Λ_pos
    _ = (∑ i in Finset.range k, ippm.delta (i + 1)) / Λ + (1/2 * ‖x₀ - xstar‖^2) / Λ := by
          rw [add_div]
    _ = (∑ i in Finset.range k, ippm.delta (i + 1)) / Λ + ‖x₀ - xstar‖^2 / (2 * Λ) := by
          congr 1
          field_simp

end InexactProximal
