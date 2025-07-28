import Mathlib.Tactic
import Mathlib.Topology.Metrizable.Urysohn

set_option autoImplicit false

/-!
In this file, we will state and prove the Lebesgue dominated convergence theorem, a classic result
in measure theory.

For a measure space (X, A, μ), if we have

1) g : X → [0, ∞] and g ∈ L¹(μ) ie integrable
2) sequence of measurable fₙ : X → [-∞, ∞] for n ∈ ℕ
   converging pointwise to f : X → [-∞, ∞] almost everywhere
3) |fₙ| ≤ g for all n ∈ ℕ

then we have ∫ |fₙ - f| dμ → 0 as n → ∞

Notation for a Lebesgue integral is also defined
* `∫ˡ x, f x ∂μ`: Lintegral of positive part minus Linegral of minus negative part

Additionally, a simple corollary is show
∫ f dμ = ∫ lim fₙ dμ = lim ∫ fₙ dμ
-/

open MeasureTheory Filter
open scoped ENNReal Classical

-- We start by defining the measure space (X, A, μ) and the functions g, f, fₙ
variable {X : Type} [MeasurableSpace X] {μ : Measure X}
  {f : X → EReal} {fₙ : ℕ → X → EReal} {g : X → ENNReal}

instance : ENorm EReal := ⟨EReal.abs⟩ -- need for integrability condition
instance : TopologicalSpace.PseudoMetrizableSpace EReal := -- needed for AEStronglyMeasurability
  TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology EReal

lemma bounded_by_integrable (hf_meas : Measurable f) (hg_int : Integrable g μ)
    (hf_bound : ∀ x, (f x).abs ≤ g x) : Integrable f μ := by
  /-
  exact MeasureTheory.Integrable.mono' hg_int hf_meas.aestronglyMeasurable (Eventually.of_forall hf_bound)
  did not work because it requires Banach co-domain of f which EReal is not so did it manually.
  maybe the mono' should be loosened in MathLib. This was the first red flag which I ignored...

  Integrable needs two proofs, one for AEStronglyMeasurable which is equivalent to measurability
  in second countable topologies which EReal is and also finite lintegral, which we have because
  g is has finite integral by its integrablility and because f is bounded by g, f also has finite
  integral due to monotonicty.
  -/
  have hf_aesm : AEStronglyMeasurable f μ := hf_meas.aestronglyMeasurable
  have h_int_bound : ∫⁻ x, (f x).abs ∂μ ≤ ∫⁻ x, g x ∂μ := lintegral_mono hf_bound
  exact ⟨hf_aesm, lt_of_le_of_lt h_int_bound hg_int.2⟩

-- this lemma should really be in MathLib but I can't find it
lemma abs_ne_top_iff {x : EReal} : x.abs ≠ ⊤ ↔ x ≠ ⊤ ∧ x ≠ ⊥ := by
  induction x <;> try simp
  exact ne_of_beq_false rfl

-- i had done this before I discovered induction but I learnt how to use lift
lemma EReal_abs_add_le_add {x y : EReal} : (x + y).abs ≤ x.abs + y.abs := by
  by_cases h1 : x.abs = ⊤
  · simp [h1]
  · by_cases h2 : y.abs = ⊤
    · simp [h2]
    · push_neg at h1 h2
      lift x to ℝ using abs_ne_top_iff.mp h1 -- thanks Bhavik and Fangming
      lift y to ℝ using abs_ne_top_iff.mp h2
      norm_cast
      rw [EReal.abs_def, EReal.abs_def, EReal.abs_def, ← ENNReal.ofReal_add (by simp) (by simp)]
      exact ENNReal.ofReal_le_ofReal (abs_add x y)

-- if i change the brack from () to {} something below breaks
-- a proof using induction and combinators -- much neater, can reformulate the above
-- but i thought it was good to show both
lemma EReal_abs_sub_le_add (x y : EReal) : (x - y).abs ≤ x.abs + y.abs := by
  induction x <;> induction y <;> try simp [EReal.abs_def]
  rw [← ENNReal.ofReal_add (by simp) (by simp)]
  exact ENNReal.ofReal_le_ofReal (abs_sub _ _)

-- some simple lemmas which I couldnt not find...
lemma EReal_neg_abs_le (x : EReal) : -x ≤ x.abs := by
  induction x <;> try simp
  norm_cast
  exact neg_le_abs _

lemma EReal_le_abs_self (x : EReal) : x.abs ≤ -x ∨ x.abs ≤ x := by
  induction x <;> try simp
  norm_cast
  rw [abs, max_le_iff, max_le_iff]
  simp only [le_neg_self_iff, le_refl, and_true, neg_le_self_iff, true_and]
  exact LinearOrder.le_total _ 0

lemma EReal_abs_le_max (x : EReal) : x.abs ≤ -x ⊔ x := le_max_iff.mpr (EReal_le_abs_self x)

lemma EReal_max_bounds_abs {a : ℕ → EReal} : (fun n ↦ ↑(a n).abs) ≤ (fun n ↦ (a n) ⊔ -(a n)) := by
  intro n
  simp only [le_sup_iff]
  rw [or_comm]
  exact EReal_le_abs_self (a n)

lemma EReal_Tendsto_neg {a : ℕ → EReal} (h : Tendsto a atTop (nhds 0)) :
    Tendsto (fun n ↦ -a n) atTop (nhds 0) := by
  have h' := h.neg
  rw [neg_zero] at h'
  exact h'

lemma EReal_tendsto_max {a : ℕ → EReal} (h : Tendsto a atTop (nhds 0)) :
    Tendsto (fun n ↦ (a n) ⊔ -(a n)) atTop (nhds 0) := by
  have hmax := h.max (EReal_Tendsto_neg h)
  rw [max_self] at hmax
  exact hmax

-- maybe this makes more sense? I do understand why abs was set up as ℕ → ENNReal though
-- def EReal_abs' : EReal → EReal
--   | ⊥ => ⊤
--   | ⊤ => ⊤
--   | (x : ℝ) => ENNReal.ofReal |x|

-- lemma EReal_abs'_eq_abs (x : EReal) : EReal_abs' x = x.abs := by
--   induction x <;> try simp [EReal_abs']
--   norm_cast

theorem extracted_1 {a : ℕ → ENNReal} (h_sq_aux : Tendsto (fun n => (a n : EReal)) atTop (nhds 0)) :
      Tendsto (fun n => (a n)) atTop (nhds 0) :=
  EReal.tendsto_coe_ennreal.mp h_sq_aux

-- another way to do below might be with EReal_tendsto_max because for (x : ℝ), |x| = x ⊔ -x
-- lemma needed to prove h_swap, linter complained so I omitted [MeasurableSpace X]
omit [MeasurableSpace X] in
lemma tendsto_EReal_abs {x : X} (hfn : Tendsto (fun n ↦ fₙ n x) atTop (nhds (0))) :
    Tendsto (fun n ↦ (fₙ n x).abs) atTop (nhds 0) := by
  have h_sq_aux := @tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ _ _ _ (fun n ↦ ↑(fₙ n x).abs)
    (fun n ↦ (0 : EReal)) (fun n ↦ (fₙ n x) ⊔ -(fₙ n x)) atTop 0 tendsto_const_nhds
    (EReal_tendsto_max hfn) (fun n ↦ EReal.coe_ennreal_nonneg (fₙ n x).abs) EReal_max_bounds_abs
  exact extracted_1 h_sq_aux

-- left these two for later
lemma Measurable_EReal_abs (hf : Measurable f) : Measurable (fun x ↦ (f x).abs) := by
  sorry

lemma Integrable_ENNReal_real_const_mul (c : ENNReal) (hg : Integrable g μ) :
    Integrable (fun x ↦ c * (g x)) μ :=
  sorry

-- this lemma is the bulk of the proof and is so that I can ultimately use
lemma limsup_aux
    (hg_int : Integrable g μ) (hf_meas : Measurable f) (hfn_meas : ∀ n, Measurable (fₙ n))
    (hfn_to_f : ∀ᵐ (x : X) ∂μ, Tendsto (fun n ↦ fₙ n x - f x) atTop (nhds 0))
    (hfn_bound : ∀ n, ∀ x, (fₙ n x).abs ≤ g x) (hf_bound : ∀ x, (f x).abs ≤ g x) :
    (limsup (fun n ↦ (∫⁻ x, (fₙ n x - f x).abs ∂μ)) atTop) ≤ 0 := by
  have hffn_le_2g : ∀ n, (fun (x : X) ↦ (fₙ n x - f x).abs) ≤ᵐ[μ] 2 * g := by
    intro n
    filter_upwards [ae_of_all _ (hfn_bound n), ae_of_all _ hf_bound] with x hfn_le_g hf_le_g
    calc
      (fₙ n x - f x).abs
      ≤ (fₙ n x).abs + (f x).abs := EReal_abs_sub_le_add (fₙ n x) (f x)
      _ ≤ g x + g x := add_le_add (hfn_le_g) (hf_le_g)
      _ = 2 * g x := by rw [two_mul]

  have h_meas : ∀ (n : ℕ), Measurable (fun (x : X) ↦ (fₙ n x - f x).abs) :=
    fun n ↦ Measurable_EReal_abs ((hfn_meas n).sub hf_meas)

  have h_2g_finite : ∫⁻ (x : X), (2 * g) x ∂μ ≠ ⊤ :=
    ne_of_lt (Integrable_ENNReal_real_const_mul 2 hg_int).2

  -- important step for going from inrgral of lim sup to 0 using pointwise convergence in calc below
  have h_swap : (fun x ↦ limsup (fun n ↦ (fₙ n x - f x).abs) atTop) =ᵐ[μ] 0 := by
    filter_upwards [hfn_to_f] with x hfn_to_f
    apply tendsto_EReal_abs at hfn_to_f
    apply Tendsto.limsup_eq at hfn_to_f
    simpa only [Pi.zero_apply]

  calc
    limsup (fun n ↦ (∫⁻ x, (fₙ n x - f x).abs ∂μ)) atTop
    ≤ ∫⁻ x, limsup (fun n ↦ (fₙ n x - f x).abs) atTop ∂μ :=
      @limsup_lintegral_le X _ μ (fun n ↦ (fun x ↦ (fₙ n x - f x).abs)) (2 * g)
        (h_meas) (hffn_le_2g) (h_2g_finite) -- Fatou
    _ = ∫⁻ x, 0 ∂μ := lintegral_congr_ae h_swap  -- ae congr for integral
    _ = 0 := by simp

-- Now we will prove the Lebesgue dominated convergence theorem for extended real valued functions
theorem LDCT
    (hg_int : Integrable g μ) -- integrability of g
    (hf_meas : Measurable f) -- measurability of f
    (hfn_meas : ∀ n, Measurable (fₙ n)) -- measurability of fₙ
    (hfn_to_f : ∀ᵐ (x : X) ∂μ, Tendsto (fun n ↦ fₙ n x - f x) atTop (nhds 0)) -- ae pntwise conv
    (hfn_bound : ∀ n, ∀ x, (fₙ n x).abs ≤ g x) -- dominated by g
    (hf_bound : ∀ x, (f x).abs ≤ g x) : -- f is dominated by g
    (Tendsto (fun n ↦ ∫⁻ x, (fₙ n x - f x).abs ∂μ) atTop (nhds 0)) := by
  /-
  integrability of fₙ and f
  this was shown in the lecture notes but not needed for the proof
    have hfn_int : ∀ n, Integrable (fₙ n) μ :=
      fun n ↦ bounded_by_integrable (hfn_meas n) hg_int (hfn_bound n)
    have hf_int : Integrable f μ := bounded_by_integrable hf_meas hg_int hf_bound
  it was included as the goal but I since removed it
  -/

  -- hypotheses to feed tendsto_of_le_liminf_of_limsup_le
  have h_liminf : 0 ≤ (liminf (fun n ↦ (∫⁻ x, (fₙ n x - f x).abs ∂μ)) atTop) := by simp
  have h_bounded : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ ∫⁻ x, (fₙ n x - f x).abs ∂μ) := by
    use ∞
    filter_upwards
    simp only [le_top, implies_true]
  have h_bounded' : IsBoundedUnder (· ≥ ·) atTop (fun n ↦ ∫⁻ x, (fₙ n x - f x).abs ∂μ) := by
    use 0
    filter_upwards
    simp only [ge_iff_le, zero_le, implies_true]
  have h_limsup := limsup_aux hg_int hf_meas hfn_meas hfn_to_f hfn_bound hf_bound

  exact tendsto_of_le_liminf_of_limsup_le h_liminf h_limsup h_bounded h_bounded'

-- Below is a statement of a corollary of LDCT,
-- ∫ x, f x ∂μ = ∫ x, lim fₙ x ∂μ = lim ∫ x, fₙ x ∂μ
-- annoyingly the Bochner integral does not allow functions in EReal
-- I included this because I wanted to figure out how to define things and give notation

/-- define Lebesgue integral -/
noncomputable def LebesgueIntegral (f : X → EReal) (μ : Measure X) : ℝ :=
  if Integrable f μ then (∫⁻ x, (f x).toENNReal ∂μ - ∫⁻ x, (-f x).toENNReal ∂μ).toReal else 0 -- jnk

/-- the natural notation -/
notation3 "∫ˡ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => LebesgueIntegral r μ

lemma lim_int_eq_int_lim
    (hg_int : Integrable g μ) (hf_meas : Measurable f) (hfn_meas : ∀ n, Measurable (fₙ n))
    (hfn_to_f : ∀ᵐ (x : X) ∂μ, Tendsto (fun n ↦ fₙ n x - f x) atTop (nhds 0))
    (hfn_bound : ∀ n, ∀ x, (fₙ n x).abs ≤ g x) (hf_bound : ∀ x, (f x).abs ≤ g x) :
    Tendsto (fun n ↦ ∫ˡ x, (fₙ n) x ∂μ) atTop (nhds (∫ˡ x, f x ∂μ)) := by
  sorry
