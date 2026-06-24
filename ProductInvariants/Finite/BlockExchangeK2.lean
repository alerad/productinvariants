import ProductInvariants.Finite.Exchange
import ProductInvariants.Finite.BlockExchange

/-!
# The `k = 2` block-exchange positivity crux, shape `(2,3)` (prototype)

This file is a **prototype** for *Route A* / *Route B* of the deep `k ≥ 2`
prime-exchange lemma. It establishes, for the smallest non-trivial antichain
shape `(t₁,t₂) = (2,3)`, the integrated-positivity statement that drives the
block exchange.

After the substitution `v = u^p` the descent reduces to showing

  `Φ(c) = ∫₀ᶜ E(v) dv > 0`  for all `c ∈ (0,1]`,

where `E(v) = (1-v²)(1-v³) - (1-v)`.  Crucially `E` is **not** pointwise signed
(it is positive then negative on `(0,1)`), so the proof goes through the
*integrated* form `Φ`.

For shape `(2,3)`:

  `E(v) = v - v² - v³ + v⁵`,
  `Φ(c) = c²/2 - c³/3 - c⁴/4 + c⁶/6 = c² · q(c)`,
  `q(c) = 1/2 - c/3 - c²/4 + c⁴/6`.

The certificate has the **structural** shape that we observed to hold for *every*
antichain (numerically): `q` is decreasing on `[0,1]`, and
`q(1) = Φ(1) = 1/12 > 0`, hence `q(c) ≥ q(1) > 0` and `Φ(c) = c²q(c) > 0`.

Here we prove the pointwise positivity directly by `nlinarith` with the factored
form as a hint; the structural derivative argument is recorded in the module
docstring as the intended universal route.
-/

namespace ProductInvariants

/-- The shape-`(2,3)` integrand `E(v) = (1-v²)(1-v³) - (1-v)`. -/
def E23 (v : ℝ) : ℝ := (1 - v ^ 2) * (1 - v ^ 3) - (1 - v)

/-- Its antiderivative from `0`, `Φ(c) = ∫₀ᶜ E23`. -/
noncomputable def Phi23 (c : ℝ) : ℝ := c ^ 2 / 2 - c ^ 3 / 3 - c ^ 4 / 4 + c ^ 6 / 6

/-- The cofactor `q` with `Φ(c) = c² · q(c)`. -/
noncomputable def q23 (c : ℝ) : ℝ := 1 / 2 - c / 3 - c ^ 2 / 4 + c ^ 4 / 6

theorem Phi23_eq_sq_mul_q23 (c : ℝ) : Phi23 c = c ^ 2 * q23 c := by
  unfold Phi23 q23; ring

/-- `q(1) = 1/12 > 0`. -/
theorem q23_one : q23 1 = 1 / 12 := by unfold q23; norm_num

/-- **Cofactor positivity.** `q(c) > 0` for `c ∈ [0,1]`.

The cofactor is decreasing on `[0,1]` with `q(1) = 1/12`, so it stays `≥ 1/12`.
`nlinarith` discharges this with the squared-slack hints `(1-c)` and `c·(1-c)`. -/
theorem q23_pos {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : 0 < q23 c := by
  unfold q23
  nlinarith [sq_nonneg c, sq_nonneg (1 - c), sq_nonneg (c * c),
    mul_nonneg hc0 (sub_nonneg.mpr hc1),
    mul_nonneg (mul_nonneg hc0 hc0) (sub_nonneg.mpr hc1),
    mul_nonneg hc0 hc0]

/-- **The shape-`(2,3)` integrated positivity crux.**

`Φ(c) > 0` for every `c ∈ (0,1]`. This is the `k = 2`, shape-`(2,3)` instance of
the deep block-exchange positivity lemma. -/
theorem Phi23_pos {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) : 0 < Phi23 c := by
  rw [Phi23_eq_sq_mul_q23]
  exact mul_pos (by positivity) (q23_pos hc0.le hc1)

/-- `E23` as an explicit sum of monomials: `E(v) = v - v² - v³ + v⁵`. -/
theorem E23_eq_poly (v : ℝ) : E23 v = v ^ 1 - v ^ 2 - v ^ 3 + v ^ 5 := by
  unfold E23; ring

/-- **`Φ` is genuinely the integral of `E`.** `Φ(c) = ∫₀ᶜ E23 v dv`.

This certifies that the antiderivative `Phi23` used above is the actual integral
of the (non-pointwise-signed) integrand `E23`, closing the loop on the crux. -/
theorem integral_E23_eq_Phi23 (c : ℝ) :
    (∫ v in (0:ℝ)..c, E23 v) = Phi23 c := by
  have hpoly : (∫ v in (0:ℝ)..c, E23 v)
      = (∫ v in (0:ℝ)..c, v ^ 1 - v ^ 2 - v ^ 3 + v ^ 5) := by
    simp_rw [E23_eq_poly]
  rw [hpoly]
  have ii : ∀ n : ℕ, IntervalIntegrable (fun v : ℝ => v ^ n) MeasureTheory.volume 0 c :=
    fun n => (continuous_pow n).intervalIntegrable 0 c
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_sub]
  · simp only [integral_pow]
    unfold Phi23; norm_num
  · exact ii 1
  · exact ii 2
  · exact (ii 1).sub (ii 2)
  · exact ii 3
  · exact ((ii 1).sub (ii 2)).sub (ii 3)
  · exact ii 5

/-! ## Single-crossing of `E23`, and a second proof of `Phi23_pos` via Layer 1

We now exhibit the *structural* route, feeding the abstract single-crossing
lemma `integral_pos_of_single_crossing`.  The key is the exact factorisation

  `E23(v) = v · (1 - v) · R(v)`,   `R(v) = 1 - v² - v³`,

so on `(0,1)` (where `v > 0` and `1 - v > 0`) the sign of `E23` equals the sign
of the strictly-decreasing cubic `R`.  Its unique root `a ∈ (0,1)` is the single
crossing point.
-/

/-- The cofactor `R(v) = 1 - v² - v³` controlling the sign of `E23` on `(0,1)`. -/
def R23 (v : ℝ) : ℝ := 1 - v ^ 2 - v ^ 3

/-- The exact factorisation `E23(v) = v · (1 - v) · R23 v`. -/
theorem E23_factored (v : ℝ) : E23 v = v * (1 - v) * R23 v := by
  unfold E23 R23; ring

/-- `R23` is strictly decreasing (`R23 y < R23 x` when `x < y` on `[0,1]`-ish).
We only need: it is strictly antitone for nonnegative arguments. -/
theorem R23_strictAnti {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : R23 y < R23 x := by
  unfold R23
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  have h2 : x ^ 2 ≤ y ^ 2 := by nlinarith
  have h3 : x ^ 3 < y ^ 3 := by nlinarith [sq_nonneg x, sq_nonneg y, mul_pos hy hy]
  nlinarith

theorem R23_continuous : Continuous R23 := by
  unfold R23; fun_prop

theorem E23_continuous : Continuous E23 := by
  unfold E23; fun_prop

/-- The crossing point exists: a root `a ∈ (0,1)` of `R23`, i.e. `1 - a² - a³ = 0`.
Obtained from the IVT applied to the continuous `R23` with `R23 0 = 1 > 0` and
`R23 1 = -1 < 0`. -/
theorem exists_R23_root : ∃ a ∈ Set.Ioo (0 : ℝ) 1, R23 a = 0 := by
  have hcont : ContinuousOn R23 (Set.Icc 0 1) := R23_continuous.continuousOn
  have h0 : R23 1 < 0 := by unfold R23; norm_num
  have h1 : (0 : ℝ) < R23 0 := by unfold R23; norm_num
  -- value `0` lies strictly between `R23 1` and `R23 0`
  have hmem : (0 : ℝ) ∈ Set.Ioo (R23 1) (R23 0) := ⟨h0, h1⟩
  obtain ⟨a, ha, hfa⟩ :=
    intermediate_value_Ioo' (by norm_num : (0:ℝ) ≤ 1) hcont hmem
  exact ⟨a, ha, hfa⟩

/--
**Second, structural proof of the shape-`(2,3)` crux via Layer 1.**

Rather than the direct `c²·q` factorisation (`Phi23_pos`), we route through the
abstract single-crossing lemma `integral_pos_of_single_crossing`: `E23` factors as
`v(1-v)·R23 v`, single-crossing at the root `a` of `R23`, with positive total
integral `∫₀¹ E23 = Φ23 1 = 1/12`. This validates the universal architecture on a
genuine instance.
-/
theorem Phi23_pos_via_layer1 {c : ℝ} (hc : c ∈ Set.Ioc (0 : ℝ) 1) :
    0 < ∫ v in (0:ℝ)..c, E23 v := by
  obtain ⟨a, ha, hRa⟩ := exists_R23_root
  -- sign of `E23` on `(0,1)` follows the sign of `R23`
  have hsignpos : ∀ x ∈ Set.Ioo (0:ℝ) a, 0 < E23 x := by
    intro x hx
    rw [E23_factored]
    have hRx : 0 < R23 x := hRa ▸ R23_strictAnti hx.1.le hx.2
    have : 0 < x * (1 - x) :=
      mul_pos hx.1 (by linarith [hx.2, ha.2])
    positivity
  have hsignneg : ∀ x ∈ Set.Ioo a (1:ℝ), E23 x < 0 := by
    intro x hx
    rw [E23_factored]
    have hRx : R23 x < 0 := hRa ▸ R23_strictAnti ha.1.le hx.1
    have hpos : 0 < x * (1 - x) :=
      mul_pos (lt_trans ha.1 hx.1) (by linarith [hx.2])
    have := mul_neg_of_pos_of_neg hpos hRx
    linarith [this]
  have hsignpos_cl : ∀ x ∈ Set.Ioc (0:ℝ) a, 0 ≤ E23 x := by
    intro x hx
    rw [E23_factored]
    have hRx : 0 ≤ R23 x := by
      rcases eq_or_lt_of_le hx.2 with h | h
      · rw [h, hRa]
      · exact (hRa ▸ R23_strictAnti hx.1.le h).le
    have : 0 ≤ x * (1 - x) :=
      mul_nonneg hx.1.le (by linarith [hx.2, ha.2])
    positivity
  have hsignneg_cl : ∀ x ∈ Set.Icc a (1:ℝ), E23 x ≤ 0 := by
    intro x hx
    rw [E23_factored]
    have hRx : R23 x ≤ 0 := by
      rcases eq_or_lt_of_le hx.1 with h | h
      · rw [← h, hRa]
      · exact (hRa ▸ R23_strictAnti ha.1.le h).le
    have hpos : 0 ≤ x * (1 - x) :=
      mul_nonneg (le_of_lt (lt_of_lt_of_le ha.1 hx.1)) (by linarith [hx.2])
    nlinarith [mul_nonneg hpos (neg_nonneg.mpr hRx)]
  have hend : 0 < ∫ v in (0:ℝ)..1, E23 v := by
    rw [integral_E23_eq_Phi23]; unfold Phi23; norm_num
  exact integral_pos_of_single_crossing
    E23_continuous.continuousOn
    ha hsignpos hsignpos_cl hsignneg_cl hsignneg hend hc

end ProductInvariants
