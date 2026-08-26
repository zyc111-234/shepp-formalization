import Mathlib

section SheppFlattenedModule001
namespace Shepp.Section2

theorem convex_profile_le_chord
    {ψ : ℝ → ℝ} {x : ℝ}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 2) ψ)
    (h0 : ψ 0 = 1)
    (h2 : ψ 2 = 0)
    (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    ψ x ≤ 1 - x / 2 := by
  have ha : 0 ≤ 1 - x / 2 := by linarith [hx.2]
  have hb : 0 ≤ x / 2 := by linarith [hx.1]
  have hab : (1 - x / 2) + x / 2 = 1 := by ring
  have h := hconv.2
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 2 by norm_num)
    (show (2 : ℝ) ∈ Set.Icc (0 : ℝ) 2 by norm_num)
    ha hb hab
  have harg :
      (1 - x / 2) • (0 : ℝ) + (x / 2) • (2 : ℝ) = x := by
    simp
  have hrhs :
      (1 - x / 2) • ψ 0 + (x / 2) • ψ 2 = 1 - x / 2 := by
    simp [h0, h2]
  rw [harg, hrhs] at h
  exact h

theorem tangent_le_convex_profile
    {ψ : ℝ → ℝ} {a x : ℝ}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 2) ψ)
    (h0 : ψ 0 = 1)
    (hderiv : HasDerivWithinAt ψ (-a) (Set.Ioi (0 : ℝ)) 0)
    (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    1 - a * x ≤ ψ x := by
  rcases eq_or_lt_of_le hx.1 with rfl | hxpos
  · simp [h0]
  · have hslope : -a ≤ slope ψ 0 x :=
      hconv.le_slope_of_hasDerivWithinAt_Ioi
        (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 2 by norm_num)
        hx hxpos hderiv
    rw [slope_def_field, sub_zero, h0] at hslope
    have hmul : -a * x ≤ ψ x - 1 := (le_div_iff₀ hxpos).mp hslope
    linarith

theorem abstract_cone_bounds
    {ψ : ℝ → ℝ} {a x : ℝ}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 2) ψ)
    (h0 : ψ 0 = 1)
    (h2 : ψ 2 = 0)
    (hnonneg : ∀ y ∈ Set.Icc (0 : ℝ) 2, 0 ≤ ψ y)
    (hderiv : HasDerivWithinAt ψ (-a) (Set.Ioi (0 : ℝ)) 0)
    (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    max (1 - a * x) 0 ≤ ψ x ∧
      ψ x ≤ max (1 - x / 2) 0 := by
  constructor
  · exact max_le
      (tangent_le_convex_profile hconv h0 hderiv hx)
      (hnonneg x hx)
  · have hlinear : 0 ≤ 1 - x / 2 := by linarith [hx.2]
    simpa [max_eq_left hlinear] using convex_profile_le_chord hconv h0 h2 hx

end Shepp.Section2
end SheppFlattenedModule001

section SheppFlattenedModule002
namespace Shepp.Section2

open Filter

noncomputable def capWeight (d : ℕ) (s : ℝ) : ℝ :=
  (Real.sqrt (max (1 - s ^ 2) 0)) ^ (d - 1)

noncomputable def capNormalizer (d : ℕ) : ℝ :=
  ∫ s in (0 : ℝ)..1, capWeight d s

noncomputable def capTail (d : ℕ) (u : ℝ) : ℝ :=
  ∫ s in u..1, capWeight d s

noncomputable def lensProfile (d : ℕ) (x : ℝ) : ℝ :=
  capTail d (x / 2) / capNormalizer d

noncomputable def coneConstant (d : ℕ) : ℝ :=
  1 / (2 * capNormalizer d)

theorem capWeight_continuous (d : ℕ) : Continuous (capWeight d) := by
  unfold capWeight
  exact (((continuous_const.sub (continuous_id.pow 2)).max continuous_const).sqrt).pow _

theorem capWeight_nonneg (d : ℕ) (s : ℝ) : 0 ≤ capWeight d s := by
  unfold capWeight
  positivity

theorem capWeight_pos_of_mem_Ioo (d : ℕ) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) : 0 < capWeight d s := by
  have hbase : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  rw [capWeight, max_eq_left hbase.le]
  exact pow_pos (Real.sqrt_pos.2 hbase) _

theorem capNormalizer_pos (d : ℕ) : 0 < capNormalizer d := by
  rw [capNormalizer]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((capWeight_continuous d).intervalIntegrable 0 1)
    (fun _ hs => capWeight_pos_of_mem_Ioo d hs)
    (by norm_num)

theorem capNormalizer_eq_integral_cos_pow (d : ℕ) (hd : 1 ≤ d) :
    capNormalizer d = ∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos θ ^ d := by
  have hsubst := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := Real.sin) (f' := Real.cos) (g := capWeight d)
    (fun θ _ => Real.hasDerivAt_sin θ)
    Real.continuous_cos.continuousOn
    (capWeight_continuous d)
  have hsubst' :
      (∫ θ in (0 : ℝ)..Real.pi / 2,
        capWeight d (Real.sin θ) * Real.cos θ) = capNormalizer d := by
    simpa only [Function.comp_apply, Real.sin_zero, Real.sin_pi_div_two,
      capNormalizer] using hsubst
  calc
    capNormalizer d =
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          capWeight d (Real.sin θ) * Real.cos θ := hsubst'.symm
    _ = ∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos θ ^ d := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [Set.uIcc_of_le Real.pi_div_two_pos.le] at hθ
      have hcos : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      have htrig : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq θ]
      change capWeight d (Real.sin θ) * Real.cos θ = Real.cos θ ^ d
      rw [capWeight, htrig, max_eq_left (sq_nonneg _), Real.sqrt_sq hcos,
        ← pow_succ, Nat.sub_add_cancel hd]

theorem lensProfile_zero (d : ℕ) : lensProfile d 0 = 1 := by
  have hn : capNormalizer d ≠ 0 := (capNormalizer_pos d).ne'
  rw [lensProfile, zero_div]
  change capNormalizer d / capNormalizer d = 1
  exact div_self hn

theorem lensProfile_two (d : ℕ) : lensProfile d 2 = 0 := by
  simp [lensProfile, capTail]

theorem lensProfile_nonneg (d : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) : 0 ≤ lensProfile d x := by
  have hhalf : x / 2 ≤ (1 : ℝ) := by linarith [hx.2]
  have htail : 0 ≤ capTail d (x / 2) := by
    rw [capTail]
    exact intervalIntegral.integral_nonneg hhalf
      (fun s _ => capWeight_nonneg d s)
  exact div_nonneg htail (capNormalizer_pos d).le

theorem capWeight_zero (d : ℕ) : capWeight d 0 = 1 := by
  simp [capWeight]

theorem coneConstant_pos (d : ℕ) : 0 < coneConstant d := by
  rw [coneConstant]
  exact one_div_pos.mpr (mul_pos (by norm_num) (capNormalizer_pos d))

theorem capTail_hasDerivAt (d : ℕ) (u : ℝ) :
    HasDerivAt (capTail d) (-capWeight d u) u := by
  change HasDerivAt (fun v => ∫ s in v..1, capWeight d s) (-capWeight d u) u
  exact intervalIntegral.integral_hasDerivAt_left
    ((capWeight_continuous d).intervalIntegrable u 1)
    ((capWeight_continuous d).stronglyMeasurableAtFilter
      MeasureTheory.volume (nhds u))
    (capWeight_continuous d).continuousAt

theorem normalizedCapTail_hasDerivAt (d : ℕ) (u : ℝ) :
    HasDerivAt
      (fun v => ∫ s in v..1, capWeight d s / capNormalizer d)
      (-(capWeight d u / capNormalizer d)) u := by
  have hcont : Continuous (fun s => capWeight d s / capNormalizer d) :=
    (capWeight_continuous d).div_const _
  exact intervalIntegral.integral_hasDerivAt_left
    (hcont.intervalIntegrable u 1)
    (hcont.stronglyMeasurableAtFilter MeasureTheory.volume (nhds u))
    hcont.continuousAt

theorem lensProfile_hasDerivAt (d : ℕ) (x : ℝ) :
    HasDerivAt (lensProfile d)
      (-(coneConstant d * capWeight d (x / 2))) x := by
  have hhalf : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
    simpa only [id_eq] using (hasDerivAt_id x).div_const 2
  have hcomp :
      HasDerivAt
        (fun y : ℝ => ∫ s in y / 2..1, capWeight d s / capNormalizer d)
        ((-(capWeight d (x / 2) / capNormalizer d)) * (1 / 2)) x := by
    simpa only [Function.comp_def] using
      (normalizedCapTail_hasDerivAt d (x / 2)).comp x hhalf
  have hcoeff :
      (-(capWeight d (x / 2) / capNormalizer d)) * (1 / 2) =
        -(coneConstant d * capWeight d (x / 2)) := by
    unfold coneConstant
    ring
  rw [hcoeff] at hcomp
  change HasDerivAt
    (fun y : ℝ => capTail d (y / 2) / capNormalizer d)
    (-(coneConstant d * capWeight d (x / 2))) x
  simpa only [capTail, intervalIntegral.integral_div] using hcomp

theorem lensProfile_deriv (d : ℕ) (x : ℝ) :
    deriv (lensProfile d) x = -(coneConstant d * capWeight d (x / 2)) :=
  (lensProfile_hasDerivAt d x).deriv

theorem lensProfile_differentiable (d : ℕ) : Differentiable ℝ (lensProfile d) :=
  fun x => (lensProfile_hasDerivAt d x).differentiableAt

theorem lensProfile_continuous (d : ℕ) : Continuous (lensProfile d) :=
  (lensProfile_differentiable d).continuous

theorem capWeight_antitoneOn (d : ℕ) :
    AntitoneOn (capWeight d) (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hsquare : x ^ 2 ≤ y ^ 2 :=
    (sq_le_sq₀ hx.1 hy.1).2 hxy
  unfold capWeight
  apply pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt ?_) _
  exact max_le_max (by linarith) le_rfl

theorem lensProfile_deriv_monotoneOn (d : ℕ) :
    MonotoneOn (deriv (lensProfile d)) (Set.Ioo (0 : ℝ) 2) := by
  intro x hx y hy hxy
  have hxhalf : x / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hyhalf : y / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have hhalf : x / 2 ≤ y / 2 := by linarith
  have hweight : capWeight d (y / 2) ≤ capWeight d (x / 2) :=
    capWeight_antitoneOn d hxhalf hyhalf hhalf
  have hmul :
      coneConstant d * capWeight d (y / 2) ≤
        coneConstant d * capWeight d (x / 2) :=
    mul_le_mul_of_nonneg_left hweight (coneConstant_pos d).le
  rw [lensProfile_deriv d x, lensProfile_deriv d y]
  exact neg_le_neg hmul

theorem lensProfile_convexOn (d : ℕ) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 2) (lensProfile d) := by
  have hmono :
      MonotoneOn (deriv (lensProfile d))
        (interior (Set.Icc (0 : ℝ) 2)) := by
    simpa only [interior_Icc] using lensProfile_deriv_monotoneOn d
  exact hmono.convexOn_of_deriv
    (convex_Icc (0 : ℝ) 2)
    (lensProfile_continuous d).continuousOn
    (lensProfile_differentiable d).differentiableOn

theorem lensProfile_hasDerivWithinAt_zero (d : ℕ) :
    HasDerivWithinAt (lensProfile d) (-coneConstant d)
      (Set.Ioi (0 : ℝ)) 0 := by
  have h := (lensProfile_hasDerivAt d 0).hasDerivWithinAt
    (s := Set.Ioi (0 : ℝ))
  simpa only [zero_div, capWeight_zero, mul_one] using h

theorem lensProfile_cone_bounds (d : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    max (1 - coneConstant d * x) 0 ≤ lensProfile d x ∧
      lensProfile d x ≤ max (1 - x / 2) 0 := by
  exact abstract_cone_bounds
    (lensProfile_convexOn d)
    (lensProfile_zero d)
    (lensProfile_two d)
    (fun y hy => lensProfile_nonneg d hy)
    (lensProfile_hasDerivWithinAt_zero d)
    hx

end Shepp.Section2
end SheppFlattenedModule002

section SheppFlattenedModule003
namespace Shepp.Section2

noncomputable def euclideanUnitBallVolume (d : ℕ) : ℝ :=
  Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)

theorem integral_cos_pow_eq_gamma (d : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos θ ^ d) =
      Real.sqrt Real.pi * Real.Gamma (((d : ℝ) + 1) / 2) /
        (2 * Real.Gamma ((d : ℝ) / 2 + 1)) := by
  induction d using Nat.twoStepInduction with
  | zero =>
      norm_num [Real.Gamma_one_half_eq, Real.Gamma_one,
        Real.sq_sqrt Real.pi_nonneg]
      nlinarith [Real.sq_sqrt Real.pi_nonneg]
  | one =>
      have hthreehalf :
          Real.Gamma ((3 : ℝ) / 2) = (1 / 2 : ℝ) * Real.sqrt Real.pi := by
        calc
          Real.Gamma ((3 : ℝ) / 2) = Real.Gamma ((1 : ℝ) / 2 + 1) := by congr 1 <;> ring
          _ = (1 / 2 : ℝ) * Real.Gamma ((1 : ℝ) / 2) :=
            Real.Gamma_add_one (by norm_num)
          _ = (1 / 2 : ℝ) * Real.sqrt Real.pi := by
            rw [Real.Gamma_one_half_eq]
      simp only [pow_one, integral_cos, Real.sin_pi_div_two, Real.sin_zero,
        sub_zero]
      have hargNum : (((1 : ℕ) : ℝ) + 1) / 2 = 1 := by norm_num
      have hargDen : ((1 : ℕ) : ℝ) / 2 + 1 = (3 : ℝ) / 2 := by norm_num
      rw [hargNum, hargDen, Real.Gamma_one, hthreehalf]
      field_simp [(Real.sqrt_pos.2 Real.pi_pos).ne']
  | more n hn _ =>
      have hnum :
          Real.Gamma ((((n + 2 : ℕ) : ℝ) + 1) / 2) =
            (((n : ℝ) + 1) / 2) *
              Real.Gamma (((n : ℝ) + 1) / 2) := by
        calc
          Real.Gamma ((((n + 2 : ℕ) : ℝ) + 1) / 2) =
              Real.Gamma (((n : ℝ) + 1) / 2 + 1) := by congr 1 <;> norm_num <;> ring
          _ = (((n : ℝ) + 1) / 2) *
              Real.Gamma (((n : ℝ) + 1) / 2) :=
            Real.Gamma_add_one (by positivity)
      have hden :
          Real.Gamma (((n + 2 : ℕ) : ℝ) / 2 + 1) =
            ((n : ℝ) / 2 + 1) *
              Real.Gamma ((n : ℝ) / 2 + 1) := by
        calc
          Real.Gamma (((n + 2 : ℕ) : ℝ) / 2 + 1) =
              Real.Gamma (((n : ℝ) / 2 + 1) + 1) := by congr 1 <;> norm_num <;> ring
          _ = ((n : ℝ) / 2 + 1) *
              Real.Gamma ((n : ℝ) / 2 + 1) :=
            Real.Gamma_add_one (by positivity)
      rw [integral_cos_pow n]
      simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero,
        Real.sin_zero, zero_pow (Nat.succ_ne_zero n), zero_mul, one_pow,
        mul_zero, sub_zero, zero_div, zero_add]
      rw [hn, hnum, hden]
      have hgammaNum : Real.Gamma (((n : ℝ) + 1) / 2) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by positivity)).ne'
      have hgammaDen : Real.Gamma ((n : ℝ) / 2 + 1) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by positivity)).ne'
      field_simp [hgammaNum, hgammaDen]

theorem euclideanUnitBallVolume_pos (d : ℕ) :
    0 < euclideanUnitBallVolume d := by
  unfold euclideanUnitBallVolume
  exact div_pos
    (pow_pos (Real.sqrt_pos.2 Real.pi_pos) _)
    (Real.Gamma_pos_of_pos (by positivity))

theorem volume_unitBall_eq_ofReal_euclideanUnitBallVolume
    (d : ℕ) (hd : 0 < d) :
    MeasureTheory.volume
        (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) =
      ENNReal.ofReal (euclideanUnitBallVolume d) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  simpa only [EuclideanSpace.volume_ball, Fintype.card_fin,
    ENNReal.ofReal_one, one_pow, one_mul, euclideanUnitBallVolume]

theorem euclideanUnitBallVolume_eq_measureReal
    (d : ℕ) (hd : 0 < d) :
    euclideanUnitBallVolume d =
      MeasureTheory.volume.real
        (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  rw [MeasureTheory.Measure.real,
    volume_unitBall_eq_ofReal_euclideanUnitBallVolume d hd,
    ENNReal.toReal_ofReal (euclideanUnitBallVolume_pos d).le]

theorem capNormalizer_eq_gamma (d : ℕ) (hd : 1 ≤ d) :
    capNormalizer d =
      Real.sqrt Real.pi * Real.Gamma (((d : ℝ) + 1) / 2) /
        (2 * Real.Gamma ((d : ℝ) / 2 + 1)) := by
  rw [capNormalizer_eq_integral_cos_pow d hd, integral_cos_pow_eq_gamma d]

theorem euclideanUnitBallVolume_slicing (d : ℕ) (hd : 1 ≤ d) :
    2 * euclideanUnitBallVolume (d - 1) * capNormalizer d =
      euclideanUnitBallVolume d := by
  rw [capNormalizer_eq_gamma d hd]
  unfold euclideanUnitBallVolume
  have hcast :
      (((d - 1 : ℕ) : ℝ) / 2 + 1) = ((d : ℝ) + 1) / 2 := by
    rw [Nat.cast_sub hd]
    ring
  rw [hcast]
  have hsqrt : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hgammaPrev : Real.Gamma (((d : ℝ) + 1) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hgammaDim : Real.Gamma ((d : ℝ) / 2 + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  field_simp [hsqrt, hgammaPrev, hgammaDim]
  rw [← pow_succ, Nat.sub_add_cancel hd]

theorem coneConstant_eq_unitBallVolume_ratio (d : ℕ) (hd : 1 ≤ d) :
    coneConstant d =
      euclideanUnitBallVolume (d - 1) / euclideanUnitBallVolume d := by
  have hslicing := euclideanUnitBallVolume_slicing d hd
  have hnorm : capNormalizer d ≠ 0 := (capNormalizer_pos d).ne'
  have hdim : euclideanUnitBallVolume d ≠ 0 :=
    (euclideanUnitBallVolume_pos d).ne'
  rw [coneConstant]
  field_simp [hnorm, hdim]
  nlinarith

theorem lensProfile_eq_unitBallVolume_capIntegral
    (d : ℕ) (hd : 1 ≤ d) (x : ℝ) :
    lensProfile d x =
      (2 * euclideanUnitBallVolume (d - 1) /
          euclideanUnitBallVolume d) * capTail d (x / 2) := by
  have hcoef :
      2 * euclideanUnitBallVolume (d - 1) /
          euclideanUnitBallVolume d = 2 * coneConstant d := by
    calc
      2 * euclideanUnitBallVolume (d - 1) /
          euclideanUnitBallVolume d =
          2 * (euclideanUnitBallVolume (d - 1) /
            euclideanUnitBallVolume d) := mul_div_assoc _ _ _
      _ = 2 * coneConstant d := by
        rw [coneConstant_eq_unitBallVolume_ratio d hd]
  rw [hcoef]
  have hnorm : capNormalizer d ≠ 0 := (capNormalizer_pos d).ne'
  unfold lensProfile coneConstant
  field_simp [hnorm]

theorem lensProfile_cone_bounds_unitBallVolume
    (d : ℕ) (hd : 1 ≤ d) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    max
        (1 -
          (euclideanUnitBallVolume (d - 1) /
            euclideanUnitBallVolume d) * x)
        0 ≤ lensProfile d x ∧
      lensProfile d x ≤ max (1 - x / 2) 0 := by
  simpa only [coneConstant_eq_unitBallVolume_ratio d hd] using
    lensProfile_cone_bounds d hx

end Shepp.Section2
end SheppFlattenedModule003

section SheppFlattenedModule004
namespace Shepp.Section2

open MeasureTheory

theorem measureReal_prod_eq_integral_fiber
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    {s : Set (α × β)} (hs : MeasurableSet s)
    (hfinite : (μ.prod ν) s ≠ ⊤) :
    (μ.prod ν).real s = ∫ x, ν.real (Prod.mk x ⁻¹' s) ∂μ := by
  rw [Measure.real, Measure.prod_apply hs]
  exact (integral_toReal
    (measurable_measure_prodMk_left hs).aemeasurable
    (Measure.ae_measure_lt_top hs hfinite)).symm

def euclideanUpperCap (d : ℕ) (u : ℝ) :
    Set (ℝ × EuclideanSpace ℝ (Fin (d - 1))) :=
  (Prod.fst ⁻¹' Set.Ioc u 1) ∩
    {p | p.1 ^ 2 + ‖p.2‖ ^ 2 < 1}

theorem euclideanUpperCap_measurable (d : ℕ) (u : ℝ) :
    MeasurableSet (euclideanUpperCap d u) := by
  apply (measurableSet_Ioc.preimage measurable_fst).inter
  exact (isOpen_lt (by fun_prop : Continuous fun p :
    ℝ × EuclideanSpace ℝ (Fin (d - 1)) => p.1 ^ 2 + ‖p.2‖ ^ 2)
    continuous_const).measurableSet

theorem norm_lt_sqrt_max_iff_sq_lt
    {E : Type*} [SeminormedAddCommGroup E] (y : E) (q : ℝ) :
    ‖y‖ < Real.sqrt (max q 0) ↔ ‖y‖ ^ 2 < q := by
  by_cases hq : 0 < q
  · rw [max_eq_left hq.le, Real.lt_sqrt (norm_nonneg y)]
  · have hq0 : q ≤ 0 := le_of_not_gt hq
    rw [max_eq_right hq0, Real.sqrt_zero]
    constructor
    · exact fun h => (not_lt_of_ge (norm_nonneg y) h).elim
    · intro h
      nlinarith [sq_nonneg ‖y‖]

theorem euclideanUpperCap_fiber (d : ℕ) (u t : ℝ) :
    Prod.mk t ⁻¹' euclideanUpperCap d u =
      if t ∈ Set.Ioc u 1 then
        Metric.ball (0 : EuclideanSpace ℝ (Fin (d - 1)))
          (Real.sqrt (max (1 - t ^ 2) 0))
      else ∅ := by
  ext y
  by_cases ht : t ∈ Set.Ioc u 1
  · simp only [euclideanUpperCap, Set.mem_preimage, Set.mem_inter_iff,
      Set.mem_setOf_eq, ht, true_and, if_pos, Metric.mem_ball,
      dist_zero_right]
    rw [norm_lt_sqrt_max_iff_sq_lt]
    constructor <;> intro h <;> linarith
  · simp [euclideanUpperCap, ht]

theorem volumeReal_euclideanBall
    (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.volume.real
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) =
      r ^ n * euclideanUnitBallVolume n := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [Measure.real, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr]
  change r ^ n * (ENNReal.ofReal (euclideanUnitBallVolume n)).toReal =
    r ^ n * euclideanUnitBallVolume n
  rw [ENNReal.toReal_ofReal (euclideanUnitBallVolume_pos n).le]

theorem euclideanUpperCap_finite (d : ℕ) (u : ℝ) :
    MeasureTheory.volume (euclideanUpperCap d u) ≠ ⊤ := by
  have hsubset :
      euclideanUpperCap d u ⊆
        Set.Ioc u 1 ×ˢ
          Metric.ball (0 : EuclideanSpace ℝ (Fin (d - 1))) 1 := by
    rintro ⟨t, y⟩ ⟨ht, hquad⟩
    refine ⟨ht, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    change t ^ 2 + ‖y‖ ^ 2 < 1 at hquad
    have hsq : ‖y‖ ^ 2 < (1 : ℝ) := by
      nlinarith [sq_nonneg t]
    exact (sq_lt_sq₀ (norm_nonneg y) zero_le_one).mp (by simpa using hsq)
  have hbox :
      MeasureTheory.volume
          (Set.Ioc u 1 ×ˢ
            Metric.ball (0 : EuclideanSpace ℝ (Fin (d - 1))) 1) < ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_ball_lt_top
  exact ((measure_mono hsubset).trans_lt hbox).ne

theorem volumeReal_euclideanUpperCap
    (d : ℕ) (hd : 2 ≤ d) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    MeasureTheory.volume.real (euclideanUpperCap d u) =
      euclideanUnitBallVolume (d - 1) * capTail d u := by
  have htrans : 0 < d - 1 := by omega
  have hfubini := measureReal_prod_eq_integral_fiber
    (μ := (MeasureTheory.volume : Measure ℝ))
    (ν := (MeasureTheory.volume :
      Measure (EuclideanSpace ℝ (Fin (d - 1)))))
    (euclideanUpperCap_measurable d u)
    (euclideanUpperCap_finite d u)
  rw [← Measure.volume_eq_prod] at hfubini
  calc
    MeasureTheory.volume.real (euclideanUpperCap d u) =
        ∫ t : ℝ,
          MeasureTheory.volume.real
            (Prod.mk t ⁻¹' euclideanUpperCap d u) := hfubini
    _ = ∫ t in Set.Ioc u 1,
        euclideanUnitBallVolume (d - 1) * capWeight d t := by
      rw [← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards with t
      rw [euclideanUpperCap_fiber]
      by_cases ht : t ∈ Set.Ioc u 1
      · simp only [ht, if_pos, Set.indicator_of_mem]
        rw [volumeReal_euclideanBall (d - 1) htrans _ (Real.sqrt_nonneg _)]
        simp only [capWeight]
        ring
      · simp [ht]
    _ = ∫ t in u..1,
        euclideanUnitBallVolume (d - 1) * capWeight d t := by
      exact (intervalIntegral.integral_of_le hu.2).symm
    _ = euclideanUnitBallVolume (d - 1) * capTail d u := by
      rw [intervalIntegral.integral_const_mul]
      rfl

def coordinateUnitBall (d : ℕ) (c : ℝ) :
    Set (ℝ × EuclideanSpace ℝ (Fin (d - 1))) :=
  {p | (p.1 - c) ^ 2 + ‖p.2‖ ^ 2 < 1}

def coordinateUnitLens (d : ℕ) (x : ℝ) :
    Set (ℝ × EuclideanSpace ℝ (Fin (d - 1))) :=
  coordinateUnitBall d 0 ∩ coordinateUnitBall d x

def lensReflection (d : ℕ) (x : ℝ)
    (p : ℝ × EuclideanSpace ℝ (Fin (d - 1))) :=
  (x - p.1, p.2)

def reflectedUpperCap (d : ℕ) (x : ℝ) :
    Set (ℝ × EuclideanSpace ℝ (Fin (d - 1))) :=
  lensReflection d x ⁻¹' euclideanUpperCap d (x / 2)

theorem coordinateUnitBall_measurable (d : ℕ) (c : ℝ) :
    MeasurableSet (coordinateUnitBall d c) := by
  exact (isOpen_lt (by fun_prop : Continuous fun p :
    ℝ × EuclideanSpace ℝ (Fin (d - 1)) =>
      (p.1 - c) ^ 2 + ‖p.2‖ ^ 2) continuous_const).measurableSet

theorem coordinateUnitLens_measurable (d : ℕ) (x : ℝ) :
    MeasurableSet (coordinateUnitLens d x) :=
  (coordinateUnitBall_measurable d 0).inter
    (coordinateUnitBall_measurable d x)

theorem lensReflection_measurePreserving (d : ℕ) (x : ℝ) :
    MeasurePreserving (lensReflection d x)
      ((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume :
          Measure (EuclideanSpace ℝ (Fin (d - 1)))))
      ((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume :
          Measure (EuclideanSpace ℝ (Fin (d - 1))))) := by
  have h :=
    (Measure.measurePreserving_sub_left
      (MeasureTheory.volume : Measure ℝ) x).prod
      (MeasurePreserving.id
        (MeasureTheory.volume :
          Measure (EuclideanSpace ℝ (Fin (d - 1)))))
  have hfun :
      lensReflection d x = Prod.map (fun t : ℝ => x - t) id := by
    funext p
    rcases p with ⟨t, y⟩
    rfl
  rw [hfun]
  exact h

theorem reflectedUpperCap_measurable (d : ℕ) (x : ℝ) :
    MeasurableSet (reflectedUpperCap d x) :=
  (euclideanUpperCap_measurable d (x / 2)).preimage
    (by
      unfold lensReflection
      fun_prop : Continuous (lensReflection d x)).measurable

theorem volume_reflectedUpperCap (d : ℕ) (x : ℝ) :
    MeasureTheory.volume (reflectedUpperCap d x) =
      MeasureTheory.volume (euclideanUpperCap d (x / 2)) := by
  rw [Measure.volume_eq_prod]
  exact (lensReflection_measurePreserving d x).measure_preimage
    (euclideanUpperCap_measurable d (x / 2)).nullMeasurableSet

theorem volumeReal_reflectedUpperCap (d : ℕ) (x : ℝ) :
    MeasureTheory.volume.real (reflectedUpperCap d x) =
      MeasureTheory.volume.real (euclideanUpperCap d (x / 2)) := by
  change
    (MeasureTheory.volume (reflectedUpperCap d x)).toReal =
      (MeasureTheory.volume (euclideanUpperCap d (x / 2))).toReal
  rw [volume_reflectedUpperCap]

theorem reflectedUpperCap_finite (d : ℕ) (x : ℝ) :
    MeasureTheory.volume (reflectedUpperCap d x) ≠ ⊤ := by
  rw [volume_reflectedUpperCap]
  exact euclideanUpperCap_finite d (x / 2)

theorem upperCaps_disjoint (d : ℕ) (x : ℝ) :
    Disjoint (euclideanUpperCap d (x / 2))
      (reflectedUpperCap d x) := by
  rw [Set.disjoint_left]
  rintro ⟨t, y⟩ hright hleft
  have hright' : t ∈ Set.Ioc (x / 2) 1 := hright.1
  have hleft' : x - t ∈ Set.Ioc (x / 2) 1 := hleft.1
  linarith [hright'.1, hleft'.1]

theorem upperCaps_subset_coordinateUnitLens
    (d : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    euclideanUpperCap d (x / 2) ∪ reflectedUpperCap d x ⊆
      coordinateUnitLens d x := by
  rintro ⟨t, y⟩ (hright | hleft)
  · rcases hright with ⟨ht, hball⟩
    change t ∈ Set.Ioc (x / 2) 1 at ht
    change t ^ 2 + ‖y‖ ^ 2 < 1 at hball
    have hfac : 0 ≤ x * (2 * t - x) :=
      mul_nonneg hx.1 (by linarith [ht.1])
    have hsecond : (t - x) ^ 2 + ‖y‖ ^ 2 < 1 := by
      nlinarith
    simpa [coordinateUnitLens, coordinateUnitBall] using
      (show
        t ^ 2 + ‖y‖ ^ 2 < 1 ∧
          (t - x) ^ 2 + ‖y‖ ^ 2 < 1
        from ⟨hball, hsecond⟩)
  · change lensReflection d x (t, y) ∈
      euclideanUpperCap d (x / 2) at hleft
    rcases hleft with ⟨ht, hball⟩
    change x - t ∈ Set.Ioc (x / 2) 1 at ht
    change (x - t) ^ 2 + ‖y‖ ^ 2 < 1 at hball
    have hfac : 0 ≤ x * (x - 2 * t) :=
      mul_nonneg hx.1 (by linarith [ht.1])
    have hfirst : t ^ 2 + ‖y‖ ^ 2 < 1 := by
      nlinarith
    have hsecond : (t - x) ^ 2 + ‖y‖ ^ 2 < 1 := by
      nlinarith
    simpa [coordinateUnitLens, coordinateUnitBall] using
      (show
        t ^ 2 + ‖y‖ ^ 2 < 1 ∧
          (t - x) ^ 2 + ‖y‖ ^ 2 < 1
        from ⟨hfirst, hsecond⟩)

theorem coordinateUnitLens_sdiff_upperCaps_subset_midplane
    (d : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    coordinateUnitLens d x \
        (euclideanUpperCap d (x / 2) ∪ reflectedUpperCap d x) ⊆
      {p | p.1 = x / 2} := by
  rintro ⟨t, y⟩ ⟨hlens, hnot⟩
  simp only [coordinateUnitLens, coordinateUnitBall,
    Set.mem_inter_iff, Set.mem_setOf_eq, sub_zero] at hlens
  rcases hlens with ⟨hfirst, hsecond⟩
  change t = x / 2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply hnot
    right
    change lensReflection d x (t, y) ∈
      euclideanUpperCap d (x / 2)
    constructor
    · change x - t ∈ Set.Ioc (x / 2) 1
      constructor
      · linarith
      · have hsq : (x - t) ^ 2 < 1 := by nlinarith [sq_nonneg ‖y‖]
        have hnonneg : 0 ≤ x - t := by linarith [hx.1, hlt]
        nlinarith
    · change (x - t) ^ 2 + ‖y‖ ^ 2 < 1
      nlinarith
  · apply hnot
    left
    constructor
    · change t ∈ Set.Ioc (x / 2) 1
      constructor
      · exact hgt
      · have hsq : t ^ 2 < 1 := by nlinarith [sq_nonneg ‖y‖]
        have hnonneg : 0 ≤ t := by linarith [hx.1, hgt]
        nlinarith
    · exact hfirst

theorem volume_midplane_zero (d : ℕ) (a : ℝ) :
    MeasureTheory.volume
      ({p : ℝ × EuclideanSpace ℝ (Fin (d - 1)) | p.1 = a}) = 0 := by
  have hset :
      ({p : ℝ × EuclideanSpace ℝ (Fin (d - 1)) | p.1 = a}) =
        ({a} : Set ℝ) ×ˢ Set.univ := by
    ext p
    simp
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton,
    zero_mul]

theorem volume_coordinateUnitLens_eq_upperCaps
    (d : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    MeasureTheory.volume (coordinateUnitLens d x) =
      MeasureTheory.volume
        (euclideanUpperCap d (x / 2) ∪ reflectedUpperCap d x) := by
  have hsubset := upperCaps_subset_coordinateUnitLens d hx
  have hdiff :
      MeasureTheory.volume
        (coordinateUnitLens d x \
          (euclideanUpperCap d (x / 2) ∪ reflectedUpperCap d x)) = 0 :=
    measure_mono_null
      (coordinateUnitLens_sdiff_upperCaps_subset_midplane d hx)
      (volume_midplane_zero d (x / 2))
  exact (measure_eq_measure_of_null_sdiff hsubset hdiff).symm

theorem volumeReal_coordinateUnitLens_eq_two_cap
    (d : ℕ) (hd : 2 ≤ d) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    MeasureTheory.volume.real (coordinateUnitLens d x) =
      2 * euclideanUnitBallVolume (d - 1) * capTail d (x / 2) := by
  have hhalf : x / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  calc
    MeasureTheory.volume.real (coordinateUnitLens d x) =
        MeasureTheory.volume.real
          (euclideanUpperCap d (x / 2) ∪ reflectedUpperCap d x) :=
      congrArg ENNReal.toReal (volume_coordinateUnitLens_eq_upperCaps d hx)
    _ = MeasureTheory.volume.real (euclideanUpperCap d (x / 2)) +
        MeasureTheory.volume.real (reflectedUpperCap d x) := by
      rw [measureReal_union
        (upperCaps_disjoint d x)
        (reflectedUpperCap_measurable d x)
        (h₁ := euclideanUpperCap_finite d (x / 2))
        (h₂ := reflectedUpperCap_finite d x)]
    _ = 2 * euclideanUnitBallVolume (d - 1) * capTail d (x / 2) := by
      rw [volumeReal_reflectedUpperCap,
        volumeReal_euclideanUpperCap d hd hhalf]
      ring

theorem volumeReal_coordinateUnitLens_eq_profile
    (d : ℕ) (hd : 2 ≤ d) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    MeasureTheory.volume.real (coordinateUnitLens d x) =
      euclideanUnitBallVolume d * lensProfile d x := by
  rw [volumeReal_coordinateUnitLens_eq_two_cap d hd hx,
    lensProfile_eq_unitBallVolume_capIntegral d (by omega) x]
  have hdim : euclideanUnitBallVolume d ≠ 0 :=
    (euclideanUnitBallVolume_pos d).ne'
  field_simp [hdim]

theorem lensProfile_eq_normalized_coordinateUnitLens
    (d : ℕ) (hd : 2 ≤ d) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    lensProfile d x =
      MeasureTheory.volume.real (coordinateUnitLens d x) /
        euclideanUnitBallVolume d := by
  rw [volumeReal_coordinateUnitLens_eq_profile d hd hx]
  exact (mul_div_cancel_left₀ _ (euclideanUnitBallVolume_pos d).ne').symm

theorem normalizedVolume_coordinateUnitLens_cone_bounds
    (d : ℕ) (hd : 2 ≤ d) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    max
        (1 -
          (euclideanUnitBallVolume (d - 1) /
            euclideanUnitBallVolume d) * x)
        0 ≤
      MeasureTheory.volume.real (coordinateUnitLens d x) /
        euclideanUnitBallVolume d ∧
      MeasureTheory.volume.real (coordinateUnitLens d x) /
          euclideanUnitBallVolume d ≤
        max (1 - x / 2) 0 := by
  rw [← lensProfile_eq_normalized_coordinateUnitLens d hd hx]
  exact lensProfile_cone_bounds_unitBallVolume d (by omega) hx

end Shepp.Section2
end SheppFlattenedModule004

section SheppFlattenedModule005
open scoped BigOperators

namespace Shepp.Section2

noncomputable def coneProfile (r t : ℝ) : ℝ := max (1 - t / r) 0

noncomputable def coneTerm (r v : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  v n * coneProfile (r n) t

noncomputable def conePrefix (r v : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), coneTerm r v n t

noncomputable def coneSum (r v : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n, coneTerm r v n t

noncomputable def prefixMass (v : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), v n

noncomputable def prefixSlope (r v : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), v n / r n

noncomputable def previousMass (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | k + 1 => prefixMass v k

noncomputable def expIncrement (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (prefixMass v n) - Real.exp (previousMass v n)

lemma coneProfile_eq_sub_div_of_lt
    {r t : ℝ} (hr : 0 < r) (ht : t < r) :
    coneProfile r t = 1 - t / r := by
  rw [coneProfile, max_eq_left]
  exact le_of_lt (sub_pos.mpr ((div_lt_one hr).2 ht))

lemma coneProfile_eq_sub_div_of_le
    {r t : ℝ} (hr : 0 < r) (ht : t ≤ r) :
    coneProfile r t = 1 - t / r := by
  rw [coneProfile, max_eq_left]
  exact sub_nonneg.mpr ((div_le_one hr).2 ht)

lemma coneProfile_eq_zero_of_le
    {r t : ℝ} (hr : 0 < r) (ht : r ≤ t) :
    coneProfile r t = 0 := by
  rw [coneProfile, max_eq_right]
  exact sub_nonpos.mpr ((one_le_div hr).2 ht)

lemma prefixMass_succ (v : ℕ → ℝ) (N : ℕ) :
    prefixMass v (N + 1) = prefixMass v N + v (N + 1) := by
  simp [prefixMass, Finset.sum_range_succ, add_assoc]

lemma prefixSlope_succ (r v : ℕ → ℝ) (N : ℕ) :
    prefixSlope r v (N + 1) = prefixSlope r v N + v (N + 1) / r (N + 1) := by
  simp [prefixSlope, Finset.sum_range_succ, add_assoc]

lemma previousMass_zero (v : ℕ → ℝ) : previousMass v 0 = 0 := rfl

lemma previousMass_succ (v : ℕ → ℝ) (n : ℕ) :
    previousMass v (n + 1) = prefixMass v n := by
  rfl

theorem conePrefix_eq_mass_sub_slope
    {r v : ℕ → ℝ} {N : ℕ} {t : ℝ}
    (hr : ∀ n, 0 < r n)
    (hmono : Antitone r)
    (ht : t < r N) :
    conePrefix r v N t = prefixMass v N - t * prefixSlope r v N := by
  have hterm : ∀ n ∈ Finset.range (N + 1),
      coneTerm r v n t = v n - t * (v n / r n) := by
    intro n hn
    have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have htrn : t < r n := lt_of_lt_of_le ht (hmono hnN)
    rw [coneTerm, coneProfile_eq_sub_div_of_lt (hr n) htrn]
    field_simp
  rw [conePrefix, prefixMass, prefixSlope]
  calc
    (∑ n ∈ Finset.range (N + 1), coneTerm r v n t)
        = ∑ n ∈ Finset.range (N + 1), (v n - t * (v n / r n)) :=
          Finset.sum_congr rfl hterm
    _ = (∑ n ∈ Finset.range (N + 1), v n) -
          t * (∑ n ∈ Finset.range (N + 1), v n / r n) := by
          simp_rw [Finset.sum_sub_distrib, Finset.mul_sum]

theorem conePrefix_eq_mass_sub_slope_closed
    {r v : ℕ → ℝ} {N : ℕ} {t : ℝ}
    (hr : ∀ n, 0 < r n)
    (hmono : Antitone r)
    (ht : t ≤ r N) :
    conePrefix r v N t = prefixMass v N - t * prefixSlope r v N := by
  have hterm : ∀ n ∈ Finset.range (N + 1),
      coneTerm r v n t = v n - t * (v n / r n) := by
    intro n hn
    have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have htrn : t ≤ r n := ht.trans (hmono hnN)
    rw [coneTerm, coneProfile_eq_sub_div_of_le (hr n) htrn]
    field_simp
  rw [conePrefix, prefixMass, prefixSlope]
  calc
    (∑ n ∈ Finset.range (N + 1), coneTerm r v n t) =
        ∑ n ∈ Finset.range (N + 1), (v n - t * (v n / r n)) :=
      Finset.sum_congr rfl hterm
    _ = (∑ n ∈ Finset.range (N + 1), v n) -
          t * (∑ n ∈ Finset.range (N + 1), v n / r n) := by
      simp_rw [Finset.sum_sub_distrib, Finset.mul_sum]

theorem coneSum_eq_mass_sub_slope
    {r v : ℕ → ℝ} {N : ℕ} {t : ℝ}
    (hr : ∀ n, 0 < r n)
    (hmono : Antitone r)
    (hlower : r (N + 1) ≤ t)
    (hupper : t < r N) :
    coneSum r v t = prefixMass v N - t * prefixSlope r v N := by
  rw [coneSum, tsum_eq_sum (s := Finset.range (N + 1))]
  · exact conePrefix_eq_mass_sub_slope hr hmono hupper
  · intro n hn
    have hNn : N + 1 ≤ n := by
      simpa [Finset.mem_range, not_lt] using hn
    have hrle : r n ≤ t := (hmono hNn).trans hlower
    simp [coneTerm, coneProfile_eq_zero_of_le (hr n) hrle]

theorem coneSum_eq_mass_sub_slope_closed
    {r v : ℕ → ℝ} {N : ℕ} {t : ℝ}
    (hr : ∀ n, 0 < r n)
    (hmono : Antitone r)
    (hlower : r (N + 1) ≤ t)
    (hupper : t ≤ r N) :
    coneSum r v t = prefixMass v N - t * prefixSlope r v N := by
  rw [coneSum, tsum_eq_sum (s := Finset.range (N + 1))]
  · exact conePrefix_eq_mass_sub_slope_closed hr hmono hupper
  · intro n hn
    have hNn : N + 1 ≤ n := by
      simpa [Finset.mem_range, not_lt] using hn
    have hrle : r n ≤ t := (hmono hNn).trans hlower
    simp [coneTerm, coneProfile_eq_zero_of_le (hr n) hrle]

theorem intervalIntegral_cone_energy_piece
    {r v : ℕ → ℝ} (q N : ℕ)
    (hr : ∀ n, 0 < r n)
    (hmono : Antitone r) :
    (∫ t in r (N + 1)..r N,
        Real.exp (coneSum r v t) * t ^ q) =
      Real.exp (prefixMass v N) *
        ∫ t in r (N + 1)..r N,
          Real.exp (-prefixSlope r v N * t) * t ^ q := by
  calc
    (∫ t in r (N + 1)..r N,
        Real.exp (coneSum r v t) * t ^ q) =
        ∫ t in r (N + 1)..r N,
          Real.exp (prefixMass v N) *
            (Real.exp (-prefixSlope r v N * t) * t ^ q) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (hmono (Nat.le_succ N))
      intro t ht
      change Real.exp (coneSum r v t) * t ^ q =
        Real.exp (prefixMass v N) *
          (Real.exp (-prefixSlope r v N * t) * t ^ q)
      rw [coneSum_eq_mass_sub_slope hr hmono (le_of_lt ht.1) ht.2]
      rw [sub_eq_add_neg, Real.exp_add]
      rw [show -(t * prefixSlope r v N) =
        -prefixSlope r v N * t by ring]
      ring
    _ = Real.exp (prefixMass v N) *
        ∫ t in r (N + 1)..r N,
          Real.exp (-prefixSlope r v N * t) * t ^ q := by
      rw [intervalIntegral.integral_const_mul]

theorem sum_expIncrement (v : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), expIncrement v n) =
      Real.exp (prefixMass v N) - 1 := by
  induction N with
  | zero =>
      simp [expIncrement, previousMass, prefixMass]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      simp only [expIncrement, previousMass_succ]
      ring

theorem sum_expIncrement_Ioc
    (v : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc a b, expIncrement v n) =
      Real.exp (prefixMass v b) - Real.exp (prefixMass v a) := by
  have hIoc : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
    ext n
    simp
  rw [hIoc, Finset.sum_Ico_eq_sub _ (Nat.add_le_add_right hab 1)]
  rw [sum_expIncrement v b, sum_expIncrement v a]
  ring

lemma prefixMass_mono
    {v : ℕ → ℝ} (hv : ∀ n, 0 ≤ v n) : Monotone (prefixMass v) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hab))
    (by
      intro i _ _
      exact hv i)

lemma expIncrement_nonneg
    {v : ℕ → ℝ} (hv : ∀ n, 0 ≤ v n) (n : ℕ) :
    0 ≤ expIncrement v n := by
  rw [expIncrement]
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  cases n with
  | zero =>
      simp [previousMass, prefixMass, hv]
  | succ k =>
      rw [previousMass_succ, prefixMass_succ]
      exact le_add_of_nonneg_right (hv (k + 1))

end Shepp.Section2
end SheppFlattenedModule005

section SheppFlattenedModule006
namespace Shepp.Section2

open MeasureTheory

def coordinateBall (d : ℕ) (r c : ℝ) :
    Set (ℝ × EuclideanSpace ℝ (Fin (d - 1))) :=
  {p | (p.1 - c) ^ 2 + ‖p.2‖ ^ 2 < r ^ 2}

def coordinateLens (d : ℕ) (r t : ℝ) :
    Set (ℝ × EuclideanSpace ℝ (Fin (d - 1))) :=
  coordinateBall d r 0 ∩ coordinateBall d r t

def coordinateDilation (d : ℕ) (r : ℝ) :
    (ℝ × EuclideanSpace ℝ (Fin (d - 1))) →ₗ[ℝ]
      (ℝ × EuclideanSpace ℝ (Fin (d - 1))) :=
  r • LinearMap.id

@[simp]
theorem coordinateDilation_apply (d : ℕ) (r : ℝ)
    (p : ℝ × EuclideanSpace ℝ (Fin (d - 1))) :
    coordinateDilation d r p = (r * p.1, r • p.2) := by
  rcases p with ⟨s, y⟩
  rfl

theorem finrank_coordinateSpace (d : ℕ) (hd : 1 ≤ d) :
    Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin (d - 1))) = d := by
  simp [Module.finrank_prod]
  omega

theorem coordinateDilation_image_unitLens
    (d : ℕ) {r t : ℝ} (hr : 0 < r) :
    coordinateDilation d r '' coordinateUnitLens d (t / r) =
      coordinateLens d r t := by
  ext p
  rcases p with ⟨a, y⟩
  constructor
  · rintro ⟨q, hq, hqimage⟩
    rcases q with ⟨s, z⟩
    simp only [coordinateUnitLens, coordinateUnitBall, Set.mem_inter_iff,
      Set.mem_setOf_eq, sub_zero] at hq
    rcases hq with ⟨hfirst, hsecond⟩
    simp only [coordinateDilation_apply, Prod.mk.injEq] at hqimage
    rcases hqimage with ⟨rfl, hy⟩
    subst y
    simp only [coordinateLens, coordinateBall, Set.mem_inter_iff,
      Set.mem_setOf_eq, sub_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    constructor
    · have hmul := mul_lt_mul_of_pos_left hfirst (sq_pos_of_pos hr)
      nlinarith
    · have hid : r * s - t = r * (s - t / r) := by
        field_simp [hr.ne']
      rw [hid]
      have hmul := mul_lt_mul_of_pos_left hsecond (sq_pos_of_pos hr)
      nlinarith
  · intro hp
    simp only [coordinateLens, coordinateBall, Set.mem_inter_iff,
      Set.mem_setOf_eq, sub_zero] at hp
    rcases hp with ⟨hfirst, hsecond⟩
    refine ⟨(a / r, (1 / r) • y), ?_, ?_⟩
    · simp only [coordinateUnitLens, coordinateUnitBall, Set.mem_inter_iff,
        Set.mem_setOf_eq, sub_zero]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hr)]
      constructor
      · calc
          (a / r) ^ 2 + (1 / r * ‖y‖) ^ 2 =
              (a ^ 2 + ‖y‖ ^ 2) / r ^ 2 := by
                field_simp [hr.ne']
          _ < 1 := (div_lt_one (sq_pos_of_pos hr)).2 hfirst
      · calc
          (a / r - t / r) ^ 2 + (1 / r * ‖y‖) ^ 2 =
              ((a - t) ^ 2 + ‖y‖ ^ 2) / r ^ 2 := by
                field_simp [hr.ne']
          _ < 1 := (div_lt_one (sq_pos_of_pos hr)).2 hsecond
    · simp only [coordinateDilation_apply, Prod.mk.injEq]
      constructor
      · exact (mul_div_cancel₀ a hr.ne')
      · rw [smul_smul]
        field_simp [hr.ne']
        simp

theorem volumeReal_coordinateLens_scaling
    (d : ℕ) (hd : 1 ≤ d) {r t : ℝ} (hr : 0 < r) :
    MeasureTheory.volume.real (coordinateLens d r t) =
      r ^ d *
        MeasureTheory.volume.real (coordinateUnitLens d (t / r)) := by
  rw [← coordinateDilation_image_unitLens d hr]
  change
    (MeasureTheory.volume
      (coordinateDilation d r '' coordinateUnitLens d (t / r))).toReal = _
  rw [Measure.volume_eq_prod]
  rw [Measure.addHaar_image_linearMap]
  have hdet :
      |LinearMap.det (coordinateDilation d r)| = r ^ d := by
    rw [coordinateDilation, LinearMap.det_smul, LinearMap.det_id,
      finrank_coordinateSpace d hd, mul_one, abs_pow, abs_of_pos hr]
  rw [hdet, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le d)]
  change
    r ^ d *
        (((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume :
            Measure (EuclideanSpace ℝ (Fin (d - 1)))))
          (coordinateUnitLens d (t / r))).toReal =
      r ^ d *
        (((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume :
            Measure (EuclideanSpace ℝ (Fin (d - 1)))))
          (coordinateUnitLens d (t / r))).toReal
  rfl

theorem volumeReal_coordinateLens_eq_profile
    (d : ℕ) (hd : 2 ≤ d) {r t : ℝ}
    (hr : 0 < r) (ht : t ∈ Set.Icc (0 : ℝ) (2 * r)) :
    MeasureTheory.volume.real (coordinateLens d r t) =
      euclideanUnitBallVolume d * r ^ d * lensProfile d (t / r) := by
  have hnormalized : t / r ∈ Set.Icc (0 : ℝ) 2 := by
    constructor
    · exact div_nonneg ht.1 hr.le
    · exact (div_le_iff₀ hr).2 (by linarith [ht.2])
  rw [volumeReal_coordinateLens_scaling d (by omega) hr,
    volumeReal_coordinateUnitLens_eq_profile d hd hnormalized]
  ring

theorem coordinateLens_eq_empty_of_two_mul_le
    (d : ℕ) {r t : ℝ} (hr : 0 ≤ r) (ht : 2 * r ≤ t) :
    coordinateLens d r t = ∅ := by
  ext p
  rcases p with ⟨a, y⟩
  constructor
  · intro hp
    simp only [coordinateLens, coordinateBall, Set.mem_inter_iff,
      Set.mem_setOf_eq, sub_zero] at hp
    rcases hp with ⟨hfirst, hsecond⟩
    have htwo : 0 ≤ 2 * r := by positivity
    have ht0 : 0 ≤ t := htwo.trans ht
    have hsq : (2 * r) ^ 2 ≤ t ^ 2 :=
      (sq_le_sq₀ htwo ht0).2 ht
    exfalso
    nlinarith [sq_nonneg (2 * a - t), sq_nonneg ‖y‖]
  · intro hp
    exact hp.elim

theorem volumeReal_coordinateLens_eq_zero_of_two_mul_le
    (d : ℕ) {r t : ℝ} (hr : 0 ≤ r) (ht : 2 * r ≤ t) :
    MeasureTheory.volume.real (coordinateLens d r t) = 0 := by
  rw [coordinateLens_eq_empty_of_two_mul_le d hr ht]
  simp

theorem normalizedVolume_coordinateLens_cone_bounds
    (d : ℕ) (hd : 2 ≤ d) {r t : ℝ}
    (hr : 0 < r) (ht : t ∈ Set.Icc (0 : ℝ) (2 * r)) :
    max
        (1 -
          (euclideanUnitBallVolume (d - 1) /
            euclideanUnitBallVolume d) * (t / r))
        0 ≤
      MeasureTheory.volume.real (coordinateLens d r t) /
        (euclideanUnitBallVolume d * r ^ d) ∧
      MeasureTheory.volume.real (coordinateLens d r t) /
          (euclideanUnitBallVolume d * r ^ d) ≤
        max (1 - (t / r) / 2) 0 := by
  have hnormalized : t / r ∈ Set.Icc (0 : ℝ) 2 := by
    constructor
    · exact div_nonneg ht.1 hr.le
    · exact (div_le_iff₀ hr).2 (by linarith [ht.2])
  have hscale : euclideanUnitBallVolume d * r ^ d ≠ 0 :=
    mul_ne_zero (euclideanUnitBallVolume_pos d).ne'
      (pow_ne_zero d hr.ne')
  rw [volumeReal_coordinateLens_eq_profile d hd hr ht]
  have hcancel :
      (euclideanUnitBallVolume d * r ^ d * lensProfile d (t / r)) /
          (euclideanUnitBallVolume d * r ^ d) =
        lensProfile d (t / r) :=
    mul_div_cancel_left₀ _ hscale
  rw [hcancel]
  exact lensProfile_cone_bounds_unitBallVolume d (by omega) hnormalized

theorem one_half_le_unitBallVolume_ratio (d : ℕ) (hd : 1 ≤ d) :
    (1 : ℝ) / 2 ≤
      euclideanUnitBallVolume (d - 1) / euclideanUnitBallVolume d := by
  rw [← coneConstant_eq_unitBallVolume_ratio d hd]
  have hend :=
    (lensProfile_cone_bounds d
      (x := (2 : ℝ)) (by norm_num : (2 : ℝ) ∈ Set.Icc 0 2)).1
  rw [lensProfile_two] at hend
  have hlinear : 1 - coneConstant d * 2 ≤ 0 :=
    (le_max_left (1 - coneConstant d * 2) 0).trans hend
  linarith

theorem volumeReal_coordinateLens_cone_bounds
    (d : ℕ) (hd : 2 ≤ d) {r t : ℝ}
    (hr : 0 < r) (ht : t ∈ Set.Icc (0 : ℝ) (2 * r)) :
    (euclideanUnitBallVolume d * r ^ d) *
        coneProfile r
          ((euclideanUnitBallVolume (d - 1) /
            euclideanUnitBallVolume d) * t) ≤
      MeasureTheory.volume.real (coordinateLens d r t) ∧
      MeasureTheory.volume.real (coordinateLens d r t) ≤
        (euclideanUnitBallVolume d * r ^ d) * coneProfile r (t / 2) := by
  have hnormalized := normalizedVolume_coordinateLens_cone_bounds d hd hr ht
  have hscalePos : 0 < euclideanUnitBallVolume d * r ^ d :=
    mul_pos (euclideanUnitBallVolume_pos d) (pow_pos hr d)
  constructor
  · have h := (le_div_iff₀ hscalePos).mp hnormalized.1
    have harg :
        (euclideanUnitBallVolume (d - 1) /
            euclideanUnitBallVolume d) * (t / r) =
          ((euclideanUnitBallVolume (d - 1) /
            euclideanUnitBallVolume d) * t) / r := by
      ring
    rw [harg] at h
    simpa only [coneProfile, mul_comm] using h
  · have h := (div_le_iff₀ hscalePos).mp hnormalized.2
    have harg : (t / r) / 2 = (t / 2) / r := by ring
    rw [harg] at h
    simpa only [coneProfile, mul_comm] using h

theorem volumeReal_coordinateLens_cone_bounds_of_nonneg
    (d : ℕ) (hd : 2 ≤ d) {r t : ℝ}
    (hr : 0 < r) (ht : 0 ≤ t) :
    (euclideanUnitBallVolume d * r ^ d) *
        coneProfile r
          ((euclideanUnitBallVolume (d - 1) /
            euclideanUnitBallVolume d) * t) ≤
      MeasureTheory.volume.real (coordinateLens d r t) ∧
      MeasureTheory.volume.real (coordinateLens d r t) ≤
        (euclideanUnitBallVolume d * r ^ d) * coneProfile r (t / 2) := by
  by_cases hsupport : t ≤ 2 * r
  · exact volumeReal_coordinateLens_cone_bounds d hd hr ⟨ht, hsupport⟩
  · have hsep : 2 * r ≤ t := le_of_not_ge hsupport
    have hhalf := one_half_le_unitBallVolume_ratio d (by omega)
    have hright : r ≤ t / 2 := by linarith
    have hleft :
        r ≤
          (euclideanUnitBallVolume (d - 1) /
            euclideanUnitBallVolume d) * t := by
      have hmul := mul_le_mul_of_nonneg_right hhalf ht
      linarith
    rw [volumeReal_coordinateLens_eq_zero_of_two_mul_le d hr.le hsep,
      coneProfile_eq_zero_of_le hr hleft,
      coneProfile_eq_zero_of_le hr hright]
    simp

end Shepp.Section2
end SheppFlattenedModule006

section SheppFlattenedModule007
namespace Shepp.Section2

open Filter
open scoped Topology

noncomputable def radiusVolume (d : ℕ) (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  euclideanUnitBallVolume d * (r n) ^ d

noncomputable def euclideanOverlapTerm
    (d : ℕ) (r : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  MeasureTheory.volume.real (coordinateLens d (r n) t)

noncomputable def euclideanOverlapSum
    (d : ℕ) (r : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n, euclideanOverlapTerm d r n t

lemma hasFiniteSupport_of_eventually_atTop_eq_zero
    {f : ℕ → ℝ} (hf : ∀ᶠ n in atTop, f n = 0) :
    f.HasFiniteSupport := by
  rw [Function.HasFiniteSupport]
  rcases Filter.eventually_atTop.mp hf with ⟨N, hN⟩
  refine (Set.finite_Iio N).subset ?_
  intro n hn
  have hne : f n ≠ 0 := by
    simpa [Function.support] using hn
  by_contra hnlt
  exact hne (hN n (Nat.le_of_not_gt hnlt))

lemma eventually_radius_le_of_tendsto_zero
    {r : ℕ → ℝ} (hrlim : Tendsto r atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n in atTop, r n ≤ t := by
  exact ((tendsto_order.mp hrlim).2 t ht).mono fun _ h => h.le

lemma eventually_two_mul_radius_le_of_tendsto_zero
    {r : ℕ → ℝ} (hrlim : Tendsto r atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n in atTop, 2 * r n ≤ t := by
  have htwo : Tendsto (fun n => 2 * r n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hrlim
  exact ((tendsto_order.mp htwo).2 t ht).mono fun _ h => h.le

theorem summable_euclideanOverlapTerm
    (d : ℕ) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun n => euclideanOverlapTerm d r n t) := by
  apply summable_of_hasFiniteSupport
  apply hasFiniteSupport_of_eventually_atTop_eq_zero
  filter_upwards [eventually_two_mul_radius_le_of_tendsto_zero hrlim ht]
    with n hn
  exact volumeReal_coordinateLens_eq_zero_of_two_mul_le d (hr n).le hn

theorem summable_coneTerm_of_tendsto_zero
    {r v : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun n => coneTerm r v n t) := by
  apply summable_of_hasFiniteSupport
  apply hasFiniteSupport_of_eventually_atTop_eq_zero
  filter_upwards [eventually_radius_le_of_tendsto_zero hrlim ht] with n hn
  rw [coneTerm, coneProfile_eq_zero_of_le (hr n) hn, mul_zero]

theorem coneTerm_le_euclideanOverlapTerm
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    coneTerm r (radiusVolume d r) n
        ((euclideanUnitBallVolume (d - 1) /
          euclideanUnitBallVolume d) * t) ≤
      euclideanOverlapTerm d r n t := by
  simpa only [coneTerm, radiusVolume, euclideanOverlapTerm] using
    (volumeReal_coordinateLens_cone_bounds_of_nonneg
      d hd (hr n) ht).1

theorem euclideanOverlapTerm_le_coneTerm
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    euclideanOverlapTerm d r n t ≤
      coneTerm r (radiusVolume d r) n (t / 2) := by
  simpa only [coneTerm, radiusVolume, euclideanOverlapTerm] using
    (volumeReal_coordinateLens_cone_bounds_of_nonneg
      d hd (hr n) ht).2

theorem coneSum_le_euclideanOverlapSum_le
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) :
    coneSum r (radiusVolume d r)
        ((euclideanUnitBallVolume (d - 1) /
          euclideanUnitBallVolume d) * t) ≤
      euclideanOverlapSum d r t ∧
      euclideanOverlapSum d r t ≤
        coneSum r (radiusVolume d r) (t / 2) := by
  have hratioPos :
      0 < euclideanUnitBallVolume (d - 1) /
        euclideanUnitBallVolume d :=
    div_pos (euclideanUnitBallVolume_pos _) (euclideanUnitBallVolume_pos _)
  have hlowerSummable :
      Summable (fun n =>
        coneTerm r (radiusVolume d r) n
          ((euclideanUnitBallVolume (d - 1) /
            euclideanUnitBallVolume d) * t)) :=
    summable_coneTerm_of_tendsto_zero hr hrlim (mul_pos hratioPos ht)
  have hoverlapSummable :=
    summable_euclideanOverlapTerm d hr hrlim ht
  have hupperSummable :
      Summable (fun n =>
        coneTerm r (radiusVolume d r) n (t / 2)) :=
    summable_coneTerm_of_tendsto_zero hr hrlim (half_pos ht)
  constructor
  · exact hlowerSummable.tsum_le_tsum
      (coneTerm_le_euclideanOverlapTerm d hd hr ht.le)
      hoverlapSummable
  · exact hoverlapSummable.tsum_le_tsum
      (euclideanOverlapTerm_le_coneTerm d hd hr ht.le)
      hupperSummable

theorem exp_coneSum_le_exp_euclideanOverlapSum_le
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) :
    Real.exp
        (coneSum r (radiusVolume d r)
          ((euclideanUnitBallVolume (d - 1) /
            euclideanUnitBallVolume d) * t)) ≤
      Real.exp (euclideanOverlapSum d r t) ∧
      Real.exp (euclideanOverlapSum d r t) ≤
        Real.exp (coneSum r (radiusVolume d r) (t / 2)) := by
  have hcompare := coneSum_le_euclideanOverlapSum_le d hd hr hrlim ht
  exact ⟨Real.exp_le_exp.mpr hcompare.1, Real.exp_le_exp.mpr hcompare.2⟩

end Shepp.Section2
end SheppFlattenedModule007

section SheppFlattenedModule008
namespace Shepp.Section2

def integerLattice (d : ℕ) :
    AddSubgroup (EuclideanSpace ℝ (Fin d)) where
  carrier := {q | ∀ i, ∃ z : ℤ, q i = (z : ℝ)}
  zero_mem' := by
    intro i
    exact ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy i
    rcases hx i with ⟨m, hm⟩
    rcases hy i with ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    simp only [PiLp.add_apply, hm, hn, Int.cast_add]
  neg_mem' := by
    intro x hx i
    rcases hx i with ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    simp only [PiLp.neg_apply, hm, Int.cast_neg]

abbrev FlatTorus (d : ℕ) :=
  EuclideanSpace ℝ (Fin d) ⧸ integerLattice d

noncomputable def flatTorusMk (d : ℕ) :
    EuclideanSpace ℝ (Fin d) →+ FlatTorus d :=
  QuotientAddGroup.mk' (integerLattice d)

@[simp]
theorem flatTorusMk_apply (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    flatTorusMk d x = QuotientAddGroup.mk' (integerLattice d) x :=
  rfl

theorem one_le_norm_of_mem_integerLattice
    {d : ℕ} {q : EuclideanSpace ℝ (Fin d)}
    (hq : q ∈ integerLattice d) (hq0 : q ≠ 0) :
    1 ≤ ‖q‖ := by
  have hexists : ∃ i, q i ≠ 0 := by
    by_contra h
    push Not at h
    apply hq0
    ext i
    exact h i
  rcases hexists with ⟨i, hi⟩
  rcases hq i with ⟨z, hz⟩
  have hz0 : z ≠ 0 := by
    intro hzzero
    apply hi
    rw [hz, hzzero]
    simp
  have hone : (1 : ℝ) ≤ |(z : ℝ)| := by
    exact_mod_cast Int.one_le_abs hz0
  have hcoord : |q i| ≤ ‖q‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le q i
  rw [hz] at hcoord
  exact hone.trans hcoord

theorem eq_of_sub_mem_integerLattice_of_norm_lt_one
    {d : ℕ} {x y : EuclideanSpace ℝ (Fin d)}
    (hmem : x - y ∈ integerLattice d) (hnorm : ‖x - y‖ < 1) :
    x = y := by
  by_contra hxy
  have hnonzero : x - y ≠ 0 := sub_ne_zero.mpr hxy
  exact (not_lt_of_ge
    (one_le_norm_of_mem_integerLattice hmem hnonzero)) hnorm

theorem quotient_norm_flatTorusMk_eq
    {d : ℕ} {z : EuclideanSpace ℝ (Fin d)} (hz : ‖z‖ < 1 / 2) :
    ‖flatTorusMk d z‖ = ‖z‖ := by
  rw [flatTorusMk, quotient_norm_mk_eq]
  have hbdd :
      BddBelow ((fun q : EuclideanSpace ℝ (Fin d) => ‖z + q‖) ''
        (integerLattice d : Set (EuclideanSpace ℝ (Fin d)))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact norm_nonneg _
  have hmem :
      ‖z‖ ∈ ((fun q : EuclideanSpace ℝ (Fin d) => ‖z + q‖) ''
        (integerLattice d : Set (EuclideanSpace ℝ (Fin d)))) := by
    exact ⟨0, (integerLattice d).zero_mem, by simp⟩
  have hnonempty :
      ((fun q : EuclideanSpace ℝ (Fin d) => ‖z + q‖) ''
        (integerLattice d : Set (EuclideanSpace ℝ (Fin d)))).Nonempty :=
    ⟨‖z‖, hmem⟩
  apply le_antisymm
  · exact csInf_le hbdd hmem
  · apply le_csInf hnonempty
    · intro w hw
      rcases hw with ⟨q, hq, rfl⟩
      by_cases hq0 : q = 0
      · subst q
        simp
      · have hqnorm : 1 ≤ ‖q‖ :=
          one_le_norm_of_mem_integerLattice hq hq0
        have htriangle : ‖q‖ ≤ ‖z + q‖ + ‖z‖ := by
          have := norm_sub_le (z + q) z
          simpa only [add_sub_cancel_left] using this
        linarith

theorem dist_flatTorusMk_eq_of_dist_lt_half
    {d : ℕ} {x y : EuclideanSpace ℝ (Fin d)}
    (hxy : dist x y < 1 / 2) :
    dist (flatTorusMk d x) (flatTorusMk d y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact quotient_norm_flatTorusMk_eq (by
    simpa only [dist_eq_norm] using hxy)

theorem image_ball_flatTorusMk
    (d : ℕ) (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    flatTorusMk d '' Metric.ball c r =
      Metric.ball (flatTorusMk d c) r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
    rw [← map_sub]
    exact QuotientAddGroup.norm_mk_le_norm.trans_lt hx
  · intro hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    rcases QuotientAddGroup.norm_lt_iff.mp hy with ⟨z, hz, hznorm⟩
    refine ⟨c + z, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hznorm
    · change flatTorusMk d z = y - flatTorusMk d c at hz
      rw [map_add, hz]
      abel

theorem image_closedBall_zero_flatTorusMk
    (d : ℕ) {r : ℝ} (hr : r < 1 / 2) :
    flatTorusMk d '' Metric.closedBall 0 r =
      Metric.closedBall (0 : FlatTorus d) r := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    calc
      ‖flatTorusMk d z‖ ≤ ‖z‖ := QuotientAddGroup.norm_mk_le_norm
      _ ≤ r := hz
  · intro hq
    rw [Metric.mem_closedBall, dist_zero_right] at hq
    have hqhalf : ‖q‖ < 1 / 2 := hq.trans_lt hr
    rcases QuotientAddGroup.norm_lt_iff.mp hqhalf with ⟨z, hz, hznorm⟩
    change flatTorusMk d z = q at hz
    refine ⟨z, ?_, hz⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have heq : ‖flatTorusMk d z‖ = ‖z‖ :=
      quotient_norm_flatTorusMk_eq hznorm
    rw [← heq, hz]
    exact hq

theorem isometryOn_flatTorusMk_ball
    (d : ℕ) {c : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hr : r < 1 / 4) :
    ∀ ⦃x⦄, x ∈ Metric.ball c r →
      ∀ ⦃y⦄, y ∈ Metric.ball c r →
        dist (flatTorusMk d x) (flatTorusMk d y) = dist x y := by
  intro x hx y hy
  apply dist_flatTorusMk_eq_of_dist_lt_half
  have hxy : dist x y < r + r :=
    calc
      dist x y ≤ dist x c + dist y c := dist_triangle_right x y c
      _ < r + r := add_lt_add hx hy
  linarith

theorem injOn_flatTorusMk_ball
    (d : ℕ) {c : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hr : r < 1 / 4) :
    Set.InjOn (flatTorusMk d) (Metric.ball c r) := by
  intro x hx y hy hxy
  have hdist := isometryOn_flatTorusMk_ball d hr hx hy
  apply dist_eq_zero.mp
  rw [← hdist, hxy, dist_self]

theorem injOn_flatTorusMk_closedBall
    (d : ℕ) {r : ℝ} (hr : r < 1 / 4) :
    Set.InjOn (flatTorusMk d)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) r) := by
  intro x hx y hy hxy
  have hxyHalf : dist x y < 1 / 2 := by
    have htri : dist x y ≤ dist x 0 + dist y 0 := dist_triangle_right x y 0
    have hx' : dist x 0 ≤ r := hx
    have hy' : dist y 0 ≤ r := hy
    linarith
  have hiso := dist_flatTorusMk_eq_of_dist_lt_half hxyHalf
  apply dist_eq_zero.mp
  rw [← hiso, hxy, dist_self]

theorem localEuclideanLift_metric
    (d : ℕ) {c : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hr : r < 1 / 4) :
    flatTorusMk d '' Metric.ball c r =
        Metric.ball (flatTorusMk d c) r ∧
      Set.InjOn (flatTorusMk d) (Metric.ball c r) ∧
      (∀ ⦃x⦄, x ∈ Metric.ball c r →
        ∀ ⦃y⦄, y ∈ Metric.ball c r →
          dist (flatTorusMk d x) (flatTorusMk d y) = dist x y) := by
  exact ⟨image_ball_flatTorusMk d c r,
    injOn_flatTorusMk_ball d hr,
    isometryOn_flatTorusMk_ball d hr⟩

end Shepp.Section2
end SheppFlattenedModule008

section SheppFlattenedModule009
namespace Shepp.Section2

open MeasureTheory
open Module
open scoped Pointwise

noncomputable def flatTorusBasis (d : ℕ) :
    Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

theorem integerLattice_eq_zspan (d : ℕ) :
    integerLattice d =
      (Submodule.span ℤ (Set.range (flatTorusBasis d))).toAddSubgroup := by
  ext x
  change x ∈ integerLattice d ↔
    x ∈ Submodule.span ℤ (Set.range (flatTorusBasis d))
  rw [(flatTorusBasis d).mem_span_iff_repr_mem ℤ x]
  simp only [integerLattice, AddSubgroup.mem_mk, flatTorusBasis, Set.mem_range]
  constructor <;> intro hx i <;> rcases hx i with ⟨z, hz⟩ <;>
    exact ⟨z, hz.symm⟩

noncomputable def flatTorusFundamentalDomain (d : ℕ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  ZSpan.fundamentalDomain (flatTorusBasis d)

theorem flatTorusFundamentalDomain_isAddFundamentalDomain (d : ℕ) :
    IsAddFundamentalDomain (integerLattice d)
      (flatTorusFundamentalDomain d) volume := by
  rw [integerLattice_eq_zspan]
  exact ZSpan.isAddFundamentalDomain' (flatTorusBasis d) volume

noncomputable instance integerLatticeCountable (d : ℕ) :
    Countable (integerLattice d) := by
  let f : (Fin d → ℤ) → EuclideanSpace ℝ (Fin d) :=
    fun z => WithLp.toLp 2 (fun i => (z i : ℝ))
  have hsub : (integerLattice d : Set (EuclideanSpace ℝ (Fin d))) ⊆
      Set.range f := by
    intro x hx
    change ∀ i, ∃ z : ℤ, x i = (z : ℝ) at hx
    choose z hz using hx
    refine ⟨z, ?_⟩
    ext i
    exact (hz i).symm
  exact ((Set.countable_range f).mono hsub).to_subtype

noncomputable instance integerLatticeDiscreteTopology (d : ℕ) :
    DiscreteTopology (integerLattice d) := by
  rw [integerLattice_eq_zspan]
  infer_instance

noncomputable instance integerLatticeIsClosed (d : ℕ) :
    IsClosed (integerLattice d : Set (EuclideanSpace ℝ (Fin d))) :=
  AddSubgroup.isClosed_of_discrete

theorem flatTorusFundamentalDomain_isAddFundamentalDomain_op (d : ℕ) :
    IsAddFundamentalDomain (integerLattice d).op
      (flatTorusFundamentalDomain d) volume := by
  have h := IsAddFundamentalDomain.preimage_of_equiv
    (flatTorusFundamentalDomain_isAddFundamentalDomain d)
    (MeasurePreserving.id volume).quasiMeasurePreserving
    (integerLattice d).equivOp.bijective
    (fun g x => by
      change x + (g : EuclideanSpace ℝ (Fin d)) =
        (g : EuclideanSpace ℝ (Fin d)) + x
      exact add_comm _ _)
  simpa using h

noncomputable instance flatTorusHasAddFundamentalDomain (d : ℕ) :
    HasAddFundamentalDomain (integerLattice d).op
      (EuclideanSpace ℝ (Fin d)) volume :=
  (flatTorusFundamentalDomain_isAddFundamentalDomain_op d).hasAddFundamentalDomain volume

noncomputable def flatTorusVolume (d : ℕ) : Measure (FlatTorus d) :=
  (volume.restrict (flatTorusFundamentalDomain d)).map (flatTorusMk d)

noncomputable instance flatTorusMeasureSpace (d : ℕ) :
    MeasureSpace (FlatTorus d) where
  volume := flatTorusVolume d

@[simp]
theorem volume_flatTorus_eq_flatTorusVolume (d : ℕ) :
    (volume : Measure (FlatTorus d)) = flatTorusVolume d :=
  rfl

noncomputable instance flatTorusAddQuotientMeasureEqMeasurePreimage (d : ℕ) :
    AddQuotientMeasureEqMeasurePreimage volume (flatTorusVolume d) := by
  exact IsAddFundamentalDomain.addQuotientMeasureEqMeasurePreimage_addQuotientMeasure
    (flatTorusFundamentalDomain_isAddFundamentalDomain_op d)

theorem volume_flatTorusFundamentalDomain (d : ℕ) :
    volume (flatTorusFundamentalDomain d) = 1 := by
  rw [flatTorusFundamentalDomain]
  rw [MeasureTheory.measure_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped (flatTorusBasis d) volume)]
  simpa [flatTorusBasis] using
    (EuclideanSpace.basisFun (Fin d) ℝ).volume_parallelepiped

@[simp]
theorem flatTorusVolume_univ (d : ℕ) :
    flatTorusVolume d Set.univ = 1 := by
  have hpres :=
    measurePreserving_quotientAddGroup_mk_of_AddQuotientMeasureEqMeasurePreimage
      volume (flatTorusFundamentalDomain_isAddFundamentalDomain_op d)
      (flatTorusVolume d)
  have hmeas : Measurable (flatTorusMk d) := hpres.measurable
  rw [flatTorusVolume, Measure.map_apply hmeas MeasurableSet.univ]
  simp [volume_flatTorusFundamentalDomain]

noncomputable instance flatTorusVolumeIsFinite (d : ℕ) :
    IsFiniteMeasure (flatTorusVolume d) where
  measure_univ_lt_top := by
    rw [flatTorusVolume_univ]
    exact ENNReal.one_lt_top

noncomputable instance flatTorusVolumeIsProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (flatTorusVolume d) where
  measure_univ := flatTorusVolume_univ d

noncomputable instance flatTorusVolumeIsAddHaarMeasure (d : ℕ) :
    Measure.IsAddHaarMeasure (flatTorusVolume d) :=
  AddQuotientMeasureEqMeasurePreimage.addHaarMeasure_quotient volume

@[simp]
theorem flatTorusMk_vadd_integerLattice_op
    (d : ℕ) (g : (integerLattice d).op)
    (x : EuclideanSpace ℝ (Fin d)) :
    flatTorusMk d (g +ᵥ x) = flatTorusMk d x := by
  change ((g +ᵥ x : EuclideanSpace ℝ (Fin d)) : FlatTorus d) =
    (x : FlatTorus d)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  change x + AddOpposite.unop (g : (EuclideanSpace ℝ (Fin d))ᵃᵒᵖ) - x ∈
    integerLattice d
  rw [add_sub_cancel_left]
  exact g.property

theorem flatTorusVolume_image_eq_volume
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : MeasurableSet s)
    (hinj : Set.InjOn (flatTorusMk d) s) :
    flatTorusVolume d (flatTorusMk d '' s) = volume s := by
  have hpre :
      flatTorusMk d ⁻¹' (flatTorusMk d '' s) =
        ⋃ g : (integerLattice d).op, g +ᵥ s := by
    exact AddAction.quotient_preimage_image_eq_union_add s
  have himage : MeasurableSet (flatTorusMk d '' s) := by
    rw [measurableSet_quotient, Quotient.mk''_eq_mk]
    change MeasurableSet (flatTorusMk d ⁻¹' (flatTorusMk d '' s))
    rw [hpre]
    exact MeasurableSet.iUnion fun g => hs.const_vadd g
  have hdisj : Pairwise (Function.onFun Disjoint
      fun g : (integerLattice d).op => g +ᵥ s) := by
    intro g h hgh
    change Disjoint (g +ᵥ s) (h +ᵥ s)
    rw [Set.disjoint_left]
    intro z hzg hzh
    change z ∈ (fun x => g +ᵥ x) '' s at hzg
    change z ∈ (fun x => h +ᵥ x) '' s at hzh
    rcases hzg with ⟨x, hx, rfl⟩
    rcases hzh with ⟨y, hy, hxy⟩
    have hmk : flatTorusMk d x = flatTorusMk d y := by
      simpa only [flatTorusMk_vadd_integerLattice_op] using
        congrArg (flatTorusMk d) hxy.symm
    have hxeq : x = y := hinj hx hy hmk
    subst y
    apply hgh
    apply Subtype.ext
    apply AddOpposite.unop_injective
    change x + AddOpposite.unop (h : (EuclideanSpace ℝ (Fin d))ᵃᵒᵖ) =
      x + AddOpposite.unop (g : (EuclideanSpace ℝ (Fin d))ᵃᵒᵖ) at hxy
    exact (add_left_cancel hxy).symm
  rw [(flatTorusFundamentalDomain_isAddFundamentalDomain_op d).addProjection_respects_measure_apply
    (flatTorusVolume d) himage]
  change volume ((flatTorusMk d ⁻¹' (flatTorusMk d '' s)) ∩
    flatTorusFundamentalDomain d) = volume s
  rw [hpre, Set.iUnion_inter]
  rw [measure_iUnion₀]
  · exact ((flatTorusFundamentalDomain_isAddFundamentalDomain_op d).measure_eq_tsum s).symm
  · exact hdisj.mono fun _ _ h =>
      Disjoint.aedisjoint (h.mono Set.inter_subset_left Set.inter_subset_left)
  · intro g
    exact (hs.const_vadd g).nullMeasurableSet.inter
      (flatTorusFundamentalDomain_isAddFundamentalDomain_op d).nullMeasurableSet

theorem flatTorusVolume_ball_eq_volume
    (d : ℕ) {c : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hr : r < 1 / 4) :
    flatTorusVolume d (Metric.ball (flatTorusMk d c) r) =
      volume (Metric.ball c r) := by
  rw [← image_ball_flatTorusMk d c r]
  exact flatTorusVolume_image_eq_volume Metric.isOpen_ball.measurableSet
    (injOn_flatTorusMk_ball d hr)

theorem flatTorusVolume_closedBall_zero_eq_volume
    (d : ℕ) {r : ℝ} (hr : r < 1 / 4) :
    flatTorusVolume d (Metric.closedBall (0 : FlatTorus d) r) =
      volume (Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin d)) r) := by
  rw [← image_closedBall_zero_flatTorusMk d (by linarith)]
  exact flatTorusVolume_image_eq_volume measurableSet_closedBall
    (injOn_flatTorusMk_closedBall d hr)

end Shepp.Section2
end SheppFlattenedModule009

section SheppFlattenedModule010
namespace Shepp.Section2

open MeasureTheory

def euclideanBallLens (d : ℕ) (r : ℝ)
    (c₁ c₂ : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  Metric.ball c₁ r ∩ Metric.ball c₂ r

def flatTorusBallLens (d : ℕ) (r : ℝ)
    (x₁ x₂ : FlatTorus d) : Set (FlatTorus d) :=
  Metric.ball x₁ r ∩ Metric.ball x₂ r

theorem flatTorusBallLens_eq_empty_of_two_mul_le
    (d : ℕ) {r : ℝ} {x₁ x₂ : FlatTorus d}
    (hsep : 2 * r ≤ dist x₁ x₂) :
    flatTorusBallLens d r x₁ x₂ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z
  rintro ⟨hz₁, hz₂⟩
  have htri : dist x₁ x₂ ≤ dist x₁ z + dist z x₂ := dist_triangle _ _ _
  have hz₁' : dist x₁ z < r := by simpa [dist_comm] using hz₁
  have hz₂' : dist z x₂ < r := hz₂
  linarith

theorem flatTorusVolumeReal_ballLens_eq_zero_of_two_mul_le
    (d : ℕ) {r : ℝ} {x₁ x₂ : FlatTorus d}
    (hsep : 2 * r ≤ dist x₁ x₂) :
    (flatTorusVolume d).real (flatTorusBallLens d r x₁ x₂) = 0 := by
  rw [flatTorusBallLens_eq_empty_of_two_mul_le d hsep]
  simp [Measure.real]

theorem image_euclideanBallLens_flatTorusMk
    (d : ℕ) {c₁ c₂ : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hr : r < 1 / 4) (hc : dist c₁ c₂ ≤ 2 * r) :
    flatTorusMk d '' euclideanBallLens d r c₁ c₂ =
      flatTorusBallLens d r (flatTorusMk d c₁) (flatTorusMk d c₂) := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    constructor
    · rw [← image_ball_flatTorusMk d c₁ r]
      exact ⟨z, hz.1, rfl⟩
    · rw [← image_ball_flatTorusMk d c₂ r]
      exact ⟨z, hz.2, rfl⟩
  · intro hq
    have hq₁ : q ∈ flatTorusMk d '' Metric.ball c₁ r := by
      rw [image_ball_flatTorusMk d c₁ r]
      exact hq.1
    have hq₂ : q ∈ flatTorusMk d '' Metric.ball c₂ r := by
      rw [image_ball_flatTorusMk d c₂ r]
      exact hq.2
    rcases hq₁ with ⟨x, hx, hxq⟩
    rcases hq₂ with ⟨y, hy, hyq⟩
    have hmk : flatTorusMk d x = flatTorusMk d y := hxq.trans hyq.symm
    have hmem : x - y ∈ integerLattice d := by
      change (x : FlatTorus d) = (y : FlatTorus d) at hmk
      exact QuotientAddGroup.eq_iff_sub_mem.mp hmk
    have htri :
        dist x y ≤ dist x c₁ + dist c₁ c₂ + dist c₂ y := by
      calc
        dist x y ≤ dist x c₁ + dist c₁ y := dist_triangle x c₁ y
        _ ≤ dist x c₁ + (dist c₁ c₂ + dist c₂ y) :=
          by linarith [dist_triangle c₁ c₂ y]
        _ = dist x c₁ + dist c₁ c₂ + dist c₂ y := by ring
    have hxlt : dist x c₁ < r := hx
    have hylt : dist c₂ y < r := by simpa [dist_comm] using hy
    have hdist : dist x y < 1 := by linarith
    have hxy : x = y :=
      eq_of_sub_mem_integerLattice_of_norm_lt_one hmem (by
        simpa only [dist_eq_norm] using hdist)
    refine ⟨x, ⟨hx, ?_⟩, hxq⟩
    simpa [hxy] using hy

theorem flatTorusVolume_ballLens_eq_volume
    (d : ℕ) {c₁ c₂ : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hr : r < 1 / 4) (hc : dist c₁ c₂ ≤ 2 * r) :
    flatTorusVolume d
        (flatTorusBallLens d r (flatTorusMk d c₁) (flatTorusMk d c₂)) =
      volume (euclideanBallLens d r c₁ c₂) := by
  rw [← image_euclideanBallLens_flatTorusMk d hr hc]
  exact flatTorusVolume_image_eq_volume
    (Metric.isOpen_ball.measurableSet.inter Metric.isOpen_ball.measurableSet)
    ((injOn_flatTorusMk_ball d hr).mono Set.inter_subset_left)

end Shepp.Section2
end SheppFlattenedModule010

section SheppFlattenedModule011
namespace Shepp.Section2

open MeasureTheory Module

abbrev CoordinateLensSpace (d : ℕ) :=
  ℝ × EuclideanSpace ℝ (Fin (d - 1))

noncomputable def coordinateLensL2EquivEuclidean
    (d : ℕ) (hd : 1 ≤ d) :
    WithLp 2 (CoordinateLensSpace d) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin d) := by
  have hdim : Module.finrank ℝ (WithLp 2 (CoordinateLensSpace d)) = d := by
    calc
      Module.finrank ℝ (WithLp 2 (CoordinateLensSpace d)) =
          Module.finrank ℝ (CoordinateLensSpace d) :=
        (WithLp.linearEquiv 2 ℝ (CoordinateLensSpace d)).finrank_eq
      _ = d := finrank_coordinateSpace d hd
  exact (stdOrthonormalBasis ℝ (WithLp 2 (CoordinateLensSpace d))).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hdim))

noncomputable def coordinateLensEquivEuclidean
    (d : ℕ) (hd : 1 ≤ d) :
    CoordinateLensSpace d ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  (WithLp.linearEquiv 2 ℝ (CoordinateLensSpace d)).symm.trans
    (coordinateLensL2EquivEuclidean d hd).toLinearEquiv

theorem coordinateLensEquivEuclidean_measurePreserving
    (d : ℕ) (hd : 1 ≤ d) :
    MeasurePreserving (coordinateLensEquivEuclidean d hd) volume volume := by
  exact (coordinateLensL2EquivEuclidean d hd).measurePreserving.comp
    (WithLp.volume_preserving_toLp ℝ (EuclideanSpace ℝ (Fin (d - 1))))

theorem coordinateLensEquivEuclidean_norm_sq
    (d : ℕ) (hd : 1 ≤ d) (p : CoordinateLensSpace d) :
    ‖coordinateLensEquivEuclidean d hd p‖ ^ 2 =
      p.1 ^ 2 + ‖p.2‖ ^ 2 := by
  change ‖coordinateLensL2EquivEuclidean d hd (WithLp.toLp 2 p)‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map, WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [Real.norm_eq_abs, sq_abs]

theorem coordinateLensEquivEuclidean_sub_center_norm_sq
    (d : ℕ) (hd : 1 ≤ d) (p : CoordinateLensSpace d) (c : ℝ) :
    ‖coordinateLensEquivEuclidean d hd p -
        coordinateLensEquivEuclidean d hd (c, 0)‖ ^ 2 =
      (p.1 - c) ^ 2 + ‖p.2‖ ^ 2 := by
  rw [← map_sub]
  have h := coordinateLensEquivEuclidean_norm_sq d hd (p - (c, 0))
  change ‖coordinateLensEquivEuclidean d hd (p - (c, 0))‖ ^ 2 =
    (p.1 - c) ^ 2 + ‖p.2 - 0‖ ^ 2 at h
  simpa only [sub_zero] using h

theorem coordinateLensEquivEuclidean_image_coordinateBall
    (d : ℕ) (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (c : ℝ) :
    coordinateLensEquivEuclidean d hd '' coordinateBall d r c =
      Metric.ball (coordinateLensEquivEuclidean d hd (c, 0)) r := by
  let e := coordinateLensEquivEuclidean d hd
  have hmem : ∀ p : CoordinateLensSpace d,
      e p ∈ Metric.ball (e (c, 0)) r ↔ p ∈ coordinateBall d r c := by
    intro p
    rw [Metric.mem_ball, dist_eq_norm]
    rw [← (sq_lt_sq₀ (norm_nonneg (e p - e (c, 0))) hr.le)]
    rw [coordinateLensEquivEuclidean_sub_center_norm_sq]
    rfl
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (hmem p).2 hp
  · intro hx
    refine ⟨e.symm x, (hmem (e.symm x)).1 ?_, e.apply_symm_apply x⟩
    simpa using hx

theorem coordinateLensEquivEuclidean_image_coordinateLens
    (d : ℕ) (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    coordinateLensEquivEuclidean d hd '' coordinateLens d r t =
      euclideanBallLens d r
        (coordinateLensEquivEuclidean d hd (0, 0))
        (coordinateLensEquivEuclidean d hd (t, 0)) := by
  rw [coordinateLens, euclideanBallLens,
    Set.image_inter (coordinateLensEquivEuclidean d hd).injective,
    coordinateLensEquivEuclidean_image_coordinateBall d hd hr,
    coordinateLensEquivEuclidean_image_coordinateBall d hd hr]

theorem coordinateBall_isOpen (d : ℕ) (r c : ℝ) :
    IsOpen (coordinateBall d r c) := by
  exact isOpen_lt
    (by fun_prop : Continuous fun p : CoordinateLensSpace d =>
      (p.1 - c) ^ 2 + ‖p.2‖ ^ 2)
    continuous_const

theorem coordinateLens_isOpen (d : ℕ) (r t : ℝ) :
    IsOpen (coordinateLens d r t) :=
  (coordinateBall_isOpen d r 0).inter (coordinateBall_isOpen d r t)

theorem volume_image_coordinateLensEquivEuclidean
    (d : ℕ) (hd : 1 ≤ d) (r t : ℝ) :
    volume (coordinateLensEquivEuclidean d hd '' coordinateLens d r t) =
      volume (coordinateLens d r t) := by
  let e := coordinateLensEquivEuclidean d hd
  have hs : MeasurableSet (e '' coordinateLens d r t) :=
    (e.toContinuousLinearEquiv.toHomeomorph.isOpenMap _
      (coordinateLens_isOpen d r t)).measurableSet
  calc
    volume (e '' coordinateLens d r t) =
        Measure.map e volume (e '' coordinateLens d r t) := by
      rw [(coordinateLensEquivEuclidean_measurePreserving d hd).map_eq]
    _ = volume (e ⁻¹' (e '' coordinateLens d r t)) :=
      Measure.map_apply
        (coordinateLensEquivEuclidean_measurePreserving d hd).measurable hs
    _ = volume (coordinateLens d r t) := by
      rw [Set.preimage_image_eq _ e.injective]

theorem volumeReal_euclideanBallLens_eq_coordinateLens
    (d : ℕ) (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    volume.real
        (euclideanBallLens d r
          (coordinateLensEquivEuclidean d hd (0, 0))
          (coordinateLensEquivEuclidean d hd (t, 0))) =
      volume.real (coordinateLens d r t) := by
  change (volume
      (euclideanBallLens d r
        (coordinateLensEquivEuclidean d hd (0, 0))
        (coordinateLensEquivEuclidean d hd (t, 0)))).toReal =
    (volume (coordinateLens d r t)).toReal
  rw [← coordinateLensEquivEuclidean_image_coordinateLens d hd hr t]
  rw [volume_image_coordinateLensEquivEuclidean d hd r t]

theorem coordinateLensCenters_dist
    (d : ℕ) (hd : 1 ≤ d) (t : ℝ) :
    dist (coordinateLensEquivEuclidean d hd (0, 0))
      (coordinateLensEquivEuclidean d hd (t, 0)) = |t| := by
  rw [dist_eq_norm, ← map_sub]
  have hsub :
      ((0, 0) : CoordinateLensSpace d) - (t, 0) =
        (-t, (0 : EuclideanSpace ℝ (Fin (d - 1)))) := by
    ext <;> simp
  rw [hsub]
  have hsq := coordinateLensEquivEuclidean_norm_sq d hd
    (-t, (0 : EuclideanSpace ℝ (Fin (d - 1))))
  have habs : |t| ^ 2 = t ^ 2 := sq_abs t
  norm_num at hsq
  nlinarith [norm_nonneg
    (coordinateLensEquivEuclidean d hd (-t, 0)), abs_nonneg t]

theorem volumeReal_euclideanBallLens_eq_profile
    (d : ℕ) (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r)
    (c₁ c₂ : EuclideanSpace ℝ (Fin d))
    (hsep : dist c₁ c₂ ≤ 2 * r) :
    volume.real (euclideanBallLens d r c₁ c₂) =
      euclideanUnitBallVolume d * r ^ d *
        lensProfile d (dist c₁ c₂ / r) := by
  let t : ℝ := dist c₁ c₂
  let e := coordinateLensEquivEuclidean d (by omega : 1 ≤ d)
  let s : EuclideanSpace ℝ (Fin d) := e (t, 0)
  let v : EuclideanSpace ℝ (Fin d) := c₂ - c₁
  have he0 : e ((0, 0) : CoordinateLensSpace d) = 0 := by
    change e 0 = 0
    exact map_zero e
  have ht0 : 0 ≤ t := dist_nonneg
  have ht : t ∈ Set.Icc (0 : ℝ) (2 * r) := ⟨ht0, hsep⟩
  have hs : ‖s‖ = t := by
    have h := coordinateLensCenters_dist d (by omega : 1 ≤ d) t
    rw [he0, dist_zero_left, abs_of_nonneg ht0] at h
    simpa [e, s] using h
  have hv : ‖v‖ = t := by
    change ‖c₂ - c₁‖ = dist c₁ c₂
    rw [← dist_eq_norm, dist_comm]
  have hsv : ‖s‖ = ‖v‖ := hs.trans hv.symm
  let R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin d) :=
    Submodule.reflection (ℝ ∙ (s - v))ᗮ
  have hRs : R s = v := Submodule.reflection_sub hsv
  have hdist₁ (z : EuclideanSpace ℝ (Fin d)) :
      dist (c₁ + R z) c₁ = dist z 0 := by
    calc
      dist (c₁ + R z) c₁ = ‖R z‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      _ = ‖z‖ := R.norm_map z
      _ = dist z 0 := by simp [dist_eq_norm]
  have hdist₂ (z : EuclideanSpace ℝ (Fin d)) :
      dist (c₁ + R z) c₂ = dist z s := by
    calc
      dist (c₁ + R z) c₂ = ‖R z - v‖ := by
        rw [dist_eq_norm]
        congr 1
        dsimp [v]
        abel
      _ = ‖R z - R s‖ := by rw [hRs]
      _ = ‖R (z - s)‖ := by rw [map_sub]
      _ = ‖z - s‖ := R.norm_map (z - s)
      _ = dist z s := by rw [dist_eq_norm]
  have hpre :
      (fun z : EuclideanSpace ℝ (Fin d) => c₁ + R z) ⁻¹'
          euclideanBallLens d r c₁ c₂ =
        euclideanBallLens d r 0 s := by
    ext z
    simp only [Set.mem_preimage, euclideanBallLens, Set.mem_inter_iff,
      Metric.mem_ball]
    rw [hdist₁ z, hdist₂ z]
  have hmp :
      MeasurePreserving
        (fun z : EuclideanSpace ℝ (Fin d) => c₁ + R z) volume volume :=
    (MeasureTheory.measurePreserving_add_left volume c₁).comp R.measurePreserving
  have hvol :
      volume
          ((fun z : EuclideanSpace ℝ (Fin d) => c₁ + R z) ⁻¹'
            euclideanBallLens d r c₁ c₂) =
        volume (euclideanBallLens d r c₁ c₂) :=
    hmp.measure_preimage
      (Metric.isOpen_ball.measurableSet.inter
        Metric.isOpen_ball.measurableSet).nullMeasurableSet
  change (volume (euclideanBallLens d r c₁ c₂)).toReal = _
  rw [← hvol, hpre]
  change volume.real (euclideanBallLens d r 0 s) = _
  rw [show (0 : EuclideanSpace ℝ (Fin d)) = e (0, 0) from he0.symm,
    show s = e (t, 0) by rfl,
    volumeReal_euclideanBallLens_eq_coordinateLens d (by omega : 1 ≤ d) hr,
    volumeReal_coordinateLens_eq_profile d hd hr ht]

theorem flatTorusVolumeReal_ballLens_eq_profile
    (d : ℕ) (hd : 2 ≤ d) {r t : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 4)
    (ht : t ∈ Set.Icc (0 : ℝ) (2 * r)) :
    (flatTorusVolume d).real
        (flatTorusBallLens d r
          (flatTorusMk d (coordinateLensEquivEuclidean d (by omega) (0, 0)))
          (flatTorusMk d (coordinateLensEquivEuclidean d (by omega) (t, 0)))) =
      euclideanUnitBallVolume d * r ^ d * lensProfile d (t / r) := by
  have hdist :
      dist (coordinateLensEquivEuclidean d (by omega) (0, 0))
        (coordinateLensEquivEuclidean d (by omega) (t, 0)) = t := by
    rw [coordinateLensCenters_dist, abs_of_nonneg ht.1]
  have hc :
      dist (coordinateLensEquivEuclidean d (by omega) (0, 0))
        (coordinateLensEquivEuclidean d (by omega) (t, 0)) ≤ 2 * r := by
    rw [hdist]
    exact ht.2
  rw [Measure.real, flatTorusVolume_ballLens_eq_volume d hrsmall hc]
  change volume.real
      (euclideanBallLens d r
        (coordinateLensEquivEuclidean d (by omega) (0, 0))
        (coordinateLensEquivEuclidean d (by omega) (t, 0))) = _
  rw [volumeReal_euclideanBallLens_eq_coordinateLens d (by omega) hr]
  exact volumeReal_coordinateLens_eq_profile d hd hr ht

theorem flatTorusVolumeReal_ballLens_eq_profile_of_lifts
    (d : ℕ) (hd : 2 ≤ d) {r : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 4)
    (c₁ c₂ : EuclideanSpace ℝ (Fin d))
    (hsep : dist c₁ c₂ ≤ 2 * r) :
    (flatTorusVolume d).real
        (flatTorusBallLens d r (flatTorusMk d c₁) (flatTorusMk d c₂)) =
      euclideanUnitBallVolume d * r ^ d *
        lensProfile d (dist c₁ c₂ / r) := by
  rw [Measure.real, flatTorusVolume_ballLens_eq_volume d hrsmall hsep]
  exact volumeReal_euclideanBallLens_eq_profile d hd hr c₁ c₂ hsep

theorem exists_compatible_flatTorus_lifts
    (d : ℕ) (x₁ x₂ : FlatTorus d)
    (hhalf : dist x₁ x₂ < 1 / 2) :
    ∃ c₁ c₂ : EuclideanSpace ℝ (Fin d),
      flatTorusMk d c₁ = x₁ ∧
      flatTorusMk d c₂ = x₂ ∧
      dist c₁ c₂ = dist x₁ x₂ := by
  rcases QuotientAddGroup.mk'_surjective (integerLattice d) x₁ with ⟨c₁, hc₁⟩
  change flatTorusMk d c₁ = x₁ at hc₁
  have hq : ‖x₂ - x₁‖ < 1 / 2 := by
    simpa only [← dist_eq_norm, dist_comm] using hhalf
  rcases QuotientAddGroup.norm_lt_iff.mp hq with ⟨z, hz, hznorm⟩
  change flatTorusMk d z = x₂ - x₁ at hz
  let c₂ : EuclideanSpace ℝ (Fin d) := c₁ + z
  have hc₂ : flatTorusMk d c₂ = x₂ := by
    dsimp [c₂]
    change flatTorusMk d c₁ + flatTorusMk d z = x₂
    rw [hc₁, hz]
    abel
  have hdistLift : dist c₁ c₂ < 1 / 2 := by
    rw [dist_eq_norm]
    have hsub : c₁ - c₂ = -z := by
      dsimp [c₂]
      abel
    rw [hsub, norm_neg]
    exact hznorm
  have hlocal := dist_flatTorusMk_eq_of_dist_lt_half hdistLift
  rw [hc₁, hc₂] at hlocal
  exact ⟨c₁, c₂, hc₁, hc₂, hlocal.symm⟩

theorem flatTorusVolumeReal_ballLens_eq_profile_of_dist_le
    (d : ℕ) (hd : 2 ≤ d) {r : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 4)
    (x₁ x₂ : FlatTorus d) (hsep : dist x₁ x₂ ≤ 2 * r) :
    (flatTorusVolume d).real (flatTorusBallLens d r x₁ x₂) =
      euclideanUnitBallVolume d * r ^ d *
        lensProfile d (dist x₁ x₂ / r) := by
  have hhalf : dist x₁ x₂ < 1 / 2 := by
    linarith
  rcases exists_compatible_flatTorus_lifts d x₁ x₂ hhalf with
    ⟨c₁, c₂, hc₁, hc₂, hdist⟩
  calc
    (flatTorusVolume d).real (flatTorusBallLens d r x₁ x₂) =
        (flatTorusVolume d).real
          (flatTorusBallLens d r (flatTorusMk d c₁) (flatTorusMk d c₂)) := by
      rw [hc₁, hc₂]
    _ = euclideanUnitBallVolume d * r ^ d *
          lensProfile d (dist c₁ c₂ / r) :=
      flatTorusVolumeReal_ballLens_eq_profile_of_lifts
        d hd hr hrsmall c₁ c₂ (by rw [hdist]; exact hsep)
    _ = euclideanUnitBallVolume d * r ^ d *
          lensProfile d (dist x₁ x₂ / r) := by rw [hdist]

end Shepp.Section2
end SheppFlattenedModule011

section SheppFlattenedModule012
namespace Shepp.Section2

open Filter
open scoped Topology

noncomputable def flatTorusOverlapTerm
    (d : ℕ) (r : ℕ → ℝ) (n : ℕ) (z : FlatTorus d) : ℝ :=
  (flatTorusVolume d).real
    (flatTorusBallLens d (r n) 0 z)

noncomputable def flatTorusOverlapSum
    (d : ℕ) (r : ℕ → ℝ) (z : FlatTorus d) : ℝ :=
  ∑' n, flatTorusOverlapTerm d r n z

theorem flatTorusOverlapTerm_eq_euclideanOverlapTerm_dist
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (n : ℕ) (z : FlatTorus d) :
    flatTorusOverlapTerm d r n z =
      euclideanOverlapTerm d r n (dist 0 z) := by
  by_cases hnear : dist (0 : FlatTorus d) z ≤ 2 * r n
  · calc
      flatTorusOverlapTerm d r n z =
          euclideanUnitBallVolume d * (r n) ^ d *
            lensProfile d (dist 0 z / r n) := by
        exact flatTorusVolumeReal_ballLens_eq_profile_of_dist_le
          d hd (hr n) (hrsmall n) 0 z hnear
      _ = euclideanOverlapTerm d r n (dist 0 z) := by
        exact (volumeReal_coordinateLens_eq_profile d hd (hr n)
          ⟨dist_nonneg, hnear⟩).symm
  · have hfar : 2 * r n ≤ dist (0 : FlatTorus d) z :=
      (lt_of_not_ge hnear).le
    calc
      flatTorusOverlapTerm d r n z = 0 := by
        exact flatTorusVolumeReal_ballLens_eq_zero_of_two_mul_le d hfar
      _ = euclideanOverlapTerm d r n (dist 0 z) := by
        exact (volumeReal_coordinateLens_eq_zero_of_two_mul_le
          d (hr n).le hfar).symm

theorem flatTorusOverlapSum_eq_euclideanOverlapSum_dist
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (z : FlatTorus d) :
    flatTorusOverlapSum d r z =
      euclideanOverlapSum d r (dist 0 z) := by
  apply tsum_congr
  intro n
  exact flatTorusOverlapTerm_eq_euclideanOverlapTerm_dist
    d hd hr hrsmall n z

theorem coneSum_le_flatTorusOverlapSum_le
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (𝓝 0))
    {z : FlatTorus d} (hz : z ≠ 0) :
    coneSum r (radiusVolume d r)
        ((euclideanUnitBallVolume (d - 1) /
          euclideanUnitBallVolume d) * dist 0 z) ≤
      flatTorusOverlapSum d r z ∧
      flatTorusOverlapSum d r z ≤
        coneSum r (radiusVolume d r) (dist 0 z / 2) := by
  have hdist : 0 < dist (0 : FlatTorus d) z :=
    dist_pos.mpr (Ne.symm hz)
  rw [flatTorusOverlapSum_eq_euclideanOverlapSum_dist d hd hr hrsmall]
  exact coneSum_le_euclideanOverlapSum_le d hd hr hrlim hdist

theorem exp_coneSum_le_exp_flatTorusOverlapSum_le
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (𝓝 0))
    {z : FlatTorus d} (hz : z ≠ 0) :
    Real.exp
        (coneSum r (radiusVolume d r)
          ((euclideanUnitBallVolume (d - 1) /
            euclideanUnitBallVolume d) * dist 0 z)) ≤
      Real.exp (flatTorusOverlapSum d r z) ∧
      Real.exp (flatTorusOverlapSum d r z) ≤
        Real.exp (coneSum r (radiusVolume d r) (dist 0 z / 2)) := by
  have h := coneSum_le_flatTorusOverlapSum_le
    d hd hr hrsmall hrlim hz
  exact ⟨Real.exp_le_exp.mpr h.1, Real.exp_le_exp.mpr h.2⟩

end Shepp.Section2
end SheppFlattenedModule012

section SheppFlattenedModule013
namespace Shepp.Section2

open MeasureTheory
open scoped ENNReal

noncomputable def flatTorusRadialMeasure (d : ℕ) : Measure ℝ :=
  Measure.map (fun z : FlatTorus d => dist 0 z) (flatTorusVolume d)

theorem measurable_dist_zero_flatTorus (d : ℕ) :
    Measurable (fun z : FlatTorus d => dist 0 z) := by
  fun_prop

theorem flatTorusRadialMeasure_Iio
    (d : ℕ) (hd : 0 < d) {r : ℝ}
    (hr : 0 ≤ r) (hrsmall : r < 1 / 4) :
    flatTorusRadialMeasure d (Set.Iio r) =
      ENNReal.ofReal (euclideanUnitBallVolume d * r ^ d) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [flatTorusRadialMeasure, Measure.map_apply
    (measurable_dist_zero_flatTorus d) measurableSet_Iio]
  have hpre :
      (fun z : FlatTorus d => dist 0 z) ⁻¹' Set.Iio r =
        Metric.ball 0 r := by
    ext z
    simp [Metric.mem_ball, dist_comm]
  rw [hpre]
  have hball := flatTorusVolume_ball_eq_volume
    (d := d) (c := (0 : EuclideanSpace ℝ (Fin d))) hrsmall
  simp only [map_zero] at hball
  rw [hball, EuclideanSpace.volume_ball, Fintype.card_fin]
  change (ENNReal.ofReal r) ^ d *
      ENNReal.ofReal (euclideanUnitBallVolume d) =
    ENNReal.ofReal (euclideanUnitBallVolume d * r ^ d)
  rw [← ENNReal.ofReal_pow hr d, mul_comm,
    ← ENNReal.ofReal_mul (euclideanUnitBallVolume_pos d).le]

theorem flatTorusRadialMeasure_Iic
    (d : ℕ) (hd : 0 < d) {r : ℝ}
    (hr : 0 ≤ r) (hrsmall : r < 1 / 4) :
    flatTorusRadialMeasure d (Set.Iic r) =
      ENNReal.ofReal (euclideanUnitBallVolume d * r ^ d) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [flatTorusRadialMeasure, Measure.map_apply
    (measurable_dist_zero_flatTorus d) measurableSet_Iic]
  have hpre :
      (fun z : FlatTorus d => dist 0 z) ⁻¹' Set.Iic r =
        Metric.closedBall 0 r := by
    ext z
    simp [Metric.mem_closedBall, dist_comm]
  rw [hpre, flatTorusVolume_closedBall_zero_eq_volume d hrsmall,
    EuclideanSpace.volume_closedBall, Fintype.card_fin]
  change (ENNReal.ofReal r) ^ d *
      ENNReal.ofReal (euclideanUnitBallVolume d) =
    ENNReal.ofReal (euclideanUnitBallVolume d * r ^ d)
  rw [← ENNReal.ofReal_pow hr d, mul_comm,
    ← ENNReal.ofReal_mul (euclideanUnitBallVolume_pos d).le]

noncomputable def euclideanRadialMeasure (d : ℕ) : Measure ℝ :=
  ENNReal.ofReal ((d : ℝ) * euclideanUnitBallVolume d) •
    Measure.map Subtype.val (Measure.volumeIoiPow (d - 1))

private theorem volumeIoiPow_singleton (n : ℕ) (x : Set.Ioi (0 : ℝ)) :
    Measure.volumeIoiPow n ({x} : Set (Set.Ioi (0 : ℝ))) = 0 := by
  apply withDensity_absolutelyContinuous
  rw [comap_subtype_coe_apply measurableSet_Ioi volume]
  simp

private theorem volumeIoiPow_apply_Iic
    (n : ℕ) (x : Set.Ioi (0 : ℝ)) :
    Measure.volumeIoiPow n (Set.Iic x) =
      ENNReal.ofReal (x.1 ^ (n + 1) / (n + 1)) := by
  have hset : Set.Iic x = Set.Iio x ∪ {x} := by
    ext y
    simp [le_iff_lt_or_eq]
  have hdisj : Disjoint (Set.Iio x) ({x} : Set (Set.Ioi (0 : ℝ))) := by
    exact Set.disjoint_singleton_right.mpr (by simp)
  rw [hset, measure_union hdisj (measurableSet_singleton x),
    volumeIoiPow_singleton, add_zero,
    Measure.volumeIoiPow_apply_Iio]

theorem euclideanRadialMeasure_Iic
    (d : ℕ) (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    euclideanRadialMeasure d (Set.Iic r) =
      ENNReal.ofReal (euclideanUnitBallVolume d * r ^ d) := by
  rw [euclideanRadialMeasure, Measure.smul_apply,
    Measure.map_apply measurable_subtype_coe measurableSet_Iic]
  have hpre :
      Subtype.val ⁻¹' Set.Iic r =
        Set.Iic (⟨r, Set.mem_Ioi.mpr hr⟩ : Set.Ioi (0 : ℝ)) := by
    ext x
    rfl
  rw [hpre, volumeIoiPow_apply_Iic]
  simp only [smul_eq_mul]
  have hcast : ((d - 1 : ℕ) : ℝ) + 1 = d := by
    exact_mod_cast Nat.sub_add_cancel hd
  rw [hcast]
  rw [← ENNReal.ofReal_mul
    (mul_nonneg (Nat.cast_nonneg d) (euclideanUnitBallVolume_pos d).le)]
  congr 1
  rw [Nat.sub_add_cancel hd]
  field_simp

theorem euclideanRadialMeasure_Iic_nonpos
    (d : ℕ) {r : ℝ} (hr : r ≤ 0) :
    euclideanRadialMeasure d (Set.Iic r) = 0 := by
  rw [euclideanRadialMeasure, Measure.smul_apply,
    Measure.map_apply measurable_subtype_coe measurableSet_Iic]
  have hpre :
      (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) ⁻¹' Set.Iic r = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false,
      iff_false]
    exact not_le_of_gt (hr.trans_lt x.property)
  rw [hpre, measure_empty]
  simp

theorem flatTorusRadialMeasure_Iic_nonpos
    (d : ℕ) (hd : 0 < d) {r : ℝ} (hr : r ≤ 0) :
    flatTorusRadialMeasure d (Set.Iic r) = 0 := by
  rcases hr.lt_or_eq with hrneg | rfl
  · rw [flatTorusRadialMeasure, Measure.map_apply
      (measurable_dist_zero_flatTorus d) measurableSet_Iic]
    have hpre :
        (fun z : FlatTorus d => dist 0 z) ⁻¹' Set.Iic r = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false,
        iff_false]
      exact not_le_of_gt (hrneg.trans_le dist_nonneg)
    rw [hpre, measure_empty]
  · rw [flatTorusRadialMeasure_Iic d hd le_rfl (by norm_num)]
    simp [hd.ne']

noncomputable instance flatTorusRadialMeasureIsFinite (d : ℕ) :
    IsFiniteMeasure (flatTorusRadialMeasure d) := by
  rw [flatTorusRadialMeasure]
  infer_instance

theorem restrict_flatTorusRadialMeasure_eq_euclideanRadialMeasure
    (d : ℕ) (hd : 0 < d) {R : ℝ} (hRsmall : R < 1 / 4) :
    (flatTorusRadialMeasure d).restrict (Set.Iic R) =
      (euclideanRadialMeasure d).restrict (Set.Iic R) := by
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.restrict_apply measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  have hinter : Set.Iic a ∩ Set.Iic R = Set.Iic (min a R) := by
    ext x
    simp
  rw [hinter]
  by_cases hmin : 0 < min a R
  · rw [flatTorusRadialMeasure_Iic d hd hmin.le
      (lt_of_le_of_lt (min_le_right _ _) hRsmall),
      euclideanRadialMeasure_Iic d hd hmin]
  · have hmin' : min a R ≤ 0 := le_of_not_gt hmin
    rw [flatTorusRadialMeasure_Iic_nonpos d hd hmin',
      euclideanRadialMeasure_Iic_nonpos d hmin']

theorem setLIntegral_euclideanRadialMeasure_eq_polar
    (d : ℕ) (R : ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Set.Iic R, f t ∂(euclideanRadialMeasure d)) =
      ENNReal.ofReal ((d : ℝ) * euclideanUnitBallVolume d) *
        ∫⁻ t in Set.Ioc 0 R,
          ENNReal.ofReal (t ^ (d - 1)) * f t ∂volume := by
  let c : ℝ≥0∞ :=
    ENNReal.ofReal ((d : ℝ) * euclideanUnitBallVolume d)
  let p : Set (Set.Ioi (0 : ℝ)) :=
    Subtype.val ⁻¹' Set.Iic R
  have hpimage : Subtype.val '' p = Set.Ioc 0 R := by
    ext t
    simp [p]
  calc
    (∫⁻ t in Set.Iic R, f t ∂(euclideanRadialMeasure d)) =
        c * ∫⁻ t in Set.Iic R,
          f t ∂Measure.map Subtype.val (Measure.volumeIoiPow (d - 1)) := by
      rw [euclideanRadialMeasure, setLIntegral_smul_measure]
      rfl
    _ = c * ∫⁻ x in p, f x.1 ∂Measure.volumeIoiPow (d - 1) := by
      congr 1
      rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioi).restrict_map,
        (MeasurableEmbedding.subtype_coe measurableSet_Ioi).lintegral_map]
    _ = c * ∫⁻ x in p,
        ENNReal.ofReal (x.1 ^ (d - 1)) * f x.1
          ∂Measure.comap Subtype.val volume := by
      congr 1
      rw [Measure.volumeIoiPow,
        setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable]
      · rfl
      · fun_prop
      · exact measurableSet_Iic.preimage measurable_subtype_coe
      · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    _ = c * ∫⁻ t in Set.Ioc 0 R,
        ENNReal.ofReal (t ^ (d - 1)) * f t ∂volume := by
      congr 1
      change (∫⁻ x in p,
        (fun t : ℝ => ENNReal.ofReal (t ^ (d - 1)) * f t) x
          ∂Measure.comap Subtype.val volume) = _
      have hsub := setLIntegral_subtype (μ := volume) measurableSet_Ioi p
        (fun t : ℝ => ENNReal.ofReal (t ^ (d - 1)) * f t)
      rw [hpimage] at hsub
      exact hsub

theorem setLIntegral_comp_dist_flatTorus_closedBall
    (d : ℕ) (R : ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : FlatTorus d in Metric.closedBall 0 R,
      f (dist 0 z) ∂(flatTorusVolume d)) =
        ∫⁻ t in Set.Iic R, f t ∂(flatTorusRadialMeasure d) := by
  have hpre :
      (fun z : FlatTorus d => dist 0 z) ⁻¹' Set.Iic R =
        Metric.closedBall 0 R := by
    ext z
    simp [Metric.mem_closedBall, dist_comm]
  rw [flatTorusRadialMeasure,
    setLIntegral_map measurableSet_Iic hf (measurable_dist_zero_flatTorus d),
    hpre]

theorem setLIntegral_comp_dist_flatTorus_closedBall_eq_polar
    (d : ℕ) (hd : 0 < d) (R : ℝ) (hRsmall : R < 1 / 4)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : FlatTorus d in Metric.closedBall 0 R,
      f (dist 0 z) ∂(flatTorusVolume d)) =
      ENNReal.ofReal ((d : ℝ) * euclideanUnitBallVolume d) *
        ∫⁻ t in Set.Ioc 0 R,
          ENNReal.ofReal (t ^ (d - 1)) * f t ∂volume := by
  calc
    (∫⁻ z : FlatTorus d in Metric.closedBall 0 R,
      f (dist 0 z) ∂(flatTorusVolume d)) =
        ∫⁻ t in Set.Iic R, f t ∂(flatTorusRadialMeasure d) :=
      setLIntegral_comp_dist_flatTorus_closedBall d R f hf
    _ = ∫⁻ t in Set.Iic R, f t ∂(euclideanRadialMeasure d) := by
      rw [restrict_flatTorusRadialMeasure_eq_euclideanRadialMeasure
        d hd hRsmall]
    _ = _ := setLIntegral_euclideanRadialMeasure_eq_polar d R f

theorem lintegral_comp_dist_flatTorus
    (d : ℕ) (f : ℝ → ℝ≥0∞)
    (hf : AEMeasurable f (flatTorusRadialMeasure d)) :
    (∫⁻ z : FlatTorus d, f (dist 0 z) ∂(flatTorusVolume d)) =
      ∫⁻ t : ℝ, f t ∂(flatTorusRadialMeasure d) := by
  exact (lintegral_map' hf
    (measurable_dist_zero_flatTorus d).aemeasurable).symm

end Shepp.Section2
end SheppFlattenedModule013

section SheppFlattenedModule014
namespace Shepp.Section2

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable def coneEnergy
    (r v : ℕ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (coneTerm r v n t)

noncomputable def coneEnergyExp
    (r v : ℕ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  EReal.exp (coneEnergy r v t : EReal)

noncomputable def flatTorusOverlapEnergy
    (d : ℕ) (r : ℕ → ℝ) (z : FlatTorus d) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (flatTorusOverlapTerm d r n z)

noncomputable def flatTorusOverlapEnergyExp
    (d : ℕ) (r : ℕ → ℝ) (z : FlatTorus d) : ℝ≥0∞ :=
  EReal.exp (flatTorusOverlapEnergy d r z : EReal)

noncomputable def radialOverlapTerm
    (d : ℕ) (r : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  if t ≤ 2 * r n then
    euclideanUnitBallVolume d * (r n) ^ d * lensProfile d (t / r n)
  else 0

theorem flatTorusOverlapTerm_eq_radialOverlapTerm
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (n : ℕ) (z : FlatTorus d) :
    flatTorusOverlapTerm d r n z =
      radialOverlapTerm d r n (dist 0 z) := by
  rw [radialOverlapTerm]
  split_ifs with hnear
  · exact flatTorusVolumeReal_ballLens_eq_profile_of_dist_le
      d hd (hr n) (hrsmall n) 0 z hnear
  · have hfar : 2 * r n ≤ dist (0 : FlatTorus d) z :=
      (lt_of_not_ge hnear).le
    exact flatTorusVolumeReal_ballLens_eq_zero_of_two_mul_le d hfar

theorem measurable_radialOverlapTerm
    (d : ℕ) (r : ℕ → ℝ) (n : ℕ) :
    Measurable (radialOverlapTerm d r n) := by
  unfold radialOverlapTerm
  apply Measurable.ite measurableSet_Iic
  · exact measurable_const.mul
      ((lensProfile_continuous d).measurable.comp
        (measurable_id.div_const (r n)))
  · exact measurable_const

theorem measurable_coneEnergy (r v : ℕ → ℝ) :
    Measurable (coneEnergy r v) := by
  apply Measurable.tsum
  intro n
  unfold coneTerm coneProfile
  fun_prop

theorem measurable_coneEnergyExp (r v : ℕ → ℝ) :
    Measurable (coneEnergyExp r v) := by
  exact EReal.measurable_exp.comp
    (measurable_coe_ennreal_ereal.comp (measurable_coneEnergy r v))

theorem measurable_flatTorusOverlapEnergy
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4) :
    Measurable (flatTorusOverlapEnergy d r) := by
  apply Measurable.tsum
  intro n
  have heq : flatTorusOverlapTerm d r n =
      fun z => radialOverlapTerm d r n (dist 0 z) := by
    funext z
    exact flatTorusOverlapTerm_eq_radialOverlapTerm
      d hd hr hrsmall n z
  apply ENNReal.measurable_ofReal.comp
  rw [heq]
  exact (measurable_radialOverlapTerm d r n).comp
    (measurable_dist_zero_flatTorus d)

theorem measurable_flatTorusOverlapEnergyExp
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4) :
    Measurable (flatTorusOverlapEnergyExp d r) := by
  exact EReal.measurable_exp.comp
    (measurable_coe_ennreal_ereal.comp
      (measurable_flatTorusOverlapEnergy d hd hr hrsmall))

theorem coneEnergy_le_flatTorusOverlapEnergy_le
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (z : FlatTorus d) :
    coneEnergy r (radiusVolume d r)
        ((euclideanUnitBallVolume (d - 1) /
          euclideanUnitBallVolume d) * dist 0 z) ≤
      flatTorusOverlapEnergy d r z ∧
      flatTorusOverlapEnergy d r z ≤
        coneEnergy r (radiusVolume d r) (dist 0 z / 2) := by
  constructor
  · apply ENNReal.tsum_le_tsum
    intro n
    apply ENNReal.ofReal_le_ofReal
    rw [flatTorusOverlapTerm_eq_euclideanOverlapTerm_dist
      d hd hr hrsmall n z]
    exact coneTerm_le_euclideanOverlapTerm d hd hr dist_nonneg n
  · apply ENNReal.tsum_le_tsum
    intro n
    apply ENNReal.ofReal_le_ofReal
    rw [flatTorusOverlapTerm_eq_euclideanOverlapTerm_dist
      d hd hr hrsmall n z]
    exact euclideanOverlapTerm_le_coneTerm d hd hr dist_nonneg n

theorem coneEnergyExp_le_flatTorusOverlapEnergyExp_le
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (z : FlatTorus d) :
    coneEnergyExp r (radiusVolume d r)
        ((euclideanUnitBallVolume (d - 1) /
          euclideanUnitBallVolume d) * dist 0 z) ≤
      flatTorusOverlapEnergyExp d r z ∧
      flatTorusOverlapEnergyExp d r z ≤
        coneEnergyExp r (radiusVolume d r) (dist 0 z / 2) := by
  have h := coneEnergy_le_flatTorusOverlapEnergy_le
    d hd hr hrsmall z
  exact ⟨EReal.exp_monotone (mod_cast h.1),
    EReal.exp_monotone (mod_cast h.2)⟩

theorem coneEnergy_eq_ofReal_coneSum
    {r v : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hrlim : Tendsto r atTop (𝓝 0)) {t : ℝ} (ht : 0 < t) :
    coneEnergy r v t = ENNReal.ofReal (coneSum r v t) := by
  rw [coneEnergy, coneSum]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (hv n) (by simp [coneProfile]))
    (summable_coneTerm_of_tendsto_zero hr hrlim ht)).symm

theorem coneSum_nonneg
    {r v : ℕ → ℝ} (hv : ∀ n, 0 ≤ v n) (t : ℝ) :
    0 ≤ coneSum r v t := by
  unfold coneSum
  exact tsum_nonneg fun n =>
    mul_nonneg (hv n) (by simp [coneProfile])

theorem coneEnergyExp_eq_ofReal_exp_coneSum
    {r v : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hrlim : Tendsto r atTop (𝓝 0)) {t : ℝ} (ht : 0 < t) :
    coneEnergyExp r v t =
      ENNReal.ofReal (Real.exp (coneSum r v t)) := by
  rw [coneEnergyExp,
    coneEnergy_eq_ofReal_coneSum hr hv hrlim ht,
    EReal.coe_ennreal_ofReal,
    max_eq_left (coneSum_nonneg hv t), EReal.exp_coe]

theorem flatTorusOverlapEnergy_eq_ofReal_flatTorusOverlapSum
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (𝓝 0)) {z : FlatTorus d} (hz : z ≠ 0) :
    flatTorusOverlapEnergy d r z =
      ENNReal.ofReal (flatTorusOverlapSum d r z) := by
  have hdist : 0 < dist (0 : FlatTorus d) z :=
    dist_pos.mpr (Ne.symm hz)
  have hsummable : Summable (fun n => flatTorusOverlapTerm d r n z) := by
    have heq : (fun n => flatTorusOverlapTerm d r n z) =
        fun n => euclideanOverlapTerm d r n (dist 0 z) := by
      funext n
      exact flatTorusOverlapTerm_eq_euclideanOverlapTerm_dist
        d hd hr hrsmall n z
    rw [heq]
    exact summable_euclideanOverlapTerm d hr hrlim hdist
  rw [flatTorusOverlapEnergy, flatTorusOverlapSum]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun n => by unfold flatTorusOverlapTerm; positivity)
    hsummable).symm

theorem flatTorusOverlapSum_nonneg
    (d : ℕ) (r : ℕ → ℝ) (z : FlatTorus d) :
    0 ≤ flatTorusOverlapSum d r z := by
  unfold flatTorusOverlapSum
  exact tsum_nonneg fun n => by
    unfold flatTorusOverlapTerm
    positivity

theorem flatTorusOverlapEnergyExp_eq_ofReal_exp_flatTorusOverlapSum
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (𝓝 0)) {z : FlatTorus d} (hz : z ≠ 0) :
    flatTorusOverlapEnergyExp d r z =
      ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z)) := by
  rw [flatTorusOverlapEnergyExp,
    flatTorusOverlapEnergy_eq_ofReal_flatTorusOverlapSum
      d hd hr hrsmall hrlim hz,
    EReal.coe_ennreal_ofReal,
    max_eq_left (flatTorusOverlapSum_nonneg d r z), EReal.exp_coe]

end Shepp.Section2
end SheppFlattenedModule014

section SheppFlattenedModule015
namespace Shepp.Section2

open Filter MeasureTheory
open scoped ENNReal Topology Pointwise

noncomputable def radialOverlapEnergy
    (d : ℕ) (r : ℕ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (radialOverlapTerm d r n t)

noncomputable def radialOverlapEnergyExp
    (d : ℕ) (r : ℕ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  EReal.exp (radialOverlapEnergy d r t : EReal)

theorem measurable_radialOverlapEnergy
    (d : ℕ) (r : ℕ → ℝ) :
    Measurable (radialOverlapEnergy d r) := by
  apply Measurable.tsum
  intro n
  exact ENNReal.measurable_ofReal.comp
    (measurable_radialOverlapTerm d r n)

theorem measurable_radialOverlapEnergyExp
    (d : ℕ) (r : ℕ → ℝ) :
    Measurable (radialOverlapEnergyExp d r) := by
  exact EReal.measurable_exp.comp
    (measurable_coe_ennreal_ereal.comp
      (measurable_radialOverlapEnergy d r))

theorem flatTorusOverlapEnergy_eq_radialOverlapEnergy_dist
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (z : FlatTorus d) :
    flatTorusOverlapEnergy d r z =
      radialOverlapEnergy d r (dist 0 z) := by
  apply tsum_congr
  intro n
  rw [flatTorusOverlapTerm_eq_radialOverlapTerm d hd hr hrsmall]

theorem flatTorusOverlapEnergyExp_eq_radialOverlapEnergyExp_dist
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (z : FlatTorus d) :
    flatTorusOverlapEnergyExp d r z =
      radialOverlapEnergyExp d r (dist 0 z) := by
  rw [flatTorusOverlapEnergyExp, radialOverlapEnergyExp,
    flatTorusOverlapEnergy_eq_radialOverlapEnergy_dist
      d hd hr hrsmall z]

theorem radialOverlapTerm_eq_euclideanOverlapTerm
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    radialOverlapTerm d r n t = euclideanOverlapTerm d r n t := by
  rw [radialOverlapTerm]
  split_ifs with hnear
  · exact (volumeReal_coordinateLens_eq_profile d hd (hr n)
      ⟨ht, hnear⟩).symm
  · have hfar : 2 * r n ≤ t := (lt_of_not_ge hnear).le
    exact (volumeReal_coordinateLens_eq_zero_of_two_mul_le
      d (hr n).le hfar).symm

theorem coneEnergy_le_radialOverlapEnergy_le
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) {t : ℝ} (ht : 0 ≤ t) :
    coneEnergy r (radiusVolume d r)
        ((euclideanUnitBallVolume (d - 1) /
          euclideanUnitBallVolume d) * t) ≤
      radialOverlapEnergy d r t ∧
      radialOverlapEnergy d r t ≤
        coneEnergy r (radiusVolume d r) (t / 2) := by
  constructor
  · apply ENNReal.tsum_le_tsum
    intro n
    apply ENNReal.ofReal_le_ofReal
    rw [radialOverlapTerm_eq_euclideanOverlapTerm d hd hr n ht]
    exact coneTerm_le_euclideanOverlapTerm d hd hr ht n
  · apply ENNReal.tsum_le_tsum
    intro n
    apply ENNReal.ofReal_le_ofReal
    rw [radialOverlapTerm_eq_euclideanOverlapTerm d hd hr n ht]
    exact euclideanOverlapTerm_le_coneTerm d hd hr ht n

theorem coneEnergyExp_le_radialOverlapEnergyExp_le
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) {t : ℝ} (ht : 0 ≤ t) :
    coneEnergyExp r (radiusVolume d r)
        ((euclideanUnitBallVolume (d - 1) /
          euclideanUnitBallVolume d) * t) ≤
      radialOverlapEnergyExp d r t ∧
      radialOverlapEnergyExp d r t ≤
        coneEnergyExp r (radiusVolume d r) (t / 2) := by
  have h := coneEnergy_le_radialOverlapEnergy_le d hd hr ht
  exact ⟨EReal.exp_monotone (mod_cast h.1),
    EReal.exp_monotone (mod_cast h.2)⟩

theorem setLIntegral_flatTorusOverlapEnergyExp_closedBall_eq_polar
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (R : ℝ) (hRsmall : R < 1 / 4) :
    (∫⁻ z : FlatTorus d in Metric.closedBall 0 R,
      flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) =
      ENNReal.ofReal ((d : ℝ) * euclideanUnitBallVolume d) *
        ∫⁻ t in Set.Ioc 0 R,
          ENNReal.ofReal (t ^ (d - 1)) *
            radialOverlapEnergyExp d r t ∂volume := by
  calc
    (∫⁻ z : FlatTorus d in Metric.closedBall 0 R,
      flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) =
        ∫⁻ z : FlatTorus d in Metric.closedBall 0 R,
          radialOverlapEnergyExp d r (dist 0 z)
            ∂(flatTorusVolume d) := by
      apply setLIntegral_congr_fun Metric.isClosed_closedBall.measurableSet
      intro z _
      exact flatTorusOverlapEnergyExp_eq_radialOverlapEnergyExp_dist
        d hd hr hrsmall z
    _ = _ := setLIntegral_comp_dist_flatTorus_closedBall_eq_polar
      d (by omega) R hRsmall (radialOverlapEnergyExp d r)
        (measurable_radialOverlapEnergyExp d r)

theorem local_cone_integral_sandwich
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (R : ℝ) (hRsmall : R < 1 / 4) :
    ENNReal.ofReal ((d : ℝ) * euclideanUnitBallVolume d) *
        (∫⁻ t in Set.Ioc 0 R,
          ENNReal.ofReal (t ^ (d - 1)) *
            coneEnergyExp r (radiusVolume d r)
              ((euclideanUnitBallVolume (d - 1) /
                euclideanUnitBallVolume d) * t) ∂volume) ≤
      (∫⁻ z : FlatTorus d in Metric.closedBall 0 R,
        flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) ∧
      (∫⁻ z : FlatTorus d in Metric.closedBall 0 R,
        flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) ≤
      ENNReal.ofReal ((d : ℝ) * euclideanUnitBallVolume d) *
        (∫⁻ t in Set.Ioc 0 R,
          ENNReal.ofReal (t ^ (d - 1)) *
            coneEnergyExp r (radiusVolume d r) (t / 2) ∂volume) := by
  rw [setLIntegral_flatTorusOverlapEnergyExp_closedBall_eq_polar
    d hd hr hrsmall R hRsmall]
  constructor
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply setLIntegral_mono' measurableSet_Ioc
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (coneEnergyExp_le_radialOverlapEnergyExp_le d hd hr ht.1.le).1
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply setLIntegral_mono' measurableSet_Ioc
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (coneEnergyExp_le_radialOverlapEnergyExp_le d hd hr ht.1.le).2

theorem setLIntegral_comp_mul_left
    (f : ℝ → ℝ≥0∞) (s : Set ℝ) {c : ℝ} (hc : 0 < c) :
    (∫⁻ x in s, f (c * x) ∂volume) =
      ENNReal.ofReal c⁻¹ * ∫⁻ y in c • s, f y ∂volume := by
  let e : ℝ ≃ᵐ ℝ :=
    (Homeomorph.smul (Units.mk0 c hc.ne')).toMeasurableEquiv
  have he_apply (x : ℝ) : e x = c * x := rfl
  have he_image : e '' s = c • s := by
    ext y
    simp only [Set.mem_image, Set.mem_smul_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [he_apply]; rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, he_apply x⟩
  have hmap : Measure.map e volume = ENNReal.ofReal c⁻¹ • volume := by
    change Measure.map (c • ·) volume = _
    rw [Measure.map_addHaar_smul volume hc.ne']
    simp [Module.finrank_self, abs_of_pos hc]
  calc
    (∫⁻ x in s, f (c * x) ∂volume) =
        ∫⁻ y, f y ∂Measure.map e (volume.restrict s) := by
      rw [e.measurableEmbedding.lintegral_map]
      simp only [he_apply]
    _ = ∫⁻ y, f y ∂(Measure.map e volume).restrict (e '' s) := by
      congr 1
      rw [e.measurableEmbedding.restrict_map]
      simp
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ y in c • s, f y ∂volume := by
      rw [hmap, Measure.restrict_smul, lintegral_smul_measure, he_image]
      rfl

theorem weighted_cone_integral_scaling_identity
    (d : ℕ) (r : ℕ → ℝ) (R : ℝ) {c : ℝ} (hc : 0 < c) :
    ENNReal.ofReal (c ^ (d - 1)) *
        (∫⁻ t in Set.Ioc 0 R,
          ENNReal.ofReal (t ^ (d - 1)) *
            coneEnergyExp r (radiusVolume d r) (c * t) ∂volume) =
      ENNReal.ofReal c⁻¹ *
        (∫⁻ s in Set.Ioc 0 (c * R),
          ENNReal.ofReal (s ^ (d - 1)) *
            coneEnergyExp r (radiusVolume d r) s ∂volume) := by
  let F : ℝ → ℝ≥0∞ := coneEnergyExp r (radiusVolume d r)
  have hchange := setLIntegral_comp_mul_left
    (fun s => ENNReal.ofReal (s ^ (d - 1)) * F s)
    (Set.Ioc 0 R) hc
  rw [LinearOrderedField.smul_Ioc hc, mul_zero] at hchange
  calc
    ENNReal.ofReal (c ^ (d - 1)) *
        (∫⁻ t in Set.Ioc 0 R,
          ENNReal.ofReal (t ^ (d - 1)) * F (c * t) ∂volume) =
        ∫⁻ t in Set.Ioc 0 R,
          ENNReal.ofReal (c ^ (d - 1)) *
            (ENNReal.ofReal (t ^ (d - 1)) * F (c * t)) ∂volume := by
      exact (lintegral_const_mul'
        (μ := volume.restrict (Set.Ioc 0 R))
        (ENNReal.ofReal (c ^ (d - 1)))
        (fun t => ENNReal.ofReal (t ^ (d - 1)) * F (c * t))
        ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ t in Set.Ioc 0 R,
          ENNReal.ofReal ((c * t) ^ (d - 1)) * F (c * t) ∂volume := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro t _
      dsimp only
      rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hc.le (d - 1))]
      simp only [mul_assoc]
    _ = _ := hchange

theorem weighted_cone_integral_scaled_eq_top_iff
    (d : ℕ) (r : ℕ → ℝ) (R : ℝ) {c : ℝ} (hc : 0 < c) :
    ((∫⁻ t in Set.Ioc 0 R,
        ENNReal.ofReal (t ^ (d - 1)) *
          coneEnergyExp r (radiusVolume d r) (c * t) ∂volume) = ∞) ↔
      ((∫⁻ s in Set.Ioc 0 (c * R),
        ENNReal.ofReal (s ^ (d - 1)) *
          coneEnergyExp r (radiusVolume d r) s ∂volume) = ∞) := by
  have hscale := weighted_cone_integral_scaling_identity d r R hc
  have ha0 : ENNReal.ofReal (c ^ (d - 1)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hc (d - 1))
  have hb0 : ENNReal.ofReal c⁻¹ ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr hc)
  calc
    ((∫⁻ t in Set.Ioc 0 R,
        ENNReal.ofReal (t ^ (d - 1)) *
          coneEnergyExp r (radiusVolume d r) (c * t) ∂volume) = ∞) ↔
        ENNReal.ofReal (c ^ (d - 1)) *
          (∫⁻ t in Set.Ioc 0 R,
            ENNReal.ofReal (t ^ (d - 1)) *
              coneEnergyExp r (radiusVolume d r) (c * t) ∂volume) = ∞ := by
      simp [ENNReal.mul_eq_top, ha0, ENNReal.ofReal_ne_top]
    _ ↔ ENNReal.ofReal c⁻¹ *
          (∫⁻ s in Set.Ioc 0 (c * R),
            ENNReal.ofReal (s ^ (d - 1)) *
              coneEnergyExp r (radiusVolume d r) s ∂volume) = ∞ := by
      rw [hscale]
    _ ↔ _ := by
      simp [ENNReal.mul_eq_top, hb0, ENNReal.ofReal_ne_top]

theorem coneProfile_antitone {a : ℝ} (ha : 0 < a) :
    Antitone (coneProfile a) := by
  intro s t hst
  unfold coneProfile
  apply max_le_max _ le_rfl
  have hdiv : s / a ≤ t / a := (div_le_div_iff_of_pos_right ha).2 hst
  linarith

theorem coneEnergy_antitone
    {r v : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n) :
    Antitone (coneEnergy r v) := by
  intro s t hst
  apply ENNReal.tsum_le_tsum
  intro n
  apply ENNReal.ofReal_le_ofReal
  unfold coneTerm
  exact mul_le_mul_of_nonneg_left
    (coneProfile_antitone (hr n) hst) (hv n)

theorem coneEnergyExp_antitone
    {r v : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n) :
    Antitone (coneEnergyExp r v) := by
  intro s t hst
  apply EReal.exp_monotone
  exact_mod_cast coneEnergy_antitone hr hv hst

noncomputable def coneRadialIntegral
    (d : ℕ) (r : ℕ → ℝ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioc 0 R,
    ENNReal.ofReal (t ^ (d - 1)) *
      coneEnergyExp r (radiusVolume d r) t ∂volume

theorem coneRadialIntegral_mono
    (d : ℕ) (r : ℕ → ℝ) {R₁ R₂ : ℝ} (hR : R₁ ≤ R₂) :
    coneRadialIntegral d r R₁ ≤ coneRadialIntegral d r R₂ := by
  unfold coneRadialIntegral
  have hsubset : Set.Ioc (0 : ℝ) R₁ ⊆ Set.Ioc 0 R₂ := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hR⟩
  exact lintegral_mono' (Measure.restrict_mono_set volume hsubset) le_rfl

theorem coneRadialIntegral_eq_top_iff_of_le
    (d : ℕ) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR : R₁ ≤ R₂) :
    coneRadialIntegral d r R₁ = ∞ ↔
      coneRadialIntegral d r R₂ = ∞ := by
  have hv : ∀ n, 0 ≤ radiusVolume d r n := by
    intro n
    unfold radiusVolume
    exact mul_nonneg (euclideanUnitBallVolume_pos d).le
      (pow_nonneg (hr n).le d)
  constructor
  · intro htop
    apply top_unique
    rw [← htop]
    exact coneRadialIntegral_mono d r hR
  · intro htop
    let c : ℝ := R₂ / R₁
    have hc : 0 < c := div_pos (hR₁.trans_le hR) hR₁
    have hc_one : 1 ≤ c := (le_div_iff₀ hR₁).2 (by simpa using hR)
    have hcR : c * R₁ = R₂ := by
      dsimp [c]
      field_simp [hR₁.ne']
    have hscaled :
        (∫⁻ t in Set.Ioc 0 R₁,
          ENNReal.ofReal (t ^ (d - 1)) *
            coneEnergyExp r (radiusVolume d r) (c * t) ∂volume) = ∞ := by
      apply (weighted_cone_integral_scaled_eq_top_iff d r R₁ hc).2
      rwa [hcR]
    have hle :
        (∫⁻ t in Set.Ioc 0 R₁,
          ENNReal.ofReal (t ^ (d - 1)) *
            coneEnergyExp r (radiusVolume d r) (c * t) ∂volume) ≤
          coneRadialIntegral d r R₁ := by
      unfold coneRadialIntegral
      apply setLIntegral_mono' measurableSet_Ioc
      intro t ht
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply coneEnergyExp_antitone hr hv
      nlinarith [ht.1]
    apply top_unique
    rw [← hscaled]
    exact hle

theorem coneRadialIntegral_eq_top_iff
    (d : ℕ) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) :
    coneRadialIntegral d r R₁ = ∞ ↔
      coneRadialIntegral d r R₂ = ∞ := by
  rcases le_total R₁ R₂ with hle | hle
  · exact coneRadialIntegral_eq_top_iff_of_le d hr hR₁ hle
  · exact (coneRadialIntegral_eq_top_iff_of_le d hr hR₂ hle).symm

theorem setLIntegral_flatTorusOverlapEnergyExp_compl_closedBall_lt_top
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (𝓝 0)) {R : ℝ} (hR : 0 < R) :
    (∫⁻ z : FlatTorus d in (Metric.closedBall 0 R)ᶜ,
      flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) < ∞ := by
  have hv : ∀ n, 0 ≤ radiusVolume d r n := by
    intro n
    unfold radiusVolume
    exact mul_nonneg (euclideanUnitBallVolume_pos d).le
      (pow_nonneg (hr n).le d)
  let C : ℝ≥0∞ := coneEnergyExp r (radiusVolume d r) (R / 2)
  have hCtop : C ≠ ∞ := by
    dsimp [C]
    rw [coneEnergyExp_eq_ofReal_exp_coneSum hr hv hrlim (half_pos hR)]
    exact ENNReal.ofReal_ne_top
  have hbound : ∀ z ∈ (Metric.closedBall (0 : FlatTorus d) R)ᶜ,
      flatTorusOverlapEnergyExp d r z ≤ C := by
    intro z hz
    have hdist : R ≤ dist (0 : FlatTorus d) z := by
      rw [Set.mem_compl_iff, Metric.mem_closedBall] at hz
      exact (le_of_not_ge hz).trans_eq (dist_comm z 0)
    exact (coneEnergyExp_le_flatTorusOverlapEnergyExp_le
      d hd hr hrsmall z).2.trans
        (coneEnergyExp_antitone hr hv
          (div_le_div_of_nonneg_right hdist zero_le_two))
  have hle :
      (∫⁻ z : FlatTorus d in (Metric.closedBall 0 R)ᶜ,
        flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) ≤
      ∫⁻ _z : FlatTorus d in (Metric.closedBall 0 R)ᶜ,
        C ∂(flatTorusVolume d) := by
    exact setLIntegral_mono measurable_const hbound
  exact hle.trans_lt
    (setLIntegral_const_lt_top (μ := flatTorusVolume d)
      (Metric.closedBall (0 : FlatTorus d) R)ᶜ hCtop)

theorem lintegral_flatTorusOverlapEnergyExp_eq_top_iff_closedBall
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (𝓝 0)) {R : ℝ} (hR : 0 < R) :
    (∫⁻ z : FlatTorus d,
      flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) = ∞ ↔
      (∫⁻ z : FlatTorus d in Metric.closedBall 0 R,
        flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) = ∞ := by
  have hout :=
    setLIntegral_flatTorusOverlapEnergyExp_compl_closedBall_lt_top
      d hd hr hrsmall hrlim hR
  have hsplit := lintegral_add_compl
    (μ := flatTorusVolume d) (flatTorusOverlapEnergyExp d r)
    (A := Metric.closedBall (0 : FlatTorus d) R)
    Metric.isClosed_closedBall.measurableSet
  rw [← hsplit, ENNReal.add_eq_top]
  exact or_iff_left hout.ne

theorem setLIntegral_flatTorusOverlapEnergyExp_eq_top_iff_coneRadialIntegral
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    {R t₀ : ℝ} (hR : 0 < R) (hRsmall : R < 1 / 4) (ht₀ : 0 < t₀) :
    (∫⁻ z : FlatTorus d in Metric.closedBall 0 R,
      flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) = ∞ ↔
      coneRadialIntegral d r t₀ = ∞ := by
  let a : ℝ := euclideanUnitBallVolume (d - 1) /
    euclideanUnitBallVolume d
  let k : ℝ≥0∞ :=
    ENNReal.ofReal ((d : ℝ) * euclideanUnitBallVolume d)
  let L : ℝ≥0∞ :=
    ∫⁻ t in Set.Ioc 0 R,
      ENNReal.ofReal (t ^ (d - 1)) *
        coneEnergyExp r (radiusVolume d r) (a * t) ∂volume
  let U : ℝ≥0∞ :=
    ∫⁻ t in Set.Ioc 0 R,
      ENNReal.ofReal (t ^ (d - 1)) *
        coneEnergyExp r (radiusVolume d r) (t / 2) ∂volume
  have ha : 0 < a := div_pos
    (euclideanUnitBallVolume_pos (d - 1))
    (euclideanUnitBallVolume_pos d)
  have hkpos : 0 < (d : ℝ) * euclideanUnitBallVolume d := by
    apply mul_pos
    · exact_mod_cast (by omega : 0 < d)
    · exact euclideanUnitBallVolume_pos d
  have hk0 : k ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hkpos
  have hktop : k ≠ ∞ := ENNReal.ofReal_ne_top
  have hsand :
      k * L ≤
        (∫⁻ z : FlatTorus d in Metric.closedBall 0 R,
          flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) ∧
        (∫⁻ z : FlatTorus d in Metric.closedBall 0 R,
          flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) ≤
          k * U := by
    simpa only [a, k, L, U] using
      (local_cone_integral_sandwich d hd hr hrsmall R hRsmall)
  have hL : L = ∞ ↔ coneRadialIntegral d r t₀ = ∞ := by
    have hscale := weighted_cone_integral_scaled_eq_top_iff d r R ha
    have hend := coneRadialIntegral_eq_top_iff d hr (mul_pos ha hR) ht₀
    exact hscale.trans (by simpa only [coneRadialIntegral] using hend)
  have hU : U = ∞ ↔ coneRadialIntegral d r t₀ = ∞ := by
    have hc : 0 < (1 / 2 : ℝ) := by norm_num
    have hscale := weighted_cone_integral_scaled_eq_top_iff d r R hc
    have hend := coneRadialIntegral_eq_top_iff d hr (mul_pos hc hR) ht₀
    have hcombined := hscale.trans
      (by simpa only [coneRadialIntegral] using hend)
    simpa only [U, coneRadialIntegral, div_eq_mul_inv, one_div,
      one_mul, mul_comm] using hcombined
  constructor
  · intro htorus
    have hkU : k * U = ∞ := by
      apply top_unique
      rw [← htorus]
      exact hsand.2
    have hUtop : U = ∞ := by
      simpa [ENNReal.mul_eq_top, hk0, hktop] using hkU
    exact hU.mp hUtop
  · intro hcone
    have hLtop : L = ∞ := hL.mpr hcone
    have hkL : k * L = ∞ :=
      ENNReal.mul_eq_top.mpr (Or.inl ⟨hk0, hLtop⟩)
    apply top_unique
    rw [← hkL]
    exact hsand.1

theorem flatTorusVolume_singleton_zero
    (d : ℕ) (hd : 0 < d) :
    flatTorusVolume d ({0} : Set (FlatTorus d)) = 0 := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have h := flatTorusVolume_closedBall_zero_eq_volume
    d (r := (0 : ℝ)) (by norm_num)
  simpa [Metric.closedBall_zero, EuclideanSpace.volume_closedBall,
    Fintype.card_fin, hd.ne'] using h

theorem lintegral_flatTorusOverlapEnergyExp_eq_real
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (𝓝 0)) :
    (∫⁻ z : FlatTorus d,
      flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) =
      ∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d) := by
  apply lintegral_congr_ae
  have hzero := flatTorusVolume_singleton_zero d (by omega)
  filter_upwards [compl_mem_ae_iff.2 hzero] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  exact flatTorusOverlapEnergyExp_eq_ofReal_exp_flatTorusOverlapSum
    d hd hr hrsmall hrlim hz0

theorem coneRadialIntegral_eq_real
    (d : ℕ) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (t₀ : ℝ) :
    coneRadialIntegral d r t₀ =
      ∫⁻ t in Set.Ioc 0 t₀,
        ENNReal.ofReal (t ^ (d - 1)) *
          ENNReal.ofReal (Real.exp
            (coneSum r (radiusVolume d r) t)) ∂volume := by
  have hv : ∀ n, 0 ≤ radiusVolume d r n := by
    intro n
    unfold radiusVolume
    exact mul_nonneg (euclideanUnitBallVolume_pos d).le
      (pow_nonneg (hr n).le d)
  unfold coneRadialIntegral
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [coneEnergyExp_eq_ofReal_exp_coneSum hr hv hrlim ht.1]

theorem cone_criterion
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (𝓝 0)) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    (∫⁻ z : FlatTorus d,
      ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
        ∂(flatTorusVolume d)) = ∞ ↔
      (∫⁻ t in Set.Ioc 0 t₀,
        ENNReal.ofReal (t ^ (d - 1)) *
          ENNReal.ofReal (Real.exp
            (coneSum r (radiusVolume d r) t)) ∂volume) = ∞ := by
  let R : ℝ := 1 / 8
  have hR : 0 < R := by norm_num [R]
  have hRsmall : R < 1 / 4 := by norm_num [R]
  rw [← lintegral_flatTorusOverlapEnergyExp_eq_real
    d hd hr hrsmall hrlim]
  rw [← coneRadialIntegral_eq_real d hr hrlim t₀]
  exact (lintegral_flatTorusOverlapEnergyExp_eq_top_iff_closedBall
    d hd hr hrsmall hrlim hR).trans
      (setLIntegral_flatTorusOverlapEnergyExp_eq_top_iff_coneRadialIntegral
        d hd hr hrsmall hR hRsmall ht₀)

end Shepp.Section2
end SheppFlattenedModule015

section SheppFlattenedModule016
open scoped BigOperators

namespace Shepp.Section2

noncomputable def intrinsicWidth
    (d : ℝ) (r v : ℕ → ℝ) (n : ℕ) : ℝ :=
  if prefixSlope r v n = 0 then r n
  else min (r n) (d / prefixSlope r v n)

lemma prefixSlope_nonneg
    {r v : ℕ → ℝ}
    (hr : ∀ n, 0 < r n)
    (hv : ∀ n, 0 ≤ v n)
    (N : ℕ) :
    0 ≤ prefixSlope r v N := by
  apply Finset.sum_nonneg
  intro n _
  exact div_nonneg (hv n) (le_of_lt (hr n))

lemma prefixSlope_mono
    {r v : ℕ → ℝ}
    (hr : ∀ n, 0 < r n)
    (hv : ∀ n, 0 ≤ v n) :
    Monotone (prefixSlope r v) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hab))
    (by
      intro i _ _
      exact div_nonneg (hv i) (le_of_lt (hr i)))

lemma intrinsicWidth_pos
    {d : ℝ} {r v : ℕ → ℝ}
    (hd : 0 < d)
    (hr : ∀ n, 0 < r n)
    (hv : ∀ n, 0 ≤ v n)
    (n : ℕ) :
    0 < intrinsicWidth d r v n := by
  have hSnonneg := prefixSlope_nonneg hr hv n
  by_cases hS : prefixSlope r v n = 0
  · simp [intrinsicWidth, hS, hr n]
  · have hSpos : 0 < prefixSlope r v n := lt_of_le_of_ne hSnonneg (Ne.symm hS)
    rw [intrinsicWidth, if_neg hS]
    exact lt_min (hr n) (div_pos hd hSpos)

lemma intrinsicWidth_le_radius
    (d : ℝ) (r v : ℕ → ℝ) (n : ℕ) :
    intrinsicWidth d r v n ≤ r n := by
  by_cases hS : prefixSlope r v n = 0
  · simp [intrinsicWidth, hS]
  · simp [intrinsicWidth, hS]

lemma intrinsicWidth_mul_prefixSlope_le
    {d : ℝ} {r v : ℕ → ℝ}
    (hd : 0 ≤ d)
    (hr : ∀ n, 0 < r n)
    (hv : ∀ n, 0 ≤ v n)
    (n : ℕ) :
    intrinsicWidth d r v n * prefixSlope r v n ≤ d := by
  have hSnonneg := prefixSlope_nonneg hr hv n
  by_cases hS : prefixSlope r v n = 0
  · simpa [hS] using hd
  · have hSpos : 0 < prefixSlope r v n :=
      lt_of_le_of_ne hSnonneg (Ne.symm hS)
    calc
      intrinsicWidth d r v n * prefixSlope r v n ≤
          (d / prefixSlope r v n) * prefixSlope r v n := by
        apply mul_le_mul_of_nonneg_right _ hSnonneg
        simp [intrinsicWidth, hS]
      _ = d := by field_simp

lemma level_bounds_of_le_intrinsicWidth
    {d ell : ℝ} {r v : ℕ → ℝ} {n : ℕ}
    (hd : 0 ≤ d)
    (hr : ∀ i, 0 < r i)
    (hv : ∀ i, 0 ≤ v i)
    (hlevel : ell ≤ intrinsicWidth d r v n) :
    ell ≤ r n ∧ ell * prefixSlope r v n ≤ d := by
  constructor
  · exact hlevel.trans (intrinsicWidth_le_radius d r v n)
  · calc
      ell * prefixSlope r v n ≤
          intrinsicWidth d r v n * prefixSlope r v n :=
        mul_le_mul_of_nonneg_right hlevel (prefixSlope_nonneg hr hv n)
      _ ≤ d := intrinsicWidth_mul_prefixSlope_le hd hr hv n

lemma intrinsicWidth_antitone
    {d : ℝ} {r v : ℕ → ℝ}
    (hd : 0 < d)
    (hr : ∀ n, 0 < r n)
    (hv : ∀ n, 0 ≤ v n)
    (hmono : Antitone r) :
    Antitone (intrinsicWidth d r v) := by
  intro n m hnm
  have hrmn : r m ≤ r n := hmono hnm
  have hSle : prefixSlope r v n ≤ prefixSlope r v m :=
    prefixSlope_mono hr hv hnm
  have hSnnonneg := prefixSlope_nonneg hr hv n
  by_cases hSn : prefixSlope r v n = 0
  · simpa [intrinsicWidth, hSn] using
      (intrinsicWidth_le_radius d r v m).trans hrmn
  · have hSnpos : 0 < prefixSlope r v n :=
      lt_of_le_of_ne hSnnonneg (Ne.symm hSn)
    have hSmpos : 0 < prefixSlope r v m := hSnpos.trans_le hSle
    simpa [intrinsicWidth, hSn, hSmpos.ne'] using
      min_le_min hrmn
        (div_le_div_of_nonneg_left (le_of_lt hd) hSnpos hSle)

lemma intrinsicWidth_tendsto_zero
    {d : ℝ} {r v : ℕ → ℝ}
    (hd : 0 < d)
    (hr : ∀ n, 0 < r n)
    (hv : ∀ n, 0 ≤ v n)
    (hr0 : Filter.Tendsto r Filter.atTop (nhds 0)) :
    Filter.Tendsto (intrinsicWidth d r v) Filter.atTop (nhds 0) := by
  exact squeeze_zero
    (fun n => le_of_lt (intrinsicWidth_pos hd hr hv n))
    (fun n => intrinsicWidth_le_radius d r v n)
    hr0

theorem exists_last_index_ge_of_tendsto_zero
    {σ : ℕ → ℝ} {ell : ℝ}
    (hell : 0 < ell)
    (hσ0 : ell ≤ σ 0)
    (hσlim : Filter.Tendsto σ Filter.atTop (nhds 0)) :
    ∃ N, ell ≤ σ N ∧ ∀ n, N < n → σ n < ell := by
  have hevent : ∀ᶠ n in Filter.atTop, σ n < ell :=
    hσlim.eventually_lt_const hell
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevent
  classical
  let N := Nat.findGreatest (fun n => ell ≤ σ n) M
  refine ⟨N, ?_, ?_⟩
  · exact Nat.findGreatest_spec (P := fun n => ell ≤ σ n) (Nat.zero_le M) hσ0
  · intro n hNn
    by_cases hnM : n ≤ M
    · exact lt_of_not_ge
        (Nat.findGreatest_is_greatest
          (P := fun i => ell ≤ σ i) hNn hnM)
    · exact hM n (by omega)

theorem exists_intrinsic_cutoff
    {d ell : ℝ} {r v : ℕ → ℝ}
    (hd : 0 < d)
    (hell : 0 < ell)
    (hr : ∀ n, 0 < r n)
    (hv : ∀ n, 0 ≤ v n)
    (hmono : Antitone r)
    (hr0 : Filter.Tendsto r Filter.atTop (nhds 0))
    (hell0 : ell ≤ intrinsicWidth d r v 0) :
    ∃ N,
      (∀ n, n ≤ N → ell ≤ intrinsicWidth d r v n) ∧
      (∀ n, N < n → intrinsicWidth d r v n < ell) := by
  obtain ⟨N, hN, hmax⟩ := exists_last_index_ge_of_tendsto_zero
    hell hell0 (intrinsicWidth_tendsto_zero hd hr hv hr0)
  refine ⟨N, ?_, hmax⟩
  intro n hn
  exact hN.trans (intrinsicWidth_antitone hd hr hv hmono hn)

lemma exp_sub_le_one_add_exp_neg_mul
    (A x : ℝ) (hx : 0 ≤ x) :
    Real.exp (A - x) ≤ 1 + Real.exp (-x) * (Real.exp A - 1) := by
  rw [sub_eq_add_neg, Real.exp_add]
  have hle : Real.exp (-x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  nlinarith [Real.exp_pos A, Real.exp_pos (-x)]

lemma scaled_div_intrinsicWidth_le
    {d t : ℝ} {r v : ℕ → ℝ} {n N : ℕ}
    (hd : 0 < d)
    (ht0 : 0 ≤ t)
    (hr : ∀ i, 0 < r i)
    (hv : ∀ i, 0 ≤ v i)
    (hmono : Antitone r)
    (hn : n ≤ N)
    (ht : t < r N) :
    d * t / intrinsicWidth d r v n ≤
      d + t * prefixSlope r v N := by
  have htrn : t < r n := lt_of_lt_of_le ht (hmono hn)
  have hSNnonneg := prefixSlope_nonneg hr hv N
  have hSnnonneg := prefixSlope_nonneg hr hv n
  have hSnSN : prefixSlope r v n ≤ prefixSlope r v N :=
    prefixSlope_mono hr hv hn
  have htSNnonneg : 0 ≤ t * prefixSlope r v N :=
    mul_nonneg ht0 hSNnonneg
  by_cases hSn : prefixSlope r v n = 0
  · rw [intrinsicWidth, if_pos hSn]
    have htdiv : t / r n < 1 := (div_lt_one (hr n)).mpr htrn
    have hstrict : d * (t / r n) < d := by
      simpa using mul_lt_mul_of_pos_left htdiv hd
    calc
      d * t / r n = d * (t / r n) := by ring
      _ ≤ d := le_of_lt hstrict
      _ ≤ d + t * prefixSlope r v N := le_add_of_nonneg_right htSNnonneg
  · have hSnpos : 0 < prefixSlope r v n :=
      lt_of_le_of_ne hSnnonneg (Ne.symm hSn)
    by_cases hbranch : r n ≤ d / prefixSlope r v n
    · rw [intrinsicWidth, if_neg hSn, min_eq_left hbranch]
      have htdiv : t / r n < 1 := (div_lt_one (hr n)).mpr htrn
      have hstrict : d * (t / r n) < d := by
        simpa using mul_lt_mul_of_pos_left htdiv hd
      calc
        d * t / r n = d * (t / r n) := by ring
        _ ≤ d := le_of_lt hstrict
        _ ≤ d + t * prefixSlope r v N := le_add_of_nonneg_right htSNnonneg
    · have hdr_le : d / prefixSlope r v n ≤ r n := le_of_not_ge hbranch
      rw [intrinsicWidth, if_neg hSn, min_eq_right hdr_le]
      calc
        d * t / (d / prefixSlope r v n) =
            t * prefixSlope r v n := by field_simp
        _ ≤ t * prefixSlope r v N := mul_le_mul_of_nonneg_left hSnSN ht0
        _ ≤ d + t * prefixSlope r v N := le_add_of_nonneg_left (le_of_lt hd)

theorem finite_packet_domination
    {d t : ℝ} {r v : ℕ → ℝ} {N : ℕ}
    (hd : 0 < d)
    (ht0 : 0 ≤ t)
    (hr : ∀ n, 0 < r n)
    (hv : ∀ n, 0 ≤ v n)
    (hmono : Antitone r)
    (ht : t < r N) :
    Real.exp (conePrefix r v N t) ≤
      1 + Real.exp d *
        (∑ n ∈ Finset.range (N + 1),
          expIncrement v n * Real.exp (-d * t / intrinsicWidth d r v n)) := by
  let S := prefixSlope r v N
  let A := prefixMass v N
  have hSnonneg : 0 ≤ S := prefixSlope_nonneg hr hv N
  have htSnonneg : 0 ≤ t * S := mul_nonneg ht0 hSnonneg
  have hbase :
      Real.exp (-d - t * S) * (Real.exp A - 1) ≤
        ∑ n ∈ Finset.range (N + 1),
          expIncrement v n * Real.exp (-d * t / intrinsicWidth d r v n) := by
    rw [← sum_expIncrement v N]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hrate := scaled_div_intrinsicWidth_le hd ht0 hr hv hmono hnN ht
    have hrate' : d * t / intrinsicWidth d r v n ≤ d + t * S := by
      simpa [S] using hrate
    have hexp : Real.exp (-d - t * S) ≤
        Real.exp (-d * t / intrinsicWidth d r v n) := by
      apply Real.exp_le_exp.mpr
      calc
        -d - t * S = -(d + t * S) := by ring
        _ ≤ -(d * t / intrinsicWidth d r v n) := neg_le_neg hrate'
        _ = -d * t / intrinsicWidth d r v n := by ring
    calc
      Real.exp (-d - t * S) * expIncrement v n =
          expIncrement v n * Real.exp (-d - t * S) := mul_comm _ _
      _ ≤ expIncrement v n * Real.exp (-d * t / intrinsicWidth d r v n) :=
          mul_le_mul_of_nonneg_left hexp (expIncrement_nonneg hv n)
  have hfactor : Real.exp d * Real.exp (-d - t * S) = Real.exp (-t * S) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [conePrefix_eq_mass_sub_slope hr hmono ht]
  change Real.exp (A - t * S) ≤ _
  calc
    Real.exp (A - t * S)
        ≤ 1 + Real.exp (-t * S) * (Real.exp A - 1) :=
          by simpa only [neg_mul] using
            exp_sub_le_one_add_exp_neg_mul A (t * S) htSnonneg
    _ = 1 + Real.exp d *
          (Real.exp (-d - t * S) * (Real.exp A - 1)) := by
          rw [← mul_assoc, hfactor]
    _ ≤ 1 + Real.exp d *
          (∑ n ∈ Finset.range (N + 1),
            expIncrement v n * Real.exp (-d * t / intrinsicWidth d r v n)) := by
          gcongr

theorem packet_block_bound
    {d t ell : ℝ} {r v : ℕ → ℝ} {a b : ℕ}
    (hd : 0 ≤ d)
    (ht : 0 ≤ t)
    (hwidth : ∀ n ∈ Finset.Ioc a b,
      intrinsicWidth d r v n < 2 * ell)
    (hwidthpos : ∀ n, 0 < intrinsicWidth d r v n)
    (hv : ∀ n, 0 ≤ v n)
    (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc a b,
        expIncrement v n *
          Real.exp (-d * t / intrinsicWidth d r v n)) ≤
      (Real.exp (prefixMass v b) - Real.exp (prefixMass v a)) *
        Real.exp (-d * t / (2 * ell)) := by
  calc
    (∑ n ∈ Finset.Ioc a b,
        expIncrement v n *
          Real.exp (-d * t / intrinsicWidth d r v n)) ≤
        ∑ n ∈ Finset.Ioc a b,
          expIncrement v n * Real.exp (-d * t / (2 * ell)) := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (expIncrement_nonneg hv n)
      apply Real.exp_le_exp.mpr
      have hrate : d * t / (2 * ell) ≤
          d * t / intrinsicWidth d r v n :=
        div_le_div_of_nonneg_left
          (mul_nonneg hd ht)
          (hwidthpos n)
          (le_of_lt (hwidth n hn))
      calc
        -d * t / intrinsicWidth d r v n =
            -(d * t / intrinsicWidth d r v n) := by ring
        _ ≤ -(d * t / (2 * ell)) := neg_le_neg hrate
        _ = -d * t / (2 * ell) := by ring
    _ = (∑ n ∈ Finset.Ioc a b, expIncrement v n) *
        Real.exp (-d * t / (2 * ell)) := by
      rw [Finset.sum_mul]
    _ = (Real.exp (prefixMass v b) - Real.exp (prefixMass v a)) *
        Real.exp (-d * t / (2 * ell)) := by
      rw [sum_expIncrement_Ioc v hab]

end Shepp.Section2
end SheppFlattenedModule016

section SheppFlattenedModule017
open scoped BigOperators ENNReal
open Filter Set

namespace Shepp.Section2

noncomputable def test_intrinsicCutoff
    (d ell : ℝ) (r v : ℕ → ℝ) : ℕ :=
  sSup {n : ℕ | ell ≤ intrinsicWidth d r v n}

lemma test_intrinsicCutoff_bddAbove
    {d ell : ℝ} {r v : ℕ → ℝ}
    (hell : 0 < ell)
    (hσlim : Tendsto (intrinsicWidth d r v) atTop (nhds 0)) :
    BddAbove {n : ℕ | ell ≤ intrinsicWidth d r v n} := by
  have hevent : ∀ᶠ n in atTop, intrinsicWidth d r v n < ell :=
    hσlim.eventually_lt_const hell
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨M, ?_⟩
  intro n hn
  by_contra hnot
  have hMn : M ≤ n := by omega
  exact (not_lt_of_ge hn) (hM n hMn)

lemma test_intrinsicCutoff_mem
    {d ell : ℝ} {r v : ℕ → ℝ}
    (hell : 0 < ell)
    (hell0 : ell ≤ intrinsicWidth d r v 0)
    (hσlim : Tendsto (intrinsicWidth d r v) atTop (nhds 0)) :
    ell ≤ intrinsicWidth d r v (test_intrinsicCutoff d ell r v) := by
  unfold test_intrinsicCutoff
  change sSup {n : ℕ | ell ≤ intrinsicWidth d r v n} ∈
    {n : ℕ | ell ≤ intrinsicWidth d r v n}
  exact Nat.sSup_mem ⟨0, hell0⟩
    (test_intrinsicCutoff_bddAbove hell hσlim)

lemma test_le_intrinsicCutoff
    {d ell : ℝ} {r v : ℕ → ℝ} {n : ℕ}
    (hell : 0 < ell)
    (hσlim : Tendsto (intrinsicWidth d r v) atTop (nhds 0))
    (hn : ell ≤ intrinsicWidth d r v n) :
    n ≤ test_intrinsicCutoff d ell r v := by
  unfold test_intrinsicCutoff
  exact le_csSup (test_intrinsicCutoff_bddAbove hell hσlim) hn

lemma test_intrinsicWidth_lt_of_cutoff_lt
    {d ell : ℝ} {r v : ℕ → ℝ} {n : ℕ}
    (hell : 0 < ell)
    (hσlim : Tendsto (intrinsicWidth d r v) atTop (nhds 0))
    (hn : test_intrinsicCutoff d ell r v < n) :
    intrinsicWidth d r v n < ell := by
  apply lt_of_not_ge
  intro hge
  exact (not_le_of_gt hn) (test_le_intrinsicCutoff hell hσlim hge)

lemma test_intrinsicCutoff_antitone_level
    {d ell₁ ell₂ : ℝ} {r v : ℕ → ℝ}
    (hell₁ : 0 < ell₁) (hell₂ : 0 < ell₂)
    (hell₂₁ : ell₂ ≤ ell₁)
    (hell₁0 : ell₁ ≤ intrinsicWidth d r v 0)
    (hσlim : Tendsto (intrinsicWidth d r v) atTop (nhds 0)) :
    test_intrinsicCutoff d ell₁ r v ≤
      test_intrinsicCutoff d ell₂ r v := by
  apply test_le_intrinsicCutoff hell₂ hσlim
  exact hell₂₁.trans (test_intrinsicCutoff_mem hell₁ hell₁0 hσlim)

noncomputable def test_dyadicLevel (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

lemma test_dyadicLevel_pos (k : ℕ) : 0 < test_dyadicLevel k := by
  unfold test_dyadicLevel
  positivity

lemma test_dyadicLevel_succ (k : ℕ) :
    test_dyadicLevel k = 2 * test_dyadicLevel (k + 1) := by
  unfold test_dyadicLevel
  rw [pow_succ]
  ring

lemma test_dyadicLevel_antitone : Antitone test_dyadicLevel := by
  apply antitone_nat_of_succ_le
  intro k
  rw [test_dyadicLevel_succ k]
  nlinarith [test_dyadicLevel_pos (k + 1)]

lemma test_dyadicLevel_tendsto_zero :
    Tendsto test_dyadicLevel atTop (nhds 0) := by
  unfold test_dyadicLevel
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)

lemma test_exists_dyadic_bracket {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ∃ K : ℕ, test_dyadicLevel K ≤ x ∧
      x < 2 * test_dyadicLevel K := by
  have hevent : ∀ᶠ k in atTop, test_dyadicLevel k < x :=
    test_dyadicLevel_tendsto_zero.eventually_lt_const hx
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevent
  have hex : ∃ k : ℕ, test_dyadicLevel k ≤ x :=
    ⟨M, (hM M le_rfl).le⟩
  let K := Nat.find hex
  have hKlower : test_dyadicLevel K ≤ x := Nat.find_spec hex
  have hKne : K ≠ 0 := by
    intro hK
    have : (1 : ℝ) ≤ x := by simpa [test_dyadicLevel, hK] using hKlower
    exact (not_le_of_gt hx1) this
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hKne
  refine ⟨K, hKlower, ?_⟩
  have hnot : ¬ test_dyadicLevel k ≤ x := by
    intro hkx
    have hfindle : K ≤ k := Nat.find_min' hex hkx
    omega
  have hxlt : x < test_dyadicLevel k := lt_of_not_ge hnot
  rw [test_dyadicLevel_succ k] at hxlt
  simpa [hk] using hxlt

noncomputable def test_packetCutoff
    (d : ℝ) (r v : ℕ → ℝ) (K k : ℕ) : ℕ :=
  test_intrinsicCutoff d (test_dyadicLevel (K + k)) r v

lemma test_packetCutoff_level_le_zero
    {d : ℝ} {r v : ℕ → ℝ} {K k : ℕ}
    (hK : test_dyadicLevel K ≤ intrinsicWidth d r v 0) :
    test_dyadicLevel (K + k) ≤ intrinsicWidth d r v 0 := by
  exact (test_dyadicLevel_antitone (Nat.le_add_right K k)).trans hK

lemma test_packetCutoff_level_mem
    {d : ℝ} {r v : ℕ → ℝ} {K k : ℕ}
    (hK : test_dyadicLevel K ≤ intrinsicWidth d r v 0)
    (hσlim : Tendsto (intrinsicWidth d r v) atTop (nhds 0)) :
    test_dyadicLevel (K + k) ≤
      intrinsicWidth d r v (test_packetCutoff d r v K k) := by
  exact test_intrinsicCutoff_mem
    (test_dyadicLevel_pos (K + k))
    (test_packetCutoff_level_le_zero hK) hσlim

lemma test_packetCutoff_monotone
    {d : ℝ} {r v : ℕ → ℝ} {K : ℕ}
    (hK : test_dyadicLevel K ≤ intrinsicWidth d r v 0)
    (hσlim : Tendsto (intrinsicWidth d r v) atTop (nhds 0)) :
    Monotone (test_packetCutoff d r v K) := by
  intro k l hkl
  apply test_intrinsicCutoff_antitone_level
  · exact test_dyadicLevel_pos (K + k)
  · exact test_dyadicLevel_pos (K + l)
  · exact test_dyadicLevel_antitone (Nat.add_le_add_left hkl K)
  · exact test_packetCutoff_level_le_zero hK
  · exact hσlim

lemma test_packetCutoff_tendsto_atTop
    {d : ℝ} {r v : ℕ → ℝ} {K : ℕ}
    (hd : 0 < d) (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hrlim : Tendsto r atTop (nhds 0)) :
    Tendsto (test_packetCutoff d r v K) atTop atTop := by
  have hσlim := intrinsicWidth_tendsto_zero hd hr hv hrlim
  rw [Filter.tendsto_atTop_atTop]
  intro B
  have hσB : 0 < intrinsicWidth d r v B :=
    intrinsicWidth_pos hd hr hv B
  have hevent : ∀ᶠ k in atTop,
      test_dyadicLevel k < intrinsicWidth d r v B :=
    test_dyadicLevel_tendsto_zero.eventually_lt_const hσB
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨M, fun k hk => ?_⟩
  apply test_le_intrinsicCutoff (test_dyadicLevel_pos (K + k)) hσlim
  exact (test_dyadicLevel_antitone (Nat.le_add_left k K)).trans_lt
    (hM k hk) |>.le

lemma test_packetCutoff_level_le_width_of_le
    {d : ℝ} {r v : ℕ → ℝ} {K k n : ℕ}
    (hK : test_dyadicLevel K ≤ intrinsicWidth d r v 0)
    (hσlim : Tendsto (intrinsicWidth d r v) atTop (nhds 0))
    (hn : n ≤ test_packetCutoff d r v K k)
    (hanti : Antitone (intrinsicWidth d r v)) :
    test_dyadicLevel (K + k) ≤ intrinsicWidth d r v n := by
  exact (test_packetCutoff_level_mem hK hσlim).trans (hanti hn)

lemma test_packetCutoff_width_lt_of_lt
    {d : ℝ} {r v : ℕ → ℝ} {K k n : ℕ}
    (hσlim : Tendsto (intrinsicWidth d r v) atTop (nhds 0))
    (hn : test_packetCutoff d r v K k < n) :
    intrinsicWidth d r v n < test_dyadicLevel (K + k) := by
  exact test_intrinsicWidth_lt_of_cutoff_lt
    (test_dyadicLevel_pos (K + k)) hσlim hn

lemma test_packetCutoff_block_width
    {d : ℝ} {r v : ℕ → ℝ} {K k n : ℕ}
    (hK : test_dyadicLevel K ≤ intrinsicWidth d r v 0)
    (hσlim : Tendsto (intrinsicWidth d r v) atTop (nhds 0))
    (hanti : Antitone (intrinsicWidth d r v))
    (hn : n ∈ Finset.Ioc (test_packetCutoff d r v K k)
      (test_packetCutoff d r v K (k + 1))) :
    test_dyadicLevel (K + (k + 1)) ≤ intrinsicWidth d r v n ∧
      intrinsicWidth d r v n <
        2 * test_dyadicLevel (K + (k + 1)) := by
  have hn' : test_packetCutoff d r v K k < n ∧
      n ≤ test_packetCutoff d r v K (k + 1) := by
    simpa using hn
  constructor
  · exact test_packetCutoff_level_le_width_of_le hK hσlim hn'.2 hanti
  · have hlt := test_packetCutoff_width_lt_of_lt hσlim hn'.1
    rw [show K + (k + 1) = (K + k) + 1 by omega]
    rw [← test_dyadicLevel_succ (K + k)]
    exact hlt

lemma test_packetCutoff_initial_block_width
    {d : ℝ} {r v : ℕ → ℝ} {K n : ℕ}
    (hKlower : test_dyadicLevel K ≤ intrinsicWidth d r v 0)
    (hKupper : intrinsicWidth d r v 0 < 2 * test_dyadicLevel K)
    (hσlim : Tendsto (intrinsicWidth d r v) atTop (nhds 0))
    (hanti : Antitone (intrinsicWidth d r v))
    (hn : n ∈ Finset.range (test_packetCutoff d r v K 0 + 1)) :
    test_dyadicLevel K ≤ intrinsicWidth d r v n ∧
      intrinsicWidth d r v n < 2 * test_dyadicLevel K := by
  have hnle : n ≤ test_packetCutoff d r v K 0 :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  constructor
  · simpa using test_packetCutoff_level_le_width_of_le
      hKlower hσlim hnle hanti
  · exact (hanti (Nat.zero_le n)).trans_lt hKupper

theorem test_packet_initial_block_bound
    {d t ell : ℝ} {r v : ℕ → ℝ} {b : ℕ}
    (hd : 0 ≤ d)
    (ht : 0 ≤ t)
    (hwidth : ∀ n ∈ Finset.range (b + 1),
      intrinsicWidth d r v n < 2 * ell)
    (hwidthpos : ∀ n, 0 < intrinsicWidth d r v n)
    (hv : ∀ n, 0 ≤ v n) :
    (∑ n ∈ Finset.range (b + 1),
        expIncrement v n *
          Real.exp (-d * t / intrinsicWidth d r v n)) ≤
      (Real.exp (prefixMass v b) - 1) *
        Real.exp (-d * t / (2 * ell)) := by
  calc
    (∑ n ∈ Finset.range (b + 1),
        expIncrement v n *
          Real.exp (-d * t / intrinsicWidth d r v n)) ≤
        ∑ n ∈ Finset.range (b + 1),
          expIncrement v n * Real.exp (-d * t / (2 * ell)) := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (expIncrement_nonneg hv n)
      apply Real.exp_le_exp.mpr
      have hrate : d * t / (2 * ell) ≤
          d * t / intrinsicWidth d r v n :=
        div_le_div_of_nonneg_left
          (mul_nonneg hd ht)
          (hwidthpos n)
          (le_of_lt (hwidth n hn))
      calc
        -d * t / intrinsicWidth d r v n =
            -(d * t / intrinsicWidth d r v n) := by ring
        _ ≤ -(d * t / (2 * ell)) := neg_le_neg hrate
        _ = -d * t / (2 * ell) := by ring
    _ = (∑ n ∈ Finset.range (b + 1), expIncrement v n) *
        Real.exp (-d * t / (2 * ell)) := by
      rw [Finset.sum_mul]
    _ = (Real.exp (prefixMass v b) - 1) *
        Real.exp (-d * t / (2 * ell)) := by
      rw [sum_expIncrement v b]

lemma test_sum_range_eq_add_sum_Ioc
    {α : Type*} [AddCommGroup α] (f : ℕ → α) {a b : ℕ}
    (hab : a ≤ b) :
    (∑ n ∈ Finset.range (b + 1), f n) =
      (∑ n ∈ Finset.range (a + 1), f n) +
        ∑ n ∈ Finset.Ioc a b, f n := by
  have hIoc : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
    ext n
    simp
  rw [hIoc, Finset.sum_Ico_eq_sub _ (Nat.add_le_add_right hab 1)]
  abel

noncomputable def test_packetCoefficient
    (d : ℝ) (r v : ℕ → ℝ) (K k : ℕ) : ℝ :=
  match k with
  | 0 => Real.exp (prefixMass v (test_packetCutoff d r v K 0)) - 1
  | j + 1 =>
      Real.exp (prefixMass v (test_packetCutoff d r v K (j + 1))) -
        Real.exp (prefixMass v (test_packetCutoff d r v K j))

lemma test_packetCoefficient_nonneg
    {d : ℝ} {r v : ℕ → ℝ} {K : ℕ}
    (hv : ∀ n, 0 ≤ v n)
    (hcutmono : Monotone (test_packetCutoff d r v K))
    (k : ℕ) :
    0 ≤ test_packetCoefficient d r v K k := by
  cases k with
  | zero =>
      rw [test_packetCoefficient]
      exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr
        (Finset.sum_nonneg fun _ _ => hv _))
  | succ k =>
      rw [test_packetCoefficient]
      exact sub_nonneg.mpr (Real.exp_le_exp.mpr
        (prefixMass_mono hv (hcutmono (Nat.le_succ k))))

theorem test_finite_packet_grouping
    {d t : ℝ} {r v : ℕ → ℝ} {K M : ℕ}
    (hd : 0 < d) (ht : 0 ≤ t)
    (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (hKlower : test_dyadicLevel K ≤ intrinsicWidth d r v 0)
    (hKupper : intrinsicWidth d r v 0 < 2 * test_dyadicLevel K) :
    (∑ n ∈ Finset.range (test_packetCutoff d r v K M + 1),
        expIncrement v n *
          Real.exp (-d * t / intrinsicWidth d r v n)) ≤
      ∑ k ∈ Finset.range (M + 1),
        test_packetCoefficient d r v K k *
          Real.exp (-d * t / (2 * test_dyadicLevel (K + k))) := by
  have hσlim := intrinsicWidth_tendsto_zero hd hr hv hrlim
  have hσanti := intrinsicWidth_antitone hd hr hv hmono
  have hcutmono := test_packetCutoff_monotone hKlower hσlim
  induction M with
  | zero =>
      simpa [test_packetCoefficient] using
        test_packet_initial_block_bound hd.le ht
          (fun n hn => (test_packetCutoff_initial_block_width
            hKlower hKupper hσlim hσanti hn).2)
          (intrinsicWidth_pos hd hr hv) hv
  | succ M ih =>
      rw [test_sum_range_eq_add_sum_Ioc _
        (hcutmono (Nat.le_succ M))]
      calc
        (∑ n ∈ Finset.range (test_packetCutoff d r v K M + 1),
            expIncrement v n *
              Real.exp (-d * t / intrinsicWidth d r v n)) +
            (∑ n ∈ Finset.Ioc (test_packetCutoff d r v K M)
              (test_packetCutoff d r v K (M + 1)),
              expIncrement v n *
                Real.exp (-d * t / intrinsicWidth d r v n)) ≤
          (∑ k ∈ Finset.range (M + 1),
            test_packetCoefficient d r v K k *
              Real.exp (-d * t / (2 * test_dyadicLevel (K + k)))) +
            (Real.exp (prefixMass v
                (test_packetCutoff d r v K (M + 1))) -
              Real.exp (prefixMass v
                (test_packetCutoff d r v K M))) *
              Real.exp (-d * t /
                (2 * test_dyadicLevel (K + (M + 1)))) := by
            gcongr
            exact packet_block_bound hd.le ht
              (fun n hn => (test_packetCutoff_block_width
                hKlower hσlim hσanti hn).2)
              (intrinsicWidth_pos hd hr hv) hv
              (hcutmono (Nat.le_succ M))
        _ = ∑ k ∈ Finset.range (M + 1 + 1),
              test_packetCoefficient d r v K k *
                Real.exp (-d * t / (2 * test_dyadicLevel (K + k))) := by
          symm
          conv_lhs => rw [Finset.sum_range_succ]
          rw [test_packetCoefficient.eq_def]

noncomputable def test_packetTerm
    (d t : ℝ) (r v : ℕ → ℝ) (K k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (test_packetCoefficient d r v K k) *
    ENNReal.ofReal
      (Real.exp (-d * t / (2 * test_dyadicLevel (K + k))))

theorem test_finite_packet_grouping_ennreal
    {d t : ℝ} {r v : ℕ → ℝ} {K M : ℕ}
    (hd : 0 < d) (ht : 0 ≤ t)
    (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (hKlower : test_dyadicLevel K ≤ intrinsicWidth d r v 0)
    (hKupper : intrinsicWidth d r v 0 < 2 * test_dyadicLevel K) :
    ENNReal.ofReal
      (∑ n ∈ Finset.range (test_packetCutoff d r v K M + 1),
        expIncrement v n *
          Real.exp (-d * t / intrinsicWidth d r v n)) ≤
      ∑' k : ℕ, test_packetTerm d t r v K k := by
  have hσlim := intrinsicWidth_tendsto_zero hd hr hv hrlim
  have hcutmono := test_packetCutoff_monotone hKlower hσlim
  have hreal := test_finite_packet_grouping
    hd ht hr hv hmono hrlim hKlower hKupper (M := M)
  calc
    ENNReal.ofReal
        (∑ n ∈ Finset.range (test_packetCutoff d r v K M + 1),
          expIncrement v n *
            Real.exp (-d * t / intrinsicWidth d r v n)) ≤
      ENNReal.ofReal
        (∑ k ∈ Finset.range (M + 1),
          test_packetCoefficient d r v K k *
            Real.exp (-d * t / (2 * test_dyadicLevel (K + k)))) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ∑ k ∈ Finset.range (M + 1),
          ENNReal.ofReal
            (test_packetCoefficient d r v K k *
              Real.exp (-d * t / (2 * test_dyadicLevel (K + k)))) := by
      apply ENNReal.ofReal_sum_of_nonneg
      intro k _
      exact mul_nonneg
        (test_packetCoefficient_nonneg hv hcutmono k)
        (Real.exp_pos _).le
    _ = ∑ k ∈ Finset.range (M + 1),
          test_packetTerm d t r v K k := by
      apply Finset.sum_congr rfl
      intro k _
      unfold test_packetTerm
      rw [ENNReal.ofReal_mul
        (test_packetCoefficient_nonneg hv hcutmono k)]
    _ ≤ ∑' k : ℕ, test_packetTerm d t r v K k :=
      ENNReal.sum_le_tsum _

theorem test_finite_ungrouped_le_packet_tsum
    {d t : ℝ} {r v : ℕ → ℝ} {K N : ℕ}
    (hd : 0 < d) (ht : 0 ≤ t)
    (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (hKlower : test_dyadicLevel K ≤ intrinsicWidth d r v 0)
    (hKupper : intrinsicWidth d r v 0 < 2 * test_dyadicLevel K) :
    ENNReal.ofReal
      (∑ n ∈ Finset.range (N + 1),
        expIncrement v n *
          Real.exp (-d * t / intrinsicWidth d r v n)) ≤
      ∑' k : ℕ, test_packetTerm d t r v K k := by
  have hcutlim := test_packetCutoff_tendsto_atTop
    hd hr hv hrlim (K := K)
  obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.mp hcutlim N
  have hNM : N ≤ test_packetCutoff d r v K M := hM M le_rfl
  have hsumle :
      (∑ n ∈ Finset.range (N + 1),
        expIncrement v n *
          Real.exp (-d * t / intrinsicWidth d r v n)) ≤
      ∑ n ∈ Finset.range (test_packetCutoff d r v K M + 1),
        expIncrement v n *
          Real.exp (-d * t / intrinsicWidth d r v n) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.succ_le_succ hNM))
    intro n _ _
    exact mul_nonneg (expIncrement_nonneg hv n) (Real.exp_pos _).le
  exact (ENNReal.ofReal_le_ofReal hsumle).trans
    (test_finite_packet_grouping_ennreal
      hd ht hr hv hmono hrlim hKlower hKupper (M := M))

lemma test_exists_radius_active_prefix
    {r : ℕ → ℝ} {t : ℝ}
    (ht : 0 < t) (ht0 : t < r 0)
    (hrlim : Tendsto r atTop (nhds 0)) :
    ∃ N : ℕ, r (N + 1) ≤ t ∧ t < r N := by
  have hevent : ∀ᶠ n in atTop, r n < t :=
    hrlim.eventually_lt_const ht
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevent
  have hex : ∃ n : ℕ, r n ≤ t := ⟨M, (hM M le_rfl).le⟩
  let J := Nat.find hex
  have hJlower : r J ≤ t := Nat.find_spec hex
  have hJne : J ≠ 0 := by
    intro hJ
    exact (not_le_of_gt ht0) (by simpa [hJ] using hJlower)
  obtain ⟨N, hJN⟩ := Nat.exists_eq_succ_of_ne_zero hJne
  refine ⟨N, by simpa [hJN] using hJlower, ?_⟩
  apply lt_of_not_ge
  intro hNt
  have hfindle : J ≤ N := Nat.find_min' hex hNt
  omega

theorem test_coneSum_packet_domination
    {d t : ℝ} {r v : ℕ → ℝ} {K : ℕ}
    (hd : 0 < d) (ht : 0 < t)
    (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (hKlower : test_dyadicLevel K ≤ intrinsicWidth d r v 0)
    (hKupper : intrinsicWidth d r v 0 < 2 * test_dyadicLevel K) :
    ENNReal.ofReal (Real.exp (coneSum r v t)) ≤
      1 + ENNReal.ofReal (Real.exp d) *
        ∑' k : ℕ, test_packetTerm d t r v K k := by
  by_cases ht0 : t < r 0
  · obtain ⟨N, hlower, hupper⟩ :=
      test_exists_radius_active_prefix ht ht0 hrlim
    have hconePrefix : coneSum r v t = conePrefix r v N t := by
      rw [coneSum_eq_mass_sub_slope hr hmono hlower hupper]
      rw [conePrefix_eq_mass_sub_slope hr hmono hupper]
    let F : ℝ :=
      ∑ n ∈ Finset.range (N + 1),
        expIncrement v n *
          Real.exp (-d * t / intrinsicWidth d r v n)
    have hFnonneg : 0 ≤ F := by
      dsimp only [F]
      exact Finset.sum_nonneg fun n _ =>
        mul_nonneg (expIncrement_nonneg hv n) (Real.exp_pos _).le
    have hfinite : Real.exp (coneSum r v t) ≤
        1 + Real.exp d * F := by
      rw [hconePrefix]
      exact finite_packet_domination
        hd ht.le hr hv hmono hupper
    calc
      ENNReal.ofReal (Real.exp (coneSum r v t)) ≤
          ENNReal.ofReal (1 + Real.exp d * F) :=
        ENNReal.ofReal_le_ofReal hfinite
      _ = 1 + ENNReal.ofReal (Real.exp d) * ENNReal.ofReal F := by
        rw [ENNReal.ofReal_add (by norm_num)
          (mul_nonneg (Real.exp_pos d).le hFnonneg)]
        rw [ENNReal.ofReal_one]
        rw [ENNReal.ofReal_mul (Real.exp_pos d).le]
      _ ≤ 1 + ENNReal.ofReal (Real.exp d) *
          ∑' k : ℕ, test_packetTerm d t r v K k := by
        gcongr
        exact test_finite_ungrouped_le_packet_tsum
          hd ht.le hr hv hmono hrlim hKlower hKupper (N := N)
  · have hrle : ∀ n, r n ≤ t := by
      intro n
      exact (hmono (Nat.zero_le n)).trans (le_of_not_gt ht0)
    have hcone : coneSum r v t = 0 := by
      rw [coneSum]
      calc
        (∑' n, coneTerm r v n t) = ∑' _n : ℕ, (0 : ℝ) := by
          apply tsum_congr
          intro n
          simp [coneTerm, coneProfile_eq_zero_of_le (hr n) (hrle n)]
        _ = 0 := by simp
    rw [hcone, Real.exp_zero, ENNReal.ofReal_one]
    exact le_add_of_nonneg_right zero_le

lemma test_packetCutoff_slope_le
    {d : ℝ} {r v : ℕ → ℝ} {K k : ℕ}
    (hd : 0 < d) (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hK : test_dyadicLevel K ≤ intrinsicWidth d r v 0)
    (hrlim : Tendsto r atTop (nhds 0)) :
    test_dyadicLevel (K + k) *
        prefixSlope r v (test_packetCutoff d r v K k) ≤ d := by
  have hσlim := intrinsicWidth_tendsto_zero hd hr hv hrlim
  exact (level_bounds_of_le_intrinsicWidth hd.le hr hv
    (test_packetCutoff_level_mem hK hσlim)).2

lemma test_packetCutoff_radius_lower
    {d : ℝ} {r v : ℕ → ℝ} {K k n : ℕ}
    (hd : 0 < d) (hr : ∀ i, 0 < r i) (hv : ∀ i, 0 ≤ v i)
    (hmono : Antitone r)
    (hK : test_dyadicLevel K ≤ intrinsicWidth d r v 0)
    (hrlim : Tendsto r atTop (nhds 0))
    (hn : n ≤ test_packetCutoff d r v K k) :
    test_dyadicLevel (K + k) ≤ r n := by
  have hσlim := intrinsicWidth_tendsto_zero hd hr hv hrlim
  have hσanti := intrinsicWidth_antitone hd hr hv hmono
  exact (test_packetCutoff_level_le_width_of_le
    hK hσlim hn hσanti).trans (intrinsicWidth_le_radius d r v n)

theorem test_exists_intrinsic_packet_start
    {d : ℝ} {r v : ℕ → ℝ}
    (hd : 0 < d) (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hr0lt : r 0 < 1) :
    ∃ K : ℕ,
      test_dyadicLevel K ≤ intrinsicWidth d r v 0 ∧
        intrinsicWidth d r v 0 < 2 * test_dyadicLevel K := by
  apply test_exists_dyadic_bracket
  · exact intrinsicWidth_pos hd hr hv 0
  · exact (intrinsicWidth_le_radius d r v 0).trans_lt hr0lt

theorem test_exists_coneSum_packet_domination
    {d : ℝ} {r v : ℕ → ℝ}
    (hd : 0 < d)
    (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (hr0lt : r 0 < 1) :
    ∃ K : ℕ,
      test_dyadicLevel K ≤ intrinsicWidth d r v 0 ∧
      intrinsicWidth d r v 0 < 2 * test_dyadicLevel K ∧
      Monotone (test_packetCutoff d r v K) ∧
      Tendsto (test_packetCutoff d r v K) atTop atTop ∧
      (∀ k,
        test_dyadicLevel (K + k) *
          prefixSlope r v (test_packetCutoff d r v K k) ≤ d) ∧
      (∀ k n, n ≤ test_packetCutoff d r v K k →
        test_dyadicLevel (K + k) ≤ r n) ∧
      ∀ t, 0 < t →
        ENNReal.ofReal (Real.exp (coneSum r v t)) ≤
          1 + ENNReal.ofReal (Real.exp d) *
            ∑' k : ℕ, test_packetTerm d t r v K k := by
  obtain ⟨K, hKlower, hKupper⟩ :=
    test_exists_intrinsic_packet_start hd hr hv hr0lt
  have hσlim := intrinsicWidth_tendsto_zero hd hr hv hrlim
  refine ⟨K, hKlower, hKupper,
    test_packetCutoff_monotone hKlower hσlim,
    test_packetCutoff_tendsto_atTop hd hr hv hrlim,
    ?_, ?_, ?_⟩
  · intro k
    exact test_packetCutoff_slope_le hd hr hv hKlower hrlim
  · intro k n hn
    exact test_packetCutoff_radius_lower
      hd hr hv hmono hKlower hrlim hn
  · intro t ht
    exact test_coneSum_packet_domination
      hd ht hr hv hmono hrlim hKlower hKupper

noncomputable abbrev intrinsicCutoff
    (d ell : ℝ) (r v : ℕ → ℝ) : ℕ :=
  test_intrinsicCutoff d ell r v

noncomputable abbrev dyadicLevel : ℕ → ℝ := test_dyadicLevel

noncomputable abbrev packetCutoff
    (d : ℝ) (r v : ℕ → ℝ) (K k : ℕ) : ℕ :=
  test_packetCutoff d r v K k

noncomputable abbrev packetCoefficient
    (d : ℝ) (r v : ℕ → ℝ) (K k : ℕ) : ℝ :=
  test_packetCoefficient d r v K k

noncomputable abbrev packetTerm
    (d t : ℝ) (r v : ℕ → ℝ) (K k : ℕ) : ℝ≥0∞ :=
  test_packetTerm d t r v K k

theorem intrinsic_laplace_packet_domination
    {d : ℝ} {r v : ℕ → ℝ}
    (hd : 0 < d)
    (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (hr0lt : r 0 < 1) :
    ∃ K : ℕ,
      dyadicLevel K ≤ intrinsicWidth d r v 0 ∧
      intrinsicWidth d r v 0 < 2 * dyadicLevel K ∧
      Monotone (packetCutoff d r v K) ∧
      Tendsto (packetCutoff d r v K) atTop atTop ∧
      (∀ k,
        dyadicLevel (K + k) *
          prefixSlope r v (packetCutoff d r v K k) ≤ d) ∧
      (∀ k n, n ≤ packetCutoff d r v K k →
        dyadicLevel (K + k) ≤ r n) ∧
      ∀ t, 0 < t →
        ENNReal.ofReal (Real.exp (coneSum r v t)) ≤
          1 + ENNReal.ofReal (Real.exp d) *
            ∑' k : ℕ, packetTerm d t r v K k := by
  exact test_exists_coneSum_packet_domination
    hd hr hv hmono hrlim hr0lt

end Shepp.Section2
end SheppFlattenedModule017

section SheppFlattenedModule018
open scoped BigOperators ENNReal Pointwise
open MeasureTheory Filter Set

namespace Shepp.Section2

noncomputable def test_laplaceMoment (d : ℕ) : ℝ≥0∞ :=
  ∫⁻ s in Set.Ioi (0 : ℝ),
    ENNReal.ofReal (s ^ (d - 1)) *
      ENNReal.ofReal (Real.exp (-(d : ℝ) * s / 2)) ∂volume

lemma test_laplaceMoment_lt_top (d : ℕ) (hd : 0 < d) :
    test_laplaceMoment d < ∞ := by
  let f : ℝ → ℝ := fun s =>
    Real.exp (-(d : ℝ) * s / 2) * s ^ (d - 1)
  have hf : IntegrableOn f (Set.Ioi (0 : ℝ)) volume := by
    have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := ((d - 1 : ℕ) : ℝ))
      (b := (d : ℝ) / 2)
      (by
        have h : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by positivity
        linarith) (by norm_num)
      (by positivity : 0 < (d : ℝ) / 2)
    apply hbase.congr_fun
    · intro s hs
      dsimp only [f]
      rw [Real.rpow_natCast, Real.rpow_one]
      have hexp : -(d : ℝ) * s / 2 = -((d : ℝ) / 2) * s := by ring
      rw [hexp]
      ring
    · exact measurableSet_Ioi
  have hlt := hf.setLIntegral_lt_top
  unfold test_laplaceMoment
  apply lt_of_eq_of_lt _ hlt
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only [f]
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  ac_rfl

noncomputable def test_laplaceBaseIntegral (d : ℕ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Set.Ioc 0 R,
    ENNReal.ofReal (s ^ (d - 1)) *
      ENNReal.ofReal (Real.exp (-(d : ℝ) * s / 2)) ∂volume

noncomputable def test_laplaceKernelIntegral
    (d : ℕ) (ell R : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioc 0 R,
    ENNReal.ofReal (t ^ (d - 1)) *
      ENNReal.ofReal (Real.exp (-(d : ℝ) * t / (2 * ell))) ∂volume

theorem test_laplaceKernelIntegral_scaling
    (d : ℕ) (hd : 0 < d) {ell R : ℝ} (hell : 0 < ell) :
    test_laplaceKernelIntegral d ell R =
      ENNReal.ofReal (ell ^ d) *
        test_laplaceBaseIntegral d (R / ell) := by
  let g : ℝ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (y ^ (d - 1)) *
      ENNReal.ofReal (Real.exp (-(d : ℝ) * y / (2 * ell)))
  have hchange := setLIntegral_comp_mul_left g
    (Set.Ioc 0 (R / ell)) hell
  have hset : ell • Set.Ioc (0 : ℝ) (R / ell) = Set.Ioc 0 R := by
    rw [LinearOrderedField.smul_Ioc hell, mul_zero]
    congr 1
    field_simp [hell.ne']
  rw [hset] at hchange
  have hleft :
      (∫⁻ s in Set.Ioc 0 (R / ell), g (ell * s) ∂volume) =
        ENNReal.ofReal (ell ^ (d - 1)) *
          test_laplaceBaseIntegral d (R / ell) := by
    calc
      (∫⁻ s in Set.Ioc 0 (R / ell), g (ell * s) ∂volume) =
          ∫⁻ s in Set.Ioc 0 (R / ell),
            ENNReal.ofReal (ell ^ (d - 1)) *
              (ENNReal.ofReal (s ^ (d - 1)) *
                ENNReal.ofReal (Real.exp (-(d : ℝ) * s / 2))) ∂volume := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro s hs
        dsimp only [g]
        rw [mul_pow]
        rw [ENNReal.ofReal_mul (pow_nonneg hell.le (d - 1))]
        have hexp : -(d : ℝ) * (ell * s) / (2 * ell) =
            -(d : ℝ) * s / 2 := by field_simp [hell.ne']
        rw [hexp]
        exact mul_assoc _ _ _
      _ = ENNReal.ofReal (ell ^ (d - 1)) *
          test_laplaceBaseIntegral d (R / ell) := by
        rw [MeasureTheory.lintegral_const_mul]
        · rfl
        · fun_prop
  have hscaled :
      ENNReal.ofReal (ell ^ (d - 1)) *
          test_laplaceBaseIntegral d (R / ell) =
        ENNReal.ofReal ell⁻¹ * test_laplaceKernelIntegral d ell R := by
    rw [← hleft]
    simpa only [g, test_laplaceKernelIntegral] using hchange
  have hinv : ENNReal.ofReal ell * ENNReal.ofReal ell⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hell.le]
    simp [hell.ne']
  have hpow : ell * ell ^ (d - 1) = ell ^ d := by
    calc
      ell * ell ^ (d - 1) = ell ^ (d - 1) * ell := mul_comm _ _
      _ = ell ^ ((d - 1) + 1) := (pow_succ ell (d - 1)).symm
      _ = ell ^ d := by congr 1; omega
  calc
    test_laplaceKernelIntegral d ell R =
        (ENNReal.ofReal ell * ENNReal.ofReal ell⁻¹) *
          test_laplaceKernelIntegral d ell R := by rw [hinv, one_mul]
    _ = ENNReal.ofReal ell *
        (ENNReal.ofReal ell⁻¹ * test_laplaceKernelIntegral d ell R) := by
      ac_rfl
    _ = ENNReal.ofReal ell *
        (ENNReal.ofReal (ell ^ (d - 1)) *
          test_laplaceBaseIntegral d (R / ell)) := by rw [hscaled]
    _ = (ENNReal.ofReal ell * ENNReal.ofReal (ell ^ (d - 1))) *
        test_laplaceBaseIntegral d (R / ell) := by ac_rfl
    _ = ENNReal.ofReal (ell ^ d) *
        test_laplaceBaseIntegral d (R / ell) := by
      rw [← ENNReal.ofReal_mul hell.le, hpow]

lemma test_laplaceBaseIntegral_le_moment (d : ℕ) (R : ℝ) :
    test_laplaceBaseIntegral d R ≤ test_laplaceMoment d := by
  unfold test_laplaceBaseIntegral test_laplaceMoment
  exact lintegral_mono'
    (Measure.restrict_mono_set (μ := volume) Set.Ioc_subset_Ioi_self) le_rfl

theorem test_laplaceKernelIntegral_le
    (d : ℕ) (hd : 0 < d) {ell R : ℝ} (hell : 0 < ell) :
    test_laplaceKernelIntegral d ell R ≤
      ENNReal.ofReal (ell ^ d) * test_laplaceMoment d := by
  rw [test_laplaceKernelIntegral_scaling d hd hell]
  gcongr
  exact test_laplaceBaseIntegral_le_moment d (R / ell)

noncomputable def test_packetMassTerm
    (d : ℕ) (r v : ℕ → ℝ) (K k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (dyadicLevel (K + k) ^ d) *
    ENNReal.ofReal (packetCoefficient (d : ℝ) r v K k)

noncomputable def test_packetIncrementMass
    (d : ℕ) (r v : ℕ → ℝ) (K : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, test_packetMassTerm d r v K k

lemma test_measurable_packetTerm
    (d : ℝ) (r v : ℕ → ℝ) (K k : ℕ) :
    Measurable (fun t => packetTerm d t r v K k) := by
  unfold packetTerm test_packetTerm
  fun_prop

lemma test_measurable_weight_mul_packetTerm
    (d : ℕ) (r v : ℕ → ℝ) (K k : ℕ) :
    Measurable (fun t : ℝ =>
      ENNReal.ofReal (t ^ (d - 1)) *
        packetTerm (d : ℝ) t r v K k) := by
  have hweight : Measurable (fun t : ℝ =>
      ENNReal.ofReal (t ^ (d - 1))) := by fun_prop
  have hpacket := test_measurable_packetTerm (d : ℝ) r v K k
  exact hweight.mul hpacket

theorem test_setLIntegral_weight_mul_packetTerm_le
    (d : ℕ) (hd : 0 < d) {r v : ℕ → ℝ} {K k : ℕ}
    {R : ℝ} :
    (∫⁻ t in Set.Ioc 0 R,
      ENNReal.ofReal (t ^ (d - 1)) *
        packetTerm (d : ℝ) t r v K k ∂volume) ≤
      test_laplaceMoment d * test_packetMassTerm d r v K k := by
  have hell : 0 < dyadicLevel (K + k) := by
    exact test_dyadicLevel_pos (K + k)
  have hkernel := test_laplaceKernelIntegral_le d hd
    (R := R) hell
  unfold packetTerm test_packetTerm
  calc
    (∫⁻ t in Set.Ioc 0 R,
      ENNReal.ofReal (t ^ (d - 1)) *
        (ENNReal.ofReal (packetCoefficient (d : ℝ) r v K k) *
          ENNReal.ofReal (Real.exp (-(d : ℝ) * t /
            (2 * dyadicLevel (K + k))))) ∂volume) =
        ∫⁻ t in Set.Ioc 0 R,
          ENNReal.ofReal (packetCoefficient (d : ℝ) r v K k) *
            (ENNReal.ofReal (t ^ (d - 1)) *
              ENNReal.ofReal (Real.exp (-(d : ℝ) * t /
                (2 * dyadicLevel (K + k))))) ∂volume := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro t _
      ac_rfl
    _ = ENNReal.ofReal (packetCoefficient (d : ℝ) r v K k) *
        test_laplaceKernelIntegral d (dyadicLevel (K + k)) R := by
      rw [MeasureTheory.lintegral_const_mul]
      · rfl
      · fun_prop
    _ ≤ ENNReal.ofReal (packetCoefficient (d : ℝ) r v K k) *
        (ENNReal.ofReal (dyadicLevel (K + k) ^ d) *
          test_laplaceMoment d) := by gcongr
    _ = test_laplaceMoment d * test_packetMassTerm d r v K k := by
      unfold test_packetMassTerm
      ac_rfl

theorem test_setLIntegral_weight_mul_packet_tsum_le
    (d : ℕ) (hd : 0 < d) {r v : ℕ → ℝ} {K : ℕ}
    {R : ℝ} :
    (∫⁻ t in Set.Ioc 0 R,
      ENNReal.ofReal (t ^ (d - 1)) *
        (∑' k : ℕ, packetTerm (d : ℝ) t r v K k) ∂volume) ≤
      test_laplaceMoment d * test_packetIncrementMass d r v K := by
  calc
    (∫⁻ t in Set.Ioc 0 R,
      ENNReal.ofReal (t ^ (d - 1)) *
        (∑' k : ℕ, packetTerm (d : ℝ) t r v K k) ∂volume) =
        ∫⁻ t in Set.Ioc 0 R,
          ∑' k : ℕ,
            ENNReal.ofReal (t ^ (d - 1)) *
              packetTerm (d : ℝ) t r v K k ∂volume := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro t _
      exact (ENNReal.tsum_mul_left).symm
    _ = ∑' k : ℕ,
        ∫⁻ t in Set.Ioc 0 R,
          ENNReal.ofReal (t ^ (d - 1)) *
            packetTerm (d : ℝ) t r v K k ∂volume := by
      exact lintegral_tsum fun k =>
        (test_measurable_weight_mul_packetTerm d r v K k).aemeasurable
    _ ≤ ∑' k : ℕ,
        test_laplaceMoment d * test_packetMassTerm d r v K k := by
      exact ENNReal.tsum_le_tsum fun k =>
        test_setLIntegral_weight_mul_packetTerm_le d hd
    _ = test_laplaceMoment d * test_packetIncrementMass d r v K := by
      rw [test_packetIncrementMass, ENNReal.tsum_mul_left]

noncomputable def test_polynomialRadialIntegral (d : ℕ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioc 0 R, ENNReal.ofReal (t ^ (d - 1)) ∂volume

lemma test_polynomialRadialIntegral_lt_top (d : ℕ) (R : ℝ) :
    test_polynomialRadialIntegral d R < ∞ := by
  have hf : IntegrableOn (fun t : ℝ => t ^ (d - 1))
      (Set.Ioc 0 R) volume := by
    exact (continuous_pow (d - 1)).integrableOn_Ioc
  exact hf.setLIntegral_lt_top

noncomputable def test_coneRealRadialIntegral
    (d : ℕ) (r v : ℕ → ℝ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioc 0 R,
    ENNReal.ofReal (t ^ (d - 1)) *
      ENNReal.ofReal (Real.exp (coneSum r v t)) ∂volume

noncomputable def test_packetSeries
    (d : ℕ) (r v : ℕ → ℝ) (K : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, packetTerm (d : ℝ) t r v K k

noncomputable def test_conePacketMajorant
    (d : ℕ) (r v : ℕ → ℝ) (K : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (t ^ (d - 1)) +
    ENNReal.ofReal (Real.exp (d : ℝ)) *
      (ENNReal.ofReal (t ^ (d - 1)) * test_packetSeries d r v K t)

lemma test_measurable_packetSeries
    (d : ℕ) (r v : ℕ → ℝ) (K : ℕ) :
    Measurable (test_packetSeries d r v K) := by
  unfold test_packetSeries
  apply Measurable.tsum
  intro k
  exact test_measurable_packetTerm (d : ℝ) r v K k

lemma test_measurable_conePacketMajorant
    (d : ℕ) (r v : ℕ → ℝ) (K : ℕ) :
    Measurable (test_conePacketMajorant d r v K) := by
  unfold test_conePacketMajorant
  have hweight : Measurable (fun t : ℝ =>
      ENNReal.ofReal (t ^ (d - 1))) := by fun_prop
  exact hweight.add (measurable_const.mul
    (hweight.mul (test_measurable_packetSeries d r v K)))

theorem test_coneRadialIntegrand_le_packetMajorant
    (d : ℕ) (hd : 0 < d) {r v : ℕ → ℝ} {K : ℕ}
    (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (hKlower : dyadicLevel K ≤ intrinsicWidth (d : ℝ) r v 0)
    (hKupper : intrinsicWidth (d : ℝ) r v 0 < 2 * dyadicLevel K)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (d - 1)) *
        ENNReal.ofReal (Real.exp (coneSum r v t)) ≤
      test_conePacketMajorant d r v K t := by
  have hdom := test_coneSum_packet_domination
    (show 0 < (d : ℝ) by exact_mod_cast hd) ht
    hr hv hmono hrlim hKlower hKupper
  unfold test_conePacketMajorant test_packetSeries
  calc
    ENNReal.ofReal (t ^ (d - 1)) *
        ENNReal.ofReal (Real.exp (coneSum r v t)) ≤
      ENNReal.ofReal (t ^ (d - 1)) *
          (1 + ENNReal.ofReal (Real.exp (d : ℝ)) *
          ∑' k : ℕ, packetTerm (d : ℝ) t r v K k) :=
      mul_le_mul_of_nonneg_left hdom zero_le
    _ = ENNReal.ofReal (t ^ (d - 1)) +
        ENNReal.ofReal (Real.exp (d : ℝ)) *
          (ENNReal.ofReal (t ^ (d - 1)) *
            ∑' k : ℕ, packetTerm (d : ℝ) t r v K k) := by
      rw [mul_add, mul_one]
      congr 1
      ac_rfl

theorem test_setLIntegral_conePacketMajorant_eq
    (d : ℕ) (r v : ℕ → ℝ) (K : ℕ) (R : ℝ) :
    (∫⁻ t in Set.Ioc 0 R,
      test_conePacketMajorant d r v K t ∂volume) =
      test_polynomialRadialIntegral d R +
        ENNReal.ofReal (Real.exp (d : ℝ)) *
          (∫⁻ t in Set.Ioc 0 R,
            ENNReal.ofReal (t ^ (d - 1)) *
              test_packetSeries d r v K t ∂volume) := by
  unfold test_conePacketMajorant test_polynomialRadialIntegral
  rw [MeasureTheory.lintegral_add_left]
  · rw [lintegral_const_mul'
      (μ := volume.restrict (Set.Ioc 0 R))
      (ENNReal.ofReal (Real.exp (d : ℝ)))
      (fun t => ENNReal.ofReal (t ^ (d - 1)) *
        test_packetSeries d r v K t)
      ENNReal.ofReal_ne_top]
  · fun_prop

theorem test_coneRealRadialIntegral_le_packetMass
    (d : ℕ) (hd : 0 < d) {r v : ℕ → ℝ} {K : ℕ}
    (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (hKlower : dyadicLevel K ≤ intrinsicWidth (d : ℝ) r v 0)
    (hKupper : intrinsicWidth (d : ℝ) r v 0 < 2 * dyadicLevel K)
    (R : ℝ) :
    test_coneRealRadialIntegral d r v R ≤
      test_polynomialRadialIntegral d R +
        ENNReal.ofReal (Real.exp (d : ℝ)) *
          (test_laplaceMoment d * test_packetIncrementMass d r v K) := by
  calc
    test_coneRealRadialIntegral d r v R ≤
        ∫⁻ t in Set.Ioc 0 R,
          test_conePacketMajorant d r v K t ∂volume := by
      unfold test_coneRealRadialIntegral
      apply setLIntegral_mono
        (test_measurable_conePacketMajorant d r v K)
      intro t ht
      exact test_coneRadialIntegrand_le_packetMajorant
        d hd hr hv hmono hrlim hKlower hKupper ht.1
    _ = test_polynomialRadialIntegral d R +
        ENNReal.ofReal (Real.exp (d : ℝ)) *
          (∫⁻ t in Set.Ioc 0 R,
            ENNReal.ofReal (t ^ (d - 1)) *
              test_packetSeries d r v K t ∂volume) :=
      test_setLIntegral_conePacketMajorant_eq d r v K R
    _ ≤ test_polynomialRadialIntegral d R +
        ENNReal.ofReal (Real.exp (d : ℝ)) *
          (test_laplaceMoment d * test_packetIncrementMass d r v K) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ zero_le
      unfold test_packetSeries
      exact test_setLIntegral_weight_mul_packet_tsum_le d hd

theorem test_divergent_increment_mass_of_cone
    (d : ℕ) (hd : 0 < d) {r v : ℕ → ℝ} {K : ℕ}
    (hr : ∀ n, 0 < r n) (hv : ∀ n, 0 ≤ v n)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (hKlower : dyadicLevel K ≤ intrinsicWidth (d : ℝ) r v 0)
    (hKupper : intrinsicWidth (d : ℝ) r v 0 < 2 * dyadicLevel K)
    {R : ℝ} (hdiv : test_coneRealRadialIntegral d r v R = ∞) :
    test_packetIncrementMass d r v K = ∞ := by
  by_contra hmass
  have hmasslt : test_packetIncrementMass d r v K < ∞ :=
    lt_top_iff_ne_top.mpr hmass
  have hmomentlt : test_laplaceMoment d < ∞ :=
    test_laplaceMoment_lt_top d hd
  have hinnerlt : test_laplaceMoment d *
      test_packetIncrementMass d r v K < ∞ :=
    ENNReal.mul_lt_top hmomentlt hmasslt
  have hscaledlt : ENNReal.ofReal (Real.exp (d : ℝ)) *
      (test_laplaceMoment d * test_packetIncrementMass d r v K) < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hinnerlt
  have hrhslt : test_polynomialRadialIntegral d R +
      ENNReal.ofReal (Real.exp (d : ℝ)) *
        (test_laplaceMoment d * test_packetIncrementMass d r v K) < ∞ :=
    ENNReal.add_lt_top.2
      ⟨test_polynomialRadialIntegral_lt_top d R, hscaledlt⟩
  have hle := test_coneRealRadialIntegral_le_packetMass
    d hd hr hv hmono hrlim hKlower hKupper R
  have htop_le : (∞ : ℝ≥0∞) ≤
      test_polynomialRadialIntegral d R +
        ENNReal.ofReal (Real.exp (d : ℝ)) *
          (test_laplaceMoment d * test_packetIncrementMass d r v K) := by
    rw [← hdiv]
    exact hle
  exact (ne_of_lt hrhslt) (top_unique htop_le)

lemma test_coneRealRadialIntegral_radiusVolume_eq
    (d : ℕ) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (nhds 0))
    (R : ℝ) :
    test_coneRealRadialIntegral d r (radiusVolume d r) R =
      coneRadialIntegral d r R := by
  symm
  simpa only [test_coneRealRadialIntegral] using
    coneRadialIntegral_eq_real d hr hrlim R

theorem test_exists_divergent_intrinsic_packets
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    {R : ℝ} (hdiv : coneRadialIntegral d r R = ∞) :
    ∃ K : ℕ,
      dyadicLevel K ≤
        intrinsicWidth (d : ℝ) r (radiusVolume d r) 0 ∧
      intrinsicWidth (d : ℝ) r (radiusVolume d r) 0 <
        2 * dyadicLevel K ∧
      Monotone (packetCutoff (d : ℝ) r (radiusVolume d r) K) ∧
      Tendsto (packetCutoff (d : ℝ) r (radiusVolume d r) K)
        atTop atTop ∧
      (∀ k,
        dyadicLevel (K + k) *
          prefixSlope r (radiusVolume d r)
            (packetCutoff (d : ℝ) r (radiusVolume d r) K k) ≤ d) ∧
      (∀ k n,
        n ≤ packetCutoff (d : ℝ) r (radiusVolume d r) K k →
          dyadicLevel (K + k) ≤ r n) ∧
      (∑' k : ℕ,
        ENNReal.ofReal (dyadicLevel (K + k) ^ d) *
          ENNReal.ofReal
            (packetCoefficient (d : ℝ) r (radiusVolume d r) K k)) = ∞ := by
  have hv : ∀ n, 0 ≤ radiusVolume d r n := by
    intro n
    unfold radiusVolume
    exact mul_nonneg (euclideanUnitBallVolume_pos d).le
      (pow_nonneg (hr n).le d)
  have hr0lt : r 0 < 1 := (hrsmall 0).trans (by norm_num)
  obtain ⟨K, hKlower, hKupper, hcutmono, hcutlim,
      hslope, hradius, _hdom⟩ :=
    intrinsic_laplace_packet_domination
      (show 0 < (d : ℝ) by exact_mod_cast hd)
      hr hv hmono hrlim hr0lt
  refine ⟨K, hKlower, hKupper, hcutmono, hcutlim,
    hslope, hradius, ?_⟩
  have hreal :
      test_coneRealRadialIntegral d r (radiusVolume d r) R = ∞ := by
    rw [test_coneRealRadialIntegral_radiusVolume_eq d hr hrlim R]
    exact hdiv
  have hmass := test_divergent_increment_mass_of_cone
    d hd hr hv hmono hrlim hKlower hKupper hreal
  simpa only [test_packetIncrementMass, test_packetMassTerm] using hmass

noncomputable abbrev laplaceMoment (d : ℕ) : ℝ≥0∞ :=
  test_laplaceMoment d

noncomputable abbrev packetMassTerm
    (d : ℕ) (r v : ℕ → ℝ) (K k : ℕ) : ℝ≥0∞ :=
  test_packetMassTerm d r v K k

noncomputable abbrev packetIncrementMass
    (d : ℕ) (r v : ℕ → ℝ) (K : ℕ) : ℝ≥0∞ :=
  test_packetIncrementMass d r v K

theorem laplaceMoment_lt_top (d : ℕ) (hd : 0 < d) :
    laplaceMoment d < ∞ :=
  test_laplaceMoment_lt_top d hd

theorem divergent_increment_mass
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    {R : ℝ} (hdiv : coneRadialIntegral d r R = ∞) :
    ∃ K : ℕ,
      dyadicLevel K ≤
        intrinsicWidth (d : ℝ) r (radiusVolume d r) 0 ∧
      intrinsicWidth (d : ℝ) r (radiusVolume d r) 0 <
        2 * dyadicLevel K ∧
      Monotone (packetCutoff (d : ℝ) r (radiusVolume d r) K) ∧
      Tendsto (packetCutoff (d : ℝ) r (radiusVolume d r) K)
        atTop atTop ∧
      (∀ k,
        dyadicLevel (K + k) *
          prefixSlope r (radiusVolume d r)
            (packetCutoff (d : ℝ) r (radiusVolume d r) K k) ≤ d) ∧
      (∀ k n,
        n ≤ packetCutoff (d : ℝ) r (radiusVolume d r) K k →
          dyadicLevel (K + k) ≤ r n) ∧
      (∑' k : ℕ,
        ENNReal.ofReal (dyadicLevel (K + k) ^ d) *
          ENNReal.ofReal
            (packetCoefficient (d : ℝ) r (radiusVolume d r) K k)) = ∞ := by
  exact test_exists_divergent_intrinsic_packets
    d hd hr hrsmall hmono hrlim hdiv

theorem divergent_increment_mass_of_torus_overlap
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (htorus :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞) :
    ∃ K : ℕ,
      dyadicLevel K ≤
        intrinsicWidth (d : ℝ) r (radiusVolume d r) 0 ∧
      intrinsicWidth (d : ℝ) r (radiusVolume d r) 0 <
        2 * dyadicLevel K ∧
      Monotone (packetCutoff (d : ℝ) r (radiusVolume d r) K) ∧
      Tendsto (packetCutoff (d : ℝ) r (radiusVolume d r) K)
        atTop atTop ∧
      (∀ k,
        dyadicLevel (K + k) *
          prefixSlope r (radiusVolume d r)
            (packetCutoff (d : ℝ) r (radiusVolume d r) K k) ≤ d) ∧
      (∀ k n,
        n ≤ packetCutoff (d : ℝ) r (radiusVolume d r) K k →
          dyadicLevel (K + k) ≤ r n) ∧
      (∑' k : ℕ,
        ENNReal.ofReal (dyadicLevel (K + k) ^ d) *
          ENNReal.ofReal
            (packetCoefficient (d : ℝ) r (radiusVolume d r) K k)) = ∞ := by
  have hconeReal :=
    (cone_criterion d hd hr hrsmall hrlim ht₀).mp htorus
  have hcone : coneRadialIntegral d r t₀ = ∞ := by
    rw [coneRadialIntegral_eq_real d hr hrlim t₀]
    exact hconeReal
  exact divergent_increment_mass
    d (by omega) hr hrsmall hmono hrlim hcone

end Shepp.Section2
end SheppFlattenedModule018

section SheppFlattenedModule019
open scoped BigOperators ENNReal
open Filter MeasureTheory

namespace Shepp.Section3

open Shepp.Section2

structure GeometricPacketInterface (d : ℕ) (r : ℕ → ℝ) where
  K : ℕ

  radius_lt_quarter : ∀ n, r n < 1 / 4
  level_le_initial :
    dyadicLevel K ≤ intrinsicWidth (d : ℝ) r (radiusVolume d r) 0
  initial_lt_two_level :
    intrinsicWidth (d : ℝ) r (radiusVolume d r) 0 < 2 * dyadicLevel K
  cutoff_monotone :
    Monotone (packetCutoff (d : ℝ) r (radiusVolume d r) K)
  cutoff_tendsto :
    Tendsto (packetCutoff (d : ℝ) r (radiusVolume d r) K) atTop atTop
  level_mul_slope_le : ∀ k,
    dyadicLevel (K + k) *
      prefixSlope r (radiusVolume d r)
        (packetCutoff (d : ℝ) r (radiusVolume d r) K k) ≤ d
  level_le_radius : ∀ k n,
    n ≤ packetCutoff (d : ℝ) r (radiusVolume d r) K k →
      dyadicLevel (K + k) ≤ r n
  increment_mass_diverges :
    (∑' k : ℕ,
      ENNReal.ofReal (dyadicLevel (K + k) ^ d) *
        ENNReal.ofReal
          (packetCoefficient (d : ℝ) r (radiusVolume d r) K k)) = ∞

noncomputable abbrev GeometricPacketInterface.level
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) : ℝ :=
  dyadicLevel (P.K + k)

noncomputable abbrev GeometricPacketInterface.cutoff
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) : ℕ :=
  packetCutoff (d : ℝ) r (radiusVolume d r) P.K k

noncomputable abbrev GeometricPacketInterface.increment
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) : ℝ :=
  packetCoefficient (d : ℝ) r (radiusVolume d r) P.K k

theorem GeometricPacketInterface.radius_pos
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (n : ℕ) :
    0 < r n := by
  have hevent : ∀ᶠ k in atTop, n ≤ P.cutoff k :=
    (tendsto_atTop.1 P.cutoff_tendsto) n
  rcases hevent.exists with ⟨k, hk⟩
  exact (test_dyadicLevel_pos (P.K + k)).trans_le
    (P.level_le_radius k n hk)

theorem GeometricPacketInterface.radiusVolume_pos
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (n : ℕ) :
    0 < radiusVolume d r n := by
  exact mul_pos (euclideanUnitBallVolume_pos d) (pow_pos (P.radius_pos n) d)

theorem GeometricPacketInterface.radiusVolume_nonneg
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (n : ℕ) :
    0 ≤ radiusVolume d r n :=
  (P.radiusVolume_pos n).le

theorem exists_geometricPacketInterface_of_torus_overlap
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (htorus :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞) :
    Nonempty (GeometricPacketInterface d r) := by
  obtain ⟨K, hKlower, hKupper, hcutmono, hcutlim,
      hslope, hradius, hmass⟩ :=
    divergent_increment_mass_of_torus_overlap
      d hd hr hrsmall hmono hrlim ht₀ htorus
  exact ⟨{
    K := K
    radius_lt_quarter := hrsmall
    level_le_initial := hKlower
    initial_lt_two_level := hKupper
    cutoff_monotone := hcutmono
    cutoff_tendsto := hcutlim
    level_mul_slope_le := hslope
    level_le_radius := hradius
    increment_mass_diverges := hmass
  }⟩

end Shepp.Section3
end SheppFlattenedModule019

section SheppFlattenedModule020
open scoped BigOperators
open Filter

namespace Shepp.Section3

open Shepp.Section2

private theorem exists_gridRefinement (d : ℕ) :
    ∃ M : ℕ,
      dyadicLevel M < 1 / (2 * (Real.sqrt (d : ℝ) + 1)) := by
  have hthreshold : 0 < 1 / (2 * (Real.sqrt (d : ℝ) + 1)) := by
    positivity
  exact (test_dyadicLevel_tendsto_zero.eventually_lt_const hthreshold).exists

noncomputable def gridRefinement (d : ℕ) : ℕ :=
  Nat.find (exists_gridRefinement d)

noncomputable def gridEta (d : ℕ) : ℝ :=
  dyadicLevel (gridRefinement d)

theorem gridEta_lt_threshold (d : ℕ) :
    gridEta d < 1 / (2 * (Real.sqrt (d : ℝ) + 1)) := by
  exact Nat.find_spec (exists_gridRefinement d)

theorem gridEta_pos (d : ℕ) : 0 < gridEta d := by
  exact test_dyadicLevel_pos (gridRefinement d)

theorem sqrt_mul_gridEta_div_two_le_quarter (d : ℕ) :
    Real.sqrt (d : ℝ) / 2 * gridEta d ≤ 1 / 4 := by
  have hη := gridEta_lt_threshold d
  have hden : 0 < 2 * (Real.sqrt (d : ℝ) + 1) := by positivity
  have hmul : gridEta d * (2 * (Real.sqrt (d : ℝ) + 1)) < 1 := by
    exact (lt_div_iff₀ hden).mp (by simpa only [one_div] using hη)
  have hsqrt : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hηpos := gridEta_pos d
  nlinarith

noncomputable def gridSide {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) : ℕ :=
  2 ^ (gridRefinement d + P.K + k)

theorem gridSide_pos {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) :
    0 < gridSide P k := by
  simp [gridSide]

noncomputable def gridMesh {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) : ℝ :=
  ((gridSide P k : ℕ) : ℝ)⁻¹

theorem gridMesh_pos {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) :
    0 < gridMesh P k := by
  unfold gridMesh
  apply inv_pos.mpr
  exact_mod_cast gridSide_pos P k

theorem gridMesh_eq_eta_mul_level {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) :
    gridMesh P k = gridEta d * P.level k := by
  change (((2 ^ (gridRefinement d + P.K + k) : ℕ) : ℝ)⁻¹) =
    (1 / 2 : ℝ) ^ gridRefinement d * (1 / 2 : ℝ) ^ (P.K + k)
  norm_num [pow_add]
  have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [← inv_pow, ← inv_pow, ← inv_pow]
  rw [hhalf]
  ring

noncomputable def gridCircumradius {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) : ℝ :=
  Real.sqrt (d : ℝ) / 2 * gridMesh P k

theorem gridCircumradius_nonneg {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) :
    0 ≤ gridCircumradius P k := by
  unfold gridCircumradius
  exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
    (gridMesh_pos P k).le

theorem gridCircumradius_le_level_div_four {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) :
    gridCircumradius P k ≤ P.level k / 4 := by
  rw [gridCircumradius, gridMesh_eq_eta_mul_level]
  have hfactor := sqrt_mul_gridEta_div_two_le_quarter d
  have hlevel : 0 ≤ P.level k :=
    (test_dyadicLevel_pos (P.K + k)).le
  calc
    Real.sqrt (d : ℝ) / 2 * (gridEta d * P.level k) =
        (Real.sqrt (d : ℝ) / 2 * gridEta d) * P.level k := by ring
    _ ≤ (1 / 4) * P.level k :=
      mul_le_mul_of_nonneg_right hfactor hlevel
    _ = P.level k / 4 := by ring

abbrev GridLabel {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) :=
  Fin d → Fin (gridSide P k)

theorem card_gridLabel {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) :
    Fintype.card (GridLabel P k) = (gridSide P k) ^ d := by
  simp [GridLabel]

theorem card_gridLabel_real {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) :
    (Fintype.card (GridLabel P k) : ℝ) =
      (gridEta d)⁻¹ ^ d * (P.level k)⁻¹ ^ d := by
  rw [card_gridLabel, Nat.cast_pow]
  change (((2 ^ (gridRefinement d + P.K + k) : ℕ) : ℝ) ^ d) =
    (((1 / 2 : ℝ) ^ gridRefinement d)⁻¹ ^ d) *
      (((1 / 2 : ℝ) ^ (P.K + k))⁻¹ ^ d)
  simp [inv_pow, pow_add]
  ring

theorem gridSide_cast_mul_gridMesh {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) :
    (gridSide P k : ℝ) * gridMesh P k = 1 := by
  unfold gridMesh
  exact mul_inv_cancel₀ (by exact_mod_cast (gridSide_pos P k).ne')

theorem gridSide_succ {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) :
    gridSide P (k + 1) = 2 * gridSide P k := by
  unfold gridSide
  rw [show gridRefinement d + P.K + (k + 1) =
      (gridRefinement d + P.K + k) + 1 by omega]
  rw [pow_succ]
  omega

theorem gridMesh_succ {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) :
    gridMesh P (k + 1) = gridMesh P k / 2 := by
  rw [gridMesh, gridMesh, gridSide_succ]
  push_cast
  ring

noncomputable def gridParent {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (β : GridLabel P (k + 1)) : GridLabel P k :=
  fun i => ⟨(β i : ℕ) / 2, by
    have hβ : (β i : ℕ) < 2 * gridSide P k :=
      (β i).isLt.trans_eq (gridSide_succ P k)
    omega⟩

noncomputable def gridChild {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) (ε : Fin d → Fin 2) :
    GridLabel P (k + 1) :=
  fun i => ⟨2 * (α i : ℕ) + (ε i : ℕ), by
    have hα := (α i).isLt
    have hε := (ε i).isLt
    rw [gridSide_succ]
    omega⟩

noncomputable def gridChildBits {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (β : GridLabel P (k + 1)) : Fin d → Fin 2 :=
  fun i => ⟨(β i : ℕ) % 2, Nat.mod_lt _ (by omega)⟩

@[simp]
theorem gridParent_gridChild {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) (ε : Fin d → Fin 2) :
    gridParent P k (gridChild P k α ε) = α := by
  ext i
  simp only [gridParent, gridChild]
  have hε := (ε i).isLt
  omega

@[simp]
theorem gridChildBits_gridChild {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) (ε : Fin d → Fin 2) :
    gridChildBits P k (gridChild P k α ε) = ε := by
  ext i
  simp only [gridChildBits, gridChild]
  have hε := (ε i).isLt
  omega

theorem gridChild_parent_bits {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (β : GridLabel P (k + 1)) :
    gridChild P k (gridParent P k β) (gridChildBits P k β) = β := by
  ext i
  simp only [gridChild, gridParent, gridChildBits]
  omega

noncomputable def gridChildrenEquiv {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) :
    (Fin d → Fin 2) ≃
      {β : GridLabel P (k + 1) // gridParent P k β = α} where
  toFun ε := ⟨gridChild P k α ε, gridParent_gridChild P k α ε⟩
  invFun β := gridChildBits P k β.1
  left_inv ε := gridChildBits_gridChild P k α ε
  right_inv β := by
    apply Subtype.ext
    change gridChild P k α (gridChildBits P k β.1) = β.1
    calc
      gridChild P k α (gridChildBits P k β.1) =
          gridChild P k (gridParent P k β.1) (gridChildBits P k β.1) :=
        congrArg (fun γ => gridChild P k γ (gridChildBits P k β.1))
          β.property.symm
      _ = β.1 := gridChild_parent_bits P k β.1

theorem existsUnique_gridParent {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (β : GridLabel P (k + 1)) :
    ∃! α : GridLabel P k, gridParent P k β = α := by
  exact ⟨gridParent P k β, rfl, fun α hα => hα.symm⟩

theorem card_gridChildren {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) :
    Fintype.card {β : GridLabel P (k + 1) // gridParent P k β = α} =
      2 ^ d := by
  calc
    Fintype.card {β : GridLabel P (k + 1) // gridParent P k β = α} =
        Fintype.card (Fin d → Fin 2) :=
      (Fintype.card_congr (gridChildrenEquiv P k α)).symm
    _ = 2 ^ d := by simp

noncomputable def gridLower {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) (i : Fin d) : ℝ :=
  (α i : ℝ) * gridMesh P k

noncomputable def gridUpper {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) (i : Fin d) : ℝ :=
  ((α i : ℝ) + 1) * gridMesh P k

noncomputable def gridCenterLift {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => ((α i : ℝ) + 1 / 2) * gridMesh P k

noncomputable def gridLiftCell {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, gridLower P k α i ≤ x i ∧ x i ≤ gridUpper P k α i}

noncomputable def gridCell {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) : Set (FlatTorus d) :=
  flatTorusMk d '' gridLiftCell P k α

noncomputable def gridFundamentalRepresentative (d : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ZSpan.fract (flatTorusBasis d) x

theorem gridFundamentalRepresentative_coordinate_mem_Ico
    (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    gridFundamentalRepresentative d x i ∈ Set.Ico (0 : ℝ) 1 := by
  have hx := ZSpan.fract_mem_fundamentalDomain (flatTorusBasis d) x
  rw [ZSpan.mem_fundamentalDomain] at hx
  simpa only [gridFundamentalRepresentative, flatTorusBasis,
    OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr] using hx i

theorem flatTorusMk_gridFundamentalRepresentative
    (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    flatTorusMk d (gridFundamentalRepresentative d x) = flatTorusMk d x := by
  change (gridFundamentalRepresentative d x : FlatTorus d) =
    (x : FlatTorus d)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  rw [integerLattice_eq_zspan]
  have hfloor :
      (↑(ZSpan.floor (flatTorusBasis d) x) :
        EuclideanSpace ℝ (Fin d)) ∈
        Submodule.span ℤ (Set.range (flatTorusBasis d)) :=
    (ZSpan.floor (flatTorusBasis d) x).property
  change ZSpan.fract (flatTorusBasis d) x - x ∈
    Submodule.span ℤ (Set.range (flatTorusBasis d))
  rw [ZSpan.fract_apply]
  convert neg_mem hfloor using 1 <;> abel

noncomputable def gridLabelOfLift
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : GridLabel P k :=
  fun i => ⟨⌊(gridSide P k : ℝ) *
      gridFundamentalRepresentative d x i⌋₊, by
    have hi := gridFundamentalRepresentative_coordinate_mem_Ico d x i
    have hs : 0 < (gridSide P k : ℝ) := by
      exact_mod_cast gridSide_pos P k
    apply (Nat.floor_lt (mul_nonneg hs.le hi.1)).2
    simpa only [mul_one] using mul_lt_mul_of_pos_left hi.2 hs⟩

theorem gridFundamentalRepresentative_mem_gridLiftCell
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) :
    gridFundamentalRepresentative d x ∈
      gridLiftCell P k (gridLabelOfLift P k x) := by
  intro i
  simp only [gridLower, gridUpper, gridLabelOfLift]
  let y : ℝ := gridFundamentalRepresentative d x i
  let s : ℝ := gridSide P k
  have hy := gridFundamentalRepresentative_coordinate_mem_Ico d x i
  change 0 ≤ y ∧ y < 1 at hy
  have hs : 0 < s := by
    dsimp only [s]
    exact_mod_cast gridSide_pos P k
  have hsy : 0 ≤ s * y := mul_nonneg hs.le hy.1
  have hfloor : ((⌊s * y⌋₊ : ℕ) : ℝ) ≤ s * y :=
    Nat.floor_le hsy
  have hnext : s * y ≤ ((⌊s * y⌋₊ : ℕ) : ℝ) + 1 :=
    (Nat.lt_floor_add_one (s * y)).le
  have hh := gridMesh_pos P k
  have hsm : s * gridMesh P k = 1 :=
    gridSide_cast_mul_gridMesh P k
  change ((⌊s * y⌋₊ : ℕ) : ℝ) * gridMesh P k ≤ y ∧
    y ≤ (((⌊s * y⌋₊ : ℕ) : ℝ) + 1) * gridMesh P k
  constructor
  · calc
      ((⌊s * y⌋₊ : ℕ) : ℝ) * gridMesh P k ≤
          (s * y) * gridMesh P k :=
        mul_le_mul_of_nonneg_right hfloor hh.le
      _ = y := by rw [show (s * y) * gridMesh P k =
          (s * gridMesh P k) * y by ring, hsm, one_mul]
  · calc
      y = (s * y) * gridMesh P k := by
        rw [show (s * y) * gridMesh P k =
          (s * gridMesh P k) * y by ring, hsm, one_mul]
      _ ≤ (((⌊s * y⌋₊ : ℕ) : ℝ) + 1) * gridMesh P k :=
        mul_le_mul_of_nonneg_right hnext hh.le

theorem exists_mem_gridCell
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) (z : FlatTorus d) :
    ∃ α : GridLabel P k, z ∈ gridCell P k α := by
  rcases QuotientAddGroup.mk'_surjective (integerLattice d) z with ⟨x, hx⟩
  change flatTorusMk d x = z at hx
  refine ⟨gridLabelOfLift P k x,
    gridFundamentalRepresentative d x,
    gridFundamentalRepresentative_mem_gridLiftCell P k x, ?_⟩
  exact (flatTorusMk_gridFundamentalRepresentative d x).trans hx

theorem iUnion_gridCell_eq_univ
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) :
    (⋃ α : GridLabel P k, gridCell P k α) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  rw [Set.mem_iUnion]
  exact exists_mem_gridCell P k z

noncomputable def gridCenter {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) : FlatTorus d :=
  flatTorusMk d (gridCenterLift P k α)

theorem gridCenterLift_mem_cell {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) :
    gridCenterLift P k α ∈ gridLiftCell P k α := by
  intro i
  simp only [gridCenterLift, PiLp.toLp_apply, gridLower, gridUpper]
  have hh := gridMesh_pos P k
  constructor <;> nlinarith

theorem gridCenter_mem_cell {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) :
    gridCenter P k α ∈ gridCell P k α := by
  exact ⟨gridCenterLift P k α, gridCenterLift_mem_cell P k α, rfl⟩

theorem gridLiftCell_child_subset_parent
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (β : GridLabel P (k + 1)) :
    gridLiftCell P (k + 1) β ⊆
      gridLiftCell P k (gridParent P k β) := by
  intro x hx i
  have hi := hx i
  simp only [gridLower, gridUpper] at hi ⊢
  rw [gridMesh_succ] at hi
  simp only [gridParent]
  have hloNat :
      2 * ((β i : ℕ) / 2) ≤ (β i : ℕ) :=
    Nat.mul_div_le _ _
  have hhiNat :
      (β i : ℕ) + 1 ≤ 2 * (((β i : ℕ) / 2) + 1) := by
    omega
  have hloReal :
      (2 : ℝ) * (((β i : ℕ) / 2 : ℕ) : ℝ) ≤ (β i : ℕ) := by
    exact_mod_cast hloNat
  have hhiReal :
      ((β i : ℕ) : ℝ) + 1 ≤
        2 * ((((β i : ℕ) / 2 : ℕ) : ℝ) + 1) := by
    exact_mod_cast hhiNat
  have hh := gridMesh_pos P k
  constructor <;> nlinarith

theorem gridCell_child_subset_parent
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (β : GridLabel P (k + 1)) :
    gridCell P (k + 1) β ⊆ gridCell P k (gridParent P k β) := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, gridLiftCell_child_subset_parent P k β hx, rfl⟩

private theorem grid_coordinate_dist_le_half_mesh
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ gridLiftCell P k α) (i : Fin d) :
    dist (gridCenterLift P k α i) (x i) ≤ gridMesh P k / 2 := by
  have hi := hx i
  simp only [gridLower, gridUpper] at hi
  rw [Real.dist_eq]
  simp only [gridCenterLift, PiLp.toLp_apply]
  rw [abs_le]
  constructor <;> nlinarith

theorem dist_gridCenterLift_le_circumradius
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ gridLiftCell P k α) :
    dist (gridCenterLift P k α) x ≤ gridCircumradius P k := by
  have hcoord : ∀ i : Fin d,
      dist (gridCenterLift P k α i) (x i) ^ 2 ≤
        (gridMesh P k / 2) ^ 2 := by
    intro i
    have hdist := grid_coordinate_dist_le_half_mesh P k α hx i
    have hnonneg : 0 ≤ dist (gridCenterLift P k α i) (x i) := dist_nonneg
    have hsq := mul_self_le_mul_self hnonneg hdist
    nlinarith
  have hsum :
      ∑ i : Fin d, dist (gridCenterLift P k α i) (x i) ^ 2 ≤
        (d : ℝ) * (gridMesh P k / 2) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, (gridMesh P k / 2) ^ 2 :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * (gridMesh P k / 2) ^ 2 := by simp
  rw [EuclideanSpace.dist_eq]
  unfold gridCircumradius
  have hsum_nonneg :
      0 ≤ ∑ i : Fin d, dist (gridCenterLift P k α i) (x i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsqrt_d : (Real.sqrt (d : ℝ)) ^ 2 = d :=
    Real.sq_sqrt (by positivity)
  have hsqrt_sum :
      (Real.sqrt
        (∑ i : Fin d, dist (gridCenterLift P k α i) (x i) ^ 2)) ^ 2 =
        ∑ i : Fin d, dist (gridCenterLift P k α i) (x i) ^ 2 :=
    Real.sq_sqrt hsum_nonneg
  have hright_nonneg :
      0 ≤ Real.sqrt (d : ℝ) / 2 * gridMesh P k :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
      (gridMesh_pos P k).le
  have hleft_nonneg := Real.sqrt_nonneg
    (∑ i : Fin d, dist (gridCenterLift P k α i) (x i) ^ 2)
  nlinarith

theorem isClosed_gridLiftCell
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) :
    IsClosed (gridLiftCell P k α) := by
  rw [show gridLiftCell P k α =
      ⋂ i : Fin d,
        (fun x : EuclideanSpace ℝ (Fin d) => x i) ⁻¹'
          Set.Icc (gridLower P k α i) (gridUpper P k α i) by
    ext x
    simp [gridLiftCell]]
  exact isClosed_iInter fun i =>
    isClosed_Icc.preimage
      (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)

theorem isCompact_gridLiftCell
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) :
    IsCompact (gridLiftCell P k α) := by
  rw [show gridLiftCell P k α =
      (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
        Set.pi Set.univ (fun i : Fin d =>
          Set.Icc (gridLower P k α i) (gridUpper P k α i)) by
    ext x
    simp only [gridLiftCell, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]
    rfl]
  apply (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isCompact_preimage.mpr
  exact isCompact_univ_pi fun _ => isCompact_Icc

theorem isCompact_gridCell
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) :
    IsCompact (gridCell P k α) := by
  unfold gridCell
  apply (isCompact_gridLiftCell P k α).image
  exact QuotientAddGroup.continuous_mk

theorem isClosed_gridCell
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) :
    IsClosed (gridCell P k α) :=
  (isCompact_gridCell P k α).isClosed

theorem dist_flatTorusMk_le_dist
    {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) :
    dist (flatTorusMk d x) (flatTorusMk d y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact QuotientAddGroup.norm_mk_le_norm

theorem gridCell_subset_closedBall
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (α : GridLabel P k) :
    gridCell P k α ⊆
      Metric.closedBall (gridCenter P k α) (gridCircumradius P k) := by
  rintro z ⟨x, hx, rfl⟩
  rw [Metric.mem_closedBall]
  rw [gridCenter, dist_comm]
  exact (dist_flatTorusMk_le_dist (gridCenterLift P k α) x).trans
    (dist_gridCenterLift_le_circumradius P k α hx)

end Shepp.Section3
end SheppFlattenedModule020

section SheppFlattenedModule021
open scoped BigOperators

namespace Shepp.Section3

open Shepp.Section2

noncomputable def intervalOverlap
    (a b c e : ℝ) : ℝ :=
  max (min b e - max a c) 0

theorem intervalOverlap_nonneg (a b c e : ℝ) :
    0 ≤ intervalOverlap a b c e := by
  exact le_max_right _ _

theorem intervalOverlap_symm (a b c e : ℝ) :
    intervalOverlap a b c e = intervalOverlap c e a b := by
  simp only [intervalOverlap, min_comm b e, max_comm a c]

theorem intervalOverlap_eq_clamp_sub
    {a b c e : ℝ} (hab : a ≤ b) (hce : c ≤ e) :
    intervalOverlap a b c e =
      min (max b c) e - min (max a c) e := by
  simp only [intervalOverlap, min_def, max_def]
  split_ifs <;> linarith

theorem intervalOverlap_le_left_length
    {a b c e : ℝ} (hab : a ≤ b) (hce : c ≤ e) :
    intervalOverlap a b c e ≤ b - a := by
  simp only [intervalOverlap, min_def, max_def]
  split_ifs <;> linarith

theorem intervalOverlap_le_right_length
    {a b c e : ℝ} (hab : a ≤ b) (hce : c ≤ e) :
    intervalOverlap a b c e ≤ e - c := by
  rw [intervalOverlap_symm]
  exact intervalOverlap_le_left_length hce hab

theorem intervalOverlap_eq_volume_inter_Ioc
    (a b c e : ℝ) :
    intervalOverlap a b c e =
      (MeasureTheory.volume (Set.Ioc a b ∩ Set.Ioc c e)).toReal := by
  have hinter :
      Set.Ioc a b ∩ Set.Ioc c e = Set.Ioc (max a c) (min b e) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, max_lt_iff, le_min_iff]
    aesop
  rw [hinter, Real.volume_Ioc]
  rw [ENNReal.toReal_ofReal']
  rfl

theorem prefixMass_sub_previousMass
    (v : ℕ → ℝ) (n : ℕ) :
    prefixMass v n - previousMass v n = v n := by
  cases n with
  | zero => simp [prefixMass, previousMass]
  | succ n => rw [previousMass_succ, prefixMass_succ]; ring

theorem previousMass_le_prefixMass
    {v : ℕ → ℝ} (hv : ∀ n, 0 ≤ v n) (n : ℕ) :
    previousMass v n ≤ prefixMass v n := by
  rw [← sub_nonneg]
  simpa only [prefixMass_sub_previousMass] using hv n

theorem sum_prefixEndpointDifference_range
    (v : ℕ → ℝ) (F : ℝ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
      (F (prefixMass v n) - F (previousMass v n))) =
        F (prefixMass v N) - F 0 := by
  induction N with
  | zero => simp [prefixMass, previousMass]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, previousMass_succ]
      ring

theorem sum_prefixEndpointDifference_Ioc
    (v : ℕ → ℝ) (F : ℝ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc a b,
      (F (prefixMass v n) - F (previousMass v n))) =
        F (prefixMass v b) - F (prefixMass v a) := by
  have hsplit := test_sum_range_eq_add_sum_Ioc
    (fun n => F (prefixMass v n) - F (previousMass v n)) hab
  rw [sum_prefixEndpointDifference_range,
    sum_prefixEndpointDifference_range] at hsplit
  linarith

theorem sum_stepDifference_range (B : ℕ → ℝ) (J : ℕ) :
    (∑ p ∈ Finset.range J, (B (p + 1) - B p)) = B J - B 0 := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      ring

noncomputable def packetIndices
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ℕ → Finset ℕ
  | 0 => Finset.range (P.cutoff 0 + 1)
  | k + 1 => Finset.Ioc (P.cutoff k) (P.cutoff (k + 1))

theorem mem_packetIndices_le_cutoff
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    {k n : ℕ} (hn : n ∈ packetIndices P k) :
    n ≤ P.cutoff k := by
  cases k with
  | zero =>
      simpa [packetIndices, Nat.lt_succ_iff] using hn
  | succ k =>
      exact (Finset.mem_Ioc.mp hn).2

noncomputable def packetStartMass
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ℕ → ℝ
  | 0 => 0
  | k + 1 => prefixMass (radiusVolume d r) (P.cutoff k)

noncomputable def packetEndMass
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) : ℝ :=
  prefixMass (radiusVolume d r) (P.cutoff k)

noncomputable def packetMass
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) : ℝ :=
  packetEndMass P k - packetStartMass P k

theorem packetMass_eq_sum
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) :
    packetMass P k =
      ∑ n ∈ packetIndices P k, radiusVolume d r n := by
  cases k with
  | zero =>
      simp [packetMass, packetEndMass, packetStartMass,
        packetIndices, prefixMass]
  | succ k =>
      have hcut : P.cutoff k ≤ P.cutoff (k + 1) :=
        P.cutoff_monotone (Nat.le_succ k)
      have hsplit := test_sum_range_eq_add_sum_Ioc
        (radiusVolume d r) hcut
      rw [packetMass, packetEndMass, packetStartMass, packetIndices]
      rw [sub_eq_iff_eq_add]
      simpa only [prefixMass, add_comm] using hsplit

theorem packetMass_nonneg
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) :
    0 ≤ packetMass P k := by
  rw [packetMass_eq_sum]
  exact Finset.sum_nonneg fun n _ => P.radiusVolume_nonneg n

theorem packetStartMass_le_endMass
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) :
    packetStartMass P k ≤ packetEndMass P k := by
  exact sub_nonneg.mp (packetMass_nonneg P k)

noncomputable def subblockCount
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) : ℕ :=
  ⌈packetMass P k⌉₊

theorem subblockCount_eq_zero_iff
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) :
    subblockCount P k = 0 ↔ packetMass P k = 0 := by
  rw [subblockCount, Nat.ceil_eq_zero]
  exact ⟨fun h => le_antisymm h (packetMass_nonneg P k),
    fun h => h.le⟩

noncomputable def subblockBoundary
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) : ℝ :=
  min (packetStartMass P k + p) (packetEndMass P k)

theorem subblockBoundary_zero
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) :
    subblockBoundary P k 0 = packetStartMass P k := by
  rw [subblockBoundary, Nat.cast_zero, add_zero,
    min_eq_left (packetStartMass_le_endMass P k)]

theorem subblockBoundary_count
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) :
    subblockBoundary P k (subblockCount P k) = packetEndMass P k := by
  rw [subblockBoundary, min_eq_right]
  have hceil : packetMass P k ≤ (subblockCount P k : ℕ) := by
    exact Nat.le_ceil (packetMass P k)
  rw [packetMass] at hceil
  linarith

theorem subblockBoundary_monotone
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) :
    Monotone (subblockBoundary P k) := by
  intro p q hpq
  unfold subblockBoundary
  apply min_le_min_right
  have hpqReal : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
  simpa only [add_comm] using add_le_add_left hpqReal (packetStartMass P k)

theorem packetStartMass_le_subblockBoundary
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) :
    packetStartMass P k ≤ subblockBoundary P k p := by
  unfold subblockBoundary
  apply le_min
  · exact le_add_of_nonneg_right (by positivity)
  · exact packetStartMass_le_endMass P k

theorem subblockBoundary_le_packetEndMass
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) :
    subblockBoundary P k p ≤ packetEndMass P k := by
  exact min_le_right _ _

noncomputable def subblockMass
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) : ℝ :=
  subblockBoundary P k (p + 1) - subblockBoundary P k p

theorem subblockMass_pos
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) :
    0 < subblockMass P k p := by
  have hp : (p : ℝ) < packetMass P k := by
    exact (Nat.lt_ceil.mp p.isLt)
  have hpEnd : packetStartMass P k + (p : ℝ) < packetEndMass P k := by
    rw [packetMass] at hp
    linarith
  have hpBoundary :
      subblockBoundary P k p = packetStartMass P k + (p : ℝ) := by
    rw [subblockBoundary, min_eq_left hpEnd.le]
  have hnextRaw :
      packetStartMass P k + (p : ℝ) <
        packetStartMass P k + ((p : ℕ) + 1 : ℕ) := by
    push_cast
    linarith
  have hboundaryLt :
      subblockBoundary P k p < subblockBoundary P k (p + 1) := by
    rw [hpBoundary, subblockBoundary]
    exact lt_min hnextRaw hpEnd
  exact sub_pos.mpr hboundaryLt

theorem subblockMass_le_one
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) :
    subblockMass P k p ≤ 1 := by
  have hp : (p : ℝ) < packetMass P k := Nat.lt_ceil.mp p.isLt
  have hpEnd : packetStartMass P k + (p : ℝ) < packetEndMass P k := by
    rw [packetMass] at hp
    linarith
  have hpBoundary :
      subblockBoundary P k p = packetStartMass P k + (p : ℝ) := by
    rw [subblockBoundary, min_eq_left hpEnd.le]
  have hnext :
      subblockBoundary P k (p + 1) ≤
        packetStartMass P k + (p : ℝ) + 1 := by
    unfold subblockBoundary
    calc
      min (packetStartMass P k + ((p : ℕ) + 1 : ℕ))
          (packetEndMass P k) ≤
          packetStartMass P k + ((p : ℕ) + 1 : ℕ) := min_le_left _ _
      _ = packetStartMass P k + (p : ℝ) + 1 := by push_cast; ring
  rw [subblockMass, hpBoundary]
  linarith

theorem sum_subblockMass
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) :
    (∑ p : Fin (subblockCount P k), subblockMass P k p) =
      packetMass P k := by
  change (∑ p : Fin (subblockCount P k),
    (subblockBoundary P k ((p : ℕ) + 1) -
      subblockBoundary P k (p : ℕ))) = packetMass P k
  rw [Fin.sum_univ_eq_sum_range
    (fun p : ℕ => subblockBoundary P k (p + 1) -
      subblockBoundary P k p) (subblockCount P k)]
  rw [sum_stepDifference_range, subblockBoundary_count,
    subblockBoundary_zero]
  rfl

noncomputable def markIntervalLower
    {d : ℕ} {r : ℕ → ℝ} (_P : GeometricPacketInterface d r)
    (n : ℕ) : ℝ :=
  previousMass (radiusVolume d r) n

noncomputable def markIntervalUpper
    {d : ℕ} {r : ℕ → ℝ} (_P : GeometricPacketInterface d r)
    (n : ℕ) : ℝ :=
  prefixMass (radiusVolume d r) n

theorem markInterval_length
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (n : ℕ) :
    markIntervalUpper P n - markIntervalLower P n = radiusVolume d r n := by
  exact prefixMass_sub_previousMass (radiusVolume d r) n

theorem markIntervalLower_le_upper
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (n : ℕ) :
    markIntervalLower P n ≤ markIntervalUpper P n := by
  exact previousMass_le_prefixMass P.radiusVolume_nonneg n

private theorem previousRadiusVolumeMass_nonneg
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (n : ℕ) :
    0 ≤ previousMass (radiusVolume d r) n := by
  cases n with
  | zero => simp [previousMass]
  | succ n =>
      rw [previousMass_succ]
      exact Finset.sum_nonneg fun i _ => P.radiusVolume_nonneg i

theorem markInterval_mem_packet_bounds
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    {k n : ℕ} (hn : n ∈ packetIndices P k) :
    packetStartMass P k ≤ markIntervalLower P n ∧
      markIntervalUpper P n ≤ packetEndMass P k := by
  have hvmono := prefixMass_mono P.radiusVolume_nonneg
  cases k with
  | zero =>
      have hncut : n ≤ P.cutoff 0 := by
        simpa [packetIndices] using hn
      constructor
      · rw [packetStartMass, markIntervalLower]
        exact previousRadiusVolumeMass_nonneg P n
      · rw [markIntervalUpper, packetEndMass]
        exact hvmono hncut
  | succ k =>
      have hnblock : P.cutoff k < n ∧ n ≤ P.cutoff (k + 1) := by
        simpa [packetIndices] using hn
      constructor
      · cases n with
        | zero => omega
        | succ n =>
            rw [packetStartMass, markIntervalLower, previousMass_succ]
            exact hvmono (by omega)
      · rw [markIntervalUpper, packetEndMass]
        exact hvmono hnblock.2

noncomputable def fractionalOverlap
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k n : ℕ) (p : Fin (subblockCount P k)) : ℝ :=
  intervalOverlap (markIntervalLower P n) (markIntervalUpper P n)
    (subblockBoundary P k p) (subblockBoundary P k (p + 1))

theorem fractionalOverlap_eq_volume_inter_Ioc
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k n : ℕ) (p : Fin (subblockCount P k)) :
    fractionalOverlap P k n p =
      (MeasureTheory.volume
        (Set.Ioc (markIntervalLower P n) (markIntervalUpper P n) ∩
          Set.Ioc (subblockBoundary P k p)
            (subblockBoundary P k (p + 1)))).toReal := by
  exact intervalOverlap_eq_volume_inter_Ioc _ _ _ _

noncomputable def fractionalWeight
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k n : ℕ) (p : Fin (subblockCount P k)) : ℝ :=
  fractionalOverlap P k n p / radiusVolume d r n

theorem fractionalWeight_nonneg
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k n : ℕ) (p : Fin (subblockCount P k)) :
    0 ≤ fractionalWeight P k n p := by
  exact div_nonneg (intervalOverlap_nonneg _ _ _ _)
    (P.radiusVolume_nonneg n)

theorem fractionalWeight_le_one
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k n : ℕ) (p : Fin (subblockCount P k)) :
    fractionalWeight P k n p ≤ 1 := by
  apply (div_le_one (P.radiusVolume_pos n)).2
  calc
    fractionalOverlap P k n p ≤
        markIntervalUpper P n - markIntervalLower P n :=
      intervalOverlap_le_left_length
        (markIntervalLower_le_upper P n)
        (subblockBoundary_monotone P k (Nat.le_succ _))
    _ = radiusVolume d r n := markInterval_length P n

theorem fractionalWeight_mul_radiusVolume
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k n : ℕ) (p : Fin (subblockCount P k)) :
    fractionalWeight P k n p * radiusVolume d r n =
      fractionalOverlap P k n p := by
  exact div_mul_cancel₀ _ (P.radiusVolume_pos n).ne'

theorem sum_fractionalOverlap_packetIndices
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) :
    (∑ n ∈ packetIndices P k, fractionalOverlap P k n p) =
      subblockMass P k p := by
  let L : ℝ := subblockBoundary P k p
  let U : ℝ := subblockBoundary P k (p + 1)
  let F : ℝ → ℝ := fun x => min (max x L) U
  have hLU : L ≤ U := subblockBoundary_monotone P k (Nat.le_succ _)
  have hterm : ∀ n,
      fractionalOverlap P k n p =
        F (prefixMass (radiusVolume d r) n) -
          F (previousMass (radiusVolume d r) n) := by
    intro n
    exact intervalOverlap_eq_clamp_sub
      (markIntervalLower_le_upper P n) hLU
  have htel :
      (∑ n ∈ packetIndices P k,
        (F (prefixMass (radiusVolume d r) n) -
          F (previousMass (radiusVolume d r) n))) =
        F (packetEndMass P k) - F (packetStartMass P k) := by
    cases k with
    | zero =>
        simpa [packetIndices, packetEndMass, packetStartMass] using
          sum_prefixEndpointDifference_range
            (radiusVolume d r) F (P.cutoff 0)
    | succ k =>
        simpa [packetIndices, packetEndMass, packetStartMass] using
          sum_prefixEndpointDifference_Ioc
            (radiusVolume d r) F
              (P.cutoff_monotone (Nat.le_succ k))
  have hstartL : packetStartMass P k ≤ L :=
    packetStartMass_le_subblockBoundary P k p
  have hLend : L ≤ packetEndMass P k :=
    subblockBoundary_le_packetEndMass P k p
  have hUend : U ≤ packetEndMass P k :=
    subblockBoundary_le_packetEndMass P k (p + 1)
  have hFstart : F (packetStartMass P k) = L := by
    dsimp only [F]
    rw [max_eq_right hstartL, min_eq_left hLU]
  have hFend : F (packetEndMass P k) = U := by
    dsimp only [F]
    rw [max_eq_left hLend, min_eq_right hUend]
  calc
    (∑ n ∈ packetIndices P k, fractionalOverlap P k n p) =
        ∑ n ∈ packetIndices P k,
          (F (prefixMass (radiusVolume d r) n) -
            F (previousMass (radiusVolume d r) n)) := by
      apply Finset.sum_congr rfl
      intro n _
      exact hterm n
    _ = F (packetEndMass P k) - F (packetStartMass P k) := htel
    _ = U - L := by rw [hFend, hFstart]
    _ = subblockMass P k p := rfl

theorem subblockMass_eq_sum_fractionalWeight
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) :
    subblockMass P k p =
      ∑ n ∈ packetIndices P k,
        fractionalWeight P k n p * radiusVolume d r n := by
  rw [← sum_fractionalOverlap_packetIndices P k p]
  apply Finset.sum_congr rfl
  intro n _
  exact (fractionalWeight_mul_radiusVolume P k n p).symm

theorem sum_fractionalOverlap_subblocks
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    {k n : ℕ} (hn : n ∈ packetIndices P k) :
    (∑ p : Fin (subblockCount P k), fractionalOverlap P k n p) =
      radiusVolume d r n := by
  let a : ℝ := markIntervalLower P n
  let b : ℝ := markIntervalUpper P n
  let B : ℕ → ℝ := subblockBoundary P k
  let F : ℝ → ℝ := fun x => min (max x a) b
  have hab : a ≤ b := markIntervalLower_le_upper P n
  have hpacket := markInterval_mem_packet_bounds P hn
  have hstarta : packetStartMass P k ≤ a := hpacket.1
  have hbend : b ≤ packetEndMass P k := hpacket.2
  have haend : a ≤ packetEndMass P k := hab.trans hbend
  have hterm : ∀ p : Fin (subblockCount P k),
      fractionalOverlap P k n p = F (B ((p : ℕ) + 1)) - F (B p) := by
    intro p
    rw [fractionalOverlap, intervalOverlap_symm]
    exact intervalOverlap_eq_clamp_sub
      (subblockBoundary_monotone P k (Nat.le_succ _)) hab
  have hFstart : F (packetStartMass P k) = a := by
    dsimp only [F]
    rw [max_eq_right hstarta, min_eq_left hab]
  have hFend : F (packetEndMass P k) = b := by
    dsimp only [F]
    rw [max_eq_left haend, min_eq_right hbend]
  calc
    (∑ p : Fin (subblockCount P k), fractionalOverlap P k n p) =
        ∑ p : Fin (subblockCount P k),
          (F (B ((p : ℕ) + 1)) - F (B p)) := by
      apply Finset.sum_congr rfl
      intro p _
      exact hterm p
    _ = ∑ p ∈ Finset.range (subblockCount P k),
          (F (B (p + 1)) - F (B p)) :=
      Fin.sum_univ_eq_sum_range
        (fun p : ℕ => F (B (p + 1)) - F (B p))
        (subblockCount P k)
    _ = F (B (subblockCount P k)) - F (B 0) :=
      sum_stepDifference_range (fun p => F (B p)) (subblockCount P k)
    _ = F (packetEndMass P k) - F (packetStartMass P k) := by
      rw [show B (subblockCount P k) = packetEndMass P k from
          subblockBoundary_count P k,
        show B 0 = packetStartMass P k from subblockBoundary_zero P k]
    _ = b - a := by rw [hFend, hFstart]
    _ = radiusVolume d r n := markInterval_length P n

theorem sum_fractionalWeight
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    {k n : ℕ} (hn : n ∈ packetIndices P k) :
    (∑ p : Fin (subblockCount P k), fractionalWeight P k n p) = 1 := by
  simp only [fractionalWeight]
  rw [← Finset.sum_div, sum_fractionalOverlap_subblocks P hn,
    div_self (P.radiusVolume_pos n).ne']

noncomputable abbrev scheduledMass
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) : ℝ :=
  subblockBoundary P k p

theorem scheduledMass_zero
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) :
    scheduledMass P k 0 = packetStartMass P k :=
  subblockBoundary_zero P k

theorem scheduledMass_count
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) :
    scheduledMass P k (subblockCount P k) = packetEndMass P k :=
  subblockBoundary_count P k

theorem scheduledMass_succ
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) :
    scheduledMass P k ((p : ℕ) + 1) =
      scheduledMass P k p + subblockMass P k p := by
  rw [subblockMass]
  ring

theorem packetIncrement_eq_exp_end_sub_exp_start
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) :
    P.increment k =
      Real.exp (packetEndMass P k) - Real.exp (packetStartMass P k) := by
  cases k with
  | zero =>
      simp [GeometricPacketInterface.increment, packetCoefficient,
        test_packetCoefficient, packetEndMass, packetStartMass]
  | succ k =>
      rfl

end Shepp.Section3
end SheppFlattenedModule021

section SheppFlattenedModule022
open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace Shepp.Section3

open ProbabilityTheory

theorem integral_pow_poissonMeasure (rate : ℝ≥0) (q : ℝ) :
    (∫ n : ℕ, q ^ n ∂(poissonMeasure rate)) =
      Real.exp ((rate : ℝ) * (q - 1)) := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    (∑' n : ℕ,
        (Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ n / n.factorial : ℝ) * q ^ n) =
        Real.exp (-(rate : ℝ)) *
          ∑' n : ℕ, (((rate : ℝ) * q) ^ n / n.factorial : ℝ) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [mul_pow]
      ring
    _ = Real.exp (-(rate : ℝ)) * Real.exp ((rate : ℝ) * q) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((rate : ℝ) * q)).tsum_eq,
        ← Real.exp_eq_exp_ℝ]
    _ = Real.exp ((rate : ℝ) * (q - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring

abbrev PoissonCloudSample (α : Type*) := ℕ × (ℕ → α)

noncomputable def poissonCloudMeasure
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ℝ≥0) :
    Measure (PoissonCloudSample α) :=
  (poissonMeasure rate).prod (Measure.infinitePi fun _ : ℕ => μ)

noncomputable instance poissonCloudMeasure_isProbabilityMeasure
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ℝ≥0) :
    IsProbabilityMeasure (poissonCloudMeasure μ rate) := by
  unfold poissonCloudMeasure
  infer_instance

def cloudAvoids
    {α : Type*} (E : Set α) : Set (PoissonCloudSample α) :=
  {ω | ∀ i < ω.1, ω.2 i ∉ E}

theorem cloudAvoids_eq_iUnion
    {α : Type*} (E : Set α) :
    cloudAvoids E =
      ⋃ n : ℕ, ({n} : Set ℕ) ×ˢ
        Set.pi (Finset.range n) (fun _ : ℕ => Eᶜ) := by
  ext ω
  simp only [cloudAvoids, Set.mem_setOf_eq, Set.mem_iUnion,
    Set.mem_prod, Set.mem_singleton_iff, Set.mem_pi, Set.mem_compl_iff]
  constructor
  · intro h
    exact ⟨ω.1, rfl, fun i hi => h i (Finset.mem_range.mp hi)⟩
  · rintro ⟨n, hn, h⟩
    subst n
    exact fun i hi => h i (Finset.mem_range.mpr hi)

theorem measurableSet_cloudAvoids
    {α : Type*} [MeasurableSpace α]
    {E : Set α} (hE : MeasurableSet E) :
    MeasurableSet (cloudAvoids E) := by
  rw [cloudAvoids_eq_iUnion]
  apply MeasurableSet.iUnion
  intro n
  exact MeasurableSet.singleton n |>.prod
    (MeasurableSet.pi (Finset.countable_toSet _) fun _ _ => hE.compl)

theorem infinitePi_avoidance
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {E : Set α} (hE : MeasurableSet E) (n : ℕ) :
    Measure.infinitePi (fun _ : ℕ => μ)
        (Set.pi (Finset.range n) (fun _ : ℕ => Eᶜ)) =
      (μ Eᶜ) ^ n := by
  rw [Measure.infinitePi_pi _ (fun _ _ => hE.compl)]
  simp

theorem prodMk_preimage_cloudAvoids
    {α : Type*} (E : Set α) (n : ℕ) :
    Prod.mk n ⁻¹' cloudAvoids E =
      Set.pi (Finset.range n) (fun _ : ℕ => Eᶜ) := by
  ext x
  simp only [Set.mem_preimage, cloudAvoids, Set.mem_setOf_eq,
    Set.mem_pi, Set.mem_compl_iff]
  constructor
  · intro h i hi
    exact h i (by simpa using hi)
  · intro h i hi
    exact h i (by simpa using hi)

theorem poissonCloudMeasure_cloudAvoids_eq_lintegral
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    {E : Set α} (hE : MeasurableSet E) :
    poissonCloudMeasure μ rate (cloudAvoids E) =
      ∫⁻ n : ℕ, (μ Eᶜ) ^ n ∂(poissonMeasure rate) := by
  rw [poissonCloudMeasure, Measure.prod_apply (measurableSet_cloudAvoids hE)]
  apply lintegral_congr
  intro n
  rw [prodMk_preimage_cloudAvoids, infinitePi_avoidance μ hE n]

theorem lintegral_pow_poissonMeasure
    (rate : ℝ≥0) (q : ℝ≥0∞) (hq : q ≠ ∞) :
    (∫⁻ n : ℕ, q ^ n ∂(poissonMeasure rate)) =
      ENNReal.ofReal
        (Real.exp ((rate : ℝ) * (q.toReal - 1))) := by
  let L : ℝ≥0∞ := ∫⁻ n : ℕ, q ^ n ∂(poissonMeasure rate)
  have hfinite : ∀ᵐ n : ℕ ∂(poissonMeasure rate), q ^ n < ∞ :=
    Filter.Eventually.of_forall fun n => ENNReal.pow_lt_top hq.lt_top
  have hrealIntegral := integral_toReal
    (μ := poissonMeasure rate)
    (Measurable.of_discrete.aemeasurable :
      AEMeasurable (fun n : ℕ => q ^ n) (poissonMeasure rate))
    hfinite
  simp only [ENNReal.toReal_pow] at hrealIntegral
  rw [integral_pow_poissonMeasure] at hrealIntegral
  have hLreal :
      L.toReal = Real.exp ((rate : ℝ) * (q.toReal - 1)) := by
    exact hrealIntegral.symm
  have hLtop : L ≠ ∞ := by
    intro h
    rw [h] at hLreal
    simp only [ENNReal.toReal_top] at hLreal
    exact (Real.exp_pos _).ne' hLreal.symm
  calc
    (∫⁻ n : ℕ, q ^ n ∂(poissonMeasure rate)) = L := rfl
    _ = ENNReal.ofReal L.toReal := (ENNReal.ofReal_toReal hLtop).symm
    _ = ENNReal.ofReal
        (Real.exp ((rate : ℝ) * (q.toReal - 1))) := by rw [hLreal]

theorem poissonCloudMeasure_cloudAvoids
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    {E : Set α} (hE : MeasurableSet E) :
    poissonCloudMeasure μ rate (cloudAvoids E) =
      ENNReal.ofReal
        (Real.exp (-(rate : ℝ) * μ.real E)) := by
  rw [poissonCloudMeasure_cloudAvoids_eq_lintegral μ rate hE,
    lintegral_pow_poissonMeasure rate (μ Eᶜ) (measure_ne_top μ Eᶜ)]
  congr 2
  have hcompl : (μ Eᶜ).toReal = 1 - μ.real E := by
    change μ.real Eᶜ = 1 - μ.real E
    rw [measureReal_compl hE, probReal_univ]
  rw [hcompl]
  ring

end Shepp.Section3
end SheppFlattenedModule022

section SheppFlattenedModule023
open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace Shepp.Section3

open ProbabilityTheory Shepp.Section2

theorem poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton]
  cases n <;> simp

theorem hasLaw_finsetSum_poisson
    {Ω ι : Type*} [MeasurableSpace Ω] {Pm : Measure Ω}
    {X : ι → Ω → ℕ} {rate : ι → ℝ≥0}
    (hIndep : iIndepFun X Pm)
    (hLaw : ∀ i, HasLaw (X i) (poissonMeasure (rate i)) Pm)
    (s : Finset ι) :
    HasLaw (∑ i ∈ s, X i)
      (poissonMeasure (∑ i ∈ s, rate i)) Pm := by
  classical
  letI : IsProbabilityMeasure Pm := hIndep.isProbabilityMeasure
  induction s using Finset.induction_on with
  | empty =>
      simpa [poissonMeasure_zero] using
        (hasLaw_dirac_of_ae_eq (X := (0 : Ω → ℕ))
          (Filter.Eventually.of_forall fun _ => (rfl : (0 : ℕ) = 0)) :
            HasLaw (0 : Ω → ℕ) (Measure.dirac 0) Pm)
  | @insert i s hi ih =>
      have hsumIndep := hIndep.indepFun_finsetSum_of_notMem₀
        (fun j => (hLaw j).aemeasurable) hi
      have hadd := hsumIndep.hasLaw_add_poissonMeasure ih (hLaw i)
      simpa [Finset.sum_insert hi, add_comm] using hadd

abbrev FiniteCloudSample (ι α : Type*) :=
  ι → PoissonCloudSample α

noncomputable def finiteCloudMeasure
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ι → ℝ≥0) :
    Measure (FiniteCloudSample ι α) :=
  Measure.pi fun i => poissonCloudMeasure μ (rate i)

noncomputable instance finiteCloudMeasure_isProbabilityMeasure
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ι → ℝ≥0) :
    IsProbabilityMeasure (finiteCloudMeasure μ rate) := by
  unfold finiteCloudMeasure
  infer_instance

theorem finiteCloudCoordinates_iIndepFun
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ι → ℝ≥0) :
    iIndepFun (fun i (ω : FiniteCloudSample ι α) => ω i)
      (finiteCloudMeasure μ rate) := by
  exact iIndepFun_pi fun _ => Measurable.aemeasurable measurable_id

theorem finiteCloudCoordinate_hasLaw
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ι → ℝ≥0)
    (i : ι) :
    HasLaw (fun ω : FiniteCloudSample ι α => ω i)
      (poissonCloudMeasure μ (rate i)) (finiteCloudMeasure μ rate) := by
  exact (measurePreserving_eval
    (fun j => poissonCloudMeasure μ (rate j)) i).hasLaw

theorem poissonCloudCount_hasLaw
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ℝ≥0) :
    HasLaw (fun ω : PoissonCloudSample α => ω.1)
      (poissonMeasure rate) (poissonCloudMeasure μ rate) := by
  unfold poissonCloudMeasure
  exact measurePreserving_fst.hasLaw

def finiteCloudAvoids
    {ι α : Type*} (E : ι → Set α) : Set (FiniteCloudSample ι α) :=
  Set.univ.pi fun i => cloudAvoids (E i)

theorem measurableSet_finiteCloudAvoids
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    {E : ι → Set α} (hE : ∀ i, MeasurableSet (E i)) :
    MeasurableSet (finiteCloudAvoids E) := by
  exact MeasurableSet.univ_pi fun i => measurableSet_cloudAvoids (hE i)

theorem finiteCloudMeasure_avoids
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ι → ℝ≥0)
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i)) :
    finiteCloudMeasure μ rate (finiteCloudAvoids E) =
      ENNReal.ofReal
        (Real.exp (-∑ i : ι, (rate i : ℝ) * μ.real (E i))) := by
  rw [finiteCloudMeasure, finiteCloudAvoids, Measure.pi_pi]
  simp_rw [poissonCloudMeasure_cloudAvoids μ (rate _) (hE _)]
  rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
    (fun i _ => Real.exp_nonneg _)]
  rw [← Real.exp_sum]
  congr 2
  simp only [neg_mul, Finset.sum_neg_distrib]

theorem finiteCloudMeasure_coordinateAvoids
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ι → ℝ≥0)
    (i : ι) {E : Set α} (hE : MeasurableSet E) :
    finiteCloudMeasure μ rate
        ((fun ω : FiniteCloudSample ι α => ω i) ⁻¹' cloudAvoids E) =
      ENNReal.ofReal
        (Real.exp (-(rate i : ℝ) * μ.real E)) := by
  rw [← Measure.map_apply (measurable_pi_apply i)
    (measurableSet_cloudAvoids hE)]
  rw [(finiteCloudCoordinate_hasLaw μ rate i).map_eq]
  exact poissonCloudMeasure_cloudAvoids μ (rate i) hE

def cloudPoints {α : Type*} (ω : PoissonCloudSample α) : Set α :=
  {x | ∃ i < ω.1, ω.2 i = x}

def markedCloudPoints {α : Type*} (n : ℕ)
    (ω : PoissonCloudSample α) : Set (α × ℕ) :=
  (fun x => (x, n)) '' cloudPoints ω

abbrev PacketMark
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :=
  ↥(packetIndices P k)

noncomputable def fractionalRate
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (n : PacketMark P k) (p : Fin (subblockCount P k)) : ℝ≥0 :=
  ⟨fractionalWeight P k n p, fractionalWeight_nonneg P k n p⟩

@[simp]
theorem coe_fractionalRate
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (n : PacketMark P k) (p : Fin (subblockCount P k)) :
    (fractionalRate P k n p : ℝ) = fractionalWeight P k n p := rfl

theorem fractionalRate_le_one
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (n : PacketMark P k) (p : Fin (subblockCount P k)) :
    fractionalRate P k n p ≤ 1 := by
  exact_mod_cast fractionalWeight_le_one P k n p

theorem subblockMass_eq_sum_fractionalRate
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) :
    subblockMass P k p =
      ∑ n : PacketMark P k,
        (fractionalRate P k n p : ℝ) * radiusVolume d r n := by
  rw [subblockMass_eq_sum_fractionalWeight P k p]
  rw [← (packetIndices P k).sum_attach]
  rfl

theorem sum_fractionalRate
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (n : PacketMark P k) :
    (∑ p : Fin (subblockCount P k), fractionalRate P k n p) = 1 := by
  apply NNReal.eq
  simpa using sum_fractionalWeight P n.property

abbrev PacketSubblockSample
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : Type*) :=
  FiniteCloudSample (PacketMark P k) α

noncomputable def packetSubblockMeasure
    {d : ℕ} {r : ℕ → ℝ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (P : GeometricPacketInterface d r) (k : ℕ)
    (p : Fin (subblockCount P k)) :
    Measure (PacketSubblockSample P k α) :=
  finiteCloudMeasure μ (fractionalRate P k · p)

noncomputable instance packetSubblockMeasure_isProbabilityMeasure
    {d : ℕ} {r : ℕ → ℝ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (P : GeometricPacketInterface d r) (k : ℕ)
    (p : Fin (subblockCount P k)) :
    IsProbabilityMeasure (packetSubblockMeasure μ P k p) := by
  unfold packetSubblockMeasure
  infer_instance

abbrev PacketCloudSample
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : Type*) :=
  (p : Fin (subblockCount P k)) → PacketSubblockSample P k α

noncomputable def packetCloudMeasure
    {d : ℕ} {r : ℕ → ℝ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (P : GeometricPacketInterface d r) (k : ℕ) :
    Measure (PacketCloudSample P k α) :=
  Measure.pi fun p => packetSubblockMeasure μ P k p

noncomputable instance packetCloudMeasure_isProbabilityMeasure
    {d : ℕ} {r : ℕ → ℝ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (P : GeometricPacketInterface d r) (k : ℕ) :
    IsProbabilityMeasure (packetCloudMeasure μ P k) := by
  unfold packetCloudMeasure
  infer_instance

theorem packetSubblocks_iIndepFun
    {d : ℕ} {r : ℕ → ℝ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (P : GeometricPacketInterface d r) (k : ℕ) :
    iIndepFun (fun p (ω : PacketCloudSample P k α) => ω p)
      (packetCloudMeasure μ P k) := by
  exact iIndepFun_pi fun _ => Measurable.aemeasurable measurable_id

noncomputable def packetFullCount
    {d : ℕ} {r : ℕ → ℝ} {α : Type*}
    {P : GeometricPacketInterface d r} {k : ℕ}
    (ω : PacketCloudSample P k α) (n : PacketMark P k) : ℕ :=
  ∑ p : Fin (subblockCount P k), (ω p n).1

theorem packetFullCount_hasLaw_poisson_one
    {d : ℕ} {r : ℕ → ℝ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (P : GeometricPacketInterface d r) (k : ℕ) (n : PacketMark P k) :
    HasLaw (fun ω : PacketCloudSample P k α => packetFullCount ω n)
      (poissonMeasure 1) (packetCloudMeasure μ P k) := by
  have hIndep :
      iIndepFun
        (fun p (ω : PacketCloudSample P k α) => (ω p n).1)
        (packetCloudMeasure μ P k) := by
    exact (packetSubblocks_iIndepFun μ P k).comp
      (fun _ block => (block n).1)
      (fun _ => measurable_fst.comp (measurable_pi_apply n))
  have hLaw : ∀ p : Fin (subblockCount P k),
      HasLaw (fun ω : PacketCloudSample P k α => (ω p n).1)
        (poissonMeasure (fractionalRate P k n p))
        (packetCloudMeasure μ P k) := by
    intro p
    have hp := (measurePreserving_eval
      (fun q => packetSubblockMeasure μ P k q) p).hasLaw
    have hn := finiteCloudCoordinate_hasLaw μ
      (fractionalRate P k · p) n
    exact (poissonCloudCount_hasLaw μ (fractionalRate P k n p)).fun_comp
      (hn.fun_comp hp)
  have hsum := hasLaw_finsetSum_poisson hIndep hLaw Finset.univ
  have hsumOne :
      HasLaw
        (∑ p : Fin (subblockCount P k),
          fun ω : PacketCloudSample P k α => (ω p n).1)
        (poissonMeasure 1) (packetCloudMeasure μ P k) := by
    simpa [sum_fractionalRate P k n] using hsum
  exact hsumOne.congr <| Filter.Eventually.of_forall fun ω => by
    simp [packetFullCount]

noncomputable def packetFullMarkAvoids
    {d : ℕ} {r : ℕ → ℝ} {α : Type*}
    {P : GeometricPacketInterface d r} {k : ℕ}
    (n : PacketMark P k) (E : Set α) : Set (PacketCloudSample P k α) :=
  Set.univ.pi fun _p =>
    (fun block : PacketSubblockSample P k α => block n) ⁻¹' cloudAvoids E

theorem measurableSet_packetFullMarkAvoids
    {d : ℕ} {r : ℕ → ℝ} {α : Type*} [MeasurableSpace α]
    {P : GeometricPacketInterface d r} {k : ℕ}
    (n : PacketMark P k) {E : Set α} (hE : MeasurableSet E) :
    MeasurableSet (packetFullMarkAvoids n E) := by
  exact MeasurableSet.univ_pi fun _ =>
    (measurableSet_cloudAvoids hE).preimage (measurable_pi_apply n)

theorem packetCloudMeasure_fullMarkAvoids
    {d : ℕ} {r : ℕ → ℝ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (P : GeometricPacketInterface d r) (k : ℕ)
    (n : PacketMark P k) {E : Set α} (hE : MeasurableSet E) :
  packetCloudMeasure μ P k (packetFullMarkAvoids n E) =
      ENNReal.ofReal (Real.exp (-μ.real E)) := by
  rw [packetCloudMeasure, packetFullMarkAvoids, Measure.pi_pi]
  simp only [packetSubblockMeasure]
  simp_rw [finiteCloudMeasure_coordinateAvoids μ
    (fractionalRate P k · _) n hE]
  rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
    (fun p _ => Real.exp_nonneg _)]
  rw [← Real.exp_sum]
  congr 2
  have hsumReal :
      (∑ p : Fin (subblockCount P k),
        (fractionalRate P k n p : ℝ)) = 1 := by
    exact_mod_cast sum_fractionalRate P k n
  calc
    (∑ p : Fin (subblockCount P k),
        -(fractionalRate P k n p : ℝ) * μ.real E) =
        -(∑ p : Fin (subblockCount P k),
          (fractionalRate P k n p : ℝ)) * μ.real E := by
      simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
    _ = -μ.real E := by rw [hsumReal]; ring

def packetSubblockAtoms
    {d : ℕ} {r : ℕ → ℝ} {α : Type*}
    {P : GeometricPacketInterface d r} {k : ℕ}
    (ω : PacketCloudSample P k α) (p : Fin (subblockCount P k)) :
    Set (α × ℕ) :=
  ⋃ n : PacketMark P k, markedCloudPoints n (ω p n)

def packetFullMarkAtoms
    {d : ℕ} {r : ℕ → ℝ} {α : Type*}
    {P : GeometricPacketInterface d r} {k : ℕ}
    (ω : PacketCloudSample P k α) (n : PacketMark P k) : Set (α × ℕ) :=
  ⋃ p : Fin (subblockCount P k), markedCloudPoints n (ω p n)

def packetFullAtoms
    {d : ℕ} {r : ℕ → ℝ} {α : Type*}
    {P : GeometricPacketInterface d r} {k : ℕ}
    (ω : PacketCloudSample P k α) : Set (α × ℕ) :=
  ⋃ n : PacketMark P k, packetFullMarkAtoms ω n

theorem packetFullAtoms_eq_iUnion_subblocks
    {d : ℕ} {r : ℕ → ℝ} {α : Type*}
    {P : GeometricPacketInterface d r} {k : ℕ}
    (ω : PacketCloudSample P k α) :
    packetFullAtoms ω =
      ⋃ p : Fin (subblockCount P k), packetSubblockAtoms ω p := by
  ext z
  simp only [packetFullAtoms, packetFullMarkAtoms, packetSubblockAtoms,
    Set.mem_iUnion]
  aesop

end Shepp.Section3
end SheppFlattenedModule023

section SheppFlattenedModule024
open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace Shepp.Section3

open ProbabilityTheory Shepp.Section2

theorem closedBall_subset_ball_of_mem_ball_sub
    {β : Type*} [PseudoMetricSpace β]
    {c y : β} {r ρ : ℝ} (hy : y ∈ Metric.ball c (r - ρ)) :
    Metric.closedBall c ρ ⊆ Metric.ball y r := by
  intro z hz
  rw [Metric.mem_closedBall] at hz
  rw [Metric.mem_ball] at hy ⊢
  calc
    dist z y ≤ dist z c + dist c y := dist_triangle z c y
    _ = dist z c + dist y c := by rw [dist_comm c y]
    _ < ρ + (r - ρ) := add_lt_add_of_le_of_lt hz hy
    _ = r := by ring

noncomputable def finiteCloudCovered
    {ι β : Type*} [Fintype ι] [PseudoMetricSpace β]
    (radius : ι → ℝ) (ω : FiniteCloudSample ι β) : Set β :=
  ⋃ i : ι, ⋃ j : Fin (ω i).1,
    Metric.ball ((ω i).2 j) (radius i)

noncomputable def finiteCloudResidual
    {ι β : Type*} [Fintype ι] [PseudoMetricSpace β]
    (radius : ι → ℝ) (ω : FiniteCloudSample ι β) : Set β :=
  (finiteCloudCovered radius ω)ᶜ

noncomputable def finiteCloudCellActive
    {ι β : Type*} [Fintype ι] [PseudoMetricSpace β]
    (radius : ι → ℝ) (Q : Set β) : Set (FiniteCloudSample ι β) :=
  {ω | (finiteCloudResidual radius ω ∩ Q).Nonempty}

theorem finiteCloudCellActive_subset_avoids
    {ι β : Type*} [Fintype ι] [PseudoMetricSpace β]
    (radius : ι → ℝ) {Q : Set β} {c : β} {ρ : ℝ}
    (hQ : Q ⊆ Metric.closedBall c ρ) :
    finiteCloudCellActive radius Q ⊆
      finiteCloudAvoids (fun i => Metric.ball c (radius i - ρ)) := by
  intro ω hactive
  rcases hactive with ⟨z, hzResidual, hzQ⟩
  rw [finiteCloudAvoids]
  intro i _
  change ∀ j < (ω i).1,
    (ω i).2 j ∉ Metric.ball c (radius i - ρ)
  intro j hj
  intro hcenter
  have hzBall : z ∈ Metric.ball ((ω i).2 j) (radius i) :=
    closedBall_subset_ball_of_mem_ball_sub hcenter (hQ hzQ)
  have hzCovered : z ∈ finiteCloudCovered radius ω := by
    simp only [finiteCloudCovered, Set.mem_iUnion]
    exact ⟨i, ⟨⟨j, hj⟩, hzBall⟩⟩
  exact hzResidual hzCovered

theorem finiteCloudMeasure_cellActive_le
    {ι β : Type*} [Fintype ι] [PseudoMetricSpace β]
    [MeasurableSpace β] [BorelSpace β]
    (μ : Measure β) [IsProbabilityMeasure μ] (rate : ι → ℝ≥0)
    (radius : ι → ℝ) {Q : Set β} {c : β} {ρ : ℝ}
    (hQ : Q ⊆ Metric.closedBall c ρ) :
    finiteCloudMeasure μ rate (finiteCloudCellActive radius Q) ≤
      ENNReal.ofReal
        (Real.exp (-∑ i : ι, (rate i : ℝ) *
          μ.real (Metric.ball c (radius i - ρ)))) := by
  calc
    finiteCloudMeasure μ rate (finiteCloudCellActive radius Q) ≤
        finiteCloudMeasure μ rate
          (finiteCloudAvoids (fun i => Metric.ball c (radius i - ρ))) :=
      measure_mono (finiteCloudCellActive_subset_avoids radius hQ)
    _ = ENNReal.ofReal
        (Real.exp (-∑ i : ι, (rate i : ℝ) *
          μ.real (Metric.ball c (radius i - ρ)))) :=
      finiteCloudMeasure_avoids μ rate _
        (fun _ => Metric.isOpen_ball.measurableSet)

theorem flatTorusVolumeReal_ball_gridCenter
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) (α : GridLabel P k)
    {t : ℝ} (ht : 0 ≤ t) (htsmall : t < 1 / 4) :
    (flatTorusVolume d).real (Metric.ball (gridCenter P k α) t) =
      euclideanUnitBallVolume d * t ^ d := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [Measure.real, gridCenter,
    flatTorusVolume_ball_eq_volume d htsmall,
    EuclideanSpace.volume_ball, Fintype.card_fin]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal ht]
  rw [ENNReal.toReal_ofReal (by
    simpa only [euclideanUnitBallVolume] using
      (euclideanUnitBallVolume_pos d).le)]
  unfold euclideanUnitBallVolume
  ring_nf

theorem pow_sub_pow_le_radius_error
    (d : ℕ) {x ρ : ℝ} (hx : 0 < x) (hρ : 0 ≤ ρ) (hρx : ρ ≤ x) :
    x ^ d - (x - ρ) ^ d ≤ ρ * (d : ℝ) * x ^ (d - 1) := by
  have hxsub : 0 ≤ x - ρ := sub_nonneg.mpr hρx
  have hxsub_le : x - ρ ≤ x := by linarith
  have hpow : (x - ρ) ^ d ≤ x ^ d := by
    gcongr
  have habsPow : |x ^ d - (x - ρ) ^ d| =
      x ^ d - (x - ρ) ^ d := abs_of_nonneg (sub_nonneg.mpr hpow)
  have hdiff : x - (x - ρ) = ρ := by ring
  have hmax : max |x| |x - ρ| = x := by
    rw [abs_of_pos hx, abs_of_nonneg hxsub, max_eq_left hxsub_le]
  have h := abs_pow_sub_pow_le (a := x) (b := x - ρ) d
  rw [habsPow, hdiff, abs_of_nonneg hρ, hmax] at h
  exact h

theorem radiusVolume_sub_inner_le_slope_error
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (n : ℕ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρr : ρ ≤ r n) :
    radiusVolume d r n -
        euclideanUnitBallVolume d * (r n - ρ) ^ d ≤
      (d : ℝ) * ρ * (radiusVolume d r n / r n) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have hpow := pow_sub_pow_le_radius_error (e + 1)
    (P.radius_pos n) hρ hρr
  have hκ := (euclideanUnitBallVolume_pos (e + 1)).le
  have hmul := mul_le_mul_of_nonneg_left hpow hκ
  rw [radiusVolume]
  calc
    euclideanUnitBallVolume (e + 1) * r n ^ (e + 1) -
        euclideanUnitBallVolume (e + 1) * (r n - ρ) ^ (e + 1) =
        euclideanUnitBallVolume (e + 1) *
          (r n ^ (e + 1) - (r n - ρ) ^ (e + 1)) := by ring
    _ ≤ euclideanUnitBallVolume (e + 1) *
        (ρ * ((e + 1 : ℕ) : ℝ) * r n ^ ((e + 1) - 1)) := hmul
    _ = ((e + 1 : ℕ) : ℝ) * ρ *
        (euclideanUnitBallVolume (e + 1) * r n ^ (e + 1) / r n) := by
      rw [Nat.add_sub_cancel, pow_succ]
      field_simp [(P.radius_pos n).ne']

abbrev PrefixMark
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :=
  Fin (P.cutoff k + 1)

theorem weighted_inner_volume_ge
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (rate : PrefixMark P k → ℝ≥0)
    (hrate : ∀ n, rate n ≤ 1) (a : ℝ)
    (hmass :
      (∑ n : PrefixMark P k,
        (rate n : ℝ) * radiusVolume d r n) = a) :
    a - (d : ℝ) ^ 2 / 4 ≤
      ∑ n : PrefixMark P k,
        (rate n : ℝ) * euclideanUnitBallVolume d *
          (r n - gridCircumradius P k) ^ d := by
  let ρ : ℝ := gridCircumradius P k
  let v : ℕ → ℝ := radiusVolume d r
  have hρ : 0 ≤ ρ := gridCircumradius_nonneg P k
  have hlevelPos : 0 < P.level k := test_dyadicLevel_pos (P.K + k)
  have hρlevel : ρ ≤ P.level k := by
    have hquarter := gridCircumradius_le_level_div_four P k
    dsimp only [ρ]
    linarith
  have hlevelRadius : ∀ n : PrefixMark P k, P.level k ≤ r n := by
    intro n
    exact P.level_le_radius k n (Nat.lt_succ_iff.mp n.isLt)
  have hρRadius : ∀ n : PrefixMark P k, ρ ≤ r n :=
    fun n => hρlevel.trans (hlevelRadius n)
  have hlossNonneg : ∀ n : PrefixMark P k,
      0 ≤ v n - euclideanUnitBallVolume d * (r n - ρ) ^ d := by
    intro n
    have hinnerNonneg : 0 ≤ r n - ρ := sub_nonneg.mpr (hρRadius n)
    have hpow : (r n - ρ) ^ d ≤ (r n) ^ d := by
      gcongr
      linarith
    dsimp only [v]
    rw [radiusVolume]
    nlinarith [euclideanUnitBallVolume_pos d]
  have hlossLe : ∀ n : PrefixMark P k,
      v n - euclideanUnitBallVolume d * (r n - ρ) ^ d ≤
        (d : ℝ) * ρ * (v n / r n) := by
    intro n
    exact radiusVolume_sub_inner_le_slope_error hd P n hρ (hρRadius n)
  have hslopeTermNonneg : ∀ n : PrefixMark P k, 0 ≤ v n / r n := by
    intro n
    exact div_nonneg (P.radiusVolume_nonneg n) (P.radius_pos n).le
  have hweightedLoss :
      (∑ n : PrefixMark P k,
        (rate n : ℝ) *
          (v n - euclideanUnitBallVolume d * (r n - ρ) ^ d)) ≤
        (d : ℝ) * ρ * prefixSlope r v (P.cutoff k) := by
    calc
      (∑ n : PrefixMark P k,
          (rate n : ℝ) *
            (v n - euclideanUnitBallVolume d * (r n - ρ) ^ d)) ≤
          ∑ n : PrefixMark P k, (d : ℝ) * ρ * (v n / r n) := by
        apply Finset.sum_le_sum
        intro n _
        calc
          (rate n : ℝ) *
              (v n - euclideanUnitBallVolume d * (r n - ρ) ^ d) ≤
              (rate n : ℝ) * ((d : ℝ) * ρ * (v n / r n)) :=
            mul_le_mul_of_nonneg_left (hlossLe n) (rate n).coe_nonneg
          _ ≤ 1 * ((d : ℝ) * ρ * (v n / r n)) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hrate n
            · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hρ)
                (hslopeTermNonneg n)
          _ = (d : ℝ) * ρ * (v n / r n) := one_mul _
      _ = (d : ℝ) * ρ *
          (∑ n : PrefixMark P k, v n / r n) := by
        rw [Finset.mul_sum]
      _ = (d : ℝ) * ρ * prefixSlope r v (P.cutoff k) := by
        congr 1
        rw [Fin.sum_univ_eq_sum_range
          (fun n : ℕ => v n / r n) (P.cutoff k + 1)]
        rfl
  have hslopeNonneg : 0 ≤ prefixSlope r v (P.cutoff k) := by
    rw [prefixSlope]
    exact Finset.sum_nonneg fun n _ =>
      div_nonneg (P.radiusVolume_nonneg n) (P.radius_pos n).le
  have hbudget :
      (d : ℝ) * ρ * prefixSlope r v (P.cutoff k) ≤
        (d : ℝ) ^ 2 / 4 := by
    have hρS : ρ * prefixSlope r v (P.cutoff k) ≤
        (P.level k / 4) * prefixSlope r v (P.cutoff k) :=
      mul_le_mul_of_nonneg_right
        (gridCircumradius_le_level_div_four P k) hslopeNonneg
    have hlevelS := P.level_mul_slope_le k
    have hdnonneg : 0 ≤ (d : ℝ) := by positivity
    nlinarith
  have hlossBudget :
      (∑ n : PrefixMark P k,
        (rate n : ℝ) *
          (v n - euclideanUnitBallVolume d * (r n - ρ) ^ d)) ≤
        (d : ℝ) ^ 2 / 4 := hweightedLoss.trans hbudget
  have hidentity :
      (∑ n : PrefixMark P k,
        (rate n : ℝ) * euclideanUnitBallVolume d * (r n - ρ) ^ d) =
      a - ∑ n : PrefixMark P k,
        (rate n : ℝ) *
          (v n - euclideanUnitBallVolume d * (r n - ρ) ^ d) := by
    have hmassv :
        (∑ n : PrefixMark P k, (rate n : ℝ) * v n) = a := by
      simpa only [v] using hmass
    calc
      (∑ n : PrefixMark P k,
          (rate n : ℝ) * euclideanUnitBallVolume d * (r n - ρ) ^ d) =
          (∑ n : PrefixMark P k, (rate n : ℝ) * v n) -
            ∑ n : PrefixMark P k,
              (rate n : ℝ) *
                (v n - euclideanUnitBallVolume d * (r n - ρ) ^ d) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = a - ∑ n : PrefixMark P k,
            (rate n : ℝ) *
              (v n - euclideanUnitBallVolume d * (r n - ρ) ^ d) := by
        rw [hmassv]
  rw [show gridCircumradius P k = ρ from rfl]
  rw [hidentity]
  linarith

theorem activeCell_probability_le_exp
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (rate : PrefixMark P k → ℝ≥0)
    (hrate : ∀ n, rate n ≤ 1) (a : ℝ)
    (hmass :
      (∑ n : PrefixMark P k,
        (rate n : ℝ) * radiusVolume d r n) = a)
    (α : GridLabel P k) :
    finiteCloudMeasure (flatTorusVolume d) rate
        (finiteCloudCellActive (fun n : PrefixMark P k => r n)
          (gridCell P k α)) ≤
      ENNReal.ofReal (Real.exp (-(a) + (d : ℝ) ^ 2 / 4)) := by
  let ρ : ℝ := gridCircumradius P k
  have hρ : 0 ≤ ρ := gridCircumradius_nonneg P k
  have hρlevel : ρ ≤ P.level k := by
    have hquarter := gridCircumradius_le_level_div_four P k
    have hlevelPos : 0 < P.level k := test_dyadicLevel_pos (P.K + k)
    dsimp only [ρ]
    linarith
  have hlevelRadius : ∀ n : PrefixMark P k, P.level k ≤ r n := by
    intro n
    exact P.level_le_radius k n (Nat.lt_succ_iff.mp n.isLt)
  have hρRadius : ∀ n : PrefixMark P k, ρ ≤ r n :=
    fun n => hρlevel.trans (hlevelRadius n)
  have hvol : ∀ n : PrefixMark P k,
      (flatTorusVolume d).real
          (Metric.ball (gridCenter P k α) (r n - ρ)) =
        euclideanUnitBallVolume d * (r n - ρ) ^ d := by
    intro n
    apply flatTorusVolumeReal_ball_gridCenter hd P k α
    · exact sub_nonneg.mpr (hρRadius n)
    · exact lt_of_le_of_lt (sub_le_self _ hρ) (P.radius_lt_quarter n)
  have hbase := finiteCloudMeasure_cellActive_le
    (flatTorusVolume d) rate (fun n : PrefixMark P k => r n)
    (hQ := gridCell_subset_closedBall P k α)
  change finiteCloudMeasure (flatTorusVolume d) rate
      (finiteCloudCellActive (fun n : PrefixMark P k => r n)
        (gridCell P k α)) ≤ _ at hbase
  simp_rw [show gridCircumradius P k = ρ from rfl, hvol] at hbase
  have hexponent := weighted_inner_volume_ge hd P k rate hrate a hmass
  rw [show gridCircumradius P k = ρ from rfl] at hexponent
  have hexponent' :
      a - (d : ℝ) ^ 2 / 4 ≤
        ∑ n : PrefixMark P k,
          (rate n : ℝ) *
            (euclideanUnitBallVolume d * (r n - ρ) ^ d) := by
    simpa only [mul_assoc] using hexponent
  refine hbase.trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  linarith

noncomputable def activeCellMean
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (rate : PrefixMark P k → ℝ≥0) : ℝ≥0∞ :=
  ∑ α : GridLabel P k,
    finiteCloudMeasure (flatTorusVolume d) rate
      (finiteCloudCellActive (fun n : PrefixMark P k => r n)
        (gridCell P k α))

theorem activeCellMean_le_card_mul
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (rate : PrefixMark P k → ℝ≥0)
    (hrate : ∀ n, rate n ≤ 1) (a : ℝ)
    (hmass :
      (∑ n : PrefixMark P k,
        (rate n : ℝ) * radiusVolume d r n) = a) :
    activeCellMean P k rate ≤
      (Fintype.card (GridLabel P k) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(a) + (d : ℝ) ^ 2 / 4)) := by
  unfold activeCellMean
  calc
    (∑ α : GridLabel P k,
        finiteCloudMeasure (flatTorusVolume d) rate
          (finiteCloudCellActive (fun n : PrefixMark P k => r n)
            (gridCell P k α))) ≤
        ∑ _α : GridLabel P k,
          ENNReal.ofReal (Real.exp (-(a) + (d : ℝ) ^ 2 / 4)) := by
      apply Finset.sum_le_sum
      intro α _
      exact activeCell_probability_le_exp hd P k rate hrate a hmass α
    _ = (Fintype.card (GridLabel P k) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(a) + (d : ℝ) ^ 2 / 4)) := by
      simp

noncomputable def firstMomentConstant (d : ℕ) : ℝ :=
  (gridEta d)⁻¹ ^ d * Real.exp ((d : ℝ) ^ 2 / 4)

theorem firstMomentConstant_pos (d : ℕ) :
    0 < firstMomentConstant d := by
  unfold firstMomentConstant
  exact mul_pos (pow_pos (inv_pos.mpr (gridEta_pos d)) d)
    (Real.exp_pos _)

theorem activeCellMean_le
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (rate : PrefixMark P k → ℝ≥0)
    (hrate : ∀ n, rate n ≤ 1) (a : ℝ)
    (hmass :
      (∑ n : PrefixMark P k,
        (rate n : ℝ) * radiusVolume d r n) = a) :
    activeCellMean P k rate ≤
      ENNReal.ofReal
        (firstMomentConstant d * (P.level k)⁻¹ ^ d * Real.exp (-a)) := by
  refine (activeCellMean_le_card_mul hd P k rate hrate a hmass).trans_eq ?_
  rw [← ENNReal.ofReal_natCast (Fintype.card (GridLabel P k))]
  rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply congrArg ENNReal.ofReal
  rw [card_gridLabel_real P k, Real.exp_add]
  unfold firstMomentConstant
  ring

end Shepp.Section3
end SheppFlattenedModule024

section SheppFlattenedModule025
open scoped BigOperators NNReal ENNReal

namespace Shepp.Section3

open Shepp.Section2

theorem packetStartMass_nonneg
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    0 ≤ packetStartMass P k := by
  cases k with
  | zero => simp [packetStartMass]
  | succ k =>
      rw [packetStartMass, prefixMass]
      exact Finset.sum_nonneg fun n _ => P.radiusVolume_nonneg n

theorem packetEndMass_nonneg
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    0 ≤ packetEndMass P k := by
  rw [packetEndMass, prefixMass]
  exact Finset.sum_nonneg fun n _ => P.radiusVolume_nonneg n

theorem markIntervalLower_nonneg
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (n : ℕ) :
    0 ≤ markIntervalLower P n := by
  cases n with
  | zero => simp [markIntervalLower, previousMass]
  | succ n =>
      rw [markIntervalLower, previousMass_succ, prefixMass]
      exact Finset.sum_nonneg fun i _ => P.radiusVolume_nonneg i

theorem scheduledMass_nonneg
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k p : ℕ) :
    0 ≤ scheduledMass P k p :=
  (packetStartMass_nonneg P k).trans
    (packetStartMass_le_subblockBoundary P k p)

noncomputable def scheduledOverlap
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) (n : PrefixMark P k) : ℝ :=
  intervalOverlap (markIntervalLower P n) (markIntervalUpper P n)
    0 (scheduledMass P k p)

theorem scheduledOverlap_nonneg
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) (n : PrefixMark P k) :
    0 ≤ scheduledOverlap P k p n :=
  intervalOverlap_nonneg _ _ _ _

theorem scheduledOverlap_le_radiusVolume
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) (n : PrefixMark P k) :
    scheduledOverlap P k p n ≤ radiusVolume d r n := by
  calc
    scheduledOverlap P k p n ≤
        markIntervalUpper P n - markIntervalLower P n :=
      intervalOverlap_le_left_length (markIntervalLower_le_upper P n)
        (scheduledMass_nonneg P k p)
    _ = radiusVolume d r n := markInterval_length P n

theorem scheduledOverlap_eq_radiusVolume_of_upper_le
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) (n : PrefixMark P k)
    (hupper : markIntervalUpper P n ≤ scheduledMass P k p) :
    scheduledOverlap P k p n = radiusVolume d r n := by
  have hlower0 : 0 ≤ markIntervalLower P n := markIntervalLower_nonneg P n
  have hlowerUpper := markIntervalLower_le_upper P n
  rw [scheduledOverlap,
    intervalOverlap_eq_clamp_sub hlowerUpper (scheduledMass_nonneg P k p)]
  rw [max_eq_left (hlower0.trans hlowerUpper),
    min_eq_left hupper, max_eq_left hlower0,
    min_eq_left (hlowerUpper.trans hupper)]
  exact markInterval_length P n

theorem scheduledOverlap_eq_zero_of_le_lower
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) (n : PrefixMark P k)
    (hleft : scheduledMass P k p ≤ markIntervalLower P n) :
    scheduledOverlap P k p n = 0 := by
  unfold scheduledOverlap intervalOverlap
  rw [min_eq_right (hleft.trans (markIntervalLower_le_upper P n)),
    max_eq_left (markIntervalLower_nonneg P n)]
  exact max_eq_right (sub_nonpos.mpr hleft)

noncomputable def scheduledRate
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) (n : PrefixMark P k) : ℝ≥0 :=
  ⟨scheduledOverlap P k p n / radiusVolume d r n,
    div_nonneg (scheduledOverlap_nonneg P k p n)
      (P.radiusVolume_nonneg n)⟩

@[simp]
theorem coe_scheduledRate
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) (n : PrefixMark P k) :
    (scheduledRate P k p n : ℝ) =
      scheduledOverlap P k p n / radiusVolume d r n := rfl

theorem scheduledRate_le_one
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) (n : PrefixMark P k) :
    scheduledRate P k p n ≤ 1 := by
  apply NNReal.coe_le_coe.mp
  rw [coe_scheduledRate]
  exact (div_le_one (P.radiusVolume_pos n)).2
    (scheduledOverlap_le_radiusVolume P k p n)

theorem scheduledRate_mul_radiusVolume
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) (n : PrefixMark P k) :
    (scheduledRate P k p n : ℝ) * radiusVolume d r n =
      scheduledOverlap P k p n := by
  rw [coe_scheduledRate]
  exact div_mul_cancel₀ _ (P.radiusVolume_pos n).ne'

theorem scheduledRate_old_eq_one
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) (n : PrefixMark P (k + 1))
    (hn : (n : ℕ) ≤ P.cutoff k) :
    scheduledRate P (k + 1) p n = 1 := by
  have hupperStart : markIntervalUpper P n ≤ packetStartMass P (k + 1) := by
    rw [markIntervalUpper, packetStartMass]
    exact prefixMass_mono P.radiusVolume_nonneg hn
  have hupper : markIntervalUpper P n ≤ scheduledMass P (k + 1) p :=
    hupperStart.trans (packetStartMass_le_subblockBoundary P (k + 1) p)
  apply NNReal.eq
  rw [coe_scheduledRate, scheduledOverlap_eq_radiusVolume_of_upper_le
    P (k + 1) p n hupper, div_self (P.radiusVolume_pos n).ne']
  rfl

theorem scheduledRate_current_zero
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (n : PacketMark P k) :
    scheduledRate P k 0
        ⟨n, Nat.lt_succ_of_le (mem_packetIndices_le_cutoff P n.property)⟩ = 0 := by
  let n' : PrefixMark P k :=
    ⟨n, Nat.lt_succ_of_le (mem_packetIndices_le_cutoff P n.property)⟩
  have hleft : scheduledMass P k 0 ≤ markIntervalLower P n' := by
    rw [scheduledMass_zero]
    exact (markInterval_mem_packet_bounds P n.property).1
  apply NNReal.eq
  rw [coe_scheduledRate, scheduledOverlap_eq_zero_of_le_lower P k 0 n' hleft]
  simp

theorem scheduledOverlap_succ
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) (n : PrefixMark P k) :
    scheduledOverlap P k ((p : ℕ) + 1) n =
      scheduledOverlap P k p n + fractionalOverlap P k n p := by
  let a : ℝ := markIntervalLower P n
  let b : ℝ := markIntervalUpper P n
  let L : ℝ := scheduledMass P k p
  let U : ℝ := scheduledMass P k ((p : ℕ) + 1)
  let F : ℝ → ℝ := fun x => min (max x a) b
  have hab : a ≤ b := markIntervalLower_le_upper P n
  have h0L : 0 ≤ L := scheduledMass_nonneg P k p
  have hLU : L ≤ U := subblockBoundary_monotone P k (Nat.le_succ _)
  have hwholeL : scheduledOverlap P k p n = F L - F 0 := by
    rw [scheduledOverlap, intervalOverlap_symm]
    exact intervalOverlap_eq_clamp_sub h0L hab
  have hwholeU : scheduledOverlap P k ((p : ℕ) + 1) n = F U - F 0 := by
    rw [scheduledOverlap, intervalOverlap_symm]
    exact intervalOverlap_eq_clamp_sub (h0L.trans hLU) hab
  have hpiece : fractionalOverlap P k n p = F U - F L := by
    rw [fractionalOverlap, intervalOverlap_symm]
    exact intervalOverlap_eq_clamp_sub hLU hab
  rw [hwholeL, hwholeU, hpiece]
  ring

theorem scheduledRate_current_succ
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) (n : PacketMark P k) :
    scheduledRate P k ((p : ℕ) + 1)
        ⟨n, Nat.lt_succ_of_le (mem_packetIndices_le_cutoff P n.property)⟩ =
      scheduledRate P k p
          ⟨n, Nat.lt_succ_of_le (mem_packetIndices_le_cutoff P n.property)⟩ +
        fractionalRate P k n p := by
  apply NNReal.eq
  simp only [NNReal.coe_add, coe_scheduledRate, coe_fractionalRate,
    fractionalWeight]
  rw [scheduledOverlap_succ]
  field_simp [(P.radiusVolume_pos n).ne']

theorem sum_scheduledOverlap
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) :
    (∑ n : PrefixMark P k, scheduledOverlap P k p n) =
      scheduledMass P k p := by
  let v : ℕ → ℝ := radiusVolume d r
  let s : ℝ := scheduledMass P k p
  let F : ℝ → ℝ := fun x => min (max x 0) s
  have hs0 : 0 ≤ s := scheduledMass_nonneg P k p
  have hsEnd : s ≤ prefixMass v (P.cutoff k) := by
    exact subblockBoundary_le_packetEndMass P k p
  have hterm : ∀ n : ℕ,
      intervalOverlap (markIntervalLower P n) (markIntervalUpper P n) 0 s =
        F (prefixMass v n) - F (previousMass v n) := by
    intro n
    exact intervalOverlap_eq_clamp_sub
      (markIntervalLower_le_upper P n) hs0
  have hEndNonneg : 0 ≤ prefixMass v (P.cutoff k) := by
    simpa only [v, packetEndMass] using packetEndMass_nonneg P k
  change (∑ n : Fin (P.cutoff k + 1),
    intervalOverlap (markIntervalLower P n) (markIntervalUpper P n) 0 s) = s
  calc
    (∑ n : Fin (P.cutoff k + 1),
        intervalOverlap (markIntervalLower P n) (markIntervalUpper P n) 0 s) =
        ∑ n ∈ Finset.range (P.cutoff k + 1),
          intervalOverlap (markIntervalLower P n) (markIntervalUpper P n) 0 s :=
      Fin.sum_univ_eq_sum_range
        (fun n : ℕ => intervalOverlap (markIntervalLower P n)
          (markIntervalUpper P n) 0 s) (P.cutoff k + 1)
    _ = ∑ n ∈ Finset.range (P.cutoff k + 1),
        (F (prefixMass v n) - F (previousMass v n)) := by
      apply Finset.sum_congr rfl
      intro n _
      exact hterm n
    _ = F (prefixMass v (P.cutoff k)) - F 0 :=
      sum_prefixEndpointDifference_range v F (P.cutoff k)
    _ = s := by
      dsimp only [F]
      rw [max_eq_left hEndNonneg, min_eq_right hsEnd]
      simp [hs0]

theorem sum_scheduledRate_mul_radiusVolume
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) :
    (∑ n : PrefixMark P k,
      (scheduledRate P k p n : ℝ) * radiusVolume d r n) =
      scheduledMass P k p := by
  calc
    (∑ n : PrefixMark P k,
        (scheduledRate P k p n : ℝ) * radiusVolume d r n) =
        ∑ n : PrefixMark P k, scheduledOverlap P k p n := by
      apply Finset.sum_congr rfl
      intro n _
      exact scheduledRate_mul_radiusVolume P k p n
    _ = scheduledMass P k p := sum_scheduledOverlap P k p

noncomputable def scheduledActiveMean
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) : ℝ≥0∞ :=
  activeCellMean P k (scheduledRate P k p)

theorem scheduledActiveMean_le
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k p : ℕ) :
    scheduledActiveMean P k p ≤
      ENNReal.ofReal
        (firstMomentConstant d * (P.level k)⁻¹ ^ d *
          Real.exp (-(scheduledMass P k p))) := by
  exact activeCellMean_le hd P k (scheduledRate P k p)
    (scheduledRate_le_one P k p) (scheduledMass P k p)
    (sum_scheduledRate_mul_radiusVolume P k p)

theorem scheduledActiveMean_lt_top
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k p : ℕ) :
    scheduledActiveMean P k p < ∞ := by
  exact (scheduledActiveMean_le hd P k p).trans_lt ENNReal.ofReal_lt_top

end Shepp.Section3
end SheppFlattenedModule025

section SheppFlattenedModule026
open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace Shepp.Section3

open ProbabilityTheory Shepp.Section2

noncomputable def killingFraction (d : ℕ) : ℝ :=
  (3 / 4 : ℝ) ^ d

theorem killingFraction_pos (d : ℕ) : 0 < killingFraction d := by
  unfold killingFraction
  positivity

theorem killingFraction_nonneg (d : ℕ) : 0 ≤ killingFraction d :=
  (killingFraction_pos d).le

noncomputable def killingLinearConstant (d : ℕ) : ℝ :=
  1 - Real.exp (-killingFraction d)

theorem killingLinearConstant_pos (d : ℕ) :
    0 < killingLinearConstant d := by
  unfold killingLinearConstant
  have hexp : Real.exp (-killingFraction d) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (killingFraction_pos d)
  linarith

theorem one_sub_exp_neg_killing_mul_ge_linear
    (d : ℕ) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    killingLinearConstant d * b ≤
      1 - Real.exp (-(killingFraction d * b)) := by
  have hconv : Real.exp (-(killingFraction d * b)) ≤
      (1 - b) * Real.exp 0 + b * Real.exp (-killingFraction d) := by
    calc
      Real.exp (-(killingFraction d * b)) =
          Real.exp ((1 - b) * 0 + b * (-killingFraction d)) := by
        congr 1
        ring
      _ ≤ (1 - b) * Real.exp 0 +
          b * Real.exp (-killingFraction d) :=
        convexOn_exp.2 (Set.mem_univ 0)
          (Set.mem_univ (-killingFraction d)) (by linarith) hb0 (by ring)
  unfold killingLinearConstant
  rw [Real.exp_zero] at hconv
  linarith

noncomputable def subblockCellCoverEvent
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) (α : GridLabel P k) :
    Set (PacketSubblockSample P k (FlatTorus d)) :=
  (finiteCloudAvoids (fun n : PacketMark P k =>
    Metric.ball (gridCenter P k α)
      (r n - gridCircumradius P k)))ᶜ

theorem measurableSet_subblockCellCoverEvent
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) (α : GridLabel P k) :
    MeasurableSet (subblockCellCoverEvent P k α) := by
  exact (measurableSet_finiteCloudAvoids
    (fun _ => Metric.isOpen_ball.measurableSet)).compl

theorem gridCell_subset_finiteCloudCovered_of_mem_coverEvent
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) (α : GridLabel P k)
    {ω : PacketSubblockSample P k (FlatTorus d)}
    (hω : ω ∈ subblockCellCoverEvent P k α) :
    gridCell P k α ⊆
      finiteCloudCovered (fun n : PacketMark P k => r n) ω := by
  intro z hzQ
  by_contra hzCovered
  apply hω
  rw [finiteCloudAvoids]
  intro n _
  change ∀ j < (ω n).1,
    (ω n).2 j ∉ Metric.ball (gridCenter P k α)
      (r n - gridCircumradius P k)
  intro j hj hcenter
  have hzBall : z ∈ Metric.ball ((ω n).2 j) (r n) :=
    closedBall_subset_ball_of_mem_ball_sub hcenter
      (gridCell_subset_closedBall P k α hzQ)
  apply hzCovered
  simp only [finiteCloudCovered, Set.mem_iUnion]
  exact ⟨n, ⟨⟨j, hj⟩, hzBall⟩⟩

theorem subset_diff_finiteCloudCovered_eq_empty_of_mem_coverEvent
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) (α : GridLabel P k)
    {A : Set (FlatTorus d)} (hA : A ⊆ gridCell P k α)
    {ω : PacketSubblockSample P k (FlatTorus d)}
    (hω : ω ∈ subblockCellCoverEvent P k α) :
    A \ finiteCloudCovered (fun n : PacketMark P k => r n) ω = ∅ := by
  ext z
  constructor
  · intro hz
    exact (hz.2 (gridCell_subset_finiteCloudCovered_of_mem_coverEvent
      P k α hω (hA hz.1))).elim
  · intro hz
    exact hz.elim

theorem packetSubblockMeasureReal_coverEvent
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (p : Fin (subblockCount P k)) (α : GridLabel P k) :
    (packetSubblockMeasure (flatTorusVolume d) P k p).real
        (subblockCellCoverEvent P k α) =
      1 - Real.exp
        (-∑ n : PacketMark P k,
          (fractionalRate P k n p : ℝ) *
            euclideanUnitBallVolume d *
              (r n - gridCircumradius P k) ^ d) := by
  let ρ : ℝ := gridCircumradius P k
  have hρ : 0 ≤ ρ := gridCircumradius_nonneg P k
  have hρlevel : ρ ≤ P.level k := by
    have hquarter := gridCircumradius_le_level_div_four P k
    have hlevelPos : 0 < P.level k := test_dyadicLevel_pos (P.K + k)
    dsimp only [ρ]
    linarith
  have hlevelRadius : ∀ n : PacketMark P k, P.level k ≤ r n := by
    intro n
    exact P.level_le_radius k n
      (mem_packetIndices_le_cutoff P n.property)
  have hρRadius : ∀ n : PacketMark P k, ρ ≤ r n :=
    fun n => hρlevel.trans (hlevelRadius n)
  have hvol : ∀ n : PacketMark P k,
      (flatTorusVolume d).real
          (Metric.ball (gridCenter P k α) (r n - ρ)) =
        euclideanUnitBallVolume d * (r n - ρ) ^ d := by
    intro n
    apply flatTorusVolumeReal_ball_gridCenter hd P k α
    · exact sub_nonneg.mpr (hρRadius n)
    · exact lt_of_le_of_lt (sub_le_self _ hρ) (P.radius_lt_quarter n)
  rw [subblockCellCoverEvent,
    measureReal_compl
      (measurableSet_finiteCloudAvoids
        (fun _ => Metric.isOpen_ball.measurableSet)),
    probReal_univ]
  change 1 - (finiteCloudMeasure (flatTorusVolume d)
    (fractionalRate P k · p)).real
      (finiteCloudAvoids (fun n : PacketMark P k =>
        Metric.ball (gridCenter P k α) (r n - ρ))) = _
  rw [Measure.real,
    finiteCloudMeasure_avoids (flatTorusVolume d)
      (fractionalRate P k · p) _
      (fun _ => Metric.isOpen_ball.measurableSet),
    ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  simp_rw [hvol]
  rw [show gridCircumradius P k = ρ from rfl]
  simp only [mul_assoc]

theorem subblock_inner_intensity_ge
    {d : ℕ} (_hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (p : Fin (subblockCount P k)) :
    killingFraction d * subblockMass P k p ≤
      ∑ n : PacketMark P k,
        (fractionalRate P k n p : ℝ) *
          euclideanUnitBallVolume d *
            (r n - gridCircumradius P k) ^ d := by
  have hκ : 0 ≤ euclideanUnitBallVolume d :=
    (euclideanUnitBallVolume_pos d).le
  have hρ : 0 ≤ gridCircumradius P k :=
    gridCircumradius_nonneg P k
  have hinner : ∀ n : PacketMark P k,
      killingFraction d * radiusVolume d r n ≤
        euclideanUnitBallVolume d *
          (r n - gridCircumradius P k) ^ d := by
    intro n
    have hlevelRadius : P.level k ≤ r n :=
      P.level_le_radius k n (mem_packetIndices_le_cutoff P n.property)
    have hρquarter : gridCircumradius P k ≤ r n / 4 :=
      (gridCircumradius_le_level_div_four P k).trans
        (div_le_div_of_nonneg_right hlevelRadius (by norm_num))
    have hrpos := P.radius_pos n
    have hthree : (3 / 4 : ℝ) * r n ≤ r n - gridCircumradius P k := by
      linarith
    have hpow : ((3 / 4 : ℝ) * r n) ^ d ≤
        (r n - gridCircumradius P k) ^ d := by
      gcongr
    calc
      killingFraction d * radiusVolume d r n =
          euclideanUnitBallVolume d * ((3 / 4 : ℝ) * r n) ^ d := by
        rw [killingFraction, radiusVolume, mul_pow]
        ring
      _ ≤ euclideanUnitBallVolume d *
          (r n - gridCircumradius P k) ^ d :=
        mul_le_mul_of_nonneg_left hpow hκ
  calc
    killingFraction d * subblockMass P k p =
        killingFraction d *
          (∑ n : PacketMark P k,
            (fractionalRate P k n p : ℝ) * radiusVolume d r n) := by
      rw [subblockMass_eq_sum_fractionalRate P k p]
    _ = ∑ n : PacketMark P k,
        (fractionalRate P k n p : ℝ) *
          (killingFraction d * radiusVolume d r n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ ∑ n : PacketMark P k,
        (fractionalRate P k n p : ℝ) *
          (euclideanUnitBallVolume d *
            (r n - gridCircumradius P k) ^ d) := by
      apply Finset.sum_le_sum
      intro n _
      exact mul_le_mul_of_nonneg_left (hinner n)
        (fractionalRate P k n p).coe_nonneg
    _ = ∑ n : PacketMark P k,
        (fractionalRate P k n p : ℝ) *
          euclideanUnitBallVolume d *
            (r n - gridCircumradius P k) ^ d := by
      apply Finset.sum_congr rfl
      intro n _
      ring

theorem packetSubblockMeasureReal_coverEvent_ge_delta
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (p : Fin (subblockCount P k)) (α : GridLabel P k) :
    1 - Real.exp (-(killingFraction d * subblockMass P k p)) ≤
      (packetSubblockMeasure (flatTorusVolume d) P k p).real
        (subblockCellCoverEvent P k α) := by
  rw [packetSubblockMeasureReal_coverEvent hd P k p α]
  have hinner := subblock_inner_intensity_ge hd P k p
  have hexp : Real.exp
      (-∑ n : PacketMark P k,
        (fractionalRate P k n p : ℝ) *
          euclideanUnitBallVolume d *
            (r n - gridCircumradius P k) ^ d) ≤
      Real.exp (-(killingFraction d * subblockMass P k p)) := by
    apply Real.exp_le_exp.mpr
    linarith
  linarith

theorem packetSubblockMeasureReal_coverEvent_ge_linear
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (p : Fin (subblockCount P k)) (α : GridLabel P k) :
    killingLinearConstant d * subblockMass P k p ≤
      (packetSubblockMeasure (flatTorusVolume d) P k p).real
        (subblockCellCoverEvent P k α) := by
  exact (one_sub_exp_neg_killing_mul_ge_linear d
    (subblockMass_pos P k p).le (subblockMass_le_one P k p)).trans
      (packetSubblockMeasureReal_coverEvent_ge_delta hd P k p α)

end Shepp.Section3
end SheppFlattenedModule026

section SheppFlattenedModule027
open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace Shepp.Section3

open ProbabilityTheory Shepp.Section2

noncomputable def subblockKillingDelta
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) : ℝ :=
  1 - Real.exp (-(killingFraction d * subblockMass P k p))

theorem subblockKillingDelta_pos
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) :
    0 < subblockKillingDelta P k p := by
  unfold subblockKillingDelta
  have hprod : 0 < killingFraction d * subblockMass P k p :=
    mul_pos (killingFraction_pos d) (subblockMass_pos P k p)
  have hexp : Real.exp (-(killingFraction d * subblockMass P k p)) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos hprod
  linarith

theorem subblockKillingDelta_ge_linear
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) :
    killingLinearConstant d * subblockMass P k p ≤
      subblockKillingDelta P k p := by
  exact one_sub_exp_neg_killing_mul_ge_linear d
    (subblockMass_pos P k p).le (subblockMass_le_one P k p)

noncomputable def reciprocalFirstMomentConstant (d : ℕ) : ℝ :=
  (firstMomentConstant d)⁻¹

theorem reciprocalFirstMomentConstant_pos (d : ℕ) :
    0 < reciprocalFirstMomentConstant d :=
  inv_pos.mpr (firstMomentConstant_pos d)

theorem scheduledActiveMean_inv_ge
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k p : ℕ) :
    ENNReal.ofReal
        (reciprocalFirstMomentConstant d * (P.level k) ^ d *
          Real.exp (scheduledMass P k p)) ≤
      (scheduledActiveMean P k p)⁻¹ := by
  let B : ℝ := firstMomentConstant d * (P.level k)⁻¹ ^ d *
    Real.exp (-(scheduledMass P k p))
  have hC : 0 < firstMomentConstant d := firstMomentConstant_pos d
  have hlevel : 0 < P.level k := test_dyadicLevel_pos (P.K + k)
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hreal :
      reciprocalFirstMomentConstant d * (P.level k) ^ d *
          Real.exp (scheduledMass P k p) = B⁻¹ := by
    dsimp only [B, reciprocalFirstMomentConstant]
    rw [Real.exp_neg]
    rw [inv_pow]
    field_simp [hC.ne', hlevel.ne', Real.exp_ne_zero]
  calc
    ENNReal.ofReal
        (reciprocalFirstMomentConstant d * (P.level k) ^ d *
          Real.exp (scheduledMass P k p)) = ENNReal.ofReal B⁻¹ := by
      rw [hreal]
    _ = (ENNReal.ofReal B)⁻¹ := ENNReal.ofReal_inv_of_pos hB
    _ ≤ (scheduledActiveMean P k p)⁻¹ := by
      apply ENNReal.inv_le_inv'
      exact scheduledActiveMean_le hd P k p

noncomputable def finiteCloudSomeCellActive
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k _p : ℕ) : Set (FiniteCloudSample (PrefixMark P k) (FlatTorus d)) :=
  ⋃ α : GridLabel P k,
    finiteCloudCellActive (fun n : PrefixMark P k => r n)
      (gridCell P k α)

theorem finiteCloudMeasure_someCellActive_le_mean
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) :
    finiteCloudMeasure (flatTorusVolume d) (scheduledRate P k p)
        (finiteCloudSomeCellActive P k p) ≤ scheduledActiveMean P k p := by
  calc
    finiteCloudMeasure (flatTorusVolume d) (scheduledRate P k p)
        (finiteCloudSomeCellActive P k p) ≤
        ∑' α : GridLabel P k,
          finiteCloudMeasure (flatTorusVolume d) (scheduledRate P k p)
            (finiteCloudCellActive (fun n : PrefixMark P k => r n)
              (gridCell P k α)) :=
      measure_iUnion_le _
    _ = scheduledActiveMean P k p := by
      rw [tsum_fintype]
      rfl

theorem finiteCloudSomeCellActive_iff_residual_nonempty
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) (ω : FiniteCloudSample (PrefixMark P k) (FlatTorus d)) :
    ω ∈ finiteCloudSomeCellActive P k p ↔
      (finiteCloudResidual (fun n : PrefixMark P k => r n) ω).Nonempty := by
  constructor
  · intro hω
    rw [finiteCloudSomeCellActive, Set.mem_iUnion] at hω
    rcases hω with ⟨α, z, hzResidual, _hzCell⟩
    exact ⟨z, hzResidual⟩
  · rintro ⟨z, hzResidual⟩
    obtain ⟨α, hzCell⟩ := exists_mem_gridCell P k z
    rw [finiteCloudSomeCellActive, Set.mem_iUnion]
    exact ⟨α, z, hzResidual, hzCell⟩

theorem scheduledResidual_ae_empty_of_mean_eq_zero
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k p : ℕ) (hmean : scheduledActiveMean P k p = 0) :
    ∀ᵐ ω ∂finiteCloudMeasure (flatTorusVolume d) (scheduledRate P k p),
      finiteCloudResidual (fun n : PrefixMark P k => r n) ω = ∅ := by
  apply ae_iff.mpr
  have hzero :
      finiteCloudMeasure (flatTorusVolume d) (scheduledRate P k p)
        (finiteCloudSomeCellActive P k p) = 0 := by
    apply le_zero_iff.mp
    exact (finiteCloudMeasure_someCellActive_le_mean P k p).trans_eq hmean
  have hevent :
      {ω | ¬ finiteCloudResidual (fun n : PrefixMark P k => r n) ω = ∅} =
        finiteCloudSomeCellActive P k p := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [finiteCloudSomeCellActive_iff_residual_nonempty]
    exact Set.nonempty_iff_ne_empty.symm
  rw [hevent]
  exact hzero

theorem exp_sub_one_le_chord {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.exp b - 1 ≤ (Real.exp 1 - 1) * b := by
  have hconv : Real.exp b ≤
      (1 - b) * Real.exp 0 + b * Real.exp 1 := by
    calc
      Real.exp b = Real.exp ((1 - b) * 0 + b * 1) := by congr 1 <;> ring
      _ ≤ (1 - b) * Real.exp 0 + b * Real.exp 1 :=
        convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ 1)
          (by linarith) hb0 (by ring)
  rw [Real.exp_zero] at hconv
  linarith

theorem exp_one_sub_one_pos : 0 < Real.exp 1 - 1 := by
  have := Real.one_lt_exp_iff.mpr zero_lt_one
  linarith

theorem subblock_exp_increment_le
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) :
    Real.exp (scheduledMass P k ((p : ℕ) + 1)) -
        Real.exp (scheduledMass P k p) ≤
      (Real.exp 1 - 1) * subblockMass P k p *
        Real.exp (scheduledMass P k p) := by
  have hchord := exp_sub_one_le_chord
    (subblockMass_pos P k p).le (subblockMass_le_one P k p)
  rw [scheduledMass_succ P k p, Real.exp_add]
  have hmul := mul_le_mul_of_nonneg_left hchord
    (Real.exp_pos (scheduledMass P k p)).le
  nlinarith

theorem packet_exp_increment_le_weighted_sum
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    P.increment k ≤
      (Real.exp 1 - 1) *
        ∑ p : Fin (subblockCount P k),
          subblockMass P k p * Real.exp (scheduledMass P k p) := by
  have htel :
      (∑ p : Fin (subblockCount P k),
        (Real.exp (scheduledMass P k ((p : ℕ) + 1)) -
          Real.exp (scheduledMass P k p))) =
        Real.exp (packetEndMass P k) - Real.exp (packetStartMass P k) := by
    calc
      (∑ p : Fin (subblockCount P k),
          (Real.exp (scheduledMass P k ((p : ℕ) + 1)) -
            Real.exp (scheduledMass P k p))) =
          ∑ p ∈ Finset.range (subblockCount P k),
            (Real.exp (scheduledMass P k (p + 1)) -
              Real.exp (scheduledMass P k p)) :=
        Fin.sum_univ_eq_sum_range
          (fun p : ℕ => Real.exp (scheduledMass P k (p + 1)) -
            Real.exp (scheduledMass P k p)) (subblockCount P k)
      _ = Real.exp (scheduledMass P k (subblockCount P k)) -
          Real.exp (scheduledMass P k 0) :=
        sum_stepDifference_range
          (fun p => Real.exp (scheduledMass P k p)) (subblockCount P k)
      _ = Real.exp (packetEndMass P k) -
          Real.exp (packetStartMass P k) := by
        rw [scheduledMass_count, scheduledMass_zero]
  rw [packetIncrement_eq_exp_end_sub_exp_start P k, ← htel]
  calc
    (∑ p : Fin (subblockCount P k),
        (Real.exp (scheduledMass P k ((p : ℕ) + 1)) -
          Real.exp (scheduledMass P k p))) ≤
        ∑ p : Fin (subblockCount P k),
          ((Real.exp 1 - 1) * subblockMass P k p *
            Real.exp (scheduledMass P k p)) := by
      apply Finset.sum_le_sum
      intro p _
      exact subblock_exp_increment_le P k p
    _ = (Real.exp 1 - 1) *
        ∑ p : Fin (subblockCount P k),
          subblockMass P k p * Real.exp (scheduledMass P k p) := by
      rw [Finset.mul_sum]
      simp only [mul_assoc]

noncomputable def exponentialChordReciprocal : ℝ :=
  (Real.exp 1 - 1)⁻¹

theorem exponentialChordReciprocal_pos :
    0 < exponentialChordReciprocal :=
  inv_pos.mpr exp_one_sub_one_pos

theorem exponentialChordReciprocal_mul_increment_le
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    exponentialChordReciprocal * P.increment k ≤
      ∑ p : Fin (subblockCount P k),
        subblockMass P k p * Real.exp (scheduledMass P k p) := by
  let S : ℝ := ∑ p : Fin (subblockCount P k),
    subblockMass P k p * Real.exp (scheduledMass P k p)
  have h := packet_exp_increment_le_weighted_sum P k
  change P.increment k ≤ (Real.exp 1 - 1) * S at h
  have hmul := mul_le_mul_of_nonneg_left h exponentialChordReciprocal_pos.le
  calc
    exponentialChordReciprocal * P.increment k ≤
        exponentialChordReciprocal * ((Real.exp 1 - 1) * S) := hmul
    _ = S := by
      rw [← mul_assoc]
      unfold exponentialChordReciprocal
      rw [inv_mul_cancel₀ exp_one_sub_one_pos.ne', one_mul]

noncomputable def baseResistanceConstant (d : ℕ) : ℝ :=
  killingLinearConstant d * reciprocalFirstMomentConstant d

theorem baseResistanceConstant_pos (d : ℕ) :
    0 < baseResistanceConstant d :=
  mul_pos (killingLinearConstant_pos d)
    (reciprocalFirstMomentConstant_pos d)

noncomputable def geometricResistanceConstant (d : ℕ) : ℝ :=
  baseResistanceConstant d * exponentialChordReciprocal

theorem geometricResistanceConstant_pos (d : ℕ) :
    0 < geometricResistanceConstant d :=
  mul_pos (baseResistanceConstant_pos d) exponentialChordReciprocal_pos

theorem packetIncrement_nonneg
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    0 ≤ P.increment k := by
  rw [packetIncrement_eq_exp_end_sub_exp_start P k]
  exact sub_nonneg.mpr (Real.exp_le_exp.mpr (packetStartMass_le_endMass P k))

noncomputable def subblockResistance
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) : ℝ≥0∞ :=
  ENNReal.ofReal (subblockKillingDelta P k p) *
    (scheduledActiveMean P k p)⁻¹

noncomputable def packetResistance
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) : ℝ≥0∞ :=
  ∑ p : Fin (subblockCount P k), subblockResistance P k p

noncomputable def geometricResistanceMass
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) : ℝ≥0∞ :=
  ∑' k : ℕ, packetResistance P k

theorem subblockResistance_ge_base
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (p : Fin (subblockCount P k)) :
    ENNReal.ofReal
        (baseResistanceConstant d * (P.level k) ^ d *
          subblockMass P k p * Real.exp (scheduledMass P k p)) ≤
      subblockResistance P k p := by
  have hdelta :
      ENNReal.ofReal (killingLinearConstant d * subblockMass P k p) ≤
        ENNReal.ofReal (subblockKillingDelta P k p) :=
    ENNReal.ofReal_le_ofReal (subblockKillingDelta_ge_linear P k p)
  have hmean := scheduledActiveMean_inv_ge hd P k p
  have hproduct := mul_le_mul' hdelta hmean
  calc
    ENNReal.ofReal
        (baseResistanceConstant d * (P.level k) ^ d *
          subblockMass P k p * Real.exp (scheduledMass P k p)) =
        ENNReal.ofReal
            ((killingLinearConstant d * subblockMass P k p) *
              (reciprocalFirstMomentConstant d * (P.level k) ^ d *
                Real.exp (scheduledMass P k p))) := by
      apply congrArg ENNReal.ofReal
      unfold baseResistanceConstant
      ring
    _ = ENNReal.ofReal
          (killingLinearConstant d * subblockMass P k p) *
        ENNReal.ofReal
          (reciprocalFirstMomentConstant d * (P.level k) ^ d *
            Real.exp (scheduledMass P k p)) := by
      rw [ENNReal.ofReal_mul]
      exact mul_nonneg (killingLinearConstant_pos d).le
        (subblockMass_pos P k p).le
    _ ≤ ENNReal.ofReal (subblockKillingDelta P k p) *
        (scheduledActiveMean P k p)⁻¹ := hproduct
    _ = subblockResistance P k p := rfl

theorem packetResistance_ge_increment
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) :
    ENNReal.ofReal
        (geometricResistanceConstant d * (P.level k) ^ d * P.increment k) ≤
      packetResistance P k := by
  let S : ℝ := ∑ p : Fin (subblockCount P k),
    subblockMass P k p * Real.exp (scheduledMass P k p)
  have hchord : exponentialChordReciprocal * P.increment k ≤ S := by
    exact exponentialChordReciprocal_mul_increment_le P k
  have hscaleNonneg :
      0 ≤ baseResistanceConstant d * (P.level k) ^ d := by
    exact mul_nonneg (baseResistanceConstant_pos d).le
      (pow_nonneg (test_dyadicLevel_pos (P.K + k)).le d)
  have hreal :
      geometricResistanceConstant d * (P.level k) ^ d * P.increment k ≤
        baseResistanceConstant d * (P.level k) ^ d * S := by
    calc
      geometricResistanceConstant d * (P.level k) ^ d * P.increment k =
          (baseResistanceConstant d * (P.level k) ^ d) *
            (exponentialChordReciprocal * P.increment k) := by
        unfold geometricResistanceConstant
        ring
      _ ≤ (baseResistanceConstant d * (P.level k) ^ d) * S :=
        mul_le_mul_of_nonneg_left hchord hscaleNonneg
  calc
    ENNReal.ofReal
        (geometricResistanceConstant d * (P.level k) ^ d * P.increment k) ≤
        ENNReal.ofReal
          (baseResistanceConstant d * (P.level k) ^ d * S) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ∑ p : Fin (subblockCount P k),
        ENNReal.ofReal
          (baseResistanceConstant d * (P.level k) ^ d *
            subblockMass P k p * Real.exp (scheduledMass P k p)) := by
      rw [show baseResistanceConstant d * (P.level k) ^ d * S =
          ∑ p : Fin (subblockCount P k),
            baseResistanceConstant d * (P.level k) ^ d *
              subblockMass P k p * Real.exp (scheduledMass P k p) by
        dsimp only [S]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring]
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro p _
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (baseResistanceConstant_pos d).le
            (pow_nonneg (test_dyadicLevel_pos (P.K + k)).le d))
          (subblockMass_pos P k p).le)
        (Real.exp_pos (scheduledMass P k p)).le
    _ ≤ ∑ p : Fin (subblockCount P k), subblockResistance P k p := by
      apply Finset.sum_le_sum
      intro p _
      exact subblockResistance_ge_base hd P k p
    _ = packetResistance P k := rfl

theorem scaled_packet_increment_tsum_eq_top
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    (∑' k : ℕ,
      ENNReal.ofReal
        (geometricResistanceConstant d * (P.level k) ^ d * P.increment k)) =
      ∞ := by
  calc
    (∑' k : ℕ,
        ENNReal.ofReal
          (geometricResistanceConstant d * (P.level k) ^ d * P.increment k)) =
        ∑' k : ℕ,
          ENNReal.ofReal (geometricResistanceConstant d) *
            (ENNReal.ofReal ((P.level k) ^ d) *
              ENNReal.ofReal (P.increment k)) := by
      apply tsum_congr
      intro k
      rw [show geometricResistanceConstant d * (P.level k) ^ d *
          P.increment k = geometricResistanceConstant d *
            ((P.level k) ^ d * P.increment k) by ring]
      rw [ENNReal.ofReal_mul (geometricResistanceConstant_pos d).le]
      rw [ENNReal.ofReal_mul]
      exact pow_nonneg (test_dyadicLevel_pos (P.K + k)).le d
    _ = ENNReal.ofReal (geometricResistanceConstant d) *
        ∑' k : ℕ,
          ENNReal.ofReal ((P.level k) ^ d) *
            ENNReal.ofReal (P.increment k) := ENNReal.tsum_mul_left
    _ = ∞ := by
      rw [P.increment_mass_diverges]
      exact ENNReal.mul_top
        (ENNReal.ofReal_ne_zero_iff.mpr (geometricResistanceConstant_pos d))

theorem geometricResistanceMass_eq_top
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) :
    geometricResistanceMass P = ∞ := by
  have hle :
      (∑' k : ℕ,
        ENNReal.ofReal
          (geometricResistanceConstant d * (P.level k) ^ d * P.increment k)) ≤
        ∑' k : ℕ, packetResistance P k :=
    ENNReal.tsum_le_tsum fun k => packetResistance_ge_increment hd P k
  rw [scaled_packet_increment_tsum_eq_top P] at hle
  unfold geometricResistanceMass
  exact top_unique hle

theorem zero_mean_or_positive_means_and_resistance_diverges
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) :
    (∃ k : ℕ, ∃ p : Fin (subblockCount P k),
      scheduledActiveMean P k p = 0) ∨
    ((∀ k : ℕ, ∀ p : Fin (subblockCount P k),
      scheduledActiveMean P k p ≠ 0) ∧
      geometricResistanceMass P = ∞) := by
  classical
  by_cases hzero : ∃ k : ℕ, ∃ p : Fin (subblockCount P k),
      scheduledActiveMean P k p = 0
  · exact Or.inl hzero
  · push Not at hzero
    exact Or.inr ⟨hzero, geometricResistanceMass_eq_top hd P⟩

theorem exists_geometricResistanceMass_eq_top_of_torus_overlap
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Filter.Tendsto r Filter.atTop (nhds 0))
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (htorus :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞) :
    ∃ P : GeometricPacketInterface d r,
      geometricResistanceMass P = ∞ := by
  obtain ⟨P⟩ := exists_geometricPacketInterface_of_torus_overlap
    d hd hr hrsmall hmono hrlim ht₀ htorus
  exact ⟨P, geometricResistanceMass_eq_top (by omega) P⟩

end Shepp.Section3
end SheppFlattenedModule027

section SheppFlattenedModule028
open scoped BigOperators ENNReal
open Finset

namespace Shepp.Section5

open Shepp.Section3

noncomputable def blockStart (J : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (J i + 1)

@[simp] theorem blockStart_zero (J : ℕ → ℕ) :
    blockStart J 0 = 0 := by
  simp [blockStart]

theorem blockStart_succ (J : ℕ → ℕ) (k : ℕ) :
    blockStart J (k + 1) = blockStart J k + J k + 1 := by
  simp [blockStart, Finset.sum_range_succ, add_assoc]

theorem blockStart_lt_succ (J : ℕ → ℕ) (k : ℕ) :
    blockStart J k < blockStart J (k + 1) := by
  rw [blockStart_succ]
  omega

theorem strictMono_blockStart (J : ℕ → ℕ) :
    StrictMono (blockStart J) :=
  strictMono_nat_of_lt_succ (blockStart_lt_succ J)

theorem monotone_blockStart (J : ℕ → ℕ) :
    Monotone (blockStart J) :=
  (strictMono_blockStart J).monotone

theorem self_le_blockStart (J : ℕ → ℕ) (k : ℕ) :
    k ≤ blockStart J k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [blockStart_succ]
      omega

theorem exists_lt_blockStart_succ (J : ℕ → ℕ) (j : ℕ) :
    ∃ k : ℕ, j < blockStart J (k + 1) := by
  refine ⟨j, ?_⟩
  exact (Nat.lt_succ_self j).trans_le (self_le_blockStart J (j + 1))

noncomputable def blockIndex (J : ℕ → ℕ) (j : ℕ) : ℕ :=
  Nat.find (exists_lt_blockStart_succ J j)

theorem blockIndex_upper (J : ℕ → ℕ) (j : ℕ) :
    j < blockStart J (blockIndex J j + 1) :=
  Nat.find_spec (exists_lt_blockStart_succ J j)

theorem blockIndex_lower (J : ℕ → ℕ) (j : ℕ) :
    blockStart J (blockIndex J j) ≤ j := by
  by_cases hzero : blockIndex J j = 0
  · simp [hzero]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    rw [hk]
    have hklt : k < blockIndex J j := by omega
    have hminimal := Nat.find_min (exists_lt_blockStart_succ J j)
      hklt
    exact Nat.le_of_not_gt hminimal

noncomputable def blockOffset (J : ℕ → ℕ) (j : ℕ) : ℕ :=
  j - blockStart J (blockIndex J j)

theorem blockOffset_lt (J : ℕ → ℕ) (j : ℕ) :
    blockOffset J j < J (blockIndex J j) + 1 := by
  have hlo := blockIndex_lower J j
  have hhi := blockIndex_upper J j
  rw [blockStart_succ] at hhi
  unfold blockOffset
  omega

theorem blockStart_add_offset (J : ℕ → ℕ) (j : ℕ) :
    blockStart J (blockIndex J j) + blockOffset J j = j := by
  exact Nat.add_sub_of_le (blockIndex_lower J j)

theorem blockIndex_start_add
    (J : ℕ → ℕ) (k : ℕ) (p : Fin (J k + 1)) :
    blockIndex J (blockStart J k + p) = k := by
  apply le_antisymm
  · apply Nat.find_min'
    rw [blockStart_succ]
    omega
  · by_contra hle
    have hlt : blockIndex J (blockStart J k + p) < k :=
      Nat.lt_of_not_ge hle
    have hsucc : blockIndex J (blockStart J k + p) + 1 ≤ k :=
      Nat.succ_le_of_lt hlt
    have hstart := monotone_blockStart J hsucc
    have hupper := blockIndex_upper J (blockStart J k + p)
    omega

theorem blockOffset_start_add
    (J : ℕ → ℕ) (k : ℕ) (p : Fin (J k + 1)) :
    blockOffset J (blockStart J k + p) = p := by
  rw [blockOffset, blockIndex_start_add J k p]
  omega

noncomputable def blockPhaseEquiv (J : ℕ → ℕ) :
    (Σ k : ℕ, Fin (J k + 1)) ≃ ℕ where
  toFun z := blockStart J z.1 + z.2
  invFun j :=
    ⟨blockIndex J j, ⟨blockOffset J j, blockOffset_lt J j⟩⟩
  left_inv := by
    rintro ⟨k, p⟩
    have hindex : blockIndex J (blockStart J k + p) = k :=
      blockIndex_start_add J k p
    have hoffset : blockOffset J (blockStart J k + p) = p :=
      blockOffset_start_add J k p
    apply Sigma.ext
    · exact hindex
    · exact (Fin.heq_ext_iff
        (congrArg (fun n => J n + 1) hindex)).2 hoffset
  right_inv := by
    intro j
    exact blockStart_add_offset J j

@[simp] theorem blockPhaseEquiv_apply
    (J : ℕ → ℕ) (k : ℕ) (p : Fin (J k + 1)) :
    blockPhaseEquiv J ⟨k, p⟩ = blockStart J k + p :=
  rfl

def IsDeletionTime (J : ℕ → ℕ) (j : ℕ) : Prop :=
  blockOffset J j < J (blockIndex J j)

theorem blockOffset_eq_count_of_not_deletion
    (J : ℕ → ℕ) (j : ℕ) (h : ¬ IsDeletionTime J j) :
    blockOffset J j = J (blockIndex J j) := by
  have hoff := blockOffset_lt J j
  unfold IsDeletionTime at h
  omega

theorem blockIndex_succ_of_deletion
    (J : ℕ → ℕ) (j : ℕ) (h : IsDeletionTime J j) :
    blockIndex J (j + 1) = blockIndex J j := by
  let k := blockIndex J j
  let p : Fin (J k + 1) :=
    ⟨blockOffset J j + 1, by
      dsimp only [k]
      unfold IsDeletionTime at h
      omega⟩
  have hj := blockStart_add_offset J j
  have hj1 : j + 1 = blockStart J k + (p : ℕ) := by
    dsimp only [k, p]
    omega
  change blockIndex J (j + 1) = k
  rw [hj1]
  exact blockIndex_start_add J k p

theorem blockIndex_succ_of_refinement
    (J : ℕ → ℕ) (j : ℕ) (h : ¬ IsDeletionTime J j) :
    blockIndex J (j + 1) = blockIndex J j + 1 := by
  let k := blockIndex J j
  let p : Fin (J (k + 1) + 1) := ⟨0, by omega⟩
  have hoff := blockOffset_eq_count_of_not_deletion J j h
  have hj := blockStart_add_offset J j
  have hnext := blockStart_succ J k
  have hj1 : j + 1 = blockStart J (k + 1) := by
    dsimp only [k] at hoff hj hnext ⊢
    omega
  change blockIndex J (j + 1) = k + 1
  rw [hj1]
  have hp := blockIndex_start_add J (k + 1) p
  simpa only [p, Fin.val_zero, Nat.add_zero] using hp

noncomputable def blockScheduledTerm
    (J : ℕ → ℕ) (g : ∀ k, Fin (J k) → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ := by
  classical
  exact if h : blockOffset J j < J (blockIndex J j) then
      g (blockIndex J j) ⟨blockOffset J j, h⟩
    else 0

@[simp] theorem blockScheduledTerm_start_add
    (J : ℕ → ℕ) (g : ∀ k, Fin (J k) → ℝ≥0∞)
    (k : ℕ) (p : Fin (J k)) :
    blockScheduledTerm J g (blockStart J k + p) = g k p := by
  let p' : Fin (J k + 1) := ⟨p, by omega⟩
  have hindex : blockIndex J (blockStart J k + p) = k := by
    change blockIndex J (blockStart J k + (p' : ℕ)) = k
    exact blockIndex_start_add J k p'
  have hoffset : blockOffset J (blockStart J k + p) = p := by
    change blockOffset J (blockStart J k + (p' : ℕ)) = (p' : ℕ)
    exact blockOffset_start_add J k p'
  have hdelete :
      blockOffset J (blockStart J k + p) <
        J (blockIndex J (blockStart J k + p)) := by
    rw [hindex, hoffset]
    exact p.isLt
  rw [blockScheduledTerm, dif_pos hdelete]
  have hz :
      (⟨blockIndex J (blockStart J k + p),
          ⟨blockOffset J (blockStart J k + p), hdelete⟩⟩ :
        Σ n : ℕ, Fin (J n)) = ⟨k, p⟩ := by
    apply Sigma.ext
    · exact hindex
    · exact (Fin.heq_ext_iff (congrArg J hindex)).2 hoffset
  exact congrArg (fun z : Σ n : ℕ, Fin (J n) => g z.1 z.2) hz

@[simp] theorem blockScheduledTerm_refinement
    (J : ℕ → ℕ) (g : ∀ k, Fin (J k) → ℝ≥0∞) (k : ℕ) :
    blockScheduledTerm J g (blockStart J k + J k) = 0 := by
  let p : Fin (J k + 1) := Fin.last (J k)
  have hindex : blockIndex J (blockStart J k + J k) = k := by
    simpa only [p, Fin.val_last] using blockIndex_start_add J k p
  have hoffset : blockOffset J (blockStart J k + J k) = J k := by
    simpa only [p, Fin.val_last] using blockOffset_start_add J k p
  rw [blockScheduledTerm, dif_neg]
  rw [hindex, hoffset]
  exact Nat.lt_irrefl _

theorem tsum_blockScheduledTerm
    (J : ℕ → ℕ) (g : ∀ k, Fin (J k) → ℝ≥0∞) :
    (∑' j : ℕ, blockScheduledTerm J g j) =
      ∑' k : ℕ, ∑ p : Fin (J k), g k p := by
  calc
    (∑' j : ℕ, blockScheduledTerm J g j) =
        ∑' z : Σ k : ℕ, Fin (J k + 1),
          blockScheduledTerm J g ((blockPhaseEquiv J) z) := by
      symm
      exact (blockPhaseEquiv J).tsum_eq _
    _ = ∑' k : ℕ, ∑' p : Fin (J k + 1),
          blockScheduledTerm J g (blockStart J k + p) := by
      rw [ENNReal.tsum_sigma']
      simp only [blockPhaseEquiv_apply]
    _ = ∑' k : ℕ, ∑ p : Fin (J k), g k p := by
      apply tsum_congr
      intro k
      rw [tsum_fintype, Fin.sum_univ_castSucc]
      simp

noncomputable abbrev spatialBlockStart
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) : ℕ → ℕ :=
  blockStart (subblockCount P)

noncomputable abbrev spatialLevel
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) : ℕ → ℕ :=
  blockIndex (subblockCount P)

noncomputable abbrev spatialOffset
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) : ℕ → ℕ :=
  blockOffset (subblockCount P)

abbrev SpatialDeletionTime
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) : Prop :=
  IsDeletionTime (subblockCount P) j

end Shepp.Section5
end SheppFlattenedModule028

section SheppFlattenedModule029
open scoped BigOperators

namespace Shepp.Section4

def slotSurvival : List ℝ → ℝ
  | [] => 0
  | u :: us => u + (1 - u) * slotSurvival us

def slotMass (us : List ℝ) : ℝ := us.sum

def slotSquareMass (us : List ℝ) : ℝ := (us.map fun u => u ^ 2).sum

def slotPairMass : List ℝ → ℝ
  | [] => 0
  | u :: us => u * slotMass us + slotPairMass us

def ValidSlotProbabilities (us : List ℝ) : Prop :=
  ∀ u ∈ us, 0 ≤ u ∧ u ≤ 1

theorem slotSquareMass_nonneg (us : List ℝ) : 0 ≤ slotSquareMass us := by
  induction us with
  | nil => simp [slotSquareMass]
  | cons u us ih =>
      simp only [slotSquareMass, List.map_cons, List.sum_cons]
      positivity

theorem slotSquareMass_le_mass {us : List ℝ} (h : ValidSlotProbabilities us) :
    slotSquareMass us ≤ slotMass us := by
  induction us with
  | nil => simp [slotSquareMass, slotMass]
  | cons u us ih =>
      have hu : 0 ≤ u ∧ u ≤ 1 := h u (by simp)
      have hvalidTail : ValidSlotProbabilities us := by
        intro v hv
        exact h v (by simp [hv])
      have htail := ih hvalidTail
      simp only [slotSquareMass, slotMass] at htail
      simp only [slotSquareMass, List.map_cons, List.sum_cons, slotMass]
      nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]

theorem slotSquareMass_le_length {us : List ℝ} (h : ValidSlotProbabilities us) :
    slotSquareMass us ≤ (us.length : ℝ) := by
  induction us with
  | nil => simp [slotSquareMass]
  | cons u us ih =>
      have hu : 0 ≤ u ∧ u ≤ 1 := h u (by simp)
      have hvalidTail : ValidSlotProbabilities us := by
        intro v hv
        exact h v (by simp [hv])
      have htail := ih hvalidTail
      simp only [slotSquareMass] at htail
      simp only [slotSquareMass, List.map_cons, List.sum_cons,
        List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]

theorem ValidSlotProbabilities.tail {u : ℝ} {us : List ℝ}
    (h : ValidSlotProbabilities (u :: us)) : ValidSlotProbabilities us := by
  intro v hv
  exact h v (by simp [hv])

theorem ValidSlotProbabilities.head {u : ℝ} {us : List ℝ}
    (h : ValidSlotProbabilities (u :: us)) : 0 ≤ u ∧ u ≤ 1 :=
  h u (by simp)

theorem slotSurvival_eq_one_sub_prod (us : List ℝ) :
    slotSurvival us = 1 - (us.map fun u => 1 - u).prod := by
  induction us with
  | nil => simp [slotSurvival]
  | cons u us ih =>
      simp only [slotSurvival, List.map_cons, List.prod_cons, ih]
      ring

theorem slotSurvival_nonneg {us : List ℝ} (h : ValidSlotProbabilities us) :
    0 ≤ slotSurvival us := by
  induction us with
  | nil => simp [slotSurvival]
  | cons u us ih =>
      have hu := h.head
      have hp := ih h.tail
      simp only [slotSurvival]
      exact add_nonneg hu.1 (mul_nonneg (sub_nonneg.mpr hu.2) hp)

theorem slotSurvival_le_one {us : List ℝ} (h : ValidSlotProbabilities us) :
    slotSurvival us ≤ 1 := by
  induction us with
  | nil => simp [slotSurvival]
  | cons u us ih =>
      have hu := h.head
      have hp := ih h.tail
      simp only [slotSurvival]
      nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hp)]

theorem slotSurvival_le_mass {us : List ℝ} (h : ValidSlotProbabilities us) :
    slotSurvival us ≤ slotMass us := by
  induction us with
  | nil => simp [slotSurvival, slotMass]
  | cons u us ih =>
      have hu := h.head
      have hp0 := slotSurvival_nonneg h.tail
      have htail := ih h.tail
      simp only [slotSurvival, slotMass, List.sum_cons]
      simp only [slotMass] at htail
      have hprod : (1 - u) * slotSurvival us ≤ slotSurvival us := by
        nlinarith [mul_nonneg hu.1 hp0]
      linarith

theorem slotMass_nonneg {us : List ℝ} (h : ValidSlotProbabilities us) :
    0 ≤ slotMass us :=
  (slotSurvival_nonneg h).trans (slotSurvival_le_mass h)

theorem slotMass_le_length_mul_survival {us : List ℝ}
    (h : ValidSlotProbabilities us) :
    slotMass us ≤ (us.length : ℝ) * slotSurvival us := by
  induction us with
  | nil => simp [slotMass, slotSurvival]
  | cons u us ih =>
      have hu := h.head
      have htail := h.tail
      have hp0 := slotSurvival_nonneg htail
      have hp1 := slotSurvival_le_one htail
      have hih := ih htail
      have hn : 0 ≤ (us.length : ℝ) := Nat.cast_nonneg _
      have hterm1 :
          0 ≤ (us.length : ℝ) * u * (1 - slotSurvival us) := by
        exact mul_nonneg (mul_nonneg hn hu.1) (sub_nonneg.mpr hp1)
      have hterm2 : 0 ≤ slotSurvival us * (1 - u) := by
        exact mul_nonneg hp0 (sub_nonneg.mpr hu.2)
      simp only [slotMass] at hih
      simp only [slotMass, List.sum_cons, slotSurvival, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      nlinarith

theorem slotMass_le_bound_mul_survival {us : List ℝ} {B : ℕ}
    (h : ValidSlotProbabilities us) (hlen : us.length ≤ B) :
    slotMass us ≤ (B : ℝ) * slotSurvival us := by
  calc
    slotMass us ≤ (us.length : ℝ) * slotSurvival us :=
      slotMass_le_length_mul_survival h
    _ ≤ (B : ℝ) * slotSurvival us := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen)
        (slotSurvival_nonneg h)

theorem slotPairMass_le_bound_mul_excess {us : List ℝ} {B : ℕ}
    (h : ValidSlotProbabilities us) (hlen : us.length ≤ B) :
    slotPairMass us ≤ (B : ℝ) * (slotMass us - slotSurvival us) := by
  induction us with
  | nil => simp [slotPairMass, slotMass, slotSurvival]
  | cons u us ih =>
      have hu := h.head
      have htail := h.tail
      have hlenTail : us.length ≤ B := Nat.le_trans (Nat.le_succ _) hlen
      have hpair := ih htail hlenTail
      have hsum := slotMass_le_bound_mul_survival htail hlenTail
      have hmul : u * slotMass us ≤ u * ((B : ℝ) * slotSurvival us) :=
        mul_le_mul_of_nonneg_left hsum hu.1
      calc
        slotPairMass (u :: us) = u * slotMass us + slotPairMass us := rfl
        _ ≤ u * ((B : ℝ) * slotSurvival us) +
            (B : ℝ) * (slotMass us - slotSurvival us) :=
          add_le_add hmul hpair
        _ = (B : ℝ) *
            (slotMass (u :: us) - slotSurvival (u :: us)) := by
          simp only [slotMass, List.sum_cons, slotSurvival]
          ring

theorem slotMass_sq_identity (us : List ℝ) :
    slotMass us ^ 2 = slotSquareMass us + 2 * slotPairMass us := by
  induction us with
  | nil => simp [slotMass, slotSquareMass, slotPairMass]
  | cons u us ih =>
      change (u + slotMass us) ^ 2 =
        u ^ 2 + slotSquareMass us +
          2 * (u * slotMass us + slotPairMass us)
      calc
        (u + slotMass us) ^ 2 =
            u ^ 2 + 2 * u * slotMass us + slotMass us ^ 2 := by ring
        _ = u ^ 2 + slotSquareMass us +
            2 * (u * slotMass us + slotPairMass us) := by
          rw [ih]
          ring

theorem slotMass_sq_le_squareMass_add_excess {us : List ℝ} {B : ℕ}
    (h : ValidSlotProbabilities us) (hlen : us.length ≤ B) :
    slotMass us ^ 2 ≤
      slotSquareMass us + 2 * (B : ℝ) * (slotMass us - slotSurvival us) := by
  rw [slotMass_sq_identity]
  have hpair := slotPairMass_le_bound_mul_excess h hlen
  nlinarith

noncomputable def resistanceLambda (B : ℕ) : ℝ :=
  (2 * (B : ℝ))⁻¹

noncomputable def quadraticPotential (B : ℕ) (u : ℝ) : ℝ :=
  u + resistanceLambda B * u ^ 2

theorem resistanceLambda_pos {B : ℕ} (hB : 1 ≤ B) :
    0 < resistanceLambda B := by
  unfold resistanceLambda
  positivity

end Shepp.Section4
end SheppFlattenedModule029

section SheppFlattenedModule030
open scoped BigOperators
open MeasureTheory Set

namespace Shepp.Section4

theorem integral_sq_le_measure_compl_mul_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {Z : Set Ω} {S : Ω → ℝ}
    (hSnonneg : ∀ ω, 0 ≤ S ω) (hS : Integrable S μ)
    (hSq : Integrable (fun ω => S ω ^ 2) μ)
    (hzero : ∀ ω ∈ Z, S ω = 0) :
    (∫ ω, S ω ∂μ) ^ 2 ≤ μ.real Zᶜ * ∫ ω, S ω ^ 2 ∂μ := by
  have hIntS : (∫ ω in Zᶜ, S ω ∂μ) = ∫ ω, S ω ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro ω hω
    apply hzero ω
    simpa using hω
  have hIntSq : (∫ ω in Zᶜ, S ω ^ 2 ∂μ) = ∫ ω, S ω ^ 2 ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro ω hω
    have hz : ω ∈ Z := by simpa using hω
    simp [hzero ω hz]
  by_cases hcomp : μ Zᶜ = 0
  · have hrestrict : μ.restrict Zᶜ = 0 := Measure.restrict_eq_zero.mpr hcomp
    have hIntZero : ∫ ω, S ω ∂μ = 0 := by
      rw [← hIntS, hrestrict, integral_zero_measure]
    simp [hIntZero, measureReal_def, hcomp]
  · have hcompTop : μ Zᶜ ≠ ⊤ := measure_ne_top μ Zᶜ
    have hmpos : 0 < μ.real Zᶜ := ENNReal.toReal_pos hcomp hcompTop
    have hJensen :
        (⨍ ω in Zᶜ, S ω ∂μ) ^ 2 ≤ ⨍ ω in Zᶜ, S ω ^ 2 ∂μ := by
      exact (convexOn_pow 2).map_set_average_le (continuousOn_pow 2)
        isClosed_Ici hcomp hcompTop
        (Filter.Eventually.of_forall fun ω => hSnonneg ω)
        hS.integrableOn hSq.integrableOn
    rw [setAverage_eq, setAverage_eq, hIntS, hIntSq] at hJensen
    simp only [smul_eq_mul] at hJensen
    calc
      (∫ ω, S ω ∂μ) ^ 2 =
          (μ.real Zᶜ) ^ 2 *
            ((μ.real Zᶜ)⁻¹ * ∫ ω, S ω ∂μ) ^ 2 := by
        field_simp
      _ ≤ (μ.real Zᶜ) ^ 2 *
          ((μ.real Zᶜ)⁻¹ * ∫ ω, S ω ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left hJensen (sq_nonneg _)
      _ = μ.real Zᶜ * ∫ ω, S ω ^ 2 ∂μ := by
        field_simp

end Shepp.Section4
end SheppFlattenedModule030

section SheppFlattenedModule031
open scoped BigOperators
open MeasureTheory Set

namespace Shepp.Section4

open ProbabilityTheory

abbrev AugmentedState (X : Type*) := X ⊕ Unit

def cemetery {X : Type*} : AugmentedState X := Sum.inr ()

def slotParameterList {Y : Type*} (n : ℕ) (s : Y → ℝ)
    (y : Fin n → Y) : List ℝ :=
  List.ofFn fun i => s (y i)

@[simp] theorem slotParameterList_length {Y : Type*} (n : ℕ) (s : Y → ℝ)
    (y : Fin n → Y) : (slotParameterList n s y).length = n := by
  simp [slotParameterList]

@[simp] theorem slotMass_slotParameterList {Y : Type*} (n : ℕ) (s : Y → ℝ)
    (y : Fin n → Y) :
    slotMass (slotParameterList n s y) = ∑ i, s (y i) := by
  simp [slotParameterList, slotMass, List.sum_ofFn]

@[simp] theorem slotSquareMass_slotParameterList {Y : Type*} (n : ℕ)
    (s : Y → ℝ) (y : Fin n → Y) :
    slotSquareMass (slotParameterList n s y) = ∑ i, (s (y i)) ^ 2 := by
  simp [slotParameterList, slotSquareMass, List.sum_ofFn, Function.comp_def]

theorem slotSurvival_slotParameterList {Y : Type*} (n : ℕ) (s : Y → ℝ)
    (y : Fin n → Y) :
    slotSurvival (slotParameterList n s y) =
      1 - ∏ i, (1 - s (y i)) := by
  rw [slotSurvival_eq_one_sub_prod]
  simp [slotParameterList, List.prod_ofFn, Function.comp_def]

theorem valid_slotParameterList {Y : Type*} {n : ℕ} {s : Y → ℝ}
    (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1) (y : Fin n → Y) :
    ValidSlotProbabilities (slotParameterList n s y) := by
  intro u hu
  simp only [slotParameterList, List.mem_ofFn] at hu
  obtain ⟨i, rfl⟩ := hu
  exact ⟨hs0 _, hs1 _⟩

theorem measurable_slotMass_slotParameterList
    {Y : Type*} [MeasurableSpace Y] {n : ℕ} {s : Y → ℝ}
    (hs : Measurable s) :
    Measurable fun y : Fin n → Y => slotMass (slotParameterList n s y) := by
  simp only [slotMass_slotParameterList]
  fun_prop

theorem measurable_slotSquareMass_slotParameterList
    {Y : Type*} [MeasurableSpace Y] {n : ℕ} {s : Y → ℝ}
    (hs : Measurable s) :
    Measurable fun y : Fin n → Y => slotSquareMass (slotParameterList n s y) := by
  simp only [slotSquareMass_slotParameterList]
  fun_prop

theorem measurable_slotSurvival_slotParameterList
    {Y : Type*} [MeasurableSpace Y] {n : ℕ} {s : Y → ℝ}
    (hs : Measurable s) :
    Measurable fun y : Fin n → Y => slotSurvival (slotParameterList n s y) := by
  rw [show (fun y : Fin n → Y => slotSurvival (slotParameterList n s y)) =
      fun y => 1 - ∏ i, (1 - s (y i)) by
    funext y
    exact slotSurvival_slotParameterList n s y]
  fun_prop

def allCemetery {Y : Type*} (n : ℕ) : Set (Fin n → AugmentedState Y) :=
  {y | ∀ i, y i = cemetery}

theorem measurableSet_allCemetery
    {Y : Type*} [MeasurableSpace Y] (n : ℕ) :
    MeasurableSet (allCemetery (Y := Y) n) := by
  have hCemetery :
      MeasurableSet ({cemetery} : Set (AugmentedState Y)) := by
    rw [show ({cemetery} : Set (AugmentedState Y)) =
        Sum.inr '' ({()} : Set Unit) by
      ext z
      cases z <;> simp [cemetery]]
    exact (measurableSet_singleton ()).inr_image
  rw [show allCemetery (Y := Y) n =
      ⋂ i : Fin n, (fun y : Fin n → AugmentedState Y => y i) ⁻¹' {cemetery} by
    ext y
    simp [allCemetery]]
  exact MeasurableSet.iInter fun i =>
    (measurable_pi_apply i) hCemetery

theorem slotMass_eq_zero_of_mem_allCemetery
    {Y : Type*} {n : ℕ} {s : AugmentedState Y → ℝ}
    (hcem : s cemetery = 0) {y : Fin n → AugmentedState Y}
    (hy : y ∈ allCemetery n) :
    slotMass (slotParameterList n s y) = 0 := by
  simp only [slotMass_slotParameterList]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [hy i, hcem]

theorem slotSurvival_eq_zero_of_mem_allCemetery
    {Y : Type*} {n : ℕ} {s : AugmentedState Y → ℝ}
    (hcem : s cemetery = 0) {y : Fin n → AugmentedState Y}
    (hy : y ∈ allCemetery n) :
    slotSurvival (slotParameterList n s y) = 0 := by
  rw [slotSurvival_slotParameterList]
  have hzero : ∀ i, s (y i) = 0 := by
    intro i
    rw [hy i, hcem]
  simp_rw [hzero]
  simp

theorem integrable_slotMass_slotParameterList
    {Y : Type*} [MeasurableSpace Y] {n : ℕ} {s : Y → ℝ}
    (μ : Measure (Fin n → Y)) [IsFiniteMeasure μ]
    (hs : Measurable s) (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1) :
    Integrable (fun y => slotMass (slotParameterList n s y)) μ := by
  apply Integrable.of_bound (measurable_slotMass_slotParameterList hs).aestronglyMeasurable
    (n : ℝ)
  filter_upwards with y
  have hvalid := valid_slotParameterList hs0 hs1 y
  have hnonneg := slotMass_nonneg hvalid
  rw [Real.norm_of_nonneg hnonneg]
  calc
    slotMass (slotParameterList n s y) ≤
        (n : ℝ) * slotSurvival (slotParameterList n s y) :=
      by simpa using slotMass_le_length_mul_survival hvalid
    _ ≤ (n : ℝ) := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith [slotSurvival_le_one hvalid]

theorem integrable_slotSurvival_slotParameterList
    {Y : Type*} [MeasurableSpace Y] {n : ℕ} {s : Y → ℝ}
    (μ : Measure (Fin n → Y)) [IsFiniteMeasure μ]
    (hs : Measurable s) (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1) :
    Integrable (fun y => slotSurvival (slotParameterList n s y)) μ := by
  apply Integrable.of_bound
    (measurable_slotSurvival_slotParameterList hs).aestronglyMeasurable 1
  filter_upwards with y
  have hvalid := valid_slotParameterList hs0 hs1 y
  rw [Real.norm_of_nonneg (slotSurvival_nonneg hvalid)]
  exact slotSurvival_le_one hvalid

theorem integrable_slotSquareMass_slotParameterList
    {Y : Type*} [MeasurableSpace Y] {n : ℕ} {s : Y → ℝ}
    (μ : Measure (Fin n → Y)) [IsFiniteMeasure μ]
    (hs : Measurable s) (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1) :
    Integrable (fun y => slotSquareMass (slotParameterList n s y)) μ := by
  apply Integrable.of_bound
    (measurable_slotSquareMass_slotParameterList hs).aestronglyMeasurable (n : ℝ)
  filter_upwards with y
  have hvalid := valid_slotParameterList hs0 hs1 y
  rw [Real.norm_of_nonneg (slotSquareMass_nonneg _)]
  simpa using slotSquareMass_le_length hvalid

theorem integrable_slotMass_sq_slotParameterList
    {Y : Type*} [MeasurableSpace Y] {n : ℕ} {s : Y → ℝ}
    (μ : Measure (Fin n → Y)) [IsFiniteMeasure μ]
    (hs : Measurable s) (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1) :
    Integrable (fun y => slotMass (slotParameterList n s y) ^ 2) μ := by
  apply Integrable.of_bound
    ((measurable_slotMass_slotParameterList hs).pow_const 2).aestronglyMeasurable
    ((n : ℝ) ^ 2)
  filter_upwards with y
  have hvalid := valid_slotParameterList hs0 hs1 y
  have hmass0 := slotMass_nonneg hvalid
  have hmassLe : slotMass (slotParameterList n s y) ≤ (n : ℝ) := by
    calc
      slotMass (slotParameterList n s y) ≤
          (n : ℝ) * slotSurvival (slotParameterList n s y) :=
        by simpa using slotMass_le_length_mul_survival hvalid
      _ ≤ (n : ℝ) := by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        nlinarith [slotSurvival_le_one hvalid]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith

noncomputable def slotMean
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel X (Fin n → Y)) (f : Y → ℝ) (x : X) : ℝ :=
  ∫ y, slotMass (slotParameterList n f y) ∂Q x

noncomputable def bellmanStep
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel X (Fin n → Y)) (s : Y → ℝ) (x : X) : ℝ :=
  ∫ y, slotSurvival (slotParameterList n s y) ∂Q x

noncomputable def slotSquareMean
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel X (Fin n → Y)) (s : Y → ℝ) (x : X) : ℝ :=
  ∫ y, slotSquareMass (slotParameterList n s y) ∂Q x

theorem measurable_slotMean
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel X (Fin n → Y)) {f : Y → ℝ} (hf : Measurable f) :
    Measurable (slotMean Q f) := by
  exact (measurable_slotMass_slotParameterList hf).stronglyMeasurable.integral_kernel.measurable

theorem measurable_bellmanStep
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel X (Fin n → Y)) {s : Y → ℝ} (hs : Measurable s) :
    Measurable (bellmanStep Q s) := by
  exact (measurable_slotSurvival_slotParameterList hs).stronglyMeasurable.integral_kernel.measurable

theorem measurable_slotSquareMean
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel X (Fin n → Y)) {s : Y → ℝ} (hs : Measurable s) :
    Measurable (slotSquareMean Q s) := by
  exact
    (measurable_slotSquareMass_slotParameterList hs).stronglyMeasurable.integral_kernel.measurable

theorem bellmanStep_eq_one_sub_integral_prod
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel X (Fin n → Y)) [IsMarkovKernel Q]
    {s : Y → ℝ} (hs : Measurable s) (hs0 : ∀ y, 0 ≤ s y)
    (hs1 : ∀ y, s y ≤ 1) (x : X) :
    bellmanStep Q s x =
      1 - ∫ y, ∏ i, (1 - s (y i)) ∂Q x := by
  have hProd : Integrable (fun y : Fin n → Y => ∏ i, (1 - s (y i))) (Q x) := by
    have hSurv := integrable_slotSurvival_slotParameterList (Q x) hs hs0 hs1
    have hEq : (fun y : Fin n → Y => ∏ i, (1 - s (y i))) =
        fun y => 1 - slotSurvival (slotParameterList n s y) := by
      funext y
      rw [slotSurvival_slotParameterList]
      ring
    rw [hEq]
    exact (integrable_const 1).sub hSurv
  rw [bellmanStep]
  have hEq : (fun y : Fin n → Y => slotSurvival (slotParameterList n s y)) =
      fun y => 1 - ∏ i, (1 - s (y i)) := by
    funext y
    exact slotSurvival_slotParameterList n s y
  rw [hEq, integral_sub (integrable_const 1) hProd, integral_const, probReal_univ]
  simp

theorem bellmanStep_nonneg
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel X (Fin n → Y)) [IsMarkovKernel Q]
    {s : Y → ℝ} (_hs : Measurable s) (hs0 : ∀ y, 0 ≤ s y)
    (hs1 : ∀ y, s y ≤ 1) (x : X) :
    0 ≤ bellmanStep Q s x := by
  rw [bellmanStep]
  exact integral_nonneg fun y =>
    slotSurvival_nonneg (valid_slotParameterList hs0 hs1 y)

theorem bellmanStep_le_one
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel X (Fin n → Y)) [IsMarkovKernel Q]
    {s : Y → ℝ} (hs : Measurable s) (hs0 : ∀ y, 0 ≤ s y)
    (hs1 : ∀ y, s y ≤ 1) (x : X) :
    bellmanStep Q s x ≤ 1 := by
  have hSurvival := integrable_slotSurvival_slotParameterList (Q x) hs hs0 hs1
  have hle :
      (∫ y, slotSurvival (slotParameterList n s y) ∂Q x) ≤
        ∫ _y : Fin n → Y, (1 : ℝ) ∂Q x :=
    integral_mono hSurvival (integrable_const 1) fun y =>
      slotSurvival_le_one (valid_slotParameterList hs0 hs1 y)
  rw [integral_const, probReal_univ] at hle
  simpa [bellmanStep] using hle

theorem bellmanStep_eq_zero_of_absorbing
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y)) [IsMarkovKernel Q]
    {s : AugmentedState Y → ℝ} (_hs : Measurable s)
    (_hs0 : ∀ y, 0 ≤ s y) (_hs1 : ∀ y, s y ≤ 1)
    (hcem : s cemetery = 0)
    (hAbsorb : Q cemetery (allCemetery n) = 1) :
    bellmanStep Q s cemetery = 0 := by
  have hmem : ∀ᵐ y ∂Q cemetery, y ∈ allCemetery n := by
    apply (ae_mem_iff_measure_eq
      (measurableSet_allCemetery n).nullMeasurableSet).mpr
    simpa using hAbsorb
  rw [bellmanStep]
  calc
    (∫ y, slotSurvival (slotParameterList n s y) ∂Q cemetery) =
        ∫ _y : Fin n → AugmentedState Y, (0 : ℝ) ∂Q cemetery := by
      apply integral_congr_ae
      filter_upwards [hmem] with y hy
      exact slotSurvival_eq_zero_of_mem_allCemetery hcem hy
    _ = 0 := by simp

end Shepp.Section4
end SheppFlattenedModule031

section SheppFlattenedModule032
open MeasureTheory Set

namespace Shepp.Section4

open ProbabilityTheory

def liveIndicator {X : Type*} : AugmentedState X → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => 0)

@[simp] theorem liveIndicator_inl {X : Type*} (x : X) :
    liveIndicator (Sum.inl x : AugmentedState X) = 1 := rfl

@[simp] theorem liveIndicator_cemetery {X : Type*} :
    liveIndicator (cemetery : AugmentedState X) = 0 := rfl

theorem measurable_liveIndicator {X : Type*} [MeasurableSpace X] :
    Measurable (liveIndicator (X := X)) := by
  exact measurable_const.sumElim measurable_const

theorem liveIndicator_mem_Icc {X : Type*} (x : AugmentedState X) :
    liveIndicator x ∈ Icc (0 : ℝ) 1 := by
  cases x <;> simp [liveIndicator]

noncomputable def bellmanFrom
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1)))) :
    (j steps : ℕ) → AugmentedState (X j) → ℝ
  | _j, 0 => liveIndicator
  | j, steps + 1 => bellmanStep (Q j) (bellmanFrom n Q (j + 1) steps)

@[simp] theorem bellmanFrom_zero
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1)))) (j : ℕ) :
    bellmanFrom n Q j 0 = liveIndicator := rfl

theorem bellmanFrom_succ
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1)))) (j steps : ℕ) :
    bellmanFrom n Q j (steps + 1) =
      bellmanStep (Q j) (bellmanFrom n Q (j + 1) steps) := rfl

noncomputable def bellmanTo
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    (j N : ℕ) : AugmentedState (X j) → ℝ :=
  bellmanFrom n Q j (N - j)

@[simp] theorem bellmanTo_self
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1)))) (N : ℕ) :
    bellmanTo n Q N N = liveIndicator := by
  simp [bellmanTo]

theorem bellmanTo_step
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    {j N : ℕ} (hjN : j < N) :
    bellmanTo n Q j N = bellmanStep (Q j) (bellmanTo n Q (j + 1) N) := by
  unfold bellmanTo
  rw [show N - j = (N - (j + 1)) + 1 by omega]
  rfl

theorem measurable_bellmanFrom
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1)))) :
    ∀ _j steps, Measurable (bellmanFrom n Q _j steps)
  | _j, 0 => measurable_liveIndicator
  | j, steps + 1 =>
      measurable_bellmanStep (Q j) (measurable_bellmanFrom n Q (j + 1) steps)

theorem measurable_bellmanTo
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1)))) (j N : ℕ) :
    Measurable (bellmanTo n Q j N) := by
  exact measurable_bellmanFrom n Q j (N - j)

theorem bellmanFrom_mem_Icc
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)] :
    ∀ j steps x, bellmanFrom n Q j steps x ∈ Icc (0 : ℝ) 1
  | _j, 0, x => liveIndicator_mem_Icc x
  | j, steps + 1, x => by
      have ih0 : ∀ y, 0 ≤ bellmanFrom n Q (j + 1) steps y :=
        fun y => (bellmanFrom_mem_Icc n Q (j + 1) steps y).1
      have ih1 : ∀ y, bellmanFrom n Q (j + 1) steps y ≤ 1 :=
        fun y => (bellmanFrom_mem_Icc n Q (j + 1) steps y).2
      exact ⟨bellmanStep_nonneg (Q j)
          (measurable_bellmanFrom n Q (j + 1) steps) ih0 ih1 x,
        bellmanStep_le_one (Q j)
          (measurable_bellmanFrom n Q (j + 1) steps) ih0 ih1 x⟩

theorem bellmanTo_mem_Icc
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)] (j N : ℕ) (x : AugmentedState (X j)) :
    bellmanTo n Q j N x ∈ Icc (0 : ℝ) 1 := by
  exact bellmanFrom_mem_Icc n Q j (N - j) x

theorem bellmanFrom_cemetery
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1) :
    ∀ j steps, bellmanFrom n Q j steps cemetery = 0
  | _j, 0 => liveIndicator_cemetery
  | j, steps + 1 => by
      exact bellmanStep_eq_zero_of_absorbing (Q j)
        (measurable_bellmanFrom n Q (j + 1) steps)
        (fun y => (bellmanFrom_mem_Icc n Q (j + 1) steps y).1)
        (fun y => (bellmanFrom_mem_Icc n Q (j + 1) steps y).2)
        (bellmanFrom_cemetery n Q hAbsorb (j + 1) steps) (hAbsorb j)

theorem bellmanTo_cemetery
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (j N : ℕ) : bellmanTo n Q j N cemetery = 0 := by
  exact bellmanFrom_cemetery n Q hAbsorb j (N - j)

theorem bellmanFrom_succ_eq_one_sub_integral_prod
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)] (j steps : ℕ)
    (x : AugmentedState (X j)) :
    bellmanFrom n Q j (steps + 1) x =
      1 - ∫ y, ∏ i, (1 - bellmanFrom n Q (j + 1) steps (y i)) ∂Q j x := by
  exact bellmanStep_eq_one_sub_integral_prod (Q j)
    (measurable_bellmanFrom n Q (j + 1) steps)
    (fun y => (bellmanFrom_mem_Icc n Q (j + 1) steps y).1)
    (fun y => (bellmanFrom_mem_Icc n Q (j + 1) steps y).2) x

end Shepp.Section4
end SheppFlattenedModule032

section SheppFlattenedModule033
open scoped BigOperators ENNReal
open MeasureTheory Set

namespace Shepp.Section4

open ProbabilityTheory

def liveExtension {Y : Type*} (f : Y → ℝ) : AugmentedState Y → ℝ :=
  Sum.elim f (fun _ => 0)

@[simp] theorem liveExtension_inl {Y : Type*} (f : Y → ℝ) (y : Y) :
    liveExtension f (Sum.inl y) = f y := rfl

@[simp] theorem liveExtension_cemetery {Y : Type*} (f : Y → ℝ) :
    liveExtension f (cemetery : AugmentedState Y) = 0 := rfl

theorem measurable_liveExtension {Y : Type*} [MeasurableSpace Y]
    {f : Y → ℝ} (hf : Measurable f) : Measurable (liveExtension f) := by
  exact hf.sumElim measurable_const

theorem measurableEmbedding_inl {Y : Type*} [MeasurableSpace Y] :
    MeasurableEmbedding (@Sum.inl Y Unit) := by
  exact ⟨Sum.inl_injective, measurable_inl,
    fun _s hs => measurableSet_inl_image.mpr hs⟩

theorem integral_comap_inl
    {Y : Type*} [MeasurableSpace Y] (μ : Measure (AugmentedState Y))
    (f : Y → ℝ) :
    ∫ y, f y ∂μ.comap (@Sum.inl Y Unit) = ∫ z, liveExtension f z ∂μ := by
  let emb : MeasurableEmbedding (@Sum.inl Y Unit) := measurableEmbedding_inl
  have hmap := emb.integral_map (μ := μ.comap (@Sum.inl Y Unit)) (liveExtension f)
  have hind : (range (@Sum.inl Y Unit)).indicator (liveExtension f) = liveExtension f := by
    funext z
    cases z with
    | inl y => simp [liveExtension]
    | inr u => simp [liveExtension]
  calc
    (∫ y, f y ∂μ.comap (@Sum.inl Y Unit)) =
        ∫ z, liveExtension f z ∂Measure.map (@Sum.inl Y Unit)
          (μ.comap (@Sum.inl Y Unit)) := by simpa [liveExtension] using hmap.symm
    _ = ∫ z in range (@Sum.inl Y Unit), liveExtension f z ∂μ := by rw [emb.map_comap]
    _ = ∫ z, (range (@Sum.inl Y Unit)).indicator (liveExtension f) z ∂μ := by
      rw [integral_indicator measurableSet_range_inl]
    _ = ∫ z, liveExtension f z ∂μ := by rw [hind]

noncomputable def liveCoordinateKernel
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y)) (i : Fin n) :
    Kernel X Y :=
  Kernel.comapRight
    ((Q.comap (@Sum.inl X Unit) measurable_inl).map (fun y => y i))
    measurableEmbedding_inl

noncomputable def liveMeanKernel
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y)) : Kernel X Y :=
  ∑ i : Fin n, liveCoordinateKernel Q i

noncomputable instance instIsFiniteKernel_liveCoordinateKernel
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y)) [IsFiniteKernel Q]
    (i : Fin n) : IsFiniteKernel (liveCoordinateKernel Q i) := by
  rw [liveCoordinateKernel]
  infer_instance

noncomputable instance instIsFiniteKernel_liveMeanKernel
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y)) [IsFiniteKernel Q] :
    IsFiniteKernel (liveMeanKernel Q) := by
  refine ⟨(n : ℝ≥0∞) * Q.bound,
    ENNReal.mul_lt_top (by simp) Q.bound_lt_top, fun x => ?_⟩
  rw [liveMeanKernel, Kernel.finsetSum_apply, Measure.finsetSum_apply]
  calc
    (∑ i : Fin n, (liveCoordinateKernel Q i x) univ) ≤
        ∑ _i : Fin n, Q.bound := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [liveCoordinateKernel, Kernel.comapRight_apply' _ _ _ MeasurableSet.univ]
      refine (measure_mono (subset_univ _)).trans ?_
      rw [Kernel.map_apply _ (by fun_prop), Measure.map_apply (by fun_prop) MeasurableSet.univ,
        preimage_univ, Kernel.comap_apply]
      exact Kernel.measure_le_bound Q (Sum.inl x) univ
    _ = (n : ℝ≥0∞) * Q.bound := by simp

theorem integral_liveCoordinateKernel
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y))
    {f : Y → ℝ} (hf : Measurable f) (i : Fin n) (x : X) :
    ∫ y, f y ∂liveCoordinateKernel Q i x =
      ∫ y, liveExtension f (y i) ∂Q (Sum.inl x) := by
  rw [liveCoordinateKernel, Kernel.comapRight_apply, integral_comap_inl]
  rw [Kernel.map_apply _ (by fun_prop)]
  rw [integral_map (measurable_pi_apply i).aemeasurable
    (measurable_liveExtension hf).aestronglyMeasurable]
  rw [Kernel.comap_apply]

theorem liveExtension_norm_le
    {Y : Type*} {f : Y → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hfC : ∀ y, ‖f y‖ ≤ C) (z : AugmentedState Y) :
    ‖liveExtension f z‖ ≤ C := by
  cases z with
  | inl y => exact hfC y
  | inr u => simpa [liveExtension] using hC0

theorem integral_liveMeanKernel
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y)) [IsMarkovKernel Q]
    {f : Y → ℝ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hfC : ∀ y, ‖f y‖ ≤ C) (x : X) :
    ∫ y, f y ∂liveMeanKernel Q x = slotMean Q (liveExtension f) (Sum.inl x) := by
  have hCoord : ∀ i : Fin n, Integrable f (liveCoordinateKernel Q i x) := by
    intro i
    apply Integrable.of_bound hf.aestronglyMeasurable C
    exact ae_of_all _ hfC
  have hQ : ∀ i : Fin n, Integrable (fun y => liveExtension f (y i)) (Q (Sum.inl x)) := by
    intro i
    apply Integrable.of_bound
      ((measurable_liveExtension hf).comp (measurable_pi_apply i)).aestronglyMeasurable C
    exact ae_of_all _ fun y => liveExtension_norm_le hC0 hfC (y i)
  rw [liveMeanKernel, Kernel.finsetSum_apply]
  rw [integral_finsetSum_measure (fun i _hi => hCoord i)]
  simp_rw [integral_liveCoordinateKernel Q hf]
  rw [slotMean]
  simp_rw [slotMass_slotParameterList]
  rw [integral_finsetSum _ fun i _hi => hQ i]

noncomputable def liveMeanPush
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y)) [IsFiniteKernel Q]
    (μ : FiniteMeasure X) : FiniteMeasure Y :=
  ⟨liveMeanKernel Q ∘ₘ (μ : Measure X), inferInstance⟩

theorem integral_liveMeanPush
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y)) [IsMarkovKernel Q]
    (μ : FiniteMeasure X)
    {f : Y → ℝ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hfC : ∀ y, ‖f y‖ ≤ C) :
    ∫ y, f y ∂(liveMeanPush Q μ : Measure Y) =
      ∫ x, slotMean Q (liveExtension f) (Sum.inl x) ∂(μ : Measure X) := by
  have hInt : Integrable f (liveMeanPush Q μ : Measure Y) := by
    apply Integrable.of_bound hf.aestronglyMeasurable C
    exact ae_of_all _ hfC
  change Integrable f (liveMeanKernel Q ∘ₘ (μ : Measure X)) at hInt
  have hEq : liveMeanKernel Q ∘ₘ (μ : Measure X) =
      (liveMeanKernel Q ∘ₖ Kernel.const Unit (μ : Measure X)) () :=
    Measure.comp_eq_comp_const_apply
  have hInt' : Integrable f
      ((liveMeanKernel Q ∘ₖ Kernel.const Unit (μ : Measure X)) ()) := hEq ▸ hInt
  change (∫ y, f y ∂(liveMeanKernel Q ∘ₘ (μ : Measure X))) = _
  calc
    (∫ y, f y ∂(liveMeanKernel Q ∘ₘ (μ : Measure X))) =
        ∫ x : X, ∫ y, f y ∂liveMeanKernel Q x
          ∂Kernel.const Unit (μ : Measure X) () := by
      rw [hEq]
      exact Kernel.integral_comp (η := liveMeanKernel Q)
        (κ := Kernel.const Unit (μ : Measure X)) (a := ()) hInt'
    _ = ∫ x, ∫ y, f y ∂liveMeanKernel Q x ∂(μ : Measure X) := by
      simp only [Kernel.const_apply]
    _ = ∫ x, slotMean Q (liveExtension f) (Sum.inl x) ∂(μ : Measure X) := by
      apply integral_congr_ae
      filter_upwards with x
      exact integral_liveMeanKernel Q hf hC0 hfC x

noncomputable def meanFlow
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (μ0 : FiniteMeasure (X 0)) : (j : ℕ) → FiniteMeasure (X j)
  | 0 => μ0
  | j + 1 => liveMeanPush (Q j) (meanFlow n Q μ0 j)

theorem meanFlow_succ_integral
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (μ0 : FiniteMeasure (X 0)) (j : ℕ)
    {f : X (j + 1) → ℝ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hfC : ∀ y, ‖f y‖ ≤ C) :
    ∫ y, f y ∂(meanFlow n Q μ0 (j + 1) : Measure (X (j + 1))) =
      ∫ x, slotMean (Q j) (liveExtension f) (Sum.inl x)
        ∂(meanFlow n Q μ0 j : Measure (X j)) := by
  simpa only [meanFlow] using
    integral_liveMeanPush (Q j) (meanFlow n Q μ0 j) hf hC0 hfC

end Shepp.Section4
end SheppFlattenedModule033

section SheppFlattenedModule034
open scoped BigOperators

namespace Shepp.Section4

noncomputable def conductanceEta (B : ℕ) : ℝ :=
  resistanceLambda B / (1 + resistanceLambda B) ^ 2

noncomputable def resistanceConstant (B : ℕ) : ℝ :=
  conductanceEta B /
    (1 + conductanceEta B * (1 + resistanceLambda B))

theorem conductanceEta_pos {B : ℕ} (hB : 1 ≤ B) :
    0 < conductanceEta B := by
  have hLambda := resistanceLambda_pos hB
  exact div_pos hLambda (sq_pos_of_pos (by linarith))

theorem resistanceConstant_pos {B : ℕ} (hB : 1 ≤ B) :
    0 < resistanceConstant B := by
  have hη := conductanceEta_pos hB
  have hLambda := resistanceLambda_pos hB
  exact div_pos hη (by positivity)

theorem quadraticPotential_nonneg {B : ℕ} (hB : 1 ≤ B)
    {u : ℝ} (hu0 : 0 ≤ u) :
    0 ≤ quadraticPotential B u := by
  unfold quadraticPotential
  exact add_nonneg hu0 (mul_nonneg (resistanceLambda_pos hB).le (sq_nonneg u))

theorem quadraticPotential_ge_self {B : ℕ} (hB : 1 ≤ B)
    {u : ℝ} (_hu0 : 0 ≤ u) :
    u ≤ quadraticPotential B u := by
  unfold quadraticPotential
  have hLambda := (resistanceLambda_pos hB).le
  nlinarith [mul_nonneg hLambda (sq_nonneg u)]

theorem quadraticPotential_le_linear {B : ℕ} (hB : 1 ≤ B)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    quadraticPotential B u ≤ (1 + resistanceLambda B) * u := by
  unfold quadraticPotential
  have hLambda := (resistanceLambda_pos hB).le
  nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]

theorem quadraticPotential_le_one_add {B : ℕ} (hB : 1 ≤ B)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    quadraticPotential B u ≤ 1 + resistanceLambda B := by
  have hlin := quadraticPotential_le_linear hB hu0 hu1
  have hfactor : 0 ≤ 1 + resistanceLambda B := by
    linarith [resistanceLambda_pos hB]
  exact hlin.trans (mul_le_of_le_one_right hfactor hu1)

theorem reciprocal_resistance_step
    {B : ℕ} (hB : 1 ≤ B) {C D r : ℝ}
    (hC : 0 < C) (hr : 0 ≤ r)
    (hgrowth : D - C ≥ conductanceEta B * r * C ^ 2)
    (hrC : r * C ≤ 1 + resistanceLambda B) :
    1 / C - 1 / D ≥ resistanceConstant B * r := by
  let η := conductanceEta B
  let lambdaCoeff := resistanceLambda B
  have hη : 0 < η := conductanceEta_pos hB
  have hLambda : 0 < lambdaCoeff := resistanceLambda_pos hB
  have ht0 : 0 ≤ η * r * C := by positivity
  have honeT : 0 < 1 + η * r * C := by linarith
  have hbase : 0 < C * (1 + η * r * C) := mul_pos hC honeT
  have hbaseD : C * (1 + η * r * C) ≤ D := by
    dsimp only [η]
    nlinarith
  have hD : 0 < D := hbase.trans_le hbaseD
  have hinv : 1 / D ≤ 1 / (C * (1 + η * r * C)) := by
    exact (div_le_div_iff₀ hD hbase).2 (by simpa using hbaseD)
  have hfirst :
      1 / C - 1 / D ≥ η * r / (1 + η * r * C) := by
    have hid :
        1 / C - 1 / (C * (1 + η * r * C)) =
          η * r / (1 + η * r * C) := by
      field_simp [ne_of_gt hC, ne_of_gt honeT]
      ring
    rw [← hid]
    linarith
  have hsmallBig :
      1 + η * r * C ≤ 1 + η * (1 + lambdaCoeff) := by
    have := mul_le_mul_of_nonneg_left hrC hη.le
    dsimp only [η, lambdaCoeff] at this ⊢
    nlinarith
  have hbig : 0 < 1 + η * (1 + lambdaCoeff) := by positivity
  have hfrac :
      η * r / (1 + η * (1 + lambdaCoeff)) ≤ η * r / (1 + η * r * C) := by
    apply (div_le_div_iff₀ hbig honeT).2
    exact mul_le_mul_of_nonneg_left hsmallBig (mul_nonneg hη.le hr)
  have hconst : resistanceConstant B * r =
      η * r / (1 + η * (1 + lambdaCoeff)) := by
    dsimp only [resistanceConstant, η, lambdaCoeff]
    field_simp [ne_of_gt hbig]
  rw [hconst]
  exact hfrac.trans hfirst

theorem finite_reciprocal_resistance
    {N : ℕ} {C r : ℕ → ℝ} {c : ℝ}
    (hstep : ∀ j < N, c * r j ≤ 1 / C j - 1 / C (j + 1)) :
    c * ∑ j ∈ Finset.range N, r j ≤ 1 / C 0 - 1 / C N := by
  calc
    c * ∑ j ∈ Finset.range N, r j =
        ∑ j ∈ Finset.range N, c * r j := by
      rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range N, (1 / C j - 1 / C (j + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hstep j (Finset.mem_range.mp hj)
    _ = 1 / C 0 - 1 / C N := by
      exact Finset.sum_range_sub' (fun j => 1 / C j) N

end Shepp.Section4
end SheppFlattenedModule034

section SheppFlattenedModule035
open scoped BigOperators
open MeasureTheory Set

namespace Shepp.Section4

open ProbabilityTheory

theorem measurable_quadraticPotential (B : ℕ) :
    Measurable (quadraticPotential B) := by
  unfold quadraticPotential
  fun_prop

theorem slotMean_nonneg_of_nonneg
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel X (Fin n → Y)) {f : Y → ℝ}
    (hf0 : ∀ y, 0 ≤ f y) (x : X) :
    0 ≤ slotMean Q f x := by
  rw [slotMean]
  apply integral_nonneg
  intro y
  change 0 ≤ slotMass (slotParameterList n f y)
  rw [slotMass_slotParameterList]
  exact Finset.sum_nonneg fun i _hi => hf0 (y i)

theorem slotMean_le_nat_mul
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel X (Fin n → Y)) [IsMarkovKernel Q]
    {f : Y → ℝ} (hf : Measurable f) {C : ℝ} (_hC0 : 0 ≤ C)
    (hf0 : ∀ y, 0 ≤ f y) (hfC : ∀ y, f y ≤ C) (x : X) :
    slotMean Q f x ≤ (n : ℝ) * C := by
  have hMeas := measurable_slotMass_slotParameterList (n := n) hf
  have hPoint : ∀ y : Fin n → Y,
      slotMass (slotParameterList n f y) ≤ (n : ℝ) * C := by
    intro y
    rw [slotMass_slotParameterList]
    calc
      (∑ i, f (y i)) ≤ ∑ _i : Fin n, C :=
        Finset.sum_le_sum fun i _hi => hfC (y i)
      _ = (n : ℝ) * C := by simp
  have hInt : Integrable (fun y : Fin n → Y => slotMass (slotParameterList n f y))
      (Q x) := by
    apply Integrable.of_bound hMeas.aestronglyMeasurable ((n : ℝ) * C)
    filter_upwards with y
    rw [Real.norm_of_nonneg]
    · exact hPoint y
    · rw [slotMass_slotParameterList]
      exact Finset.sum_nonneg fun i _hi => hf0 (y i)
  have hle := integral_mono hInt (integrable_const ((n : ℝ) * C)) hPoint
  rw [integral_const, probReal_univ] at hle
  simpa [slotMean] using hle

theorem slotMean_norm_le_bound_mul
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n B : ℕ}
    (Q : Kernel X (Fin n → Y)) [IsMarkovKernel Q]
    (hnB : n ≤ B) {f : Y → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hf0 : ∀ y, 0 ≤ f y)
    (hfC : ∀ y, f y ≤ C) (x : X) :
    ‖slotMean Q f x‖ ≤ (B : ℝ) * C := by
  have hnonneg := slotMean_nonneg_of_nonneg Q hf0 x
  rw [Real.norm_of_nonneg hnonneg]
  calc
    slotMean Q f x ≤ (n : ℝ) * C :=
      slotMean_le_nat_mul Q hf hC0 hf0 hfC x
    _ ≤ (B : ℝ) * C := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnB) hC0

noncomputable def meanPopulation {X : Type*} [MeasurableSpace X]
    (μ : FiniteMeasure X) : ℝ :=
  (μ : Measure X).real univ

noncomputable def survivalIntegral
    {X : Type*} [MeasurableSpace X] (μ : FiniteMeasure X)
    (s : AugmentedState X → ℝ) : ℝ :=
  ∫ x, s (Sum.inl x) ∂(μ : Measure X)

noncomputable def squareSurvivalIntegral
    {X : Type*} [MeasurableSpace X] (μ : FiniteMeasure X)
    (s : AugmentedState X → ℝ) : ℝ :=
  ∫ x, (s (Sum.inl x)) ^ 2 ∂(μ : Measure X)

noncomputable def conductance
    {X : Type*} [MeasurableSpace X] (B : ℕ) (μ : FiniteMeasure X)
    (s : AugmentedState X → ℝ) : ℝ :=
  ∫ x, quadraticPotential B (s (Sum.inl x)) ∂(μ : Measure X)

theorem survivalIntegral_sq_le_population_mul_square
    {X : Type*} [MeasurableSpace X] (μ : FiniteMeasure X)
    {s : AugmentedState X → ℝ} (hs : Measurable s)
    (hs0 : ∀ z, 0 ≤ s z) (hs1 : ∀ z, s z ≤ 1) :
    survivalIntegral μ s ^ 2 ≤
      meanPopulation μ * squareSurvivalIntegral μ s := by
  have hMeas : Measurable fun x : X => s (Sum.inl x) := hs.comp measurable_inl
  have hInt : Integrable (fun x : X => s (Sum.inl x)) (μ : Measure X) := by
    apply Integrable.of_bound hMeas.aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_of_nonneg (hs0 _)]
    exact hs1 _
  have hSq : Integrable (fun x : X => (s (Sum.inl x)) ^ 2) (μ : Measure X) := by
    apply Integrable.of_bound (hMeas.pow_const 2).aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [hs0 (Sum.inl x), hs1 (Sum.inl x)]
  have h := integral_sq_le_measure_compl_mul_integral_sq (μ : Measure X)
    (Z := (∅ : Set X)) (S := fun x => s (Sum.inl x))
    (fun x => hs0 (Sum.inl x)) hInt hSq
    (fun _x hx => False.elim hx)
  simpa [survivalIntegral, meanPopulation, squareSurvivalIntegral] using h

theorem survivalIntegral_le_conductance
    {X : Type*} [MeasurableSpace X] {B : ℕ} (hB : 1 ≤ B)
    (μ : FiniteMeasure X) {s : AugmentedState X → ℝ} (hs : Measurable s)
    (hs0 : ∀ z, 0 ≤ s z) (hs1 : ∀ z, s z ≤ 1) :
    survivalIntegral μ s ≤ conductance B μ s := by
  have hS : Integrable (fun x : X => s (Sum.inl x)) (μ : Measure X) := by
    apply Integrable.of_bound (hs.comp measurable_inl).aestronglyMeasurable 1
    filter_upwards with x
    simp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (hs0 _)]
    exact hs1 _
  have hQ : Integrable (fun x : X => quadraticPotential B (s (Sum.inl x)))
      (μ : Measure X) := by
    apply Integrable.of_bound
      ((measurable_quadraticPotential B).comp (hs.comp measurable_inl)).aestronglyMeasurable
      (1 + resistanceLambda B)
    filter_upwards with x
    simp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (quadraticPotential_nonneg hB (hs0 _))]
    exact quadraticPotential_le_one_add hB (hs0 _) (hs1 _)
  exact integral_mono hS hQ fun x => quadraticPotential_ge_self hB (hs0 _)

theorem conductance_le_linear_survivalIntegral
    {X : Type*} [MeasurableSpace X] {B : ℕ} (hB : 1 ≤ B)
    (μ : FiniteMeasure X) {s : AugmentedState X → ℝ} (hs : Measurable s)
    (hs0 : ∀ z, 0 ≤ s z) (hs1 : ∀ z, s z ≤ 1) :
    conductance B μ s ≤
      (1 + resistanceLambda B) * survivalIntegral μ s := by
  have hQ : Integrable (fun x : X => quadraticPotential B (s (Sum.inl x)))
      (μ : Measure X) := by
    apply Integrable.of_bound
      ((measurable_quadraticPotential B).comp (hs.comp measurable_inl)).aestronglyMeasurable
      (1 + resistanceLambda B)
    filter_upwards with x
    simp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (quadraticPotential_nonneg hB (hs0 _))]
    exact quadraticPotential_le_one_add hB (hs0 _) (hs1 _)
  have hS : Integrable (fun x : X => s (Sum.inl x)) (μ : Measure X) := by
    apply Integrable.of_bound (hs.comp measurable_inl).aestronglyMeasurable 1
    filter_upwards with x
    simp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (hs0 _)]
    exact hs1 _
  have hle := integral_mono hQ (hS.const_mul (1 + resistanceLambda B))
    fun x => quadraticPotential_le_linear hB (hs0 _) (hs1 _)
  rw [integral_const_mul] at hle
  simpa [conductance, survivalIntegral] using hle

theorem conductance_le_one_add_mul_population
    {X : Type*} [MeasurableSpace X] {B : ℕ} (hB : 1 ≤ B)
    (μ : FiniteMeasure X) {s : AugmentedState X → ℝ} (hs : Measurable s)
    (hs0 : ∀ z, 0 ≤ s z) (hs1 : ∀ z, s z ≤ 1) :
    conductance B μ s ≤ (1 + resistanceLambda B) * meanPopulation μ := by
  have hInt : Integrable (fun x : X => quadraticPotential B (s (Sum.inl x)))
      (μ : Measure X) := by
    apply Integrable.of_bound
      ((measurable_quadraticPotential B).comp (hs.comp measurable_inl)).aestronglyMeasurable
      (1 + resistanceLambda B)
    filter_upwards with x
    simp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (quadraticPotential_nonneg hB (hs0 _))]
    exact quadraticPotential_le_one_add hB (hs0 _) (hs1 _)
  have hle := integral_mono hInt (integrable_const (1 + resistanceLambda B))
    fun x => quadraticPotential_le_one_add hB (hs0 _) (hs1 _)
  rw [integral_const] at hle
  simpa [conductance, meanPopulation, mul_comm] using hle

theorem liveExtension_quadraticPotential_restrict
    {X : Type*} (B : ℕ) {s : AugmentedState X → ℝ}
    (hcem : s cemetery = 0) :
    liveExtension (fun x => quadraticPotential B (s (Sum.inl x))) =
      quadraticPotential B ∘ s := by
  funext z
  cases z with
  | inl x => rfl
  | inr u =>
      cases u
      have hz : s (Sum.inr ()) = 0 := by simpa [cemetery] using hcem
      simp [liveExtension, quadraticPotential, hz]

noncomputable def horizonSurvivalIntegral
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (μ0 : FiniteMeasure (X 0)) (j N : ℕ) : ℝ :=
  survivalIntegral (meanFlow n Q μ0 j) (bellmanTo n Q j N)

noncomputable def horizonSquareIntegral
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (μ0 : FiniteMeasure (X 0)) (j N : ℕ) : ℝ :=
  squareSurvivalIntegral (meanFlow n Q μ0 j) (bellmanTo n Q j N)

noncomputable def horizonConductance
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (B : ℕ) (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (μ0 : FiniteMeasure (X 0)) (j N : ℕ) : ℝ :=
  conductance B (meanFlow n Q μ0 j) (bellmanTo n Q j N)

theorem horizonConductance_succ_eq_slotMean
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (B : ℕ) (hB : 1 ≤ B) (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (μ0 : FiniteMeasure (X 0)) (j N : ℕ) :
    horizonConductance B n Q μ0 (j + 1) N =
      ∫ x, slotMean (Q j) (quadraticPotential B ∘ bellmanTo n Q (j + 1) N)
        (Sum.inl x) ∂(meanFlow n Q μ0 j : Measure (X j)) := by
  let sNext := bellmanTo n Q (j + 1) N
  have hsMeas : Measurable sNext := measurable_bellmanTo n Q (j + 1) N
  have hs0 : ∀ z, 0 ≤ sNext z :=
    fun z => (bellmanTo_mem_Icc n Q (j + 1) N z).1
  have hs1 : ∀ z, sNext z ≤ 1 :=
    fun z => (bellmanTo_mem_Icc n Q (j + 1) N z).2
  let f : X (j + 1) → ℝ :=
    fun y => quadraticPotential B (sNext (Sum.inl y))
  have hfMeas : Measurable f :=
    (measurable_quadraticPotential B).comp (hsMeas.comp measurable_inl)
  have hfactor : 0 ≤ 1 + resistanceLambda B := by
    linarith [resistanceLambda_pos hB]
  have hfBound : ∀ y, ‖f y‖ ≤ 1 + resistanceLambda B := by
    intro y
    rw [Real.norm_of_nonneg (quadraticPotential_nonneg hB (hs0 _))]
    exact quadraticPotential_le_one_add hB (hs0 _) (hs1 _)
  have hflow := meanFlow_succ_integral n Q μ0 j hfMeas hfactor hfBound
  have hcem : sNext cemetery = 0 :=
    bellmanTo_cemetery n Q hAbsorb (j + 1) N
  have hExt : liveExtension f = quadraticPotential B ∘ sNext := by
    exact liveExtension_quadraticPotential_restrict B hcem
  rw [hExt] at hflow
  simpa only [horizonConductance, conductance, sNext, f] using hflow

theorem horizonSurvival_nonneg
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (μ0 : FiniteMeasure (X 0)) (j N : ℕ) :
    0 ≤ horizonSurvivalIntegral n Q μ0 j N := by
  rw [horizonSurvivalIntegral, survivalIntegral]
  exact integral_nonneg fun x => (bellmanTo_mem_Icc n Q j N (Sum.inl x)).1

@[simp] theorem horizonSurvival_terminal
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (μ0 : FiniteMeasure (X 0)) (N : ℕ) :
    horizonSurvivalIntegral n Q μ0 N N = meanPopulation (meanFlow n Q μ0 N) := by
  simp [horizonSurvivalIntegral, survivalIntegral, meanPopulation, bellmanTo_self,
    liveIndicator, integral_const]

@[simp] theorem horizonConductance_terminal
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (B : ℕ) (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (μ0 : FiniteMeasure (X 0)) (N : ℕ) :
    horizonConductance B n Q μ0 N N =
      (1 + resistanceLambda B) * meanPopulation (meanFlow n Q μ0 N) := by
  simp [horizonConductance, conductance, meanPopulation, bellmanTo_self,
    liveIndicator, quadraticPotential, integral_const, mul_comm]

end Shepp.Section4
end SheppFlattenedModule035

section SheppFlattenedModule036
open MeasureTheory

namespace Shepp.Section4

structure AssociatedFunction
    {W : Type*} [MeasurableSpace W] [Preorder W] (f : W → ℝ) : Prop where
  measurable : Measurable f
  nonnegative : ∀ w, 0 ≤ f w
  monotone : Monotone f
  bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ w, f w ≤ C

def PositivelyAssociated
    {W : Type*} [MeasurableSpace W] [Preorder W] (μ : Measure W) : Prop :=
  ∀ f g : W → ℝ, AssociatedFunction f → AssociatedFunction g →
    (∫ w, f w ∂μ) * (∫ w, g w ∂μ) ≤ ∫ w, f w * g w ∂μ

def functionListProduct {W : Type*} (fs : List (W → ℝ)) (w : W) : ℝ :=
  (fs.map fun f => f w).prod

@[simp] theorem functionListProduct_nil {W : Type*} :
    functionListProduct ([] : List (W → ℝ)) = fun _ => 1 := by
  funext w
  simp [functionListProduct]

@[simp] theorem functionListProduct_cons {W : Type*}
    (f : W → ℝ) (fs : List (W → ℝ)) (w : W) :
    functionListProduct (f :: fs) w = f w * functionListProduct fs w := by
  simp [functionListProduct]

theorem AssociatedFunction.one
    {W : Type*} [MeasurableSpace W] [Preorder W] :
    AssociatedFunction (fun _w : W => (1 : ℝ)) := by
  exact ⟨measurable_const, fun _ => by norm_num, monotone_const,
    ⟨1, by norm_num, fun _ => le_rfl⟩⟩

theorem AssociatedFunction.mul
    {W : Type*} [MeasurableSpace W] [Preorder W]
    {f g : W → ℝ} (hf : AssociatedFunction f) (hg : AssociatedFunction g) :
    AssociatedFunction (fun w => f w * g w) := by
  refine ⟨hf.measurable.mul hg.measurable,
    fun w => mul_nonneg (hf.nonnegative w) (hg.nonnegative w), ?_, ?_⟩
  · intro a b hab
    exact mul_le_mul (hf.monotone hab) (hg.monotone hab)
      (hg.nonnegative a) (hf.nonnegative b)
  · obtain ⟨Cf, hCf0, hCf⟩ := hf.bounded
    obtain ⟨Cg, hCg0, hCg⟩ := hg.bounded
    exact ⟨Cf * Cg, mul_nonneg hCf0 hCg0, fun w =>
      mul_le_mul (hCf w) (hCg w) (hg.nonnegative w) hCf0⟩

theorem associatedFunction_functionListProduct
    {W : Type*} [MeasurableSpace W] [Preorder W]
    (fs : List (W → ℝ)) (hfs : ∀ f ∈ fs, AssociatedFunction f) :
    AssociatedFunction (functionListProduct fs) := by
  induction fs with
  | nil => exact AssociatedFunction.one
  | cons f fs ih =>
      rw [show functionListProduct (f :: fs) =
          fun w => f w * functionListProduct fs w by funext w; simp]
      exact (hfs f (by simp)).mul (ih fun g hg => hfs g (by simp [hg]))

theorem AssociatedFunction.integrable
    {W : Type*} [MeasurableSpace W] [Preorder W]
    {μ : Measure W} [IsFiniteMeasure μ] {f : W → ℝ}
    (hf : AssociatedFunction f) : Integrable f μ := by
  obtain ⟨C, hC0, hC⟩ := hf.bounded
  apply Integrable.of_bound hf.measurable.aestronglyMeasurable C
  filter_upwards with w
  rw [Real.norm_of_nonneg (hf.nonnegative w)]
  exact hC w

theorem AssociatedFunction.integral_nonneg
    {W : Type*} [MeasurableSpace W] [Preorder W]
    {μ : Measure W} {f : W → ℝ} (hf : AssociatedFunction f) :
    0 ≤ ∫ w, f w ∂μ :=
  MeasureTheory.integral_nonneg hf.nonnegative

theorem positivelyAssociated_listProduct
    {W : Type*} [MeasurableSpace W] [Preorder W]
    (μ : Measure W) [IsProbabilityMeasure μ]
    (hassoc : PositivelyAssociated μ)
    (fs : List (W → ℝ)) (hfs : ∀ f ∈ fs, AssociatedFunction f) :
    (fs.map fun f => ∫ w, f w ∂μ).prod ≤
      ∫ w, functionListProduct fs w ∂μ := by
  induction fs with
  | nil => simp [functionListProduct, integral_const, probReal_univ]
  | cons f fs ih =>
      have hf : AssociatedFunction f := hfs f (by simp)
      have htail : ∀ g ∈ fs, AssociatedFunction g :=
        fun g hg => hfs g (by simp [hg])
      have hprod := associatedFunction_functionListProduct fs htail
      have hpair := hassoc f (functionListProduct fs) hf hprod
      have hih := ih htail
      calc
        ((f :: fs).map fun g => ∫ w, g w ∂μ).prod =
            (∫ w, f w ∂μ) * (fs.map fun g => ∫ w, g w ∂μ).prod := by simp
        _ ≤ (∫ w, f w ∂μ) * (∫ w, functionListProduct fs w ∂μ) :=
          mul_le_mul_of_nonneg_left hih hf.integral_nonneg
        _ ≤ ∫ w, f w * functionListProduct fs w ∂μ := hpair
        _ = ∫ w, functionListProduct (f :: fs) w ∂μ := by
          apply integral_congr_ae
          filter_upwards with w
          simp

theorem one_sub_integral_functionListProduct_le
    {W : Type*} [MeasurableSpace W] [Preorder W]
    (μ : Measure W) [IsProbabilityMeasure μ]
    (hassoc : PositivelyAssociated μ)
    (fs : List (W → ℝ)) (hfs : ∀ f ∈ fs, AssociatedFunction f) :
    1 - ∫ w, functionListProduct fs w ∂μ ≤
      1 - (fs.map fun f => ∫ w, f w ∂μ).prod := by
  linarith [positivelyAssociated_listProduct μ hassoc fs hfs]

end Shepp.Section4
end SheppFlattenedModule036

section SheppFlattenedModule037
open scoped BigOperators
open MeasureTheory

namespace Shepp.Section4

open ProbabilityTheory

def noDescendantFactor
    {X W Y : Type*} {n : ℕ}
    (T : X → W → Fin n → AugmentedState Y)
    (s : AugmentedState Y → ℝ) (x : X) (w : W) : ℝ :=
  ∏ i, (1 - s (T x w i))

theorem associatedFunction_noDescendantFactor
    {X W Y : Type*} [MeasurableSpace W] [MeasurableSpace Y] [Preorder W]
    [Preorder (AugmentedState Y)] {n : ℕ}
    (T : X → W → Fin n → AugmentedState Y)
    (s : AugmentedState Y → ℝ) (hs : Measurable s)
    (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1) (hsMono : Monotone s)
    (hTMeas : ∀ x i, Measurable fun w => T x w i)
    (hDestructive : ∀ x i, Antitone fun w => T x w i)
    (x : X) : AssociatedFunction (noDescendantFactor T s x) := by
  have hMeas : Measurable (noDescendantFactor T s x) := by
    unfold noDescendantFactor
    exact Finset.measurable_fun_prod Finset.univ fun i _hi =>
      measurable_const.sub (hs.comp (hTMeas x i))
  have hNonneg : ∀ w, 0 ≤ noDescendantFactor T s x w := by
    intro w
    unfold noDescendantFactor
    exact Finset.prod_nonneg fun i _hi => sub_nonneg.mpr (hs1 _)
  have hMono : Monotone (noDescendantFactor T s x) := by
    intro a b hab
    unfold noDescendantFactor
    apply Finset.prod_le_prod
    · intro i _hi
      exact sub_nonneg.mpr (hs1 _)
    · intro i _hi
      have hstate := hDestructive x i hab
      have hsOrder := hsMono hstate
      linarith
  have hBound : ∀ w, noDescendantFactor T s x w ≤ 1 := by
    intro w
    unfold noDescendantFactor
    exact Finset.prod_le_one
      (fun i _hi => sub_nonneg.mpr (hs1 _))
      (fun i _hi => by linarith [hs0 (T x w i)])
  exact ⟨hMeas, hNonneg, hMono, ⟨1, by norm_num, hBound⟩⟩

theorem measurable_slotNoDescendantProduct
    {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    {s : AugmentedState Y → ℝ} (hs : Measurable s) :
    Measurable fun y : Fin n → AugmentedState Y => ∏ i, (1 - s (y i)) := by
  fun_prop

theorem integral_noDescendantFactor_eq_one_sub_bellmanStep
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Y]
    {n : ℕ} (ν : Measure W)
    (Q : Kernel A (Fin n → AugmentedState Y)) [IsMarkovKernel Q]
    (T : A → W → Fin n → AugmentedState Y)
    {s : AugmentedState Y → ℝ} (hs : Measurable s)
    (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1)
    (hTMeas : ∀ x i, Measurable fun w => T x w i)
    (hLaw : ∀ x, Measure.map (fun w i => T x w i) ν = Q x)
    (x : A) :
    ∫ w, noDescendantFactor T s x w ∂ν =
      1 - bellmanStep Q s x := by
  have hVector : Measurable fun w => (fun i => T x w i) :=
    measurable_pi_lambda _ fun i => hTMeas x i
  have hProd := measurable_slotNoDescendantProduct (n := n) hs
  have hmap := integral_map (μ := ν) hVector.aemeasurable hProd.aestronglyMeasurable
  rw [hLaw x] at hmap
  have hBellman := bellmanStep_eq_one_sub_integral_prod Q hs hs0 hs1 x
  change (∫ w, ∏ i, (1 - s (T x w i)) ∂ν) =
    1 - bellmanStep Q s x
  calc
    (∫ w, ∏ i, (1 - s (T x w i)) ∂ν) =
        ∫ y, ∏ i, (1 - s (y i)) ∂Q x := hmap.symm
    _ = 1 - bellmanStep Q s x := by linarith

def populationPotential {X : Type*} (s : X → ℝ) (xs : List X) : ℝ :=
  slotSurvival (xs.map s)

def sharedPopulationUpdate
    {A W Y : Type*} {n : ℕ}
    (T : A → W → Fin n → Y) (xs : List A) (w : W) : List Y :=
  xs.flatMap fun x => List.ofFn (T x w)

@[simp] theorem sharedPopulationUpdate_nil
    {A W Y : Type*} {n : ℕ} (T : A → W → Fin n → Y) (w : W) :
    sharedPopulationUpdate T [] w = [] := rfl

@[simp] theorem sharedPopulationUpdate_cons
    {A W Y : Type*} {n : ℕ} (T : A → W → Fin n → Y)
    (x : A) (xs : List A) (w : W) :
    sharedPopulationUpdate T (x :: xs) w =
      List.ofFn (T x w) ++ sharedPopulationUpdate T xs w := by
  simp [sharedPopulationUpdate]

theorem functionListProduct_noDescendantFactor_eq_update_prod
    {A W Y : Type*} {n : ℕ}
    (T : A → W → Fin n → AugmentedState Y) (s : AugmentedState Y → ℝ)
    (xs : List A) (w : W) :
    functionListProduct (xs.map fun x => noDescendantFactor T s x) w =
      ((sharedPopulationUpdate T xs w).map fun y => 1 - s y).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      calc
        functionListProduct ((x :: xs).map fun z => noDescendantFactor T s z) w =
            noDescendantFactor T s x w *
              functionListProduct (xs.map fun z => noDescendantFactor T s z) w := by
          simp
        _ = noDescendantFactor T s x w *
              ((sharedPopulationUpdate T xs w).map fun y => 1 - s y).prod := by
          rw [ih]
        _ = ((sharedPopulationUpdate T (x :: xs) w).map fun y => 1 - s y).prod := by
          simp [sharedPopulationUpdate, noDescendantFactor, List.prod_ofFn]

theorem populationPotential_sharedPopulationUpdate
    {A W Y : Type*} {n : ℕ}
    (T : A → W → Fin n → AugmentedState Y) (s : AugmentedState Y → ℝ)
    (xs : List A) (w : W) :
    populationPotential s (sharedPopulationUpdate T xs w) =
      1 - functionListProduct (xs.map fun x => noDescendantFactor T s x) w := by
  rw [populationPotential, slotSurvival_eq_one_sub_prod]
  simp only [List.map_map, Function.comp_def]
  congr 1
  exact (functionListProduct_noDescendantFactor_eq_update_prod T s xs w).symm

theorem populationPotential_eq_one_sub_prod
    {X : Type*} (s : X → ℝ) (xs : List X) :
    populationPotential s xs = 1 - (xs.map fun x => 1 - s x).prod := by
  rw [populationPotential, slotSurvival_eq_one_sub_prod]
  simp only [List.map_map, Function.comp_def]

@[simp] theorem populationPotential_nil {X : Type*} (s : X → ℝ) :
    populationPotential s [] = 0 := by
  simp [populationPotential, slotSurvival]

theorem populationPotential_le_sum
    {X : Type*} {s : X → ℝ} (hs0 : ∀ x, 0 ≤ s x)
    (hs1 : ∀ x, s x ≤ 1) (xs : List X) :
    populationPotential s xs ≤ (xs.map s).sum := by
  exact slotSurvival_le_mass (fun u hu => by
    simp only [List.mem_map] at hu
    obtain ⟨x, _hx, rfl⟩ := hu
    exact ⟨hs0 x, hs1 x⟩)

theorem shared_oneStep_populationPotential_le
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Y]
    [Preorder W] [Preorder (AugmentedState Y)] {n : ℕ}
    (ν : Measure W) [IsProbabilityMeasure ν] (hassoc : PositivelyAssociated ν)
    (Q : Kernel A (Fin n → AugmentedState Y)) [IsMarkovKernel Q]
    (T : A → W → Fin n → AugmentedState Y)
    {s : AugmentedState Y → ℝ} (hs : Measurable s)
    (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1) (hsMono : Monotone s)
    (hTMeas : ∀ x i, Measurable fun w => T x w i)
    (hDestructive : ∀ x i, Antitone fun w => T x w i)
    (hLaw : ∀ x, Measure.map (fun w i => T x w i) ν = Q x)
    (xs : List A) :
    1 - ∫ w, functionListProduct (xs.map fun x => noDescendantFactor T s x) w ∂ν ≤
      populationPotential (bellmanStep Q s) xs := by
  let fs : List (W → ℝ) := xs.map fun x => noDescendantFactor T s x
  have hfs : ∀ f ∈ fs, AssociatedFunction f := by
    intro f hf
    simp only [fs, List.mem_map] at hf
    obtain ⟨x, _hx, rfl⟩ := hf
    exact associatedFunction_noDescendantFactor T s hs hs0 hs1 hsMono
      hTMeas hDestructive x
  have hassocBound := one_sub_integral_functionListProduct_le ν hassoc fs hfs
  have hIntegrals :
      (fs.map fun f => ∫ w, f w ∂ν) =
        xs.map fun x => 1 - bellmanStep Q s x := by
    simp only [fs, List.map_map]
    apply List.map_congr_left
    intro x hx
    exact integral_noDescendantFactor_eq_one_sub_bellmanStep ν Q T hs hs0 hs1
      hTMeas hLaw x
  rw [hIntegrals] at hassocBound
  rw [populationPotential_eq_one_sub_prod]
  exact hassocBound

theorem integral_populationPotential_sharedPopulationUpdate_le
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Y]
    [Preorder W] [Preorder (AugmentedState Y)] {n : ℕ}
    (ν : Measure W) [IsProbabilityMeasure ν] (hassoc : PositivelyAssociated ν)
    (Q : Kernel A (Fin n → AugmentedState Y)) [IsMarkovKernel Q]
    (T : A → W → Fin n → AugmentedState Y)
    {s : AugmentedState Y → ℝ} (hs : Measurable s)
    (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1) (hsMono : Monotone s)
    (hTMeas : ∀ x i, Measurable fun w => T x w i)
    (hDestructive : ∀ x i, Antitone fun w => T x w i)
    (hLaw : ∀ x, Measure.map (fun w i => T x w i) ν = Q x)
    (xs : List A) :
    ∫ w, populationPotential s (sharedPopulationUpdate T xs w) ∂ν ≤
      populationPotential (bellmanStep Q s) xs := by
  let fs : List (W → ℝ) := xs.map fun x => noDescendantFactor T s x
  have hfs : ∀ f ∈ fs, AssociatedFunction f := by
    intro f hf
    simp only [fs, List.mem_map] at hf
    obtain ⟨x, _hx, rfl⟩ := hf
    exact associatedFunction_noDescendantFactor T s hs hs0 hs1 hsMono
      hTMeas hDestructive x
  have hprodInt : Integrable (functionListProduct fs) ν :=
    (associatedFunction_functionListProduct fs hfs).integrable
  have hbase := shared_oneStep_populationPotential_le ν hassoc Q T hs hs0 hs1
    hsMono hTMeas hDestructive hLaw xs
  calc
    (∫ w, populationPotential s (sharedPopulationUpdate T xs w) ∂ν) =
        ∫ w, (1 - functionListProduct fs w) ∂ν := by
      apply integral_congr_ae
      filter_upwards with w
      exact populationPotential_sharedPopulationUpdate T s xs w
    _ = 1 - ∫ w, functionListProduct fs w ∂ν := by
      rw [integral_sub (integrable_const 1) hprodInt, integral_const, probReal_univ]
      norm_num
    _ ≤ populationPotential (bellmanStep Q s) xs := hbase

theorem monotone_liveIndicator_of_cemetery_le
    {X : Type*} [PartialOrder (AugmentedState X)]
    (hLeast : ∀ z : AugmentedState X, cemetery ≤ z) :
    Monotone (liveIndicator (X := X)) := by
  intro a b hab
  cases a with
  | inl x =>
      cases b with
      | inl y => simp
      | inr u =>
          cases u
          have hEq : (Sum.inl x : AugmentedState X) = cemetery :=
            le_antisymm hab (hLeast (Sum.inl x))
          cases hEq
  | inr u =>
      cases u
      cases b with
      | inl y =>
          change (0 : ℝ) ≤ 1
          norm_num
      | inr v =>
          cases v
          change (0 : ℝ) ≤ 0
          exact le_rfl

theorem monotone_bellmanStep_of_realization
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Y]
    [Preorder A] [Preorder W] [Preorder (AugmentedState Y)] {n : ℕ}
    (ν : Measure W) [IsProbabilityMeasure ν]
    (Q : Kernel A (Fin n → AugmentedState Y)) [IsMarkovKernel Q]
    (T : A → W → Fin n → AugmentedState Y)
    {s : AugmentedState Y → ℝ} (hs : Measurable s)
    (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1) (hsMono : Monotone s)
    (hTMeas : ∀ x i, Measurable fun w => T x w i)
    (hStateMono : ∀ w i, Monotone fun x => T x w i)
    (hDestructive : ∀ x i, Antitone fun w => T x w i)
    (hLaw : ∀ x, Measure.map (fun w i => T x w i) ν = Q x) :
    Monotone (bellmanStep Q s) := by
  intro x x' hxx'
  have hfx := associatedFunction_noDescendantFactor T s hs hs0 hs1 hsMono
    hTMeas hDestructive x
  have hfx' := associatedFunction_noDescendantFactor T s hs hs0 hs1 hsMono
    hTMeas hDestructive x'
  have hpoint : ∀ w, noDescendantFactor T s x' w ≤ noDescendantFactor T s x w := by
    intro w
    unfold noDescendantFactor
    apply Finset.prod_le_prod
    · intro i _hi
      exact sub_nonneg.mpr (hs1 _)
    · intro i _hi
      have hstate := hStateMono w i hxx'
      have hsOrder := hsMono hstate
      linarith
  have hint :
      (∫ w, noDescendantFactor T s x' w ∂ν) ≤
        ∫ w, noDescendantFactor T s x w ∂ν :=
    integral_mono hfx'.integrable hfx.integrable hpoint
  have hx := integral_noDescendantFactor_eq_one_sub_bellmanStep
    ν Q T hs hs0 hs1 hTMeas hLaw x
  have hx' := integral_noDescendantFactor_eq_one_sub_bellmanStep
    ν Q T hs hs0 hs1 hTMeas hLaw x'
  linarith

theorem monotone_bellmanFrom_of_sharedRealization
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    [∀ j, PartialOrder (AugmentedState (X j))] [∀ j, Preorder (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (ν : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (ν j)]
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hLeast : ∀ j z, cemetery ≤ (z : AugmentedState (X j)))
    (hTMeas : ∀ j x i, Measurable fun w => T j x w i)
    (hStateMono : ∀ j w i, Monotone fun x => T j x w i)
    (hDestructive : ∀ j x i, Antitone fun w => T j x w i)
    (hLaw : ∀ j x, Measure.map (fun w i => T j x w i) (ν j) = Q j x) :
    ∀ j steps, Monotone (bellmanFrom n Q j steps) := by
  intro j steps
  induction steps generalizing j with
  | zero =>
      exact monotone_liveIndicator_of_cemetery_le (hLeast j)
  | succ steps ih =>
      rw [bellmanFrom_succ]
      exact monotone_bellmanStep_of_realization (ν j) (Q j) (T j)
        (measurable_bellmanFrom n Q (j + 1) steps)
        (fun y => (bellmanFrom_mem_Icc n Q (j + 1) steps y).1)
        (fun y => (bellmanFrom_mem_Icc n Q (j + 1) steps y).2)
        (ih (j + 1)) (hTMeas j) (hStateMono j) (hDestructive j) (hLaw j)

theorem monotone_bellmanTo_of_sharedRealization
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    [∀ j, PartialOrder (AugmentedState (X j))] [∀ j, Preorder (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (ν : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (ν j)]
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hLeast : ∀ j z, cemetery ≤ (z : AugmentedState (X j)))
    (hTMeas : ∀ j x i, Measurable fun w => T j x w i)
    (hStateMono : ∀ j w i, Monotone fun x => T j x w i)
    (hDestructive : ∀ j x i, Antitone fun w => T j x w i)
    (hLaw : ∀ j x, Measure.map (fun w i => T j x w i) (ν j) = Q j x)
    (j N : ℕ) : Monotone (bellmanTo n Q j N) := by
  exact monotone_bellmanFrom_of_sharedRealization n Q ν T hLeast hTMeas
    hStateMono hDestructive hLaw j (N - j)

theorem shared_bellman_update_expectation_le
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    [∀ j, PartialOrder (AugmentedState (X j))] [∀ j, Preorder (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (ν : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (ν j)]
    (hassoc : ∀ j, PositivelyAssociated (ν j))
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hLeast : ∀ j z, cemetery ≤ (z : AugmentedState (X j)))
    (hTMeas : ∀ j x i, Measurable fun w => T j x w i)
    (hStateMono : ∀ j w i, Monotone fun x => T j x w i)
    (hDestructive : ∀ j x i, Antitone fun w => T j x w i)
    (hLaw : ∀ j x, Measure.map (fun w i => T j x w i) (ν j) = Q j x)
    {j N : ℕ} (hjN : j < N) (xs : List (AugmentedState (X j))) :
    ∫ w, populationPotential (bellmanTo n Q (j + 1) N)
        (sharedPopulationUpdate (T j) xs w) ∂ν j ≤
      populationPotential (bellmanTo n Q j N) xs := by
  have hmono := monotone_bellmanTo_of_sharedRealization n Q ν T hLeast hTMeas
    hStateMono hDestructive hLaw (j + 1) N
  have hstep := integral_populationPotential_sharedPopulationUpdate_le
    (ν j) (hassoc j) (Q j) (T j)
    (measurable_bellmanTo n Q (j + 1) N)
    (fun y => (bellmanTo_mem_Icc n Q (j + 1) N y).1)
    (fun y => (bellmanTo_mem_Icc n Q (j + 1) N y).2)
    hmono (hTMeas j) (hDestructive j) (hLaw j) xs
  rw [bellmanTo_step n Q hjN]
  exact hstep

end Shepp.Section4
end SheppFlattenedModule037

section SheppFlattenedModule038
open scoped BigOperators ENNReal
open MeasureTheory Set

namespace Shepp.Section4

abbrev FinitePopulation (X : Type*) := Σ q : ℕ, Fin q → X

theorem measurable_sigmaMk_branch
    {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)] (i : ι) :
    Measurable (Sigma.mk i : β i → Σ i, β i) := by
  apply Measurable.of_comap_le
  apply MeasurableSpace.comap_le_iff_le_map.mpr
  exact iInf_le (fun j => MeasurableSpace.map (Sigma.mk j) inferInstance) i

theorem measurable_sigma_elim_iff
    {ι : Type*} {β : ι → Type*} {γ : Type*}
    [∀ i, MeasurableSpace (β i)] [MeasurableSpace γ]
    (f : (i : ι) → β i → γ) :
    Measurable (fun z : Σ i, β i => f z.1 z.2) ↔
      ∀ i, Measurable (f i) := by
  constructor
  · intro hf i
    exact hf.comp (measurable_sigmaMk_branch i)
  · intro hf
    apply Measurable.of_comap_le
    change MeasurableSpace.comap (fun z : Σ i, β i => f z.1 z.2) inferInstance ≤
      ⨅ i, MeasurableSpace.map (Sigma.mk i) inferInstance
    apply le_iInf
    intro i
    have hi :
        MeasurableSpace.comap (Sigma.mk i)
            (MeasurableSpace.comap (fun z : Σ i, β i => f z.1 z.2)
              (inferInstance : MeasurableSpace γ)) ≤
          (inferInstance : MeasurableSpace (β i)) := by
      simpa only [MeasurableSpace.comap_comp, Function.comp_def] using (hf i).comap_le
    exact MeasurableSpace.comap_le_iff_le_map.mp hi

theorem measurable_sigma_elim
    {ι : Type*} {β : ι → Type*} {γ : Type*}
    [∀ i, MeasurableSpace (β i)] [MeasurableSpace γ]
    (f : (i : ι) → β i → γ) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun z : Σ i, β i => f z.1 z.2) :=
  (measurable_sigma_elim_iff f).2 hf

def finitePopulationPotential {X : Type*}
    (s : X → ℝ) (ξ : FinitePopulation X) : ℝ :=
  1 - ∏ i, (1 - s (ξ.2 i))

theorem finitePopulationPotential_eq_populationPotential_ofFn
    {X : Type*} (s : X → ℝ) (q : ℕ) (xs : Fin q → X) :
    finitePopulationPotential s ⟨q, xs⟩ = populationPotential s (List.ofFn xs) := by
  rw [finitePopulationPotential, populationPotential_eq_one_sub_prod]
  simp [List.prod_ofFn]

theorem measurable_finitePopulationPotential
    {X : Type*} [MeasurableSpace X]
    {s : X → ℝ} (hs : Measurable s) :
    Measurable (finitePopulationPotential s) := by
  exact measurable_sigma_elim
    (fun q (xs : Fin q → X) => 1 - ∏ i, (1 - s (xs i))) fun q => by
      fun_prop

theorem finitePopulationPotential_nonneg
    {X : Type*} {s : X → ℝ}
    (hs0 : ∀ x, 0 ≤ s x) (hs1 : ∀ x, s x ≤ 1)
    (ξ : FinitePopulation X) :
    0 ≤ finitePopulationPotential s ξ := by
  obtain ⟨q, xs⟩ := ξ
  rw [finitePopulationPotential, ← slotSurvival_slotParameterList]
  exact slotSurvival_nonneg (valid_slotParameterList hs0 hs1 xs)

theorem finitePopulationPotential_le_one
    {X : Type*} {s : X → ℝ}
    (hs0 : ∀ x, 0 ≤ s x) (hs1 : ∀ x, s x ≤ 1)
    (ξ : FinitePopulation X) :
    finitePopulationPotential s ξ ≤ 1 := by
  obtain ⟨q, xs⟩ := ξ
  rw [finitePopulationPotential, ← slotSurvival_slotParameterList]
  exact slotSurvival_le_one (valid_slotParameterList hs0 hs1 xs)

theorem finitePopulationPotential_liveIndicator_eq_one_of_live
    {X : Type*} {q : ℕ} {xs : Fin q → AugmentedState X}
    {i : Fin q} {x : X} (hix : xs i = Sum.inl x) :
    finitePopulationPotential liveIndicator ⟨q, xs⟩ = 1 := by
  rw [finitePopulationPotential]
  have hzero : ∏ k, (1 - liveIndicator (xs k)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hix]
    simp
  rw [hzero]
  norm_num

theorem finitePopulationPotential_liveIndicator_eq_zero_of_all_cemetery
    {X : Type*} {q : ℕ} {xs : Fin q → AugmentedState X}
    (hcem : ∀ i, xs i = cemetery) :
    finitePopulationPotential liveIndicator ⟨q, xs⟩ = 0 := by
  rw [finitePopulationPotential]
  simp_rw [hcem, liveIndicator_cemetery]
  simp

def livePopulationEvent {X : Type*} : Set (FinitePopulation (AugmentedState X)) :=
  {ξ | ∃ i, ∃ x : X, ξ.2 i = Sum.inl x}

theorem mem_livePopulationEvent_iff
    {X : Type*} (ξ : FinitePopulation (AugmentedState X)) :
    ξ ∈ livePopulationEvent ↔ ∃ i, ∃ x : X, ξ.2 i = Sum.inl x := Iff.rfl

theorem finitePopulationPotential_liveIndicator_eq_one_iff
    {X : Type*} (ξ : FinitePopulation (AugmentedState X)) :
    finitePopulationPotential liveIndicator ξ = 1 ↔ ξ ∈ livePopulationEvent := by
  obtain ⟨q, xs⟩ := ξ
  constructor
  · intro hone
    by_contra hnot
    have hcem : ∀ i, xs i = cemetery := by
      intro i
      cases hxi : xs i with
      | inl x =>
          exfalso
          exact hnot ⟨i, x, hxi⟩
      | inr u =>
          cases u
          rfl
    have hzero := finitePopulationPotential_liveIndicator_eq_zero_of_all_cemetery hcem
    rw [hzero] at hone
    norm_num at hone
  · rintro ⟨i, x, hix⟩
    exact finitePopulationPotential_liveIndicator_eq_one_of_live hix

theorem finitePopulationPotential_liveIndicator_eq_zero_of_not_mem
    {X : Type*} {ξ : FinitePopulation (AugmentedState X)}
    (hξ : ξ ∉ livePopulationEvent) :
    finitePopulationPotential liveIndicator ξ = 0 := by
  obtain ⟨q, xs⟩ := ξ
  apply finitePopulationPotential_liveIndicator_eq_zero_of_all_cemetery
  intro i
  cases hxi' : xs i with
  | inl x =>
      exfalso
      exact hξ ⟨i, x, hxi'⟩
  | inr u =>
      cases u
      rfl

theorem measurableSet_livePopulationEvent
    {X : Type*} [MeasurableSpace X] :
    MeasurableSet (livePopulationEvent (X := X)) := by
  rw [show livePopulationEvent (X := X) =
      {ξ | finitePopulationPotential liveIndicator ξ = 1} by
    ext ξ
    exact (finitePopulationPotential_liveIndicator_eq_one_iff ξ).symm]
  exact measurableSet_eq_fun
    (measurable_finitePopulationPotential measurable_liveIndicator) measurable_const

theorem ofReal_finitePopulationPotential_liveIndicator_eq_indicator
    {X : Type*} (ξ : FinitePopulation (AugmentedState X)) :
    ENNReal.ofReal (finitePopulationPotential liveIndicator ξ) =
      (livePopulationEvent (X := X)).indicator (fun _ => (1 : ℝ≥0∞)) ξ := by
  by_cases hξ : ξ ∈ livePopulationEvent
  · rw [(finitePopulationPotential_liveIndicator_eq_one_iff ξ).2 hξ]
    simp [hξ]
  · rw [finitePopulationPotential_liveIndicator_eq_zero_of_not_mem hξ]
    simp [hξ]

theorem lintegral_finitePopulationPotential_liveIndicator
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (FinitePopulation (AugmentedState X))) :
    (∫⁻ ξ, ENNReal.ofReal (finitePopulationPotential liveIndicator ξ) ∂μ) =
      μ livePopulationEvent := by
  rw [show (fun ξ => ENNReal.ofReal (finitePopulationPotential liveIndicator ξ)) =
      (livePopulationEvent (X := X)).indicator (fun _ => (1 : ℝ≥0∞)) by
    funext ξ
    exact ofReal_finitePopulationPotential_liveIndicator_eq_indicator ξ]
  exact lintegral_indicator_one measurableSet_livePopulationEvent

end Shepp.Section4
end SheppFlattenedModule038

section SheppFlattenedModule039
open scoped BigOperators ENNReal ProbabilityTheory
open MeasureTheory Set

namespace Shepp.Section4

open ProbabilityTheory

def sharedFinitePopulationUpdate
    {A W Y : Type*} {n : ℕ}
    (T : A → W → Fin n → Y) (ξ : FinitePopulation A) (w : W) :
    FinitePopulation Y :=
  match ξ with
  | ⟨q, xs⟩ =>
      ⟨q * n, fun k =>
        let ij := finProdFinEquiv.symm k
        T (xs ij.1) w ij.2⟩

theorem finitePopulationPotential_sharedUpdate_eq_list
    {A W Y : Type*} {n q : ℕ}
    (T : A → W → Fin n → AugmentedState Y)
    (s : AugmentedState Y → ℝ) (xs : Fin q → A) (w : W) :
    finitePopulationPotential s (sharedFinitePopulationUpdate T ⟨q, xs⟩ w) =
      populationPotential s (sharedPopulationUpdate T (List.ofFn xs) w) := by
  rw [finitePopulationPotential, populationPotential_eq_one_sub_prod]
  congr 1
  rw [← functionListProduct_noDescendantFactor_eq_update_prod T s (List.ofFn xs) w]
  simp only [functionListProduct, List.map_ofFn, List.prod_ofFn]
  change
    (∏ k : Fin (q * n),
      (1 - s (T (xs (finProdFinEquiv.symm k).1) w (finProdFinEquiv.symm k).2))) =
      ∏ i : Fin q, ∏ l : Fin n, (1 - s (T (xs i) w l))
  calc
    (∏ k : Fin (q * n),
        (1 - s (T (xs (finProdFinEquiv.symm k).1) w (finProdFinEquiv.symm k).2))) =
        ∏ ij : Fin q × Fin n, (1 - s (T (xs ij.1) w ij.2)) := by
      apply Fintype.prod_equiv finProdFinEquiv.symm
      intro k
      rfl
    _ = ∏ i : Fin q, ∏ l : Fin n, (1 - s (T (xs i) w l)) := by
      simpa using
        (Finset.prod_product (Finset.univ : Finset (Fin q))
          (Finset.univ : Finset (Fin n))
          (fun ij : Fin q × Fin n => 1 - s (T (xs ij.1) w ij.2)))

theorem measurable_sharedFinitePopulationUpdate_branch
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Y]
    {n : ℕ} (T : A → W → Fin n → Y)
    (hTJoint : ∀ i, Measurable fun p : A × W => T p.1 p.2 i)
    (q : ℕ) :
    Measurable fun p : (Fin q → A) × W =>
      sharedFinitePopulationUpdate T ⟨q, p.1⟩ p.2 := by
  apply (measurable_sigmaMk_branch (q * n)).comp
  apply measurable_pi_lambda
  intro k
  let ij : Fin q × Fin n := finProdFinEquiv.symm k
  change Measurable fun p : (Fin q → A) × W => T (p.1 ij.1) p.2 ij.2
  have hpair : Measurable fun p : (Fin q → A) × W => (p.1 ij.1, p.2) :=
    ((measurable_pi_apply ij.1).comp measurable_fst).prodMk measurable_snd
  exact (hTJoint ij.2).comp hpair

noncomputable def branchInnovationKernel
    {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    (ν : Measure W) : Kernel A (A × W) :=
  Kernel.compProd (Kernel.id : Kernel A A) (Kernel.const (A × A) ν)

instance branchInnovationKernel.instIsMarkovKernel
    {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    (ν : Measure W) [IsProbabilityMeasure ν] :
    IsMarkovKernel (branchInnovationKernel (A := A) ν) := by
  unfold branchInnovationKernel
  infer_instance

theorem branchInnovationKernel_apply
    {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    (ν : Measure W) [SFinite ν] (a : A) :
    branchInnovationKernel ν a = Measure.map (fun w => (a, w)) ν := by
  ext s hs
  rw [branchInnovationKernel, Kernel.compProd_apply hs, Kernel.id_apply]
  rw [lintegral_dirac']
  · rw [Kernel.const_apply]
    exact (Measure.map_apply (measurable_const.prodMk measurable_id) hs).symm
  · exact Kernel.measurable_kernel_prodMk_left' hs a

noncomputable def sharedPopulationBranchKernel
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Y]
    {n : ℕ} (ν : Measure W)
    (T : A → W → Fin n → Y)
    (_hTJoint : ∀ i, Measurable fun p : A × W => T p.1 p.2 i)
    (q : ℕ) : Kernel (Fin q → A) (FinitePopulation Y) :=
  (branchInnovationKernel (A := Fin q → A) ν).map
    (fun p => sharedFinitePopulationUpdate T ⟨q, p.1⟩ p.2)

instance sharedPopulationBranchKernel.instIsMarkovKernel
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Y]
    {n : ℕ} (ν : Measure W) [IsProbabilityMeasure ν]
    (T : A → W → Fin n → Y)
    (hTJoint : ∀ i, Measurable fun p : A × W => T p.1 p.2 i)
    (q : ℕ) :
    IsMarkovKernel (sharedPopulationBranchKernel ν T hTJoint q) := by
  unfold sharedPopulationBranchKernel
  exact Kernel.IsMarkovKernel.map _
    (measurable_sharedFinitePopulationUpdate_branch T hTJoint q)

theorem sharedPopulationBranchKernel_apply
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Y]
    {n : ℕ} (ν : Measure W) [SFinite ν]
    (T : A → W → Fin n → Y)
    (hTJoint : ∀ i, Measurable fun p : A × W => T p.1 p.2 i)
    (q : ℕ) (xs : Fin q → A) :
    sharedPopulationBranchKernel ν T hTJoint q xs =
      Measure.map (fun w => sharedFinitePopulationUpdate T ⟨q, xs⟩ w) ν := by
  rw [sharedPopulationBranchKernel,
    Kernel.map_apply _ (measurable_sharedFinitePopulationUpdate_branch T hTJoint q),
    branchInnovationKernel_apply]
  rw [Measure.map_map]
  · rfl
  · exact measurable_sharedFinitePopulationUpdate_branch T hTJoint q
  · exact measurable_const.prodMk measurable_id

noncomputable def sharedPopulationKernel
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Y]
    {n : ℕ} (ν : Measure W)
    (T : A → W → Fin n → Y)
    (hTJoint : ∀ i, Measurable fun p : A × W => T p.1 p.2 i) :
    Kernel (FinitePopulation A) (FinitePopulation Y) where
  toFun ξ := match ξ with
    | ⟨q, xs⟩ => sharedPopulationBranchKernel ν T hTJoint q xs
  measurable' := measurable_sigma_elim
    (fun q xs => sharedPopulationBranchKernel ν T hTJoint q xs)
    (fun q => (sharedPopulationBranchKernel ν T hTJoint q).measurable)

instance sharedPopulationKernel.instIsMarkovKernel
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Y]
    {n : ℕ} (ν : Measure W) [IsProbabilityMeasure ν]
    (T : A → W → Fin n → Y)
    (hTJoint : ∀ i, Measurable fun p : A × W => T p.1 p.2 i) :
    IsMarkovKernel (sharedPopulationKernel ν T hTJoint) :=
  ⟨fun ξ => by
    obtain ⟨q, xs⟩ := ξ
    change IsProbabilityMeasure (sharedPopulationBranchKernel ν T hTJoint q xs)
    infer_instance⟩

theorem integral_finitePopulationPotential_sharedKernel_le
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Y]
    [Preorder W] [Preorder (AugmentedState Y)] {n : ℕ}
    (ν : Measure W) [IsProbabilityMeasure ν] (hassoc : PositivelyAssociated ν)
    (Q : Kernel A (Fin n → AugmentedState Y)) [IsMarkovKernel Q]
    (T : A → W → Fin n → AugmentedState Y)
    (hTJoint : ∀ i, Measurable fun p : A × W => T p.1 p.2 i)
    {s : AugmentedState Y → ℝ} (hs : Measurable s)
    (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1) (hsMono : Monotone s)
    (hDestructive : ∀ x i, Antitone fun w => T x w i)
    (hLaw : ∀ x, Measure.map (fun w i => T x w i) ν = Q x)
    (ξ : FinitePopulation A) :
    ∫ η, finitePopulationPotential s η ∂sharedPopulationKernel ν T hTJoint ξ ≤
      finitePopulationPotential (bellmanStep Q s) ξ := by
  obtain ⟨q, xs⟩ := ξ
  let hTMeas : ∀ x i, Measurable fun w => T x w i := fun x i =>
    (hTJoint i).comp (measurable_const.prodMk measurable_id)
  have hUpdate : Measurable fun w => sharedFinitePopulationUpdate T ⟨q, xs⟩ w :=
    (measurable_sharedFinitePopulationUpdate_branch T hTJoint q).comp
      (measurable_const.prodMk measurable_id)
  change (∫ η, finitePopulationPotential s η
      ∂sharedPopulationBranchKernel ν T hTJoint q xs) ≤ _
  rw [sharedPopulationBranchKernel_apply]
  rw [integral_map hUpdate.aemeasurable
    (measurable_finitePopulationPotential hs).aestronglyMeasurable]
  have hlist := integral_populationPotential_sharedPopulationUpdate_le
    ν hassoc Q T hs hs0 hs1 hsMono hTMeas hDestructive hLaw (List.ofFn xs)
  calc
    (∫ w, finitePopulationPotential s
        (sharedFinitePopulationUpdate T ⟨q, xs⟩ w) ∂ν) =
        ∫ w, populationPotential s
          (sharedPopulationUpdate T (List.ofFn xs) w) ∂ν := by
      apply integral_congr_ae
      filter_upwards with w
      exact finitePopulationPotential_sharedUpdate_eq_list T s xs w
    _ ≤ populationPotential (bellmanStep Q s) (List.ofFn xs) := hlist
    _ = finitePopulationPotential (bellmanStep Q s) ⟨q, xs⟩ :=
      (finitePopulationPotential_eq_populationPotential_ofFn
        (bellmanStep Q s) q xs).symm

theorem lintegral_finitePopulationPotential_sharedKernel_le
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Y]
    [Preorder W] [Preorder (AugmentedState Y)] {n : ℕ}
    (ν : Measure W) [IsProbabilityMeasure ν] (hassoc : PositivelyAssociated ν)
    (Q : Kernel A (Fin n → AugmentedState Y)) [IsMarkovKernel Q]
    (T : A → W → Fin n → AugmentedState Y)
    (hTJoint : ∀ i, Measurable fun p : A × W => T p.1 p.2 i)
    {s : AugmentedState Y → ℝ} (hs : Measurable s)
    (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1) (hsMono : Monotone s)
    (hDestructive : ∀ x i, Antitone fun w => T x w i)
    (hLaw : ∀ x, Measure.map (fun w i => T x w i) ν = Q x)
    (ξ : FinitePopulation A) :
    ∫⁻ η, ENNReal.ofReal (finitePopulationPotential s η)
        ∂sharedPopulationKernel ν T hTJoint ξ ≤
      ENNReal.ofReal (finitePopulationPotential (bellmanStep Q s) ξ) := by
  let K := sharedPopulationKernel ν T hTJoint
  have hMeas : Measurable (finitePopulationPotential s) :=
    measurable_finitePopulationPotential hs
  have hInt : Integrable (finitePopulationPotential s) (K ξ) := by
    apply Integrable.of_bound hMeas.aestronglyMeasurable 1
    filter_upwards with η
    rw [Real.norm_of_nonneg (finitePopulationPotential_nonneg hs0 hs1 η)]
    exact finitePopulationPotential_le_one hs0 hs1 η
  have hreal := integral_finitePopulationPotential_sharedKernel_le
    ν hassoc Q T hTJoint hs hs0 hs1 hsMono hDestructive hLaw ξ
  change (∫⁻ η, ENNReal.ofReal (finitePopulationPotential s η) ∂K ξ) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (ae_of_all _ fun η => finitePopulationPotential_nonneg hs0 hs1 η)]
  exact ENNReal.ofReal_le_ofReal hreal

end Shepp.Section4
end SheppFlattenedModule039

section SheppFlattenedModule040
open scoped BigOperators ENNReal ProbabilityTheory
open MeasureTheory Set

namespace Shepp.Section4

open ProbabilityTheory

def generationAfter : ℕ → ℕ → ℕ
  | j, 0 => j
  | j, steps + 1 => generationAfter (j + 1) steps

@[simp] theorem generationAfter_zero (j : ℕ) : generationAfter j 0 = j := rfl

@[simp] theorem generationAfter_succ (j steps : ℕ) :
    generationAfter j (steps + 1) = generationAfter (j + 1) steps := rfl

theorem generationAfter_eq_add (j steps : ℕ) :
    generationAfter j steps = j + steps := by
  induction steps generalizing j with
  | zero => simp
  | succ steps ih =>
      rw [generationAfter_succ, ih]
      omega

noncomputable def sharedEvolutionKernel
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    (n : ℕ → ℕ)
    (ν : (j : ℕ) → Measure (W j))
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i) :
    (j steps : ℕ) → Kernel (FinitePopulation (AugmentedState (X j)))
      (FinitePopulation (AugmentedState (X (generationAfter j steps))))
  | _j, 0 => Kernel.id
  | j, steps + 1 =>
      Kernel.comp (sharedEvolutionKernel n ν T hTJoint (j + 1) steps)
        (sharedPopulationKernel (ν j) (T j) (hTJoint j))

@[simp] theorem sharedEvolutionKernel_zero
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    (n : ℕ → ℕ) (ν : (j : ℕ) → Measure (W j))
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i) (j : ℕ) :
    sharedEvolutionKernel n ν T hTJoint j 0 = Kernel.id := rfl

theorem sharedEvolutionKernel_succ
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    (n : ℕ → ℕ) (ν : (j : ℕ) → Measure (W j))
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i) (j steps : ℕ) :
    sharedEvolutionKernel n ν T hTJoint j (steps + 1) =
      Kernel.comp (sharedEvolutionKernel n ν T hTJoint (j + 1) steps)
        (sharedPopulationKernel (ν j) (T j) (hTJoint j)) := by
  rfl

instance sharedEvolutionKernel.instIsMarkovKernel
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    (n : ℕ → ℕ) (ν : (j : ℕ) → Measure (W j))
    [∀ j, IsProbabilityMeasure (ν j)]
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i) (j steps : ℕ) :
    IsMarkovKernel (sharedEvolutionKernel n ν T hTJoint j steps) := by
  induction steps generalizing j with
  | zero =>
      rw [sharedEvolutionKernel_zero]
      exact (inferInstance : IsMarkovKernel
        (Kernel.id : Kernel (FinitePopulation (AugmentedState (X j)))
          (FinitePopulation (AugmentedState (X j)))))
  | succ steps ih =>
      rw [sharedEvolutionKernel_succ]
      letI hFuture : IsMarkovKernel
          (sharedEvolutionKernel n ν T hTJoint (j + 1) steps) :=
        ih (j + 1)
      letI hStep : IsMarkovKernel
          (sharedPopulationKernel (ν j) (T j) (hTJoint j)) := inferInstance
      exact Kernel.IsMarkovKernel.comp
        (sharedEvolutionKernel n ν T hTJoint (j + 1) steps)
        (sharedPopulationKernel (ν j) (T j) (hTJoint j))

theorem sharedEvolution_terminalPotential_le_bellman
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    [∀ j, PartialOrder (AugmentedState (X j))] [∀ j, Preorder (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (ν : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (ν j)]
    (hassoc : ∀ j, PositivelyAssociated (ν j))
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (hLeast : ∀ j z, cemetery ≤ (z : AugmentedState (X j)))
    (hStateMono : ∀ j w i, Monotone fun x => T j x w i)
    (hDestructive : ∀ j x i, Antitone fun w => T j x w i)
    (hLaw : ∀ j x, Measure.map (fun w i => T j x w i) (ν j) = Q j x) :
    ∀ j steps (ξ : FinitePopulation (AugmentedState (X j))),
      (∫⁻ η, ENNReal.ofReal
          (finitePopulationPotential
            (liveIndicator (X := X (generationAfter j steps))) η)
        ∂sharedEvolutionKernel n ν T hTJoint j steps ξ) ≤
        ENNReal.ofReal (finitePopulationPotential (bellmanFrom n Q j steps) ξ) := by
  let hTMeas : ∀ j x i, Measurable fun w => T j x w i := fun j x i =>
    (hTJoint j i).comp (measurable_const.prodMk measurable_id)
  intro j steps
  induction steps generalizing j with
  | zero =>
      intro ξ
      have hterminal : Measurable fun η : FinitePopulation (AugmentedState (X j)) =>
          ENNReal.ofReal (finitePopulationPotential liveIndicator η) :=
        (measurable_finitePopulationPotential measurable_liveIndicator).ennreal_ofReal
      change (∫⁻ η : FinitePopulation (AugmentedState (X j)),
          ENNReal.ofReal (finitePopulationPotential liveIndicator η)
          ∂(Kernel.id : Kernel (FinitePopulation (AugmentedState (X j)))
            (FinitePopulation (AugmentedState (X j)))) ξ) ≤
        ENNReal.ofReal (finitePopulationPotential liveIndicator ξ)
      rw [Kernel.lintegral_id' hterminal]
  | succ steps ih =>
      intro ξ
      let Kstep := sharedPopulationKernel (ν j) (T j) (hTJoint j)
      let Kfuture := sharedEvolutionKernel n ν T hTJoint (j + 1) steps
      let terminal : FinitePopulation
          (AugmentedState (X (generationAfter (j + 1) steps))) → ℝ≥0∞ :=
        fun η => ENNReal.ofReal
          (finitePopulationPotential
            (liveIndicator (X := X (generationAfter (j + 1) steps))) η)
      have hterminal : Measurable terminal :=
        (measurable_finitePopulationPotential measurable_liveIndicator).ennreal_ofReal
      simp only [generationAfter_succ]
      rw [sharedEvolutionKernel_succ]
      change (∫⁻ η, terminal η ∂Kernel.comp Kfuture Kstep ξ) ≤ _
      rw [Kernel.lintegral_comp _ _ _ hterminal]
      calc
        (∫⁻ ζ, ∫⁻ η, terminal η ∂Kfuture ζ ∂Kstep ξ) ≤
            ∫⁻ ζ, ENNReal.ofReal
              (finitePopulationPotential (bellmanFrom n Q (j + 1) steps) ζ)
              ∂Kstep ξ := by
          apply lintegral_mono
          intro ζ
          exact ih (j + 1) ζ
        _ ≤ ENNReal.ofReal
            (finitePopulationPotential
              (bellmanStep (Q j) (bellmanFrom n Q (j + 1) steps)) ξ) := by
          have hmono := monotone_bellmanFrom_of_sharedRealization
            n Q ν T hLeast hTMeas hStateMono hDestructive hLaw (j + 1) steps
          exact lintegral_finitePopulationPotential_sharedKernel_le
            (ν j) (hassoc j) (Q j) (T j) (hTJoint j)
            (measurable_bellmanFrom n Q (j + 1) steps)
            (fun y => (bellmanFrom_mem_Icc n Q (j + 1) steps y).1)
            (fun y => (bellmanFrom_mem_Icc n Q (j + 1) steps y).2)
            hmono (hDestructive j) (hLaw j) ξ
        _ = ENNReal.ofReal
            (finitePopulationPotential (bellmanFrom n Q j (steps + 1)) ξ) := rfl

noncomputable def sharedPopulationLaw
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    (n : ℕ → ℕ) (ν : (j : ℕ) → Measure (W j))
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (ρ0 : Measure (FinitePopulation (AugmentedState (X 0)))) (steps : ℕ) :
    Measure (FinitePopulation (AugmentedState (X (generationAfter 0 steps)))) :=
  ρ0.bind (sharedEvolutionKernel n ν T hTJoint 0 steps)

instance sharedPopulationLaw.instIsProbabilityMeasure
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    (n : ℕ → ℕ) (ν : (j : ℕ) → Measure (W j))
    [∀ j, IsProbabilityMeasure (ν j)]
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (ρ0 : Measure (FinitePopulation (AugmentedState (X 0))))
    [IsProbabilityMeasure ρ0] (steps : ℕ) :
    IsProbabilityMeasure (sharedPopulationLaw n ν T hTJoint ρ0 steps) := by
  unfold sharedPopulationLaw
  apply isProbabilityMeasure_bind (Kernel.aemeasurable _)
  filter_upwards with ξ
  infer_instance

theorem sharedPopulationLaw_terminalPotential_le_bellman
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    [∀ j, PartialOrder (AugmentedState (X j))] [∀ j, Preorder (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (ν : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (ν j)]
    (hassoc : ∀ j, PositivelyAssociated (ν j))
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (hLeast : ∀ j z, cemetery ≤ (z : AugmentedState (X j)))
    (hStateMono : ∀ j w i, Monotone fun x => T j x w i)
    (hDestructive : ∀ j x i, Antitone fun w => T j x w i)
    (hLaw : ∀ j x, Measure.map (fun w i => T j x w i) (ν j) = Q j x)
    (ρ0 : Measure (FinitePopulation (AugmentedState (X 0)))) (steps : ℕ) :
    (∫⁻ η, ENNReal.ofReal
        (finitePopulationPotential
          (liveIndicator (X := X (generationAfter 0 steps))) η)
      ∂sharedPopulationLaw n ν T hTJoint ρ0 steps) ≤
      ∫⁻ ξ, ENNReal.ofReal
        (finitePopulationPotential (bellmanFrom n Q 0 steps) ξ) ∂ρ0 := by
  let terminal : FinitePopulation
      (AugmentedState (X (generationAfter 0 steps))) → ℝ≥0∞ :=
    fun η => ENNReal.ofReal
      (finitePopulationPotential
        (liveIndicator (X := X (generationAfter 0 steps))) η)
  have hterminal : Measurable terminal :=
    (measurable_finitePopulationPotential measurable_liveIndicator).ennreal_ofReal
  rw [sharedPopulationLaw, Measure.lintegral_bind (Kernel.aemeasurable _)
    hterminal.aemeasurable]
  apply lintegral_mono
  intro ξ
  exact sharedEvolution_terminalPotential_le_bellman n Q ν hassoc T hTJoint
    hLeast hStateMono hDestructive hLaw 0 steps ξ

theorem association_decoupling_probability
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    [∀ j, PartialOrder (AugmentedState (X j))] [∀ j, Preorder (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (ν : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (ν j)]
    (hassoc : ∀ j, PositivelyAssociated (ν j))
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (hLeast : ∀ j z, cemetery ≤ (z : AugmentedState (X j)))
    (hStateMono : ∀ j w i, Monotone fun x => T j x w i)
    (hDestructive : ∀ j x i, Antitone fun w => T j x w i)
    (hLaw : ∀ j x, Measure.map (fun w i => T j x w i) (ν j) = Q j x)
    (ρ0 : Measure (FinitePopulation (AugmentedState (X 0)))) (steps : ℕ) :
    sharedPopulationLaw n ν T hTJoint ρ0 steps livePopulationEvent ≤
      ∫⁻ ξ, ENNReal.ofReal
        (finitePopulationPotential (bellmanFrom n Q 0 steps) ξ) ∂ρ0 := by
  rw [← lintegral_finitePopulationPotential_liveIndicator]
  exact sharedPopulationLaw_terminalPotential_le_bellman n Q ν hassoc T hTJoint
    hLeast hStateMono hDestructive hLaw ρ0 steps

end Shepp.Section4
end SheppFlattenedModule040

section SheppFlattenedModule041
open scoped BigOperators ENNReal ProbabilityTheory
open MeasureTheory Set

namespace Shepp.Section4

open ProbabilityTheory

noncomputable def liveDirac {X : Type*} [MeasurableSpace X] :
    AugmentedState X → Measure X :=
  Sum.elim Measure.dirac (fun _ => 0)

@[simp] theorem liveDirac_inl
    {X : Type*} [MeasurableSpace X] (x : X) :
    liveDirac (Sum.inl x : AugmentedState X) = Measure.dirac x := rfl

@[simp] theorem liveDirac_cemetery
    {X : Type*} [MeasurableSpace X] :
    liveDirac (cemetery : AugmentedState X) = 0 := rfl

theorem measurable_liveDirac
    {X : Type*} [MeasurableSpace X] :
    Measurable (liveDirac (X := X)) := by
  exact Measure.measurable_dirac.sumElim measurable_const

noncomputable instance liveDirac.instIsFiniteMeasure
    {X : Type*} [MeasurableSpace X] (z : AugmentedState X) :
    IsFiniteMeasure (liveDirac z) := by
  cases z with
  | inl x =>
      simp only [liveDirac_inl]
      infer_instance
  | inr u =>
      cases u
      change IsFiniteMeasure (0 : Measure X)
      infer_instance

def liveENNExtension {X : Type*} (f : X → ℝ≥0∞) :
    AugmentedState X → ℝ≥0∞ :=
  Sum.elim f (fun _ => 0)

@[simp] theorem liveENNExtension_inl
    {X : Type*} (f : X → ℝ≥0∞) (x : X) :
    liveENNExtension f (Sum.inl x) = f x := rfl

@[simp] theorem liveENNExtension_cemetery
    {X : Type*} (f : X → ℝ≥0∞) :
    liveENNExtension f (cemetery : AugmentedState X) = 0 := rfl

theorem measurable_liveENNExtension
    {X : Type*} [MeasurableSpace X]
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (liveENNExtension f) := by
  exact hf.sumElim measurable_const

theorem lintegral_liveDirac
    {X : Type*} [MeasurableSpace X]
    {f : X → ℝ≥0∞} (hf : Measurable f) (z : AugmentedState X) :
    (∫⁻ x, f x ∂liveDirac z) = liveENNExtension f z := by
  cases z with
  | inl x => exact lintegral_dirac' x hf
  | inr u => simp [liveDirac, liveENNExtension]

noncomputable def finitePopulationLiveMeasure
    {X : Type*} [MeasurableSpace X]
    (ξ : FinitePopulation (AugmentedState X)) : Measure X :=
  ∑ i, liveDirac (ξ.2 i)

theorem finitePopulationLiveMeasure_mk
    {X : Type*} [MeasurableSpace X] (q : ℕ)
    (xs : Fin q → AugmentedState X) :
    finitePopulationLiveMeasure ⟨q, xs⟩ = ∑ i, liveDirac (xs i) := rfl

theorem measurable_finitePopulationLiveMeasure
    {X : Type*} [MeasurableSpace X] :
    Measurable (finitePopulationLiveMeasure
      (X := X) : FinitePopulation (AugmentedState X) → Measure X) := by
  exact measurable_sigma_elim
    (fun q (xs : Fin q → AugmentedState X) => ∑ i, liveDirac (xs i)) fun q => by
      apply Finset.measurable_fun_sum
      intro i _hi
      exact measurable_liveDirac.comp (measurable_pi_apply i)

instance finitePopulationLiveMeasure.instIsFiniteMeasure
    {X : Type*} [MeasurableSpace X]
    (ξ : FinitePopulation (AugmentedState X)) :
    IsFiniteMeasure (finitePopulationLiveMeasure ξ) := by
  obtain ⟨q, xs⟩ := ξ
  change IsFiniteMeasure (∑ i : Fin q, liveDirac (xs i))
  infer_instance

theorem lintegral_finitePopulationLiveMeasure
    {X : Type*} [MeasurableSpace X]
    {f : X → ℝ≥0∞} (hf : Measurable f)
    (q : ℕ) (xs : Fin q → AugmentedState X) :
    (∫⁻ x, f x ∂finitePopulationLiveMeasure ⟨q, xs⟩) =
      ∑ i, liveENNExtension f (xs i) := by
  rw [finitePopulationLiveMeasure_mk, lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i _hi
  exact lintegral_liveDirac hf (xs i)

theorem liveSum_sharedFinitePopulationUpdate
    {A W Y : Type*} [MeasurableSpace Y] {n q : ℕ}
    (T : A → W → Fin n → AugmentedState Y)
    (f : Y → ℝ≥0∞) (hf : Measurable f)
    (xs : Fin q → A) (w : W) :
    (∫⁻ y, f y ∂finitePopulationLiveMeasure
      (sharedFinitePopulationUpdate T ⟨q, xs⟩ w)) =
      ∑ a, ∑ i, liveENNExtension f (T (xs a) w i) := by
  rw [lintegral_finitePopulationLiveMeasure hf]
  change
    (∑ k : Fin (q * n), liveENNExtension f
      (T (xs (finProdFinEquiv.symm k).1) w (finProdFinEquiv.symm k).2)) = _
  calc
    (∑ k : Fin (q * n), liveENNExtension f
        (T (xs (finProdFinEquiv.symm k).1) w (finProdFinEquiv.symm k).2)) =
        ∑ ai : Fin q × Fin n, liveENNExtension f (T (xs ai.1) w ai.2) := by
      apply Fintype.sum_equiv finProdFinEquiv.symm
      intro k
      rfl
    _ = ∑ a, ∑ i, liveENNExtension f (T (xs a) w i) := by
      simpa using
        (Finset.sum_product (Finset.univ : Finset (Fin q))
          (Finset.univ : Finset (Fin n))
          (fun ai : Fin q × Fin n => liveENNExtension f (T (xs ai.1) w ai.2)))

theorem lintegral_sharedSlotSum_eq_kernel
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W]
    [MeasurableSpace Y] {n : ℕ}
    (ν : Measure W)
    (Q : Kernel A (Fin n → AugmentedState Y))
    (T : A → W → Fin n → AugmentedState Y)
    (hTMeas : ∀ x i, Measurable fun w => T x w i)
    (hLaw : ∀ x, Measure.map (fun w i => T x w i) ν = Q x)
    (f : Y → ℝ≥0∞) (hf : Measurable f) (x : A) :
    (∫⁻ w, ∑ i, liveENNExtension f (T x w i) ∂ν) =
      ∫⁻ ys, ∑ i, liveENNExtension f (ys i) ∂Q x := by
  have hvec : Measurable fun w i => T x w i := by
    apply measurable_pi_lambda
    intro i
    exact hTMeas x i
  have hsum : Measurable fun ys : Fin n → AugmentedState Y =>
      ∑ i, liveENNExtension f (ys i) := by
    apply Finset.measurable_fun_sum
    intro i _hi
    exact (measurable_liveENNExtension hf).comp (measurable_pi_apply i)
  rw [← hLaw x, lintegral_map hsum hvec]

theorem lintegral_comap_inl
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure (AugmentedState Y)) (f : Y → ℝ≥0∞) :
    (∫⁻ y, f y ∂μ.comap (@Sum.inl Y Unit)) =
      ∫⁻ z, liveENNExtension f z ∂μ := by
  let emb : MeasurableEmbedding (@Sum.inl Y Unit) := measurableEmbedding_inl
  have hmap := emb.lintegral_map
    (μ := μ.comap (@Sum.inl Y Unit)) (liveENNExtension f)
  have hind : (range (@Sum.inl Y Unit)).indicator (liveENNExtension f) =
      liveENNExtension f := by
    funext z
    cases z with
    | inl y => simp [liveENNExtension]
    | inr u => simp [liveENNExtension]
  calc
    (∫⁻ y, f y ∂μ.comap (@Sum.inl Y Unit)) =
        ∫⁻ z, liveENNExtension f z
          ∂Measure.map (@Sum.inl Y Unit) (μ.comap (@Sum.inl Y Unit)) := by
      simpa [liveENNExtension] using hmap.symm
    _ = ∫⁻ z in range (@Sum.inl Y Unit), liveENNExtension f z ∂μ := by
      rw [emb.map_comap]
    _ = ∫⁻ z, (range (@Sum.inl Y Unit)).indicator
        (liveENNExtension f) z ∂μ := by
      rw [lintegral_indicator measurableSet_range_inl]
    _ = ∫⁻ z, liveENNExtension f z ∂μ := by rw [hind]

theorem lintegral_liveCoordinateKernel
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y))
    {f : Y → ℝ≥0∞} (hf : Measurable f) (i : Fin n) (x : X) :
    (∫⁻ y, f y ∂liveCoordinateKernel Q i x) =
      ∫⁻ ys, liveENNExtension f (ys i) ∂Q (Sum.inl x) := by
  rw [liveCoordinateKernel, Kernel.comapRight_apply, lintegral_comap_inl]
  rw [Kernel.map_apply _ (by fun_prop)]
  rw [lintegral_map (measurable_liveENNExtension hf) (measurable_pi_apply i)]
  rw [Kernel.comap_apply]

noncomputable def slotLiveENNMean
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y))
    (f : Y → ℝ≥0∞) (z : AugmentedState X) : ℝ≥0∞ :=
  ∫⁻ ys, ∑ i, liveENNExtension f (ys i) ∂Q z

theorem measurable_slotLiveENNMean
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y))
    {f : Y → ℝ≥0∞} (hf : Measurable f) :
    Measurable (slotLiveENNMean Q f) := by
  apply Measurable.lintegral_kernel
  apply Finset.measurable_fun_sum
  intro i _hi
  exact (measurable_liveENNExtension hf).comp (measurable_pi_apply i)

theorem slotLiveENNMean_cemetery
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y))
    [IsMarkovKernel Q]
    (hAbsorb : Q cemetery (allCemetery n) = 1)
    (f : Y → ℝ≥0∞) :
    slotLiveENNMean Q f cemetery = 0 := by
  have hmem : ∀ᵐ ys ∂Q cemetery, ys ∈ allCemetery n := by
    apply (ae_mem_iff_measure_eq
      (measurableSet_allCemetery n).nullMeasurableSet).mpr
    simpa using hAbsorb
  rw [slotLiveENNMean]
  calc
    (∫⁻ ys, ∑ i, liveENNExtension f (ys i) ∂Q cemetery) =
        ∫⁻ _ys : Fin n → AugmentedState Y, (0 : ℝ≥0∞) ∂Q cemetery := by
      apply lintegral_congr_ae
      filter_upwards [hmem] with ys hys
      apply Finset.sum_eq_zero
      intro i _hi
      rw [hys i, liveENNExtension_cemetery]
    _ = 0 := by simp

theorem lintegral_liveMeanKernel
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y))
    {f : Y → ℝ≥0∞} (hf : Measurable f) (x : X) :
    (∫⁻ y, f y ∂liveMeanKernel Q x) =
      slotLiveENNMean Q f (Sum.inl x) := by
  rw [liveMeanKernel, Kernel.finsetSum_apply,
    lintegral_finsetSum_measure]
  simp_rw [lintegral_liveCoordinateKernel Q hf]
  rw [slotLiveENNMean, lintegral_finsetSum]
  intro i _hi
  exact (measurable_liveENNExtension hf).comp (measurable_pi_apply i)

theorem lintegral_liveMeasure_sharedPopulationKernel
    {A W Y : Type*} [MeasurableSpace A] [MeasurableSpace W]
    [MeasurableSpace Y] {n : ℕ}
    (ν : Measure W) [SFinite ν]
    (Q : Kernel A (Fin n → AugmentedState Y))
    (T : A → W → Fin n → AugmentedState Y)
    (hTJoint : ∀ i, Measurable fun p : A × W => T p.1 p.2 i)
    (hLaw : ∀ x, Measure.map (fun w i => T x w i) ν = Q x)
    (f : Y → ℝ≥0∞) (hf : Measurable f)
    (q : ℕ) (xs : Fin q → A) :
    (∫⁻ η, ∫⁻ y, f y ∂finitePopulationLiveMeasure η
      ∂sharedPopulationKernel ν T hTJoint ⟨q, xs⟩) =
      ∑ a, ∫⁻ ys, ∑ i, liveENNExtension f (ys i) ∂Q (xs a) := by
  let hTMeas : ∀ x i, Measurable fun w => T x w i := fun x i =>
    (hTJoint i).comp (measurable_const.prodMk measurable_id)
  have hUpdate : Measurable fun w =>
      sharedFinitePopulationUpdate T ⟨q, xs⟩ w :=
    (measurable_sharedFinitePopulationUpdate_branch T hTJoint q).comp
      (measurable_const.prodMk measurable_id)
  have hInner : Measurable fun η : FinitePopulation (AugmentedState Y) =>
      ∫⁻ y, f y ∂finitePopulationLiveMeasure η :=
    (Measure.measurable_lintegral hf).comp measurable_finitePopulationLiveMeasure
  change (∫⁻ η, ∫⁻ y, f y ∂finitePopulationLiveMeasure η
    ∂sharedPopulationBranchKernel ν T hTJoint q xs) = _
  rw [sharedPopulationBranchKernel_apply]
  rw [lintegral_map hInner hUpdate]
  simp_rw [liveSum_sharedFinitePopulationUpdate T f hf xs]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _ha
    exact lintegral_sharedSlotSum_eq_kernel ν Q T hTMeas hLaw f hf (xs a)
  · intro a _ha
    apply Finset.measurable_fun_sum
    intro i _hi
    exact (measurable_liveENNExtension hf).comp (hTMeas (xs a) i)

noncomputable def populationMeanMeasure
    {X : Type*} [MeasurableSpace X]
    (ρ : Measure (FinitePopulation (AugmentedState X))) : Measure X :=
  ρ.bind finitePopulationLiveMeasure

theorem lintegral_populationMeanMeasure
    {X : Type*} [MeasurableSpace X]
    (ρ : Measure (FinitePopulation (AugmentedState X)))
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂populationMeanMeasure ρ) =
      ∫⁻ ξ, ∫⁻ x, f x ∂finitePopulationLiveMeasure ξ ∂ρ := by
  rw [populationMeanMeasure, Measure.lintegral_bind
    measurable_finitePopulationLiveMeasure.aemeasurable hf.aemeasurable]

theorem populationMeanMeasure_sharedPopulationKernel
    {X W Y : Type*} [MeasurableSpace X] [MeasurableSpace W]
    [MeasurableSpace Y] {n : ℕ}
    (ν : Measure W) [IsProbabilityMeasure ν]
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y))
    [IsMarkovKernel Q]
    (T : AugmentedState X → W → Fin n → AugmentedState Y)
    (hTJoint : ∀ i, Measurable fun p : AugmentedState X × W =>
      T p.1 p.2 i)
    (hLaw : ∀ z, Measure.map (fun w i => T z w i) ν = Q z)
    (hAbsorb : Q cemetery (allCemetery n) = 1)
    (ξ : FinitePopulation (AugmentedState X)) :
    populationMeanMeasure (sharedPopulationKernel ν T hTJoint ξ) =
      liveMeanKernel Q ∘ₘ finitePopulationLiveMeasure ξ := by
  obtain ⟨q, xs⟩ := ξ
  rw [Measure.ext_iff_lintegral]
  intro f hf
  rw [lintegral_populationMeanMeasure _ hf]
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
  have hFixed := lintegral_liveMeasure_sharedPopulationKernel
    ν Q T hTJoint hLaw f hf q xs
  have hMeanMeas : Measurable fun x : X => ∫⁻ y, f y ∂liveMeanKernel Q x :=
    hf.lintegral_kernel
  calc
    (∫⁻ η, ∫⁻ y, f y ∂finitePopulationLiveMeasure η
        ∂sharedPopulationKernel ν T hTJoint ⟨q, xs⟩) =
        ∑ a, slotLiveENNMean Q f (xs a) := by
      simpa only [slotLiveENNMean] using hFixed
    _ = ∑ a, liveENNExtension
        (fun x : X => ∫⁻ y, f y ∂liveMeanKernel Q x) (xs a) := by
      apply Finset.sum_congr rfl
      intro a _ha
      cases hxa : xs a with
      | inl x =>
          simpa only [liveENNExtension_inl] using
            (lintegral_liveMeanKernel Q hf x).symm
      | inr u =>
          cases u
          change slotLiveENNMean Q f cemetery =
            liveENNExtension
              (fun x : X => ∫⁻ y, f y ∂liveMeanKernel Q x) cemetery
          rw [slotLiveENNMean_cemetery Q hAbsorb,
            liveENNExtension_cemetery]
    _ = ∫⁻ x, (∫⁻ y, f y ∂liveMeanKernel Q x)
        ∂finitePopulationLiveMeasure ⟨q, xs⟩ := by
      rw [lintegral_finitePopulationLiveMeasure hMeanMeas]

theorem populationMeanMeasure_bind_sharedPopulationKernel
    {X W Y : Type*} [MeasurableSpace X] [MeasurableSpace W]
    [MeasurableSpace Y] {n : ℕ}
    (ν : Measure W) [IsProbabilityMeasure ν]
    (Q : Kernel (AugmentedState X) (Fin n → AugmentedState Y))
    [IsMarkovKernel Q]
    (T : AugmentedState X → W → Fin n → AugmentedState Y)
    (hTJoint : ∀ i, Measurable fun p : AugmentedState X × W =>
      T p.1 p.2 i)
    (hLaw : ∀ z, Measure.map (fun w i => T z w i) ν = Q z)
    (hAbsorb : Q cemetery (allCemetery n) = 1)
    (ρ : Measure (FinitePopulation (AugmentedState X))) :
    populationMeanMeasure (ρ.bind (sharedPopulationKernel ν T hTJoint)) =
      liveMeanKernel Q ∘ₘ populationMeanMeasure ρ := by
  rw [Measure.ext_iff_lintegral]
  intro f hf
  let inner : FinitePopulation (AugmentedState Y) → ℝ≥0∞ :=
    fun η => ∫⁻ y, f y ∂finitePopulationLiveMeasure η
  have hinner : Measurable inner :=
    (Measure.measurable_lintegral hf).comp measurable_finitePopulationLiveMeasure
  have hmean : Measurable fun x : X => ∫⁻ y, f y ∂liveMeanKernel Q x :=
    hf.lintegral_kernel
  calc
    (∫⁻ y, f y ∂populationMeanMeasure
        (ρ.bind (sharedPopulationKernel ν T hTJoint))) =
        ∫⁻ η, inner η ∂ρ.bind (sharedPopulationKernel ν T hTJoint) := by
      exact lintegral_populationMeanMeasure
        (ρ.bind (sharedPopulationKernel ν T hTJoint)) hf
    _ = ∫⁻ ξ, ∫⁻ η, inner η
        ∂sharedPopulationKernel ν T hTJoint ξ ∂ρ := by
      rw [Measure.lintegral_bind (Kernel.aemeasurable _) hinner.aemeasurable]
    _ = ∫⁻ ξ, ∫⁻ y, f y
        ∂(liveMeanKernel Q ∘ₘ finitePopulationLiveMeasure ξ) ∂ρ := by
      apply lintegral_congr_ae
      filter_upwards with ξ
      calc
        (∫⁻ η, inner η ∂sharedPopulationKernel ν T hTJoint ξ) =
            ∫⁻ y, f y ∂populationMeanMeasure
              (sharedPopulationKernel ν T hTJoint ξ) := by
          exact (lintegral_populationMeanMeasure
            (sharedPopulationKernel ν T hTJoint ξ) hf).symm
        _ = ∫⁻ y, f y
            ∂(liveMeanKernel Q ∘ₘ finitePopulationLiveMeasure ξ) := by
          rw [populationMeanMeasure_sharedPopulationKernel
            ν Q T hTJoint hLaw hAbsorb ξ]
    _ = ∫⁻ ξ, ∫⁻ x, (∫⁻ y, f y ∂liveMeanKernel Q x)
        ∂finitePopulationLiveMeasure ξ ∂ρ := by
      apply lintegral_congr_ae
      filter_upwards with ξ
      rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
    _ = ∫⁻ x, (∫⁻ y, f y ∂liveMeanKernel Q x)
        ∂populationMeanMeasure ρ := by
      exact (lintegral_populationMeanMeasure ρ hmean).symm
    _ = ∫⁻ y, f y ∂(liveMeanKernel Q ∘ₘ populationMeanMeasure ρ) := by
      exact (Measure.lintegral_bind
        (Kernel.aemeasurable _) hf.aemeasurable).symm

noncomputable def meanEvolutionMeasure
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)] :
    (j steps : ℕ) → Measure (X j) →
      Measure (X (generationAfter j steps))
  | _j, 0, μ => μ
  | j, steps + 1, μ =>
      meanEvolutionMeasure n Q (j + 1) steps (liveMeanKernel (Q j) ∘ₘ μ)

@[simp] theorem meanEvolutionMeasure_zero
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)] (j : ℕ) (μ : Measure (X j)) :
    meanEvolutionMeasure n Q j 0 μ = μ := rfl

theorem meanEvolutionMeasure_succ
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)] (j steps : ℕ) (μ : Measure (X j)) :
    meanEvolutionMeasure n Q j (steps + 1) μ =
      meanEvolutionMeasure n Q (j + 1) steps
        (liveMeanKernel (Q j) ∘ₘ μ) := rfl

theorem populationMeanMeasure_sharedEvolutionKernel
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (ν : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (ν j)]
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (hLaw : ∀ j z, Measure.map (fun w i => T j z w i) (ν j) = Q j z)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1) :
    ∀ j steps (ρ : Measure (FinitePopulation (AugmentedState (X j)))),
      populationMeanMeasure
          (ρ.bind (sharedEvolutionKernel n ν T hTJoint j steps)) =
        meanEvolutionMeasure n Q j steps (populationMeanMeasure ρ) := by
  intro j steps
  induction steps generalizing j with
  | zero =>
      intro ρ
      change populationMeanMeasure
          (ρ.bind (Kernel.id : Kernel
            (FinitePopulation (AugmentedState (X j)))
            (FinitePopulation (AugmentedState (X j))))) =
        populationMeanMeasure ρ
      apply congrArg populationMeanMeasure
      change ρ.bind Measure.dirac = ρ
      exact Measure.bind_dirac
  | succ steps ih =>
      intro ρ
      let Kstep := sharedPopulationKernel (ν j) (T j) (hTJoint j)
      let Kfuture := sharedEvolutionKernel n ν T hTJoint (j + 1) steps
      have hAssoc :
          ρ.bind (sharedEvolutionKernel n ν T hTJoint j (steps + 1)) =
            (ρ.bind Kstep).bind Kfuture := by
        rw [sharedEvolutionKernel_succ]
        change ρ.bind (fun ξ => Kernel.comp Kfuture Kstep ξ) =
          (ρ.bind Kstep).bind Kfuture
        simp_rw [Kernel.comp_apply]
        exact (Measure.bind_bind (Kernel.aemeasurable Kstep)
          (Kernel.aemeasurable Kfuture)).symm
      rw [hAssoc, meanEvolutionMeasure_succ]
      calc
        populationMeanMeasure ((ρ.bind Kstep).bind Kfuture) =
            meanEvolutionMeasure n Q (j + 1) steps
              (populationMeanMeasure (ρ.bind Kstep)) := by
          exact ih (j + 1) (ρ.bind Kstep)
        _ = meanEvolutionMeasure n Q (j + 1) steps
              (liveMeanKernel (Q j) ∘ₘ populationMeanMeasure ρ) := by
          rw [populationMeanMeasure_bind_sharedPopulationKernel
            (ν j) (Q j) (T j) (hTJoint j) (hLaw j) (hAbsorb j) ρ]

theorem meanEvolutionMeasure_meanFlow
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (μ0 : FiniteMeasure (X 0)) :
    ∀ j steps,
      meanEvolutionMeasure n Q j steps
          (meanFlow n Q μ0 j : Measure (X j)) =
        (meanFlow n Q μ0 (generationAfter j steps) :
          Measure (X (generationAfter j steps))) := by
  intro j steps
  induction steps generalizing j with
  | zero => rfl
  | succ steps ih =>
      rw [meanEvolutionMeasure_succ]
      have hPush :
          liveMeanKernel (Q j) ∘ₘ
              (meanFlow n Q μ0 j : Measure (X j)) =
            (meanFlow n Q μ0 (j + 1) : Measure (X (j + 1))) := by
        rfl
      rw [hPush]
      exact ih (j + 1)

noncomputable def initialMeanFiniteMeasure
    {X : Type*} [MeasurableSpace X]
    (ρ : Measure (FinitePopulation (AugmentedState X)))
    [IsFiniteMeasure (populationMeanMeasure ρ)] : FiniteMeasure X :=
  ⟨populationMeanMeasure ρ, inferInstance⟩

theorem sharedPopulationLaw_firstMoment_eq_meanFlow
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (ν : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (ν j)]
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (hLaw : ∀ j z, Measure.map (fun w i => T j z w i) (ν j) = Q j z)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (ρ0 : Measure (FinitePopulation (AugmentedState (X 0))))
    [IsFiniteMeasure (populationMeanMeasure ρ0)] (steps : ℕ) :
    populationMeanMeasure (sharedPopulationLaw n ν T hTJoint ρ0 steps) =
      (meanFlow n Q (initialMeanFiniteMeasure ρ0)
        (generationAfter 0 steps) : Measure (X (generationAfter 0 steps))) := by
  rw [sharedPopulationLaw]
  calc
    populationMeanMeasure
        (ρ0.bind (sharedEvolutionKernel n ν T hTJoint 0 steps)) =
        meanEvolutionMeasure n Q 0 steps (populationMeanMeasure ρ0) :=
      populationMeanMeasure_sharedEvolutionKernel n Q ν T hTJoint hLaw hAbsorb
        0 steps ρ0
    _ = meanEvolutionMeasure n Q 0 steps
        (meanFlow n Q (initialMeanFiniteMeasure ρ0) 0 : Measure (X 0)) := by
      rfl
    _ = (meanFlow n Q (initialMeanFiniteMeasure ρ0)
        (generationAfter 0 steps) : Measure (X (generationAfter 0 steps))) :=
      meanEvolutionMeasure_meanFlow n Q (initialMeanFiniteMeasure ρ0) 0 steps

theorem ofReal_finitePopulationPotential_le_liveMeasure
    {X : Type*} [MeasurableSpace X]
    {s : AugmentedState X → ℝ} (hs : Measurable s)
    (hs0 : ∀ z, 0 ≤ s z) (hs1 : ∀ z, s z ≤ 1)
    (hcem : s cemetery = 0)
    (ξ : FinitePopulation (AugmentedState X)) :
    ENNReal.ofReal (finitePopulationPotential s ξ) ≤
      ∫⁻ x, ENNReal.ofReal (s (Sum.inl x))
        ∂finitePopulationLiveMeasure ξ := by
  obtain ⟨q, xs⟩ := ξ
  have hUnion := populationPotential_le_sum hs0 hs1 (List.ofFn xs)
  rw [← finitePopulationPotential_eq_populationPotential_ofFn] at hUnion
  have hOfReal :
      ENNReal.ofReal (∑ i, s (xs i)) =
        ∑ i, ENNReal.ofReal (s (xs i)) := by
    exact ENNReal.ofReal_sum_of_nonneg fun i _hi => hs0 (xs i)
  have hTerms :
      (∑ i, ENNReal.ofReal (s (xs i))) =
        ∑ i, liveENNExtension
          (fun x : X => ENNReal.ofReal (s (Sum.inl x))) (xs i) := by
    apply Finset.sum_congr rfl
    intro i _hi
    cases hxi : xs i with
    | inl x => rfl
    | inr u =>
        cases u
        change ENNReal.ofReal (s cemetery) = 0
        rw [hcem]
        simp
  have hf : Measurable fun x : X => ENNReal.ofReal (s (Sum.inl x)) :=
    (hs.comp measurable_inl).ennreal_ofReal
  calc
    ENNReal.ofReal (finitePopulationPotential s ⟨q, xs⟩) ≤
        ENNReal.ofReal ((List.ofFn xs |>.map s).sum) :=
      ENNReal.ofReal_le_ofReal hUnion
    _ = ENNReal.ofReal (∑ i, s (xs i)) := by
      simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    _ = ∑ i, ENNReal.ofReal (s (xs i)) := hOfReal
    _ = ∑ i, liveENNExtension
        (fun x : X => ENNReal.ofReal (s (Sum.inl x))) (xs i) := hTerms
    _ = ∫⁻ x, ENNReal.ofReal (s (Sum.inl x))
        ∂finitePopulationLiveMeasure ⟨q, xs⟩ := by
      rw [lintegral_finitePopulationLiveMeasure hf]

theorem lintegral_finitePopulationPotential_le_populationMean
    {X : Type*} [MeasurableSpace X]
    (ρ : Measure (FinitePopulation (AugmentedState X)))
    {s : AugmentedState X → ℝ} (hs : Measurable s)
    (hs0 : ∀ z, 0 ≤ s z) (hs1 : ∀ z, s z ≤ 1)
    (hcem : s cemetery = 0) :
    (∫⁻ ξ, ENNReal.ofReal (finitePopulationPotential s ξ) ∂ρ) ≤
      ∫⁻ x, ENNReal.ofReal (s (Sum.inl x)) ∂populationMeanMeasure ρ := by
  let f : X → ℝ≥0∞ := fun x => ENNReal.ofReal (s (Sum.inl x))
  have hf : Measurable f := (hs.comp measurable_inl).ennreal_ofReal
  calc
    (∫⁻ ξ, ENNReal.ofReal (finitePopulationPotential s ξ) ∂ρ) ≤
        ∫⁻ ξ, ∫⁻ x, f x ∂finitePopulationLiveMeasure ξ ∂ρ := by
      apply lintegral_mono
      intro ξ
      exact ofReal_finitePopulationPotential_le_liveMeasure hs hs0 hs1 hcem ξ
    _ = ∫⁻ x, f x ∂populationMeanMeasure ρ :=
      (lintegral_populationMeanMeasure ρ hf).symm

theorem initialBellmanPotential_le_horizonSurvival
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (ρ0 : Measure (FinitePopulation (AugmentedState (X 0))))
    [IsFiniteMeasure (populationMeanMeasure ρ0)] (N : ℕ) :
    (∫⁻ ξ, ENNReal.ofReal
        (finitePopulationPotential (bellmanFrom n Q 0 N) ξ) ∂ρ0) ≤
      ENNReal.ofReal (horizonSurvivalIntegral n Q
        (initialMeanFiniteMeasure ρ0) 0 N) := by
  let s := bellmanFrom n Q 0 N
  let μ0 := initialMeanFiniteMeasure ρ0
  have hs : Measurable s := measurable_bellmanFrom n Q 0 N
  have hs0 : ∀ z, 0 ≤ s z := fun z => (bellmanFrom_mem_Icc n Q 0 N z).1
  have hs1 : ∀ z, s z ≤ 1 := fun z => (bellmanFrom_mem_Icc n Q 0 N z).2
  have hcem : s cemetery = 0 := bellmanFrom_cemetery n Q hAbsorb 0 N
  have hLinear := lintegral_finitePopulationPotential_le_populationMean
    ρ0 hs hs0 hs1 hcem
  have hf : Measurable fun x : X 0 => s (Sum.inl x) := hs.comp measurable_inl
  have hInt : Integrable (fun x : X 0 => s (Sum.inl x))
      (populationMeanMeasure ρ0) := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_of_nonneg (hs0 _)]
    exact hs1 _
  have hNonneg : 0 ≤ᵐ[populationMeanMeasure ρ0]
      fun x : X 0 => s (Sum.inl x) :=
    ae_of_all _ fun x => hs0 _
  calc
    (∫⁻ ξ, ENNReal.ofReal (finitePopulationPotential s ξ) ∂ρ0) ≤
        ∫⁻ x, ENNReal.ofReal (s (Sum.inl x))
          ∂populationMeanMeasure ρ0 := hLinear
    _ = ENNReal.ofReal
        (∫ x, s (Sum.inl x) ∂populationMeanMeasure ρ0) :=
      (ofReal_integral_eq_lintegral_ofReal hInt hNonneg).symm
    _ = ENNReal.ofReal (horizonSurvivalIntegral n Q μ0 0 N) := by
      have hflow0 :
          (meanFlow n Q μ0 0 : Measure (X 0)) =
            populationMeanMeasure ρ0 := by
        change (μ0 : Measure (X 0)) = populationMeanMeasure ρ0
        rfl
      simp only [horizonSurvivalIntegral, survivalIntegral, bellmanTo,
        Nat.sub_zero, s]
      rw [hflow0]

theorem initialBellmanPotential_le_horizonConductance
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (B : ℕ) (hB : 1 ≤ B)
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (ρ0 : Measure (FinitePopulation (AugmentedState (X 0))))
    [IsFiniteMeasure (populationMeanMeasure ρ0)] (N : ℕ) :
    (∫⁻ ξ, ENNReal.ofReal
        (finitePopulationPotential (bellmanFrom n Q 0 N) ξ) ∂ρ0) ≤
      ENNReal.ofReal (horizonConductance B n Q
        (initialMeanFiniteMeasure ρ0) 0 N) := by
  have hSurv := initialBellmanPotential_le_horizonSurvival
    n Q hAbsorb ρ0 N
  have hSC := survivalIntegral_le_conductance hB
    (meanFlow n Q (initialMeanFiniteMeasure ρ0) 0)
    (measurable_bellmanTo n Q 0 N)
    (fun z => (bellmanTo_mem_Icc n Q 0 N z).1)
    (fun z => (bellmanTo_mem_Icc n Q 0 N z).2)
  exact hSurv.trans (ENNReal.ofReal_le_ofReal (by
    simpa only [horizonSurvivalIntegral, horizonConductance] using hSC))

theorem sharedPopulationLaw_meanPopulation
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (ν : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (ν j)]
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (hLaw : ∀ j z, Measure.map (fun w i => T j z w i) (ν j) = Q j z)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (ρ0 : Measure (FinitePopulation (AugmentedState (X 0))))
    [IsFiniteMeasure (populationMeanMeasure ρ0)] (steps : ℕ) :
    (populationMeanMeasure
      (sharedPopulationLaw n ν T hTJoint ρ0 steps)).real univ =
      meanPopulation (meanFlow n Q (initialMeanFiniteMeasure ρ0)
        (generationAfter 0 steps)) := by
  rw [sharedPopulationLaw_firstMoment_eq_meanFlow
    n Q ν T hTJoint hLaw hAbsorb ρ0 steps]
  rfl

end Shepp.Section4
end SheppFlattenedModule041

section SheppFlattenedModule042
open scoped BigOperators ENNReal ProbabilityTheory Topology
open MeasureTheory Set Filter

namespace Shepp.Section4

open ProbabilityTheory

noncomputable def resistanceTermENN (δ m : ℕ → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (δ j / m j)

noncomputable def resistancePartialENN (δ m : ℕ → ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range N, resistanceTermENN δ m j

def DivergentResistance (δ m : ℕ → ℝ) : Prop :=
  ∑' j, resistanceTermENN δ m j = ∞

theorem resistancePartialENN_tendsto_top
    {δ m : ℕ → ℝ} (hdiv : DivergentResistance δ m) :
    Tendsto (resistancePartialENN δ m) atTop (𝓝 ∞) := by
  have h := ENNReal.tendsto_nat_tsum (resistanceTermENN δ m)
  rw [hdiv] at h
  change Tendsto
    (fun N => ∑ j ∈ Finset.range N, resistanceTermENN δ m j)
    atTop (𝓝 ∞)
  exact h

theorem ofReal_inverse_add_mul_sum_le
    {ι : Type*} (s : Finset ι) {a c : ℝ} {r : ι → ℝ}
    (ha : 0 < a) (hc : 0 < c) (hr : ∀ i ∈ s, 0 ≤ r i) :
    ENNReal.ofReal ((a + c * ∑ i ∈ s, r i)⁻¹) ≤
      (ENNReal.ofReal c * ∑ i ∈ s, ENNReal.ofReal (r i))⁻¹ := by
  let R : ℝ := ∑ i ∈ s, r i
  have hR0 : 0 ≤ R := Finset.sum_nonneg hr
  have hsumENN : ENNReal.ofReal R =
      ∑ i ∈ s, ENNReal.ofReal (r i) :=
    ENNReal.ofReal_sum_of_nonneg hr
  by_cases hR : R = 0
  · rw [← hsumENN, hR]
    simp
  · have hRpos : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hR)
    have hcRpos : 0 < c * R := mul_pos hc hRpos
    have hdenom : 0 < a + c * R := add_pos_of_pos_of_nonneg ha hcRpos.le
    have hinv : (a + c * R)⁻¹ ≤ (c * R)⁻¹ :=
      inv_anti₀ hcRpos (le_add_of_nonneg_left ha.le)
    calc
      ENNReal.ofReal ((a + c * ∑ i ∈ s, r i)⁻¹) =
          ENNReal.ofReal ((a + c * R)⁻¹) := by rfl
      _ ≤ ENNReal.ofReal ((c * R)⁻¹) := ENNReal.ofReal_le_ofReal hinv
      _ = (ENNReal.ofReal (c * R))⁻¹ := ENNReal.ofReal_inv_of_pos hcRpos
      _ = (ENNReal.ofReal c * ENNReal.ofReal R)⁻¹ := by
        rw [ENNReal.ofReal_mul hc.le]
      _ = (ENNReal.ofReal c *
          ∑ i ∈ s, ENNReal.ofReal (r i))⁻¹ := by rw [hsumENN]

theorem resistanceInverse_tendsto_zero
    {δ m : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hdiv : DivergentResistance δ m) :
    Tendsto (fun N =>
      (ENNReal.ofReal c * resistancePartialENN δ m N)⁻¹)
      atTop (𝓝 0) := by
  have hS : Tendsto (resistancePartialENN δ m) atTop (𝓝 ∞) :=
    resistancePartialENN_tendsto_top hdiv
  have hcENN : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hmul : Tendsto
      (fun N => ENNReal.ofReal c * resistancePartialENN δ m N)
      atTop (𝓝 ∞) := by
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c)
      hS (Or.inl ENNReal.top_ne_zero)
    simpa [hcENN] using h
  simpa only [ENNReal.inv_top] using (tendsto_inv_iff.mpr hmul)

theorem measure_livePopulationEvent_le_meanMass
    {X : Type*} [MeasurableSpace X]
    (ρ : Measure (FinitePopulation (AugmentedState X))) :
    ρ livePopulationEvent ≤ populationMeanMeasure ρ univ := by
  rw [← lintegral_finitePopulationPotential_liveIndicator]
  have h := lintegral_finitePopulationPotential_le_populationMean
    ρ measurable_liveIndicator
    (fun z => (liveIndicator_mem_Icc z).1)
    (fun z => (liveIndicator_mem_Icc z).2)
    liveIndicator_cemetery
  simpa [liveIndicator, MeasureTheory.lintegral_one] using h

theorem sharedExtinction_of_meanPopulation_eq_zero
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (ν : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (ν j)]
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (hLaw : ∀ j z, Measure.map (fun w i => T j z w i) (ν j) = Q j z)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (ρ0 : Measure (FinitePopulation (AugmentedState (X 0))))
    [IsFiniteMeasure (populationMeanMeasure ρ0)] (steps : ℕ)
    (hmzero : meanPopulation
      (meanFlow n Q (initialMeanFiniteMeasure ρ0)
        (generationAfter 0 steps)) = 0) :
    sharedPopulationLaw n ν T hTJoint ρ0 steps
      (livePopulationEvent (X := X (generationAfter 0 steps))) = 0 := by
  let ρN := sharedPopulationLaw n ν T hTJoint ρ0 steps
  have hMeanEq := sharedPopulationLaw_firstMoment_eq_meanFlow
    n Q ν T hTJoint hLaw hAbsorb ρ0 steps
  have hMeanReal : (populationMeanMeasure ρN).real univ = 0 := by
    change (populationMeanMeasure
      (sharedPopulationLaw n ν T hTJoint ρ0 steps)).real univ = 0
    rw [hMeanEq]
    exact hmzero
  have hMeanNeTop : populationMeanMeasure ρN univ ≠ ∞ := by
    rw [hMeanEq]
    exact measure_ne_top _ _
  have hMeanMass : populationMeanMeasure ρN univ = 0 := by
    rw [← ofReal_measureReal hMeanNeTop, hMeanReal]
    simp
  apply le_zero_iff.mp
  exact (measure_livePopulationEvent_le_meanMass ρN).trans_eq hMeanMass

end Shepp.Section4
end SheppFlattenedModule042

section SheppFlattenedModule043
open scoped ENNReal ProbabilityTheory Topology
open MeasureTheory Set Filter

namespace Shepp.Section4

open ProbabilityTheory TopologicalSpace

theorem decreasing_compact_iInter_nonempty
    {K : Type*} [TopologicalSpace K] [T2Space K]
    (F : ℕ → Set K) (hdec : ∀ N, F (N + 1) ⊆ F N)
    (hne : ∀ N, (F N).Nonempty) (hcompact : ∀ N, IsCompact (F N)) :
    (⋂ N, F N).Nonempty := by
  exact (hcompact 0).nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    F hdec hne (fun N => (hcompact N).isClosed)

abbrev CompactResidual (K : Type*) [TopologicalSpace K] := Compacts K

noncomputable instance CompactResidual.instMeasurableSpace
    (K : Type*) [MetricSpace K] : MeasurableSpace (CompactResidual K) :=
  borel _

instance CompactResidual.instBorelSpace
    (K : Type*) [MetricSpace K] : BorelSpace (CompactResidual K) :=
  ⟨rfl⟩

theorem isOpen_singleton_empty_compactResidual
    {K : Type*} [MetricSpace K] :
    IsOpen ({(⊥ : CompactResidual K)} : Set (CompactResidual K)) := by
  have hball : Metric.eball (⊥ : CompactResidual K) ∞ =
      ({(⊥ : CompactResidual K)} : Set (CompactResidual K)) := by
    ext A
    simp only [Metric.mem_eball, mem_singleton_iff]
    constructor
    · intro hdist
      by_contra hA
      have hnonempty : (A : Set K).Nonempty :=
        Compacts.coe_nonempty.mpr hA
      have htop : edist A (⊥ : CompactResidual K) = ∞ := by
        rw [Compacts.edist_eq]
        exact Metric.hausdorffEDist_empty hnonempty
      rw [htop] at hdist
      exact (lt_irrefl ∞ hdist)
    · rintro rfl
      simp
  rw [← hball]
  exact Metric.isOpen_eball

def compactResidualNonemptySet
    {K : Type*} [MetricSpace K] : Set (CompactResidual K) :=
  {A | A ≠ ⊥}

theorem measurableSet_compactResidualNonemptySet
    {K : Type*} [MetricSpace K] :
    MeasurableSet (compactResidualNonemptySet (K := K)) := by
  rw [show compactResidualNonemptySet (K := K) =
      ({(⊥ : CompactResidual K)} : Set (CompactResidual K))ᶜ by
    ext A
    simp [compactResidualNonemptySet]]
  exact isClosed_singleton.measurableSet.compl

def residualNonemptyEvent
    {K Ω : Type*} [MetricSpace K]
    (R : ℕ → Ω → CompactResidual K) (N : ℕ) : Set Ω :=
  {ω | R N ω ≠ ⊥}

def residualFiniteTimeExtinctionEvent
    {K Ω : Type*} [MetricSpace K]
    (R : ℕ → Ω → CompactResidual K) : Set Ω :=
  {ω | ∃ N, R N ω = ⊥}

def residualLimitSet
    {K Ω : Type*} [MetricSpace K]
    (R : ℕ → Ω → CompactResidual K) (ω : Ω) : Set K :=
  ⋂ N, (R N ω : Set K)

def residualLimitNonemptyEvent
    {K Ω : Type*} [MetricSpace K]
    (R : ℕ → Ω → CompactResidual K) : Set Ω :=
  {ω | (residualLimitSet R ω).Nonempty}

theorem measurableSet_residualNonemptyEvent
    {K Ω : Type*} [MetricSpace K] [MeasurableSpace Ω]
    (R : ℕ → Ω → CompactResidual K) {N : ℕ}
    (hR : Measurable (R N)) :
    MeasurableSet (residualNonemptyEvent R N) := by
  change MeasurableSet ((R N) ⁻¹' compactResidualNonemptySet)
  exact measurableSet_compactResidualNonemptySet.preimage hR

theorem residualLimitSet_nonempty_iff
    {K : Type*} [MetricSpace K]
    (R : ℕ → CompactResidual K) (hdec : Antitone R) :
    (residualLimitSet (fun N (_ : Unit) => R N) ()).Nonempty ↔
      ∀ N, R N ≠ ⊥ := by
  constructor
  · intro h N
    rw [← Compacts.coe_nonempty]
    exact h.mono (iInter_subset (fun j => (R j : Set K)) N)
  · intro h
    apply decreasing_compact_iInter_nonempty
      (fun N => (R N : Set K))
    · intro N
      exact hdec (Nat.le_succ N)
    · intro N
      exact Compacts.coe_nonempty.mpr (h N)
    · intro N
      exact Compacts.isCompact (R N)

theorem antitone_residualNonemptyEvent
    {K Ω : Type*} [MetricSpace K]
    (R : ℕ → Ω → CompactResidual K)
    (hdec : ∀ ω, Antitone fun N => R N ω) :
    Antitone (residualNonemptyEvent R) := by
  intro i j hij ω hω
  simp only [residualNonemptyEvent, mem_setOf_eq] at hω ⊢
  rw [← Compacts.coe_nonempty] at hω ⊢
  exact hω.mono (hdec ω hij)

theorem residualLimitNonemptyEvent_eq_iInter
    {K Ω : Type*} [MetricSpace K]
    (R : ℕ → Ω → CompactResidual K)
    (hdec : ∀ ω, Antitone fun N => R N ω) :
    residualLimitNonemptyEvent R = ⋂ N, residualNonemptyEvent R N := by
  ext ω
  simp only [residualLimitNonemptyEvent, residualNonemptyEvent,
    mem_setOf_eq, mem_iInter]
  change (residualLimitSet R ω).Nonempty ↔ ∀ N, R N ω ≠ ⊥
  simpa only [residualLimitSet] using
    (residualLimitSet_nonempty_iff (fun N => R N ω) (hdec ω))

theorem measurableSet_residualLimitNonemptyEvent
    {K Ω : Type*} [MetricSpace K] [MeasurableSpace Ω]
    (R : ℕ → Ω → CompactResidual K)
    (hR : ∀ N, Measurable (R N))
    (hdec : ∀ ω, Antitone fun N => R N ω) :
    MeasurableSet (residualLimitNonemptyEvent R) := by
  rw [residualLimitNonemptyEvent_eq_iInter R hdec]
  exact MeasurableSet.iInter fun N =>
    measurableSet_residualNonemptyEvent R (hR N)

theorem residualFiniteTimeExtinctionEvent_eq_compl_limit
    {K Ω : Type*} [MetricSpace K]
    (R : ℕ → Ω → CompactResidual K)
    (hdec : ∀ ω, Antitone fun N => R N ω) :
    residualFiniteTimeExtinctionEvent R =
      (residualLimitNonemptyEvent R)ᶜ := by
  classical
  ext ω
  change (∃ N, R N ω = ⊥) ↔ ¬ (residualLimitSet R ω).Nonempty
  rw [show (residualLimitSet R ω).Nonempty ↔
      ∀ N, R N ω ≠ ⊥ by
    simpa only [residualLimitSet] using
      (residualLimitSet_nonempty_iff (fun N => R N ω) (hdec ω))]
  simp

theorem measurableSet_residualFiniteTimeExtinctionEvent
    {K Ω : Type*} [MetricSpace K] [MeasurableSpace Ω]
    (R : ℕ → Ω → CompactResidual K)
    (hR : ∀ N, Measurable (R N))
    (hdec : ∀ ω, Antitone fun N => R N ω) :
    MeasurableSet (residualFiniteTimeExtinctionEvent R) := by
  rw [residualFiniteTimeExtinctionEvent_eq_compl_limit R hdec]
  exact (measurableSet_residualLimitNonemptyEvent R hR hdec).compl

theorem tendsto_measure_residualNonemptyEvent
    {K Ω : Type*} [MetricSpace K] [MeasurableSpace Ω]
    (R : ℕ → Ω → CompactResidual K)
    (hR : ∀ N, Measurable (R N))
    (hdec : ∀ ω, Antitone fun N => R N ω)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Tendsto (fun N => μ (residualNonemptyEvent R N)) atTop
      (𝓝 (μ (residualLimitNonemptyEvent R))) := by
  rw [residualLimitNonemptyEvent_eq_iInter R hdec]
  exact tendsto_measure_iInter_atTop
    (fun N => (measurableSet_residualNonemptyEvent R (hR N)).nullMeasurableSet)
    (antitone_residualNonemptyEvent R hdec) ⟨0, measure_ne_top μ _⟩

theorem residualFiniteTimeExtinction_of_nonempty_tendsto_zero
    {K Ω : Type*} [MetricSpace K] [MeasurableSpace Ω]
    (R : ℕ → Ω → CompactResidual K)
    (hR : ∀ N, Measurable (R N))
    (hdec : ∀ ω, Antitone fun N => R N ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hzero : Tendsto (fun N => μ (residualNonemptyEvent R N))
      atTop (𝓝 0)) :
    μ (residualFiniteTimeExtinctionEvent R) = 1 := by
  have hcont := tendsto_measure_residualNonemptyEvent R hR hdec μ
  have hlimit : μ (residualLimitNonemptyEvent R) = 0 :=
    tendsto_nhds_unique hcont hzero
  rw [residualFiniteTimeExtinctionEvent_eq_compl_limit R hdec]
  rw [measure_compl (measurableSet_residualLimitNonemptyEvent R hR hdec)
    (measure_ne_top μ _), hlimit, measure_univ]
  simp

theorem residualFiniteTimeExtinction_of_nonempty_measure_eq_zero
    {K Ω : Type*} [MetricSpace K] [MeasurableSpace Ω]
    (R : ℕ → Ω → CompactResidual K)
    (hR : ∀ N, Measurable (R N))
    (hdec : ∀ ω, Antitone fun N => R N ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (hzero : μ (residualNonemptyEvent R N) = 0) :
    μ (residualFiniteTimeExtinctionEvent R) = 1 := by
  have hsubset : residualLimitNonemptyEvent R ⊆
      residualNonemptyEvent R N := by
    rw [residualLimitNonemptyEvent_eq_iInter R hdec]
    exact iInter_subset _ N
  have hlimit : μ (residualLimitNonemptyEvent R) = 0 := by
    apply le_zero_iff.mp
    exact (measure_mono hsubset).trans_eq hzero
  rw [residualFiniteTimeExtinctionEvent_eq_compl_limit R hdec]
  rw [measure_compl (measurableSet_residualLimitNonemptyEvent R hR hdec)
    (measure_ne_top μ _), hlimit, measure_univ]
  simp

theorem residualNonempty_measure_eq_sharedPopulationLaw_of_pathwise_identification
    {K Ω : Type*} [MetricSpace K] [MeasurableSpace Ω]
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    (n : ℕ → ℕ)
    (nu : (j : ℕ) → Measure (W j))
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (rho0 : Measure (FinitePopulation (AugmentedState (X 0))))
    (μ : Measure Ω)
    (Xi : (N : ℕ) → Ω →
      FinitePopulation (AugmentedState (X (generationAfter 0 N))))
    (hXiMeas : ∀ N, Measurable (Xi N))
    (hXiLaw : ∀ N, Measure.map (Xi N) μ =
      sharedPopulationLaw n nu T hTJoint rho0 N)
    (R : ℕ → Ω → CompactResidual K)
    (hEvent : ∀ N, (Xi N) ⁻¹'
      (livePopulationEvent (X := X (generationAfter 0 N))) =
        residualNonemptyEvent R N)
    (N : ℕ) :
    μ (residualNonemptyEvent R N) =
      sharedPopulationLaw n nu T hTJoint rho0 N
        (livePopulationEvent (X := X (generationAfter 0 N))) := by
  calc
    μ (residualNonemptyEvent R N) =
        μ ((Xi N) ⁻¹'
          (livePopulationEvent (X := X (generationAfter 0 N)))) := by
      rw [hEvent N]
    _ = Measure.map (Xi N) μ
        (livePopulationEvent (X := X (generationAfter 0 N))) := by
      exact (Measure.map_apply (hXiMeas N)
        measurableSet_livePopulationEvent).symm
    _ = sharedPopulationLaw n nu T hTJoint rho0 N
        (livePopulationEvent (X := X (generationAfter 0 N))) := by
      rw [hXiLaw N]

theorem sharedFiniteTimeExtinction_of_meanPopulation_eq_zero
    {K Ω : Type*} [MetricSpace K] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : ℕ → Ω → CompactResidual K)
    (hR : ∀ N, Measurable (R N))
    (hRdec : ∀ ω, Antitone fun N => R N ω)
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (nu : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (nu j)]
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (hLaw : ∀ j z, Measure.map (fun w i => T j z w i) (nu j) = Q j z)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (rho0 : Measure (FinitePopulation (AugmentedState (X 0))))
    [IsFiniteMeasure (populationMeanMeasure rho0)]
    (Xi : (N : ℕ) → Ω →
      FinitePopulation (AugmentedState (X (generationAfter 0 N))))
    (hXiMeas : ∀ N, Measurable (Xi N))
    (hXiLaw : ∀ N, Measure.map (Xi N) μ =
      sharedPopulationLaw n nu T hTJoint rho0 N)
    (hEvent : ∀ N, (Xi N) ⁻¹'
      (livePopulationEvent (X := X (generationAfter 0 N))) =
        residualNonemptyEvent R N)
    (steps : ℕ)
    (hmzero : meanPopulation
      (meanFlow n Q (initialMeanFiniteMeasure rho0)
        (generationAfter 0 steps)) = 0) :
    μ (residualFiniteTimeExtinctionEvent R) = 1 := by
  apply residualFiniteTimeExtinction_of_nonempty_measure_eq_zero
    R hR hRdec μ steps
  rw [residualNonempty_measure_eq_sharedPopulationLaw_of_pathwise_identification
    n nu T hTJoint rho0 μ Xi hXiMeas hXiLaw R hEvent steps]
  exact sharedExtinction_of_meanPopulation_eq_zero
    n Q nu T hTJoint hLaw hAbsorb rho0 steps hmzero

end Shepp.Section4
end SheppFlattenedModule043

section SheppFlattenedModule044
open scoped Topology
open MeasureTheory Set

namespace Shepp.Section5

open Shepp.Section4 TopologicalSpace

noncomputable def compactIntersection
    {K : Type*} [MetricSpace K]
    (A Q : CompactResidual K) : CompactResidual K :=
  A ⊓ Q

@[simp] theorem coe_compactIntersection
    {K : Type*} [MetricSpace K]
    (A Q : CompactResidual K) :
    ((compactIntersection A Q : CompactResidual K) : Set K) =
      (A : Set K) ∩ (Q : Set K) := by
  rfl

@[simp] theorem compactIntersection_eq_bot_iff
    {K : Type*} [MetricSpace K]
    (A Q : CompactResidual K) :
    compactIntersection A Q = ⊥ ↔
      ¬ ((A : Set K) ∩ (Q : Set K)).Nonempty := by
  rw [← Compacts.coe_eq_empty]
  simp only [coe_compactIntersection]
  exact not_nonempty_iff_eq_empty.symm

noncomputable def compactOpenCore
    {K : Type*} [MetricSpace K]
    (Q : CompactResidual K) (U : Set K) (n : ℕ) : Set K :=
  (Q : Set K) ∩
    {x | (1 / 2 : ℝ) ^ n ≤ Metric.infDist x Uᶜ}

theorem isClosed_compactOpenCore
    {K : Type*} [MetricSpace K]
    (Q : CompactResidual K) (U : Set K) (n : ℕ) :
    IsClosed (compactOpenCore Q U n) := by
  apply Q.isCompact.isClosed.inter
  exact isClosed_Ici.preimage (Metric.continuous_infDist_pt Uᶜ)

theorem isCompact_compactOpenCore
    {K : Type*} [MetricSpace K]
    (Q : CompactResidual K) (U : Set K) (n : ℕ) :
    IsCompact (compactOpenCore Q U n) := by
  exact Q.isCompact.inter_right
    (isClosed_Ici.preimage (Metric.continuous_infDist_pt Uᶜ))

theorem iUnion_compactOpenCore
    {K : Type*} [MetricSpace K]
    (Q : CompactResidual K) {U : Set K} (hU : IsOpen U)
    (hUc : Uᶜ.Nonempty) :
    ⋃ n : ℕ, compactOpenCore Q U n = (Q : Set K) ∩ U := by
  ext x
  constructor
  · intro hx
    rw [mem_iUnion] at hx
    obtain ⟨n, hxQ, hxn⟩ := hx
    refine ⟨hxQ, ?_⟩
    by_contra hxU
    have hxUc : x ∈ Uᶜ := hxU
    change (1 / 2 : ℝ) ^ n ≤ Metric.infDist x Uᶜ at hxn
    rw [Metric.infDist_zero_of_mem hxUc] at hxn
    have hpow : 0 < (1 / 2 : ℝ) ^ n := by positivity
    linarith
  · rintro ⟨hxQ, hxU⟩
    have hxnot : x ∉ Uᶜ := by simpa
    have hdist : 0 < Metric.infDist x Uᶜ :=
      (hU.isClosed_compl.notMem_iff_infDist_pos hUc).1 hxnot
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hdist one_half_lt_one
    rw [mem_iUnion]
    exact ⟨n, hxQ, hn.le⟩

theorem measurableSet_compact_inter_hits_open
    {K : Type*} [MetricSpace K]
    (Q : CompactResidual K) {U : Set K} (hU : IsOpen U) :
    MeasurableSet
      {A : CompactResidual K |
        ((A : Set K) ∩ ((Q : Set K) ∩ U)).Nonempty} := by
  by_cases hUtop : U = univ
  · subst U
    simpa [inter_assoc] using
      (Compacts.isClosed_inter_nonempty_of_isClosed
        Q.isCompact.isClosed).measurableSet
  · have hUc : Uᶜ.Nonempty := Set.nonempty_compl.2 hUtop
    let F : ℕ → Set K := fun n => compactOpenCore Q U n
    have hFclosed : ∀ n, IsClosed (F n) := fun n =>
      isClosed_compactOpenCore Q U n
    have heq :
        {A : CompactResidual K |
          ((A : Set K) ∩ ((Q : Set K) ∩ U)).Nonempty} =
        ⋃ n : ℕ,
          {A : CompactResidual K | ((A : Set K) ∩ F n).Nonempty} := by
      rw [← iUnion_compactOpenCore Q hU hUc]
      ext A
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨x, hxA, hxUnion⟩
        rw [mem_iUnion] at hxUnion
        obtain ⟨n, hxn⟩ := hxUnion
        exact ⟨n, x, hxA, hxn⟩
      · rintro ⟨n, x, hxA, hxn⟩
        exact ⟨x, hxA, mem_iUnion.2 ⟨n, hxn⟩⟩
    rw [heq]
    exact MeasurableSet.iUnion fun n =>
      (Compacts.isClosed_inter_nonempty_of_isClosed
        (hFclosed n)).measurableSet

theorem measurableSet_compactIntersection_subset_open
    {K : Type*} [MetricSpace K]
    (Q : CompactResidual K) {U : Set K} (hU : IsOpen U) :
    MeasurableSet
      {A : CompactResidual K |
        (A : Set K) ∩ (Q : Set K) ⊆ U} := by
  let F : Set K := (Q : Set K) ∩ Uᶜ
  have hFclosed : IsClosed F :=
    Q.isCompact.isClosed.inter hU.isClosed_compl
  have hhit : MeasurableSet
      {A : CompactResidual K | ((A : Set K) ∩ F).Nonempty} :=
    (Compacts.isClosed_inter_nonempty_of_isClosed hFclosed).measurableSet
  have heq :
      {A : CompactResidual K | (A : Set K) ∩ (Q : Set K) ⊆ U} =
      {A : CompactResidual K | ((A : Set K) ∩ F).Nonempty}ᶜ := by
    ext A
    constructor
    · intro hA
      simp only [mem_compl_iff, mem_setOf_eq, not_nonempty_iff_eq_empty]
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      exact hx.2.2 (hA ⟨hx.1, hx.2.1⟩)
    · intro hA x hx
      by_contra hxU
      have hxF : x ∈ F := ⟨hx.2, hxU⟩
      exact hA ⟨x, hx.1, hxF⟩
  rw [heq]
  exact hhit.compl

theorem measurable_compactIntersection_right
    {K : Type*} [MetricSpace K] [SecondCountableTopology K]
    (Q : CompactResidual K) :
    Measurable fun A : CompactResidual K => compactIntersection A Q := by
  let basis : Set (Set (CompactResidual K)) :=
    (fun u : Set (Set K) =>
      {A : CompactResidual K |
        (A : Set K) ⊆ ⋃₀ u ∧
          ∀ U ∈ u, ((A : Set K) ∩ U).Nonempty}) ''
      {u : Set (Set K) | u.Finite ∧ u ⊆ {U | IsOpen U}}
  have hbasis : IsTopologicalBasis basis := by
    simpa only [basis] using
      (isTopologicalBasis_opens.compacts (α := K))
  have hgen : borel (CompactResidual K) =
      MeasurableSpace.generateFrom basis :=
    hbasis.borel_eq_generateFrom
  have hm : @Measurable (CompactResidual K) (CompactResidual K)
      (CompactResidual.instMeasurableSpace K)
      (MeasurableSpace.generateFrom basis)
      (fun A => compactIntersection A Q) := by
    apply measurable_generateFrom
    intro V hV
    rcases hV with ⟨u, ⟨huFinite, huOpen⟩, rfl⟩
    let Uall : Set K := ⋃₀ u
    have hUall : IsOpen Uall :=
      isOpen_sUnion fun U hU => huOpen hU
    have hsubset : MeasurableSet
        {A : CompactResidual K |
          (A : Set K) ∩ (Q : Set K) ⊆ Uall} :=
      measurableSet_compactIntersection_subset_open Q hUall
    have hhits : MeasurableSet
        (⋂ U ∈ u,
          {A : CompactResidual K |
            ((A : Set K) ∩ ((Q : Set K) ∩ U)).Nonempty}) :=
      huFinite.measurableSet_biInter fun U hU =>
        measurableSet_compact_inter_hits_open Q (huOpen hU)
    have heq :
        (fun A : CompactResidual K => compactIntersection A Q) ⁻¹'
            {A : CompactResidual K |
              (A : Set K) ⊆ ⋃₀ u ∧
                ∀ U ∈ u, ((A : Set K) ∩ U).Nonempty} =
          {A : CompactResidual K |
            (A : Set K) ∩ (Q : Set K) ⊆ Uall} ∩
          ⋂ U ∈ u,
            {A : CompactResidual K |
              ((A : Set K) ∩ ((Q : Set K) ∩ U)).Nonempty} := by
      ext A
      simp only [mem_preimage, mem_setOf_eq, mem_inter_iff, mem_iInter,
        coe_compactIntersection, Uall]
      constructor
      · rintro ⟨hsub, hhit⟩
        refine ⟨hsub, fun U hU => ?_⟩
        simpa only [inter_assoc] using hhit U hU
      · rintro ⟨hsub, hhit⟩
        refine ⟨hsub, fun U hU => ?_⟩
        simpa only [inter_assoc] using hhit U hU
    rw [heq]
    exact hsubset.inter hhits
  change @Measurable (CompactResidual K) (CompactResidual K)
    (CompactResidual.instMeasurableSpace K) (borel (CompactResidual K))
    (fun A => compactIntersection A Q)
  rw [hgen]
  exact hm

end Shepp.Section5
end SheppFlattenedModule044

section SheppFlattenedModule045
open scoped ENNReal Topology
open MeasureTheory Set

namespace Shepp.Section5

open Shepp.Section2 Shepp.Section3 Shepp.Section4 TopologicalSpace

theorem isOpen_finiteCloudCovered
    {ι K : Type*} [Fintype ι] [PseudoMetricSpace K]
    (radius : ι → ℝ) (ω : FiniteCloudSample ι K) :
    IsOpen (finiteCloudCovered radius ω) := by
  unfold finiteCloudCovered
  exact isOpen_iUnion fun i => isOpen_iUnion fun j => Metric.isOpen_ball

noncomputable def compactDeleteFiniteCloud
    {ι K : Type*} [Fintype ι] [MetricSpace K]
    (radius : ι → ℝ) (A : CompactResidual K)
    (ω : FiniteCloudSample ι K) : CompactResidual K :=
  ⟨(A : Set K) \ finiteCloudCovered radius ω,
    A.isCompact.inter_right (isOpen_finiteCloudCovered radius ω).isClosed_compl⟩

@[simp] theorem coe_compactDeleteFiniteCloud
    {ι K : Type*} [Fintype ι] [MetricSpace K]
    (radius : ι → ℝ) (A : CompactResidual K)
    (ω : FiniteCloudSample ι K) :
    ((compactDeleteFiniteCloud radius A ω : CompactResidual K) : Set K) =
      (A : Set K) \ finiteCloudCovered radius ω :=
  rfl

theorem compactDeleteFiniteCloud_le
    {ι K : Type*} [Fintype ι] [MetricSpace K]
    (radius : ι → ℝ) (A : CompactResidual K)
    (ω : FiniteCloudSample ι K) :
    compactDeleteFiniteCloud radius A ω ≤ A := by
  intro x hx
  exact hx.1

theorem isClosed_compactResidual_membership
    {K : Type*} [MetricSpace K] :
    IsClosed
      {p : CompactResidual K × K | p.2 ∈ (p.1 : Set K)} := by
  let e : CompactResidual K × K → ℝ≥0∞ := fun p =>
    Metric.infEDist p.2 (p.1 : Set K)
  have he : Continuous e := by
    exact TopologicalSpace.Closeds.continuous_infEDist.comp
      (continuous_snd.prodMk
        (Compacts.isometry_toCloseds.continuous.comp continuous_fst))
  have hset :
      {p : CompactResidual K × K | p.2 ∈ (p.1 : Set K)} =
        e ⁻¹' ({0} : Set ℝ≥0∞) := by
    ext p
    change p.2 ∈ (p.1 : Set K) ↔ Metric.infEDist p.2 (p.1 : Set K) = 0
    exact Metric.mem_iff_infEDist_zero_of_closed p.1.isCompact.isClosed
  rw [hset]
  exact isClosed_singleton.preimage he

abbrev CompactCloudParameter (ι K : Type*) [TopologicalSpace K] :=
  CompactResidual K × FiniteCloudSample ι K

def finiteCloudClosedWitness
    {ι K : Type*} [Fintype ι] [MetricSpace K]
    (radius : ι → ℝ) (q : ι → ℕ) (C : Set K) :
    Set (CompactCloudParameter ι K × K) :=
  {z | z.2 ∈ (z.1.1 : Set K) ∧ z.2 ∈ C ∧
    (∀ i, (z.1.2 i).1 = q i) ∧
    ∀ i (j : Fin (q i)),
      radius i ≤ dist z.2 ((z.1.2 i).2 j)}

theorem isClosed_finiteCloudClosedWitness
    {ι K : Type*} [Fintype ι] [MetricSpace K]
    (radius : ι → ℝ) (q : ι → ℕ) {C : Set K} (hC : IsClosed C) :
    IsClosed (finiteCloudClosedWitness radius q C) := by
  let parameter : Type _ := CompactCloudParameter ι K
  have hmem : IsClosed
      {z : parameter × K | z.2 ∈ (z.1.1 : Set K)} := by
    exact isClosed_compactResidual_membership.preimage
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hCmem : IsClosed {z : parameter × K | z.2 ∈ C} :=
    hC.preimage continuous_snd
  have hcount : IsClosed
      {z : parameter × K | ∀ i, (z.1.2 i).1 = q i} := by
    rw [show {z : parameter × K | ∀ i, (z.1.2 i).1 = q i} =
        ⋂ i, {z : parameter × K | (z.1.2 i).1 = q i} by
      ext z
      simp]
    apply isClosed_iInter
    intro i
    have hcontinuous : Continuous fun z : parameter × K => (z.1.2 i).1 :=
      continuous_fst.comp
        ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
    exact isClosed_singleton.preimage hcontinuous
  have havoid : IsClosed
      {z : parameter × K | ∀ i (j : Fin (q i)),
        radius i ≤ dist z.2 ((z.1.2 i).2 j)} := by
    rw [show {z : parameter × K | ∀ i (j : Fin (q i)),
        radius i ≤ dist z.2 ((z.1.2 i).2 j)} =
      ⋂ i, ⋂ j : Fin (q i),
        {z : parameter × K |
          radius i ≤ dist z.2 ((z.1.2 i).2 j)} by
      ext z
      simp]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    have hcenter : Continuous fun z : parameter × K => (z.1.2 i).2 j :=
      (continuous_apply (j : ℕ)).comp
        (continuous_snd.comp
          ((continuous_apply i).comp (continuous_snd.comp continuous_fst)))
    exact isClosed_Ici.preimage (continuous_snd.dist hcenter)
  rw [show finiteCloudClosedWitness radius q C =
      ({z : CompactCloudParameter ι K × K |
        z.2 ∈ (z.1.1 : Set K)} ∩
        {z | z.2 ∈ C} ∩
        {z | ∀ i, (z.1.2 i).1 = q i} ∩
        {z | ∀ i (j : Fin (q i)),
          radius i ≤ dist z.2 ((z.1.2 i).2 j)}) by
    ext z
    simp only [finiteCloudClosedWitness, mem_setOf_eq, mem_inter_iff]
    tauto]
  exact ((hmem.inter hCmem).inter hcount).inter havoid

def finiteCloudClosedHitEvent
    {ι K : Type*} [Fintype ι] [MetricSpace K]
    (radius : ι → ℝ) (q : ι → ℕ) (C : Set K) :
    Set (CompactCloudParameter ι K) :=
  Prod.fst '' finiteCloudClosedWitness radius q C

theorem isClosed_finiteCloudClosedHitEvent
    {ι K : Type*} [Fintype ι] [MetricSpace K] [CompactSpace K]
    (radius : ι → ℝ) (q : ι → ℕ) {C : Set K} (hC : IsClosed C) :
    IsClosed (finiteCloudClosedHitEvent radius q C) := by
  exact isClosedMap_fst_of_compactSpace _
    (isClosed_finiteCloudClosedWitness radius q hC)

theorem mem_finiteCloudClosedHitEvent_iff
    {ι K : Type*} [Fintype ι] [MetricSpace K]
    (radius : ι → ℝ) (q : ι → ℕ) (C : Set K)
    (p : CompactCloudParameter ι K) :
    p ∈ finiteCloudClosedHitEvent radius q C ↔
      (∀ i, (p.2 i).1 = q i) ∧
      (((compactDeleteFiniteCloud radius p.1 p.2 : CompactResidual K) : Set K) ∩ C).Nonempty := by
  constructor
  · rintro ⟨⟨p', z⟩, hz, hp⟩
    simp only at hp
    subst p'
    rcases hz with ⟨hxA, hxC, hcount, havoid⟩
    refine ⟨hcount, z, ?_, hxC⟩
    refine ⟨hxA, ?_⟩
    intro hzCovered
    simp only [finiteCloudCovered, mem_iUnion, Metric.mem_ball] at hzCovered
    obtain ⟨i, j, hjball⟩ := hzCovered
    let jq : Fin (q i) :=
      ⟨j, by simpa only [← hcount i] using j.isLt⟩
    have hfar := havoid i jq
    have hcenter : (p.2 i).2 jq = (p.2 i).2 j := by rfl
    rw [hcenter] at hfar
    exact (not_lt_of_ge hfar) hjball
  · rintro ⟨hcount, x, hxResidual, hxC⟩
    refine ⟨(p, x), ?_, rfl⟩
    refine ⟨hxResidual.1, hxC, hcount, ?_⟩
    intro i j
    by_contra hdist
    have hball : x ∈ Metric.ball ((p.2 i).2 j) (radius i) := by
      rw [Metric.mem_ball]
      exact lt_of_not_ge hdist
    apply hxResidual.2
    simp only [finiteCloudCovered, mem_iUnion]
    let jc : Fin (p.2 i).1 :=
      ⟨j, by simpa only [hcount i] using j.isLt⟩
    exact ⟨i, jc, by simpa only [jc] using hball⟩

theorem measurableSet_compactDelete_hits_open
    {ι K : Type*} [Fintype ι] [MetricSpace K] [CompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (radius : ι → ℝ) {U : Set K} (hU : IsOpen U) :
    MeasurableSet
      {p : CompactCloudParameter ι K |
        (((compactDeleteFiniteCloud radius p.1 p.2 : CompactResidual K) : Set K) ∩ U).Nonempty} := by
  by_cases hUtop : U = univ
  · subst U
    have heq :
        {p : CompactCloudParameter ι K |
          (((compactDeleteFiniteCloud radius p.1 p.2 : CompactResidual K) : Set K) ∩ univ).Nonempty} =
        ⋃ q : ι → ℕ, finiteCloudClosedHitEvent radius q univ := by
      ext p
      simp only [mem_setOf_eq, inter_univ, mem_iUnion]
      constructor
      · intro hp
        let q : ι → ℕ := fun i => (p.2 i).1
        exact ⟨q, (mem_finiteCloudClosedHitEvent_iff radius q univ p).2
          ⟨fun _ => rfl, by simpa using hp⟩⟩
      · rintro ⟨q, hp⟩
        exact (mem_finiteCloudClosedHitEvent_iff radius q univ p).1 hp |>.2.mono
          inter_subset_left
    rw [heq]
    exact MeasurableSet.iUnion fun q =>
      (isClosed_finiteCloudClosedHitEvent radius q isClosed_univ).measurableSet
  · have hUc : Uᶜ.Nonempty := Set.nonempty_compl.2 hUtop
    have heq :
        {p : CompactCloudParameter ι K |
          (((compactDeleteFiniteCloud radius p.1 p.2 : CompactResidual K) : Set K) ∩ U).Nonempty} =
        ⋃ q : ι → ℕ, ⋃ n : ℕ,
          finiteCloudClosedHitEvent radius q
            (compactOpenCore (⊤ : CompactResidual K) U n) := by
      ext p
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨x, hxResidual, hxU⟩
        have hxCores : x ∈ ⋃ n : ℕ,
            compactOpenCore (⊤ : CompactResidual K) U n := by
          rw [iUnion_compactOpenCore (⊤ : CompactResidual K) hU hUc]
          exact ⟨by simp, hxU⟩
        rw [mem_iUnion] at hxCores
        obtain ⟨n, hxn⟩ := hxCores
        let q : ι → ℕ := fun i => (p.2 i).1
        exact ⟨q, n,
          (mem_finiteCloudClosedHitEvent_iff radius q _ p).2
            ⟨fun _ => rfl, x, hxResidual, hxn⟩⟩
      · rintro ⟨q, n, hp⟩
        rcases (mem_finiteCloudClosedHitEvent_iff radius q _ p).1 hp with
          ⟨_hcount, x, hxResidual, hxn⟩
        refine ⟨x, hxResidual, ?_⟩
        have hxUnion : x ∈ ⋃ n : ℕ,
            compactOpenCore (⊤ : CompactResidual K) U n :=
          mem_iUnion.2 ⟨n, hxn⟩
        rw [iUnion_compactOpenCore (⊤ : CompactResidual K) hU hUc] at hxUnion
        exact hxUnion.2
    rw [heq]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun n =>
      (isClosed_finiteCloudClosedHitEvent radius q
        (isClosed_compactOpenCore (⊤ : CompactResidual K) U n)).measurableSet

theorem measurableSet_compactDelete_subset_open
    {ι K : Type*} [Fintype ι] [MetricSpace K] [CompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (radius : ι → ℝ) {U : Set K} (hU : IsOpen U) :
    MeasurableSet
      {p : CompactCloudParameter ι K |
        ((compactDeleteFiniteCloud radius p.1 p.2 : CompactResidual K) : Set K) ⊆ U} := by
  have heq :
      {p : CompactCloudParameter ι K |
        ((compactDeleteFiniteCloud radius p.1 p.2 : CompactResidual K) : Set K) ⊆ U} =
      (⋃ q : ι → ℕ,
        finiteCloudClosedHitEvent radius q Uᶜ)ᶜ := by
    ext p
    constructor
    · intro hp
      simp only [mem_compl_iff, mem_iUnion, not_exists]
      intro q hq
      rcases (mem_finiteCloudClosedHitEvent_iff radius q Uᶜ p).1 hq with
        ⟨_hcount, x, hxResidual, hxUc⟩
      exact hxUc (hp hxResidual)
    · intro hp x hxResidual
      by_contra hxU
      have hxUc : x ∈ Uᶜ := hxU
      let q : ι → ℕ := fun i => (p.2 i).1
      have hhit : p ∈ finiteCloudClosedHitEvent radius q Uᶜ :=
        (mem_finiteCloudClosedHitEvent_iff radius q Uᶜ p).2
          ⟨fun _ => rfl, x, hxResidual, hxUc⟩
      exact hp (mem_iUnion.2 ⟨q, hhit⟩)
  rw [heq]
  exact (MeasurableSet.iUnion fun q =>
    (isClosed_finiteCloudClosedHitEvent radius q
      hU.isClosed_compl).measurableSet).compl

theorem measurable_compactDeleteFiniteCloud
    {ι K : Type*} [Fintype ι] [MetricSpace K] [CompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (radius : ι → ℝ) :
    Measurable fun p : CompactCloudParameter ι K =>
      compactDeleteFiniteCloud radius p.1 p.2 := by
  let basis : Set (Set (CompactResidual K)) :=
    (fun u : Set (Set K) =>
      {A : CompactResidual K |
        (A : Set K) ⊆ ⋃₀ u ∧
          ∀ U ∈ u, ((A : Set K) ∩ U).Nonempty}) ''
      {u : Set (Set K) | u.Finite ∧ u ⊆ {U | IsOpen U}}
  have hbasis : IsTopologicalBasis basis := by
    simpa only [basis] using
      (isTopologicalBasis_opens.compacts (α := K))
  have hgen : borel (CompactResidual K) =
      MeasurableSpace.generateFrom basis :=
    hbasis.borel_eq_generateFrom
  have hm : @Measurable (CompactCloudParameter ι K) (CompactResidual K)
      (inferInstance : MeasurableSpace (CompactCloudParameter ι K))
      (MeasurableSpace.generateFrom basis)
      (fun p => compactDeleteFiniteCloud radius p.1 p.2) := by
    apply measurable_generateFrom
    intro V hV
    rcases hV with ⟨u, ⟨huFinite, huOpen⟩, rfl⟩
    let Uall : Set K := ⋃₀ u
    have hUall : IsOpen Uall :=
      isOpen_sUnion fun U hU => huOpen hU
    have hsubset : MeasurableSet
        {p : CompactCloudParameter ι K |
          ((compactDeleteFiniteCloud radius p.1 p.2 : CompactResidual K) : Set K) ⊆ Uall} :=
      measurableSet_compactDelete_subset_open radius hUall
    have hhits : MeasurableSet
        (⋂ U ∈ u,
          {p : CompactCloudParameter ι K |
            (((compactDeleteFiniteCloud radius p.1 p.2 : CompactResidual K) : Set K) ∩ U).Nonempty}) :=
      huFinite.measurableSet_biInter fun U hU =>
        measurableSet_compactDelete_hits_open radius (huOpen hU)
    have heq :
        (fun p : CompactCloudParameter ι K =>
          compactDeleteFiniteCloud radius p.1 p.2) ⁻¹'
            {A : CompactResidual K |
              (A : Set K) ⊆ ⋃₀ u ∧
                ∀ U ∈ u, ((A : Set K) ∩ U).Nonempty} =
          {p : CompactCloudParameter ι K |
            ((compactDeleteFiniteCloud radius p.1 p.2 : CompactResidual K) : Set K) ⊆ Uall} ∩
          ⋂ U ∈ u,
            {p : CompactCloudParameter ι K |
              (((compactDeleteFiniteCloud radius p.1 p.2 : CompactResidual K) : Set K) ∩ U).Nonempty} := by
      ext p
      simp only [mem_preimage, mem_setOf_eq, mem_inter_iff, mem_iInter, Uall]
    rw [heq]
    exact hsubset.inter hhits
  change @Measurable (CompactCloudParameter ι K) (CompactResidual K)
    (inferInstance : MeasurableSpace (CompactCloudParameter ι K))
    (borel (CompactResidual K))
    (fun p => compactDeleteFiniteCloud radius p.1 p.2)
  rw [hgen]
  exact hm

end Shepp.Section5
end SheppFlattenedModule045

section SheppFlattenedModule046
open scoped Topology
open MeasureTheory Set

namespace Shepp.Section5

open Shepp.Section2 Shepp.Section3 Shepp.Section4 TopologicalSpace

noncomputable def compactGridCell
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) : CompactResidual (FlatTorus d) :=
  ⟨gridCell P k α, isCompact_gridCell P k α⟩

@[simp] theorem coe_compactGridCell
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) :
    ((compactGridCell P k α : CompactResidual (FlatTorus d)) :
        Set (FlatTorus d)) = gridCell P k α :=
  rfl

abbrev SpatialLabel
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :=
  Σ k : ℕ, GridLabel P k

abbrev SpatialFiber
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (label : SpatialLabel P) :=
  {A : CompactResidual (FlatTorus d) //
    (A : Set (FlatTorus d)) ⊆ gridCell P label.1 label.2}

abbrev SpatialParticle
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :=
  Σ label : SpatialLabel P, SpatialFiber P label

noncomputable def SpatialParticle.level
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (x : SpatialParticle P) : ℕ :=
  x.1.1

noncomputable def SpatialParticle.label
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (x : SpatialParticle P) : GridLabel P x.level :=
  x.1.2

noncomputable def SpatialParticle.residual
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (x : SpatialParticle P) : CompactResidual (FlatTorus d) :=
  x.2.1

theorem SpatialParticle.residual_subset_cell
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (x : SpatialParticle P) :
    (x.residual : Set (FlatTorus d)) ⊆ gridCell P x.level x.label :=
  x.2.2

def spatialParticleLE
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (x y : SpatialParticle P) : Prop :=
  x.1 = y.1 ∧ x.residual ≤ y.residual

noncomputable abbrev spatialParticlePartialOrder
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    PartialOrder (SpatialParticle P) where
  le := spatialParticleLE
  lt := fun x y => spatialParticleLE x y ∧ ¬spatialParticleLE y x
  le_refl x := ⟨rfl, le_rfl⟩
  le_trans x y z hxy hyz :=
    ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩
  le_antisymm x y hxy hyx := by
    rcases x with ⟨xLabel, xResidual⟩
    rcases y with ⟨yLabel, yResidual⟩
    have hLabel : xLabel = yLabel := hxy.1
    subst yLabel
    have hResidual : xResidual = yResidual :=
      Subtype.ext (le_antisymm hxy.2 hyx.2)
    subst yResidual
    rfl
  lt_iff_le_not_ge := fun _ _ => Iff.rfl

theorem spatialParticle_le_iff
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    {x y : SpatialParticle P} :
    @LE.le _ (spatialParticlePartialOrder P).toPreorder.toLE x y ↔
      x.1 = y.1 ∧ x.residual ≤ y.residual :=
  Iff.rfl

def spatialAugmentedLE
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r} :
    AugmentedState (SpatialParticle P) →
      AugmentedState (SpatialParticle P) → Prop
  | Sum.inr _, _ => True
  | Sum.inl x, Sum.inl y => spatialParticleLE x y
  | Sum.inl _, Sum.inr _ => False

noncomputable abbrev spatialAugmentedPartialOrder
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    PartialOrder (AugmentedState (SpatialParticle P)) where
  le := spatialAugmentedLE
  lt := fun x y => spatialAugmentedLE x y ∧ ¬spatialAugmentedLE y x
  le_refl x := by
    cases x with
    | inl x => exact (spatialParticlePartialOrder P).le_refl x
    | inr _ => trivial
  le_trans x y z hxy hyz := by
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            cases z with
            | inl z =>
                exact (spatialParticlePartialOrder P).le_trans x y z hxy hyz
            | inr _ => exact hyz.elim
        | inr _ => exact hxy.elim
    | inr _ => trivial
  le_antisymm x y hxy hyx := by
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            exact congrArg Sum.inl
              ((spatialParticlePartialOrder P).le_antisymm x y hxy hyx)
        | inr _ => exact hxy.elim
    | inr x =>
        cases y with
        | inl _ => exact hyx.elim
        | inr y => cases x; cases y; rfl
  lt_iff_le_not_ge := fun _ _ => Iff.rfl

@[simp] theorem cemetery_le_spatialState
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (z : AugmentedState (SpatialParticle P)) :
    @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE
      cemetery z := by
  change spatialAugmentedLE cemetery z
  cases z <;> simp [spatialAugmentedLE, cemetery]

@[simp] theorem spatial_live_le_live_iff
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    {x y : SpatialParticle P} :
    @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE
        (Sum.inl x) (Sum.inl y) ↔
      @LE.le _ (spatialParticlePartialOrder P).toPreorder.toLE x y := by
  rfl

@[simp] theorem spatial_live_not_le_cemetery
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (x : SpatialParticle P) :
    ¬@LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE
      (Sum.inl x) cemetery := by
  change ¬spatialAugmentedLE (Sum.inl x) cemetery
  simp [spatialAugmentedLE, cemetery]

noncomputable def spatialState
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (A : CompactResidual (FlatTorus d)) :
    AugmentedState (SpatialParticle P) := by
  classical
  let B := compactIntersection A (compactGridCell P k α)
  exact if _hB : B = ⊥ then cemetery
    else
      Sum.inl ⟨⟨k, α⟩, ⟨B, by
        intro x hx
        exact hx.2⟩⟩

theorem spatialState_eq_cemetery_iff
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (A : CompactResidual (FlatTorus d)) :
    spatialState P k α A = cemetery ↔
      compactIntersection A (compactGridCell P k α) = ⊥ := by
  classical
  unfold spatialState
  by_cases hB : compactIntersection A (compactGridCell P k α) = ⊥
  · simp [hB]
  · simp [hB, cemetery]

theorem spatialState_ne_cemetery_iff
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (A : CompactResidual (FlatTorus d)) :
    spatialState P k α A ≠ cemetery ↔
      compactIntersection A (compactGridCell P k α) ≠ ⊥ := by
  rw [ne_eq, spatialState_eq_cemetery_iff]

theorem spatialState_eq_live_of_nonempty
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (A : CompactResidual (FlatTorus d))
    (hA : compactIntersection A (compactGridCell P k α) ≠ ⊥) :
    spatialState P k α A =
      Sum.inl ⟨⟨k, α⟩,
        ⟨compactIntersection A (compactGridCell P k α), by
          intro x hx
          exact hx.2⟩⟩ := by
  simp [spatialState, hA]

theorem compactIntersection_mono_left
    {K : Type*} [MetricSpace K]
    {A B Q : CompactResidual K} (hAB : A ≤ B) :
    compactIntersection A Q ≤ compactIntersection B Q := by
  exact inf_le_inf hAB le_rfl

theorem spatialState_mono
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) {A B : CompactResidual (FlatTorus d)}
    (hAB : A ≤ B) :
    @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE
      (spatialState P k α A) (spatialState P k α B) := by
  classical
  by_cases hA : compactIntersection A (compactGridCell P k α) = ⊥
  · rw [(spatialState_eq_cemetery_iff P k α A).2 hA]
    exact cemetery_le_spatialState _
  · have hB : compactIntersection B (compactGridCell P k α) ≠ ⊥ := by
      intro hB
      have hle := compactIntersection_mono_left
        (Q := compactGridCell P k α) hAB
      rw [hB] at hle
      exact hA (bot_unique hle)
    rw [spatialState_eq_live_of_nonempty P k α A hA,
      spatialState_eq_live_of_nonempty P k α B hB]
    change spatialParticleLE _ _
    exact ⟨rfl, compactIntersection_mono_left hAB⟩

theorem measurable_sigmaMk
    {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)] (i : ι) :
    Measurable (@Sigma.mk ι β i) := by
  apply Measurable.of_le_map
  exact iInf_le (fun j => MeasurableSpace.map (Sigma.mk j) inferInstance) i

theorem measurableSet_sigma_iff
    {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {s : Set (Σ i, β i)} :
    MeasurableSet s ↔ ∀ i, MeasurableSet (Sigma.mk i ⁻¹' s) := by
  change MeasurableSet[
      (⨅ i, MeasurableSpace.map (Sigma.mk i) inferInstance)] s ↔ _
  rw [MeasurableSpace.measurableSet_iInf]
  rfl

theorem measurable_sigmaElim
    {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {γ : Type*} [MeasurableSpace γ] {f : (Σ i, β i) → γ}
    (hf : ∀ i, Measurable fun b => f ⟨i, b⟩) : Measurable f := by
  intro s hs
  rw [measurableSet_sigma_iff]
  intro i
  exact hf i hs

theorem measurableEmbedding_sigmaMk
    {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)] (i : ι) :
    MeasurableEmbedding (@Sigma.mk ι β i) where
  injective := sigma_mk_injective
  measurable := measurable_sigmaMk i
  measurableSet_image' := by
    intro s hs
    rw [measurableSet_sigma_iff]
    intro j
    classical
    by_cases hji : j = i
    · subst j
      rw [sigma_mk_injective.preimage_image]
      exact hs
    · have hempty :
          Sigma.mk j ⁻¹' Sigma.mk i '' s = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_image,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨y, _hy, hxy⟩
        exact hji (congrArg Sigma.fst hxy).symm
      rw [hempty]
      exact MeasurableSet.empty

theorem measurable_sigmaProdDistrib
    {ι : Type*} [Countable ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] {γ : Type*} [MeasurableSpace γ] :
    Measurable (Equiv.sigmaProdDistrib β γ) := by
  intro s hs
  have hsFiber : ∀ i, MeasurableSet
      ((@Sigma.mk ι (fun i => β i × γ) i) ⁻¹' s) :=
    measurableSet_sigma_iff.mp hs
  let embed : (i : ι) → β i × γ → (Σ i, β i) × γ :=
    fun i p => (⟨i, p.1⟩, p.2)
  have hEmbed : ∀ i, MeasurableEmbedding (embed i) := by
    intro i
    exact (measurableEmbedding_sigmaMk i).prodMap MeasurableEmbedding.id
  have heq :
      (Equiv.sigmaProdDistrib β γ) ⁻¹' s =
        ⋃ i, embed i ''
          ((@Sigma.mk ι (fun i => β i × γ) i) ⁻¹' s) := by
    ext p
    rcases p with ⟨⟨i, b⟩, c⟩
    constructor
    · intro hp
      exact Set.mem_iUnion.2 ⟨i, ⟨(b, c), hp, rfl⟩⟩
    · intro hp
      rcases Set.mem_iUnion.1 hp with ⟨j, q, hq, hqeq⟩
      cases hqeq
      exact hq
  rw [heq]
  exact MeasurableSet.iUnion fun i => (hEmbed i).measurableSet_image' (hsFiber i)

theorem measurable_sigmaProdElim
    {ι : Type*} [Countable ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] {γ δ : Type*}
    [MeasurableSpace γ] [MeasurableSpace δ]
    {f : (Σ i, β i) × γ → δ}
    (hf : ∀ i, Measurable fun p : β i × γ => f (⟨i, p.1⟩, p.2)) :
    Measurable f := by
  let g : (Σ i, β i × γ) → δ := fun p => f (⟨p.1, p.2.1⟩, p.2.2)
  have hg : Measurable g := measurable_sigmaElim hf
  have hcomp := hg.comp (measurable_sigmaProdDistrib (β := β) (γ := γ))
  have heq : g ∘ (Equiv.sigmaProdDistrib β γ) = f := by
    funext p
    rcases p with ⟨⟨i, b⟩, c⟩
    rfl
  rw [← heq]
  exact hcomp

theorem measurable_sumProdElim
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    {f : (α ⊕ β) × γ → δ}
    (hl : Measurable fun p : α × γ => f (Sum.inl p.1, p.2))
    (hr : Measurable fun p : β × γ => f (Sum.inr p.1, p.2)) :
    Measurable f := by
  have h := (hl.sumElim hr).comp
    (MeasurableEquiv.sumProdDistrib α β γ).measurable
  have heq :
      (Sum.elim (fun p : α × γ => f (Sum.inl p.1, p.2))
        (fun p : β × γ => f (Sum.inr p.1, p.2))) ∘
          (MeasurableEquiv.sumProdDistrib α β γ) = f := by
    funext p
    rcases p with ⟨x, c⟩
    cases x <;> rfl
  rw [← heq]
  exact h

theorem measurable_spatialState
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) :
    Measurable fun A : CompactResidual (FlatTorus d) =>
      spatialState P k α A := by
  classical
  let Q := compactGridCell P k α
  let clip : CompactResidual (FlatTorus d) → CompactResidual (FlatTorus d) :=
    fun A => compactIntersection A Q
  have hclip : Measurable clip :=
    measurable_compactIntersection_right Q
  have hempty : MeasurableSet {A : CompactResidual (FlatTorus d) | clip A = ⊥} :=
    (measurableSet_singleton (⊥ : CompactResidual (FlatTorus d))).preimage hclip
  have hlive : Measurable fun A : CompactResidual (FlatTorus d) =>
      (Sum.inl
        (⟨⟨k, α⟩, ⟨clip A, by
          intro x hx
          exact hx.2⟩⟩ : SpatialParticle P) :
        AugmentedState (SpatialParticle P)) := by
    apply measurable_inl.comp
    apply (measurable_sigmaMk (β := SpatialFiber P) (⟨k, α⟩ : SpatialLabel P)).comp
    exact Measurable.subtype_mk hclip
  change Measurable fun A : CompactResidual (FlatTorus d) =>
    if _hB : clip A = ⊥ then cemetery else
      Sum.inl (⟨⟨k, α⟩, ⟨clip A, by
        intro x hx
        exact hx.2⟩⟩ : SpatialParticle P)
  exact Measurable.ite hempty measurable_const hlive

end Shepp.Section5
end SheppFlattenedModule046

section SheppFlattenedModule047
open MeasureTheory

namespace Shepp.Section4

theorem AssociatedFunction.comp_monotone
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Preorder A] [Preorder B]
    {f : B → ℝ} (hf : AssociatedFunction f)
    {φ : A → B} (hφmeas : Measurable φ) (hφmono : Monotone φ) :
    AssociatedFunction (f ∘ φ) := by
  refine ⟨hf.measurable.comp hφmeas, fun a => hf.nonnegative (φ a),
    hf.monotone.comp hφmono, ?_⟩
  rcases hf.bounded with ⟨C, hC0, hC⟩
  exact ⟨C, hC0, fun a => hC (φ a)⟩

theorem positivelyAssociated_dirac
    {W : Type*} [MeasurableSpace W] [Preorder W] (w : W) :
    PositivelyAssociated (Measure.dirac w) := by
  intro f g hf hg
  rw [MeasureTheory.integral_dirac' f w hf.measurable.stronglyMeasurable,
    MeasureTheory.integral_dirac' g w hg.measurable.stronglyMeasurable,
    MeasureTheory.integral_dirac' (fun u => f u * g u) w
      (hf.measurable.mul hg.measurable).stronglyMeasurable]

theorem PositivelyAssociated.map
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Preorder A] [Preorder B]
    {μ : Measure A} (hμ : PositivelyAssociated μ)
    [IsProbabilityMeasure μ]
    {φ : A → B} (hφmeas : Measurable φ) (hφmono : Monotone φ) :
    PositivelyAssociated (Measure.map φ μ) := by
  intro f g hf hg
  have hfcomp := hf.comp_monotone hφmeas hφmono
  have hgcomp := hg.comp_monotone hφmeas hφmono
  rw [MeasureTheory.integral_map_of_stronglyMeasurable hφmeas
      hf.measurable.stronglyMeasurable,
    MeasureTheory.integral_map_of_stronglyMeasurable hφmeas
      hg.measurable.stronglyMeasurable]
  have hmapfg :
      (∫ w, f w * g w ∂Measure.map φ μ) =
        ∫ a, f (φ a) * g (φ a) ∂μ :=
    MeasureTheory.integral_map_of_stronglyMeasurable hφmeas
      (hf.measurable.mul hg.measurable).stronglyMeasurable
  rw [hmapfg]
  exact hμ (f ∘ φ) (g ∘ φ) hfcomp hgcomp

private theorem associatedFunction_prod_slice_right
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Preorder A] [Preorder B]
    {f : A × B → ℝ} (hf : AssociatedFunction f) (a : A) :
    AssociatedFunction (fun b => f (a, b)) := by
  refine ⟨hf.measurable.comp (measurable_const.prodMk measurable_id),
    fun b => hf.nonnegative (a, b), ?_, ?_⟩
  · intro b b' hbb'
    exact hf.monotone ⟨le_rfl, hbb'⟩
  · rcases hf.bounded with ⟨C, hC0, hC⟩
    exact ⟨C, hC0, fun b => hC (a, b)⟩

private theorem associatedFunction_integral_prod_right
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Preorder A] [Preorder B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    {f : A × B → ℝ} (hf : AssociatedFunction f) :
    AssociatedFunction (fun a => ∫ b, f (a, b) ∂ν) := by
  let F : A → ℝ := fun a => ∫ b, f (a, b) ∂ν
  have hslice : ∀ a, AssociatedFunction (fun b => f (a, b)) :=
    associatedFunction_prod_slice_right hf
  refine ⟨hf.measurable.stronglyMeasurable.integral_prod_right'.measurable,
    fun a => (hslice a).integral_nonneg, ?_, ?_⟩
  · intro a a' haa'
    exact integral_mono (hslice a).integrable (hslice a').integrable
      (fun b => hf.monotone ⟨haa', le_rfl⟩)
  · rcases hf.bounded with ⟨C, hC0, hC⟩
    refine ⟨C, hC0, fun a => ?_⟩
    calc
      F a ≤ ∫ _b : B, C ∂ν :=
        integral_mono (hslice a).integrable (integrable_const C) (fun b => hC (a, b))
      _ = C := by simp [probReal_univ]

theorem PositivelyAssociated.prod
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Preorder A] [Preorder B]
    (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : PositivelyAssociated μ) (hν : PositivelyAssociated ν) :
    PositivelyAssociated (μ.prod ν) := by
  intro f g hf hg
  let F : A → ℝ := fun a => ∫ b, f (a, b) ∂ν
  let G : A → ℝ := fun a => ∫ b, g (a, b) ∂ν
  have hF : AssociatedFunction F :=
    associatedFunction_integral_prod_right ν hf
  have hG : AssociatedFunction G :=
    associatedFunction_integral_prod_right ν hg
  have hfg : AssociatedFunction (fun z => f z * g z) := hf.mul hg
  have hinner : ∀ a, F a * G a ≤ ∫ b, f (a, b) * g (a, b) ∂ν := by
    intro a
    exact hν (fun b => f (a, b)) (fun b => g (a, b))
      (associatedFunction_prod_slice_right hf a)
      (associatedFunction_prod_slice_right hg a)
  calc
    (∫ z, f z ∂μ.prod ν) * (∫ z, g z ∂μ.prod ν) =
        (∫ a, F a ∂μ) * (∫ a, G a ∂μ) := by
      rw [MeasureTheory.integral_prod f hf.integrable,
        MeasureTheory.integral_prod g hg.integrable]
    _ ≤ ∫ a, F a * G a ∂μ := hμ F G hF hG
    _ ≤ ∫ a, ∫ b, f (a, b) * g (a, b) ∂ν ∂μ := by
      exact integral_mono (hF.mul hG).integrable
        hfg.integrable.integral_prod_left hinner
    _ = ∫ z, f z * g z ∂μ.prod ν :=
      (MeasureTheory.integral_prod (fun z => f z * g z) hfg.integrable).symm

theorem positivelyAssociated_of_subsingleton
    {W : Type*} [MeasurableSpace W] [Preorder W]
    [Subsingleton W] [Nonempty W]
    (μ : Measure W) [IsProbabilityMeasure μ] :
    PositivelyAssociated μ := by
  let w : W := Classical.choice (inferInstance : Nonempty W)
  intro f g hf hg
  have hfw : f = fun _ => f w := by
    funext u
    exact congrArg f (Subsingleton.elim u w)
  have hgw : g = fun _ => g w := by
    funext u
    exact congrArg g (Subsingleton.elim u w)
  rw [hfw, hgw]
  simp [integral_const, probReal_univ]

theorem positivelyAssociated_pi_fin
    {X : Type*} [MeasurableSpace X] [Preorder X]
    {n : ℕ} (μ : Fin n → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, PositivelyAssociated (μ i)) :
    PositivelyAssociated (Measure.pi μ) := by
  induction n with
  | zero =>
      exact positivelyAssociated_of_subsingleton (Measure.pi μ)
  | succ n ih =>
      let tail : Fin n → Measure X := fun i => μ (Fin.succAbove 0 i)
      have htail : ∀ i, PositivelyAssociated (tail i) := fun i => hμ _
      have hassocTail : PositivelyAssociated (Measure.pi tail) := ih tail htail
      have hassocProd :
          PositivelyAssociated ((μ 0).prod (Measure.pi tail)) :=
        PositivelyAssociated.prod (μ 0) (Measure.pi tail) (hμ 0) hassocTail
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      have hemono : Monotone e.symm := by
        intro a b hab
        exact (Fin.insertNthOrderIso (fun _ : Fin (n + 1) => X) 0).monotone hab
      have hmapped := hassocProd.map e.symm.measurable hemono
      have hmap : ((μ 0).prod (Measure.pi tail)).map e.symm = Measure.pi μ :=
        (MeasureTheory.measurePreserving_piFinSuccAbove μ 0).symm.map_eq
      rw [hmap] at hmapped
      exact hmapped

theorem positivelyAssociated_pi_finite
    {ι X : Type*} [Fintype ι] [MeasurableSpace X] [Preorder X]
    (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, PositivelyAssociated (μ i)) :
    PositivelyAssociated (Measure.pi μ) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let μfin : Fin (Fintype.card ι) → Measure X := fun i => μ (e i)
  have hfin : PositivelyAssociated (Measure.pi μfin) :=
    positivelyAssociated_pi_fin μfin (fun i => hμ (e i))
  let reindex := MeasurableEquiv.piCongrLeft (fun _ : ι => X) e
  have hreindexMono : Monotone reindex := by
    intro a b hab i
    let j := e.symm i
    have hij : e j = i := e.apply_symm_apply i
    rw [← hij]
    simpa [reindex, MeasurableEquiv.coe_piCongrLeft] using hab j
  have hmapped := hfin.map reindex.measurable hreindexMono
  have hmap : (Measure.pi μfin).map reindex = Measure.pi μ := by
    exact Measure.pi_map_piCongrLeft e μ
  rw [hmap] at hmapped
  exact hmapped

end Shepp.Section4
end SheppFlattenedModule047

section SheppFlattenedModule048
open scoped BigOperators

namespace Shepp.Section4

theorem sum_finset_compl
    {α : Type*} [Fintype α] [DecidableEq α]
    (g : Finset α → ℝ) :
    (∑ s : Finset α, g (Finset.univ \ s)) = ∑ s, g s := by
  let e : Finset α ≃ Finset α :=
    { toFun := fun s => Finset.univ \ s
      invFun := fun s => Finset.univ \ s
      left_inv := fun s => by ext x; simp
      right_inv := fun s => by ext x; simp }
  exact e.sum_comp g

theorem sum_mul_compl_le_sum_mul_self
    {α : Type*} [Fintype α] [DecidableEq α]
    (f g : Finset α → ℝ) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g) :
    (∑ s : Finset α, f s * g (Finset.univ \ s)) ≤
      ∑ s : Finset α, f s * g s := by
  let comp : Finset α → Finset α := fun s => Finset.univ \ s
  let A : ℝ := ∑ s : Finset α, f s
  let B : ℝ := ∑ s : Finset α, g s
  let C : ℝ := ∑ s : Finset α, f s * g s
  let D : ℝ := ∑ s : Finset α, f s * g (comp s)
  let N : ℝ := Fintype.card (Finset α)
  have hcompSum : (∑ s : Finset α, g (comp s)) = B := by
    let e : Finset α ≃ Finset α :=
      { toFun := comp
        invFun := comp
        left_inv := fun s => by ext x; simp [comp]
        right_inv := fun s => by ext x; simp [comp] }
    exact e.sum_comp g
  have hg_le_B : ∀ s : Finset α, g s ≤ B := by
    intro s
    exact Finset.single_le_sum (fun t _ => hg0 t) (Finset.mem_univ s)
  let h : Finset α → ℝ := fun s => B - g (comp s)
  have hh0 : 0 ≤ h := fun s => sub_nonneg.mpr (hg_le_B (comp s))
  have hhmono : Monotone h := by
    intro s t hst
    have hcomp : comp t ⊆ comp s := by
      intro x hx
      simp only [comp, Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
      exact fun hxs => hx (hst hxs)
    dsimp [h]
    linarith [hg hcomp]
  have hpositive := fkg f g (fun _ : Finset α => (1 : ℝ))
    (fun _ => by norm_num) hf0 hg0 hf hg (fun _ _ => by norm_num)
  have hnegative := fkg f h (fun _ : Finset α => (1 : ℝ))
    (fun _ => by norm_num) hf0 hh0 hf hhmono (fun _ _ => by norm_num)
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨∅⟩
  have hsumOne : (∑ _s : Finset α, (1 : ℝ)) = N := by
    simp [N]
  have hpositive' : A * B ≤ N * C := by
    simpa only [one_mul, hsumOne, A, B, C] using hpositive
  have hsumH : (∑ s : Finset α, h s) = N * B - B := by
    simp only [h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      hcompSum, N, Finset.card_univ]
  have hsumFH : (∑ s : Finset α, f s * h s) = B * A - D := by
    calc
      (∑ s : Finset α, f s * h s) =
          ∑ s : Finset α, (f s * B - f s * g (comp s)) := by
            apply Finset.sum_congr rfl
            intro s _hs
            simp only [h, mul_sub]
      _ = (∑ s : Finset α, f s * B) - D := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ s : Finset α, f s) * B - D := by
            rw [Finset.sum_mul]
      _ = B * A - D := by simp only [A]; rw [mul_comm]
  have hnegative' : N * D ≤ A * B := by
    simp only [one_mul, hsumOne] at hnegative
    rw [hsumH, hsumFH] at hnegative
    nlinarith
  have hNDNC : N * D ≤ N * C := hnegative'.trans hpositive'
  have hDC : D ≤ C := by nlinarith
  simpa only [D, C, comp] using hDC

end Shepp.Section4
end SheppFlattenedModule048

section SheppFlattenedModule049
open scoped BigOperators NNReal
open MeasureTheory Set

namespace Shepp.Section5

open ProbabilityTheory Shepp.Section3 Shepp.Section4

def cloudPointsLE {α : Type*}
    (ω ω' : PoissonCloudSample α) : Prop :=
  cloudPoints ω ⊆ cloudPoints ω'

noncomputable abbrev cloudPointsPreorder
    {α : Type*} : Preorder (PoissonCloudSample α) where
  le := cloudPointsLE
  lt := fun ω ω' => cloudPointsLE ω ω' ∧ ¬cloudPointsLE ω' ω
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ := Set.Subset.trans
  lt_iff_le_not_ge := fun _ _ => Iff.rfl

def finiteCloudPointsLE
    {ι α : Type*} [Fintype ι]
    (ω ω' : FiniteCloudSample ι α) : Prop :=
  ∀ i, cloudPointsLE (ω i) (ω' i)

noncomputable abbrev finiteCloudPointsPreorder
    {ι α : Type*} [Fintype ι] : Preorder (FiniteCloudSample ι α) where
  le := finiteCloudPointsLE
  lt := fun ω ω' =>
    finiteCloudPointsLE ω ω' ∧ ¬finiteCloudPointsLE ω' ω
  le_refl _ _ := Set.Subset.rfl
  le_trans _ _ _ h₁ h₂ i := Set.Subset.trans (h₁ i) (h₂ i)
  lt_iff_le_not_ge := fun _ _ => Iff.rfl

noncomputable def selectedCloud
    {κ α : Type*} [Fintype κ] [LinearOrder κ] [Inhabited α]
    (y : κ → α) (s : Finset κ) : PoissonCloudSample α :=
  (s.card, fun n =>
    if hn : n < s.card then
      y (s.orderEmbOfFin rfl ⟨n, hn⟩)
    else default)

theorem mem_cloudPoints_selectedCloud_iff
    {κ α : Type*} [Fintype κ] [LinearOrder κ] [Inhabited α]
    (y : κ → α) (s : Finset κ) (x : α) :
    x ∈ cloudPoints (selectedCloud y s) ↔
      ∃ i ∈ s, y i = x := by
  constructor
  · rintro ⟨j, hj, hvalue⟩
    have hj' : j < s.card := by
      simpa only [selectedCloud] using hj
    let q : Fin s.card := ⟨j, hj'⟩
    let i : κ := s.orderEmbOfFin rfl q
    refine ⟨i, s.orderEmbOfFin_mem rfl q, ?_⟩
    have hseq : (selectedCloud y s).2 j = y i := by
      simp only [selectedCloud, hj', dite_true, i, q]
    exact hseq.symm.trans hvalue
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨q, hq⟩ := (s.orderIsoOfFin rfl).surjective ⟨i, hi⟩
    refine ⟨q, q.isLt, ?_⟩
    have hindex : s.orderEmbOfFin rfl q = i := congrArg Subtype.val hq
    simp only [selectedCloud, q.isLt, dite_true, hindex]

theorem cloudPoints_selectedCloud
    {κ α : Type*} [Fintype κ] [LinearOrder κ] [Inhabited α]
    (y : κ → α) (s : Finset κ) :
    cloudPoints (selectedCloud y s) = y '' (s : Set κ) := by
  ext x
  rw [mem_cloudPoints_selectedCloud_iff]
  simp only [Set.mem_image, Finset.mem_coe]

theorem selectedCloud_pointsLE
    {κ α : Type*} [Fintype κ] [LinearOrder κ] [Inhabited α]
    (y : κ → α) {s t : Finset κ} (hst : s ⊆ t) :
    cloudPointsLE (selectedCloud y s) (selectedCloud y t) := by
  intro x hx
  rw [mem_cloudPoints_selectedCloud_iff] at hx ⊢
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, hst hi, rfl⟩

theorem measurable_selectedCloud
    {κ α : Type*} [Fintype κ] [LinearOrder κ] [Inhabited α]
    [MeasurableSpace α] (s : Finset κ) :
    Measurable fun y : κ → α => selectedCloud y s := by
  apply measurable_const.prodMk
  apply measurable_pi_lambda
  intro n
  by_cases hn : n < s.card
  · simp only [hn, dite_true]
    exact measurable_pi_apply _
  · simp only [hn, dite_false]
    exact measurable_const

theorem sum_selectedCloud_compl_le_sum_selectedCloud_self
    {κ α : Type*} [Fintype κ] [LinearOrder κ] [Inhabited α]
    [MeasurableSpace α]
    (f g : PoissonCloudSample α → ℝ)
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    (hg : @AssociatedFunction _ inferInstance cloudPointsPreorder g)
    (y : κ → α) :
    (∑ s : Finset κ,
        f (selectedCloud y s) *
          g (selectedCloud y (Finset.univ \ s))) ≤
      ∑ s : Finset κ,
        f (selectedCloud y s) * g (selectedCloud y s) := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  refine sum_mul_compl_le_sum_mul_self
    (fun s => f (selectedCloud y s))
    (fun s => g (selectedCloud y s)) ?_ ?_ ?_ ?_
  · exact fun s => hf.nonnegative _
  · exact fun s => hg.nonnegative _
  · intro s t hst
    exact hf.monotone (selectedCloud_pointsLE y hst)
  · intro s t hst
    exact hg.monotone (selectedCloud_pointsLE y hst)

theorem cloudPoints_selectedCloud_range_univ
    {α : Type*} [Inhabited α] (n : ℕ) (z : ℕ → α) :
    cloudPoints
        (selectedCloud ((Finset.range n).restrict z) Finset.univ) =
      cloudPoints (n, z) := by
  ext x
  rw [mem_cloudPoints_selectedCloud_iff]
  constructor
  · rintro ⟨i, _hi, hix⟩
    exact ⟨i, Finset.mem_range.mp i.property, hix⟩
  · rintro ⟨i, hi, hix⟩
    let j : ↥(Finset.range n) := ⟨i, Finset.mem_range.mpr hi⟩
    exact ⟨j, Finset.mem_univ j, hix⟩

theorem associatedFunction_eq_of_cloudPoints_eq
    {α : Type*} [MeasurableSpace α]
    {f : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    {ω ω' : PoissonCloudSample α}
    (hpoints : cloudPoints ω = cloudPoints ω') :
    f ω = f ω' := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  apply le_antisymm
  · exact hf.monotone hpoints.subset
  · exact hf.monotone hpoints.symm.subset

noncomputable def poissonCloudLevelIntegral
    {α : Type*} [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) (f : PoissonCloudSample α → ℝ) (n : ℕ) : ℝ :=
  ∫ y : ↥(Finset.range n) → α,
    f (selectedCloud y Finset.univ)
      ∂Measure.pi (fun _ : ↥(Finset.range n) => μ)

theorem integral_infinitePi_eq_poissonCloudLevelIntegral
    {α : Type*} [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    (n : ℕ) :
    (∫ z : ℕ → α, f (n, z)
        ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      poissonCloudLevelIntegral μ f n := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  let F : (↥(Finset.range n) → α) → ℝ := fun y =>
    f (selectedCloud y Finset.univ)
  have hF : Measurable F :=
    hf.measurable.comp (measurable_selectedCloud Finset.univ)
  calc
    (∫ z : ℕ → α, f (n, z)
        ∂Measure.infinitePi (fun _ : ℕ => μ)) =
        ∫ z : ℕ → α, F ((Finset.range n).restrict z)
          ∂Measure.infinitePi (fun _ : ℕ => μ) := by
            apply integral_congr_ae
            filter_upwards with z
            exact associatedFunction_eq_of_cloudPoints_eq hf
              (cloudPoints_selectedCloud_range_univ n z).symm
    _ = ∫ y : ↥(Finset.range n) → α, F y
          ∂Measure.pi (fun _ : ↥(Finset.range n) => μ) :=
      integral_restrict_infinitePi (fun _ : ℕ => μ) hF.aestronglyMeasurable
    _ = poissonCloudLevelIntegral μ f n := rfl

theorem integral_poissonCloudMeasure_eq_tsum_level
    {α : Type*} [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    {f : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f) :
    (∫ ω, f ω ∂poissonCloudMeasure μ rate) =
      ∑' n : ℕ,
        (Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ n / n.factorial) *
          poissonCloudLevelIntegral μ f n := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  rw [poissonCloudMeasure, MeasureTheory.integral_prod f hf.integrable,
    ProbabilityTheory.integral_poissonMeasure]
  apply tsum_congr
  intro n
  simp only [smul_eq_mul]
  rw [integral_infinitePi_eq_poissonCloudLevelIntegral μ hf n]

theorem map_pi_precomp_embedding
    {κ ι α : Type*} [Fintype κ] [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (e : ι ↪ κ) :
    (Measure.pi (fun _ : κ => μ)).map
        (fun y : κ → α => fun i : ι => y (e i)) =
      Measure.pi (fun _ : ι => μ) := by
  have hfull : iIndepFun
      (fun i : κ => fun y : κ → α => y i)
      (Measure.pi (fun _ : κ => μ)) :=
    iIndepFun_pi fun _ => Measurable.aemeasurable measurable_id
  have hselected := hfull.precomp e.injective
  have hmap := hselected.map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (e i)).aemeasurable)
  rw [hmap]
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : κ => μ) (e i)).map_eq

theorem measurable_pi_precomp_embedding
    {κ ι α : Type*} [MeasurableSpace α] (e : ι ↪ κ) :
    Measurable fun y : κ → α => fun i : ι => y (e i) := by
  exact measurable_pi_lambda _ fun i => measurable_pi_apply (e i)

theorem cloudPoints_selectedCloud_univ_precomp_equiv
    {κ ι α : Type*} [Fintype κ] [Fintype ι]
    [LinearOrder κ] [LinearOrder ι] [Inhabited α]
    (e : ι ≃ κ) (y : κ → α) :
    cloudPoints (selectedCloud (fun i => y (e i)) Finset.univ) =
      cloudPoints (selectedCloud y Finset.univ) := by
  ext x
  simp only [mem_cloudPoints_selectedCloud_iff, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨i, hix⟩
    exact ⟨e i, hix⟩
  · rintro ⟨j, hjx⟩
    exact ⟨e.symm j, by simpa using hjx⟩

theorem integral_selectedCloud_univ_eq_level
    {κ α : Type*} [Fintype κ] [LinearOrder κ]
    [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f) :
    (∫ y : κ → α, f (selectedCloud y Finset.univ)
        ∂Measure.pi (fun _ : κ => μ)) =
      poissonCloudLevelIntegral μ f (Fintype.card κ) := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  let ι := ↥(Finset.range (Fintype.card κ))
  let e : ι ≃ κ := Fintype.equivOfCardEq (by simp [ι])
  let φ : (κ → α) → (ι → α) := fun y i => y (e i)
  let H : (ι → α) → ℝ := fun v => f (selectedCloud v Finset.univ)
  have hφ : Measurable φ :=
    measurable_pi_precomp_embedding e.toEmbedding
  have hH : Measurable H :=
    hf.measurable.comp (measurable_selectedCloud Finset.univ)
  have hmap :
      (Measure.pi (fun _ : κ => μ)).map φ =
        Measure.pi (fun _ : ι => μ) :=
    map_pi_precomp_embedding μ e.toEmbedding
  have hintegral :
      (∫ v : ι → α, H v ∂Measure.pi (fun _ : ι => μ)) =
        ∫ y : κ → α, H (φ y) ∂Measure.pi (fun _ : κ => μ) := by
    rw [← hmap]
    exact integral_map hφ.aemeasurable hH.aestronglyMeasurable
  calc
    (∫ y : κ → α, f (selectedCloud y Finset.univ)
        ∂Measure.pi (fun _ : κ => μ)) =
        ∫ y : κ → α, H (φ y) ∂Measure.pi (fun _ : κ => μ) := by
          apply integral_congr_ae
          filter_upwards with y
          exact associatedFunction_eq_of_cloudPoints_eq hf
            (cloudPoints_selectedCloud_univ_precomp_equiv e y).symm
    _ = ∫ v : ι → α, H v ∂Measure.pi (fun _ : ι => μ) :=
      hintegral.symm
    _ = poissonCloudLevelIntegral μ f (Fintype.card κ) := rfl

theorem cloudPoints_selectedCloud_restrict_univ
    {κ α : Type*} [Fintype κ] [LinearOrder κ] [Inhabited α]
    (y : κ → α) (s : Finset κ) :
    cloudPoints
        (selectedCloud (fun i : ↥s => y i) Finset.univ) =
      cloudPoints (selectedCloud y s) := by
  ext x
  simp only [mem_cloudPoints_selectedCloud_iff, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨i, hix⟩
    exact ⟨i, i.property, hix⟩
  · rintro ⟨i, hi, hix⟩
    exact ⟨⟨i, hi⟩, hix⟩

theorem integral_selectedCloud_eq_level
    {κ α : Type*} [Fintype κ] [LinearOrder κ]
    [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    (s : Finset κ) :
    (∫ y : κ → α, f (selectedCloud y s)
        ∂Measure.pi (fun _ : κ => μ)) =
      poissonCloudLevelIntegral μ f s.card := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  let e : ↥s ↪ κ :=
    { toFun := Subtype.val
      inj' := Subtype.val_injective }
  let φ : (κ → α) → (↥s → α) := fun y i => y (e i)
  let H : (↥s → α) → ℝ := fun v => f (selectedCloud v Finset.univ)
  have hφ : Measurable φ := measurable_pi_precomp_embedding e
  have hH : Measurable H :=
    hf.measurable.comp (measurable_selectedCloud Finset.univ)
  have hmap :
      (Measure.pi (fun _ : κ => μ)).map φ =
        Measure.pi (fun _ : ↥s => μ) :=
    map_pi_precomp_embedding μ e
  have hintegral :
      (∫ v : ↥s → α, H v ∂Measure.pi (fun _ : ↥s => μ)) =
        ∫ y : κ → α, H (φ y) ∂Measure.pi (fun _ : κ => μ) := by
    rw [← hmap]
    exact integral_map hφ.aemeasurable hH.aestronglyMeasurable
  calc
    (∫ y : κ → α, f (selectedCloud y s)
        ∂Measure.pi (fun _ : κ => μ)) =
        ∫ y : κ → α, H (φ y) ∂Measure.pi (fun _ : κ => μ) := by
          apply integral_congr_ae
          filter_upwards with y
          exact associatedFunction_eq_of_cloudPoints_eq hf
            (cloudPoints_selectedCloud_restrict_univ y s).symm
    _ = ∫ v : ↥s → α, H v ∂Measure.pi (fun _ : ↥s => μ) :=
      hintegral.symm
    _ = poissonCloudLevelIntegral μ f (Fintype.card ↥s) :=
      integral_selectedCloud_univ_eq_level μ hf
    _ = poissonCloudLevelIntegral μ f s.card := by simp

theorem integral_selectedCloud_mul_compl_eq_levels
    {κ α : Type*} [Fintype κ] [LinearOrder κ]
    [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f g : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    (hg : @AssociatedFunction _ inferInstance cloudPointsPreorder g)
    (s : Finset κ) :
    (∫ y : κ → α,
        f (selectedCloud y s) *
          g (selectedCloud y (Finset.univ \ s))
        ∂Measure.pi (fun _ : κ => μ)) =
      poissonCloudLevelIntegral μ f s.card *
        poissonCloudLevelIntegral μ g (Finset.univ \ s).card := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  let t : Finset κ := Finset.univ \ s
  let X : (κ → α) → (↥s → α) := fun y i => y i
  let Y : (κ → α) → (↥t → α) := fun y i => y i
  let F : (↥s → α) → ℝ := fun v => f (selectedCloud v Finset.univ)
  let G : (↥t → α) → ℝ := fun v => g (selectedCloud v Finset.univ)
  have hcoords : iIndepFun
      (fun i : κ => fun y : κ → α => y i)
      (Measure.pi (fun _ : κ => μ)) :=
    iIndepFun_pi fun _ => Measurable.aemeasurable measurable_id
  have hXY : IndepFun X Y (Measure.pi (fun _ : κ => μ)) := by
    exact hcoords.indepFun_finset s t Finset.disjoint_sdiff
      (fun i => measurable_pi_apply i)
  have hX : Measurable X := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (i : κ)
  have hY : Measurable Y := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (i : κ)
  have hF : Measurable F :=
    hf.measurable.comp (measurable_selectedCloud Finset.univ)
  have hG : Measurable G :=
    hg.measurable.comp (measurable_selectedCloud Finset.univ)
  have hfactor := hXY.integral_fun_comp_mul_comp
    hX.aemeasurable hY.aemeasurable
    hF.aestronglyMeasurable hG.aestronglyMeasurable
  have hleft :
      (∫ y : κ → α,
          f (selectedCloud y s) * g (selectedCloud y t)
          ∂Measure.pi (fun _ : κ => μ)) =
        ∫ y : κ → α, F (X y) * G (Y y)
          ∂Measure.pi (fun _ : κ => μ) := by
    apply integral_congr_ae
    filter_upwards with y
    have hfEq : f (selectedCloud y s) = F (X y) :=
      associatedFunction_eq_of_cloudPoints_eq hf
        (cloudPoints_selectedCloud_restrict_univ y s).symm
    have hgEq : g (selectedCloud y t) = G (Y y) :=
      associatedFunction_eq_of_cloudPoints_eq hg
        (cloudPoints_selectedCloud_restrict_univ y t).symm
    rw [hfEq, hgEq]
  have hrightF :
      (∫ y : κ → α, F (X y) ∂Measure.pi (fun _ : κ => μ)) =
        poissonCloudLevelIntegral μ f s.card := by
    calc
      (∫ y : κ → α, F (X y) ∂Measure.pi (fun _ : κ => μ)) =
          ∫ y : κ → α, f (selectedCloud y s)
            ∂Measure.pi (fun _ : κ => μ) := by
              apply integral_congr_ae
              filter_upwards with y
              exact (associatedFunction_eq_of_cloudPoints_eq hf
                (cloudPoints_selectedCloud_restrict_univ y s).symm).symm
      _ = poissonCloudLevelIntegral μ f s.card :=
        integral_selectedCloud_eq_level μ hf s
  have hrightG :
      (∫ y : κ → α, G (Y y) ∂Measure.pi (fun _ : κ => μ)) =
        poissonCloudLevelIntegral μ g t.card := by
    calc
      (∫ y : κ → α, G (Y y) ∂Measure.pi (fun _ : κ => μ)) =
          ∫ y : κ → α, g (selectedCloud y t)
            ∂Measure.pi (fun _ : κ => μ) := by
              apply integral_congr_ae
              filter_upwards with y
              exact (associatedFunction_eq_of_cloudPoints_eq hg
                (cloudPoints_selectedCloud_restrict_univ y t).symm).symm
      _ = poissonCloudLevelIntegral μ g t.card :=
        integral_selectedCloud_eq_level μ hg t
  rw [show Finset.univ \ s = t by rfl, hleft, hfactor, hrightF, hrightG]

theorem integral_selectedCloud_mul_self_eq_level
    {κ α : Type*} [Fintype κ] [LinearOrder κ]
    [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f g : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    (hg : @AssociatedFunction _ inferInstance cloudPointsPreorder g)
    (s : Finset κ) :
    (∫ y : κ → α,
        f (selectedCloud y s) * g (selectedCloud y s)
        ∂Measure.pi (fun _ : κ => μ)) =
      poissonCloudLevelIntegral μ (fun ω => f ω * g ω) s.card := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  exact integral_selectedCloud_eq_level μ (hf.mul hg) s

theorem integrable_selectedCloud_mul_selectedCloud
    {κ α : Type*} [Fintype κ] [LinearOrder κ]
    [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f g : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    (hg : @AssociatedFunction _ inferInstance cloudPointsPreorder g)
    (s t : Finset κ) :
    Integrable
      (fun y : κ → α =>
        f (selectedCloud y s) * g (selectedCloud y t))
      (Measure.pi (fun _ : κ => μ)) := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bounded
  obtain ⟨Cg, hCg0, hCg⟩ := hg.bounded
  have hmeas : Measurable
      (fun y : κ → α =>
        f (selectedCloud y s) * g (selectedCloud y t)) :=
    (hf.measurable.comp (measurable_selectedCloud s)).mul
      (hg.measurable.comp (measurable_selectedCloud t))
  apply Integrable.of_bound hmeas.aestronglyMeasurable (Cf * Cg)
  filter_upwards with y
  rw [Real.norm_of_nonneg
    (mul_nonneg (hf.nonnegative _) (hg.nonnegative _))]
  exact mul_le_mul (hCf _) (hCg _) (hg.nonnegative _) hCf0

theorem sum_level_mul_compl_le_sum_level_mul_self
    {κ α : Type*} [Fintype κ] [LinearOrder κ]
    [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f g : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    (hg : @AssociatedFunction _ inferInstance cloudPointsPreorder g) :
    (∑ s : Finset κ,
        poissonCloudLevelIntegral μ f s.card *
          poissonCloudLevelIntegral μ g (Finset.univ \ s).card) ≤
      ∑ s : Finset κ,
        poissonCloudLevelIntegral μ (fun ω => f ω * g ω) s.card := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  let ν : Measure (κ → α) := Measure.pi (fun _ : κ => μ)
  have hcross : ∀ s : Finset κ, Integrable
      (fun y : κ → α =>
        f (selectedCloud y s) *
          g (selectedCloud y (Finset.univ \ s))) ν :=
    fun s => integrable_selectedCloud_mul_selectedCloud μ hf hg s
      (Finset.univ \ s)
  have hsame : ∀ s : Finset κ, Integrable
      (fun y : κ → α =>
        f (selectedCloud y s) * g (selectedCloud y s)) ν :=
    fun s => integrable_selectedCloud_mul_selectedCloud μ hf hg s s
  calc
    (∑ s : Finset κ,
        poissonCloudLevelIntegral μ f s.card *
          poissonCloudLevelIntegral μ g (Finset.univ \ s).card) =
        ∫ y : κ → α,
          ∑ s : Finset κ,
            f (selectedCloud y s) *
              g (selectedCloud y (Finset.univ \ s)) ∂ν := by
          rw [integral_finsetSum Finset.univ]
          · apply Finset.sum_congr rfl
            intro s _hs
            exact (integral_selectedCloud_mul_compl_eq_levels μ hf hg s).symm
          · intro s _hs
            exact hcross s
    _ ≤ ∫ y : κ → α,
          ∑ s : Finset κ,
            f (selectedCloud y s) * g (selectedCloud y s) ∂ν := by
      exact integral_mono
        (integrable_finset_sum Finset.univ fun s _ => hcross s)
        (integrable_finset_sum Finset.univ fun s _ => hsame s)
        (sum_selectedCloud_compl_le_sum_selectedCloud_self f g hf hg)
    _ = ∑ s : Finset κ,
        poissonCloudLevelIntegral μ (fun ω => f ω * g ω) s.card := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro s _hs
        exact integral_selectedCloud_mul_self_eq_level μ hf hg s
      · intro s _hs
        exact hsame s

theorem sum_finset_card
    {κ : Type*} [Fintype κ] (h : ℕ → ℝ) :
    (∑ s : Finset κ, h s.card) =
      ∑ n ∈ Finset.range (Fintype.card κ + 1),
        (Nat.choose (Fintype.card κ) n : ℝ) * h n := by
  classical
  calc
    (∑ s : Finset κ, h s.card) =
        ∑ s ∈ Finset.univ.powerset, h s.card := by
          rw [show (Finset.univ : Finset κ).powerset =
              (Finset.univ : Finset (Finset κ)) by
            ext s
            simp]
    _ = ∑ n ∈ Finset.range (Finset.univ.card + 1),
          ∑ s ∈ Finset.powersetCard n Finset.univ, h s.card :=
      Finset.sum_powerset Finset.univ (fun s => h s.card)
    _ = ∑ n ∈ Finset.range (Fintype.card κ + 1),
          (Nat.choose (Fintype.card κ) n : ℝ) * h n := by
      simp only [Finset.card_univ]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.sum_powersetCard]
      simp only [Finset.card_univ, nsmul_eq_mul]

theorem sum_finset_card_compl
    {κ : Type*} [Fintype κ] [DecidableEq κ] (a b : ℕ → ℝ) :
    (∑ s : Finset κ, a s.card * b (Finset.univ \ s).card) =
      ∑ n ∈ Finset.range (Fintype.card κ + 1),
        (Nat.choose (Fintype.card κ) n : ℝ) *
          (a n * b (Fintype.card κ - n)) := by
  classical
  have hcomp : ∀ s : Finset κ,
      (Finset.univ \ s).card = Fintype.card κ - s.card := by
    intro s
    simpa using Finset.card_sdiff_of_subset (Finset.subset_univ s)
  simp_rw [hcomp]
  simpa only using
    sum_finset_card (κ := κ)
      (fun n => a n * b (Fintype.card κ - n))

noncomputable def expSeriesCoeff (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / n.factorial

theorem summable_expSeriesCoeff (x : ℝ) :
    Summable (expSeriesCoeff x) := by
  change Summable (fun n : ℕ => x ^ n / n.factorial)
  exact Real.summable_pow_div_factorial x

theorem tsum_expSeriesCoeff (x : ℝ) :
    (∑' n, expSeriesCoeff x n) = Real.exp x := by
  simpa [expSeriesCoeff, div_eq_mul_inv, smul_eq_mul, mul_comm,
    ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq

theorem choose_mul_expSeriesCoeff
    {k n : ℕ} (h : n ≤ k) (x : ℝ) :
    (Nat.choose k n : ℝ) * expSeriesCoeff x k =
      expSeriesCoeff x n * expSeriesCoeff x (k - n) := by
  rw [Nat.cast_choose ℝ h]
  unfold expSeriesCoeff
  have hk : k = n + (k - n) := (Nat.add_sub_of_le h).symm
  conv_lhs =>
    enter [2, 1]
    rw [hk, pow_add]
  field_simp

theorem expSeriesCoeff_nonneg
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ expSeriesCoeff x n := by
  unfold expSeriesCoeff
  positivity

theorem poissonCloudLevelIntegral_nonneg
    {α : Type*} [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    (n : ℕ) :
    0 ≤ poissonCloudLevelIntegral μ f n := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  exact integral_nonneg fun y => hf.nonnegative (selectedCloud y Finset.univ)

theorem poissonCloudLevelIntegral_le
    {α : Type*} [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    {C : ℝ} (_hC0 : 0 ≤ C) (hC : ∀ ω, f ω ≤ C)
    (n : ℕ) :
    poissonCloudLevelIntegral μ f n ≤ C := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  let ν : Measure (↥(Finset.range n) → α) :=
    Measure.pi (fun _ : ↥(Finset.range n) => μ)
  have hi : Integrable
      (fun y : ↥(Finset.range n) → α =>
        f (selectedCloud y Finset.univ)) ν := by
    apply Integrable.of_bound
      (hf.measurable.comp
        (measurable_selectedCloud Finset.univ)).aestronglyMeasurable C
    filter_upwards with y
    change ‖f (selectedCloud y Finset.univ)‖ ≤ C
    rw [Real.norm_of_nonneg (hf.nonnegative _)]
    exact hC _
  calc
    poissonCloudLevelIntegral μ f n ≤
        ∫ _y : ↥(Finset.range n) → α, C ∂ν :=
      integral_mono hi (integrable_const C) (fun y => hC _)
    _ = C := by simp [ν, probReal_univ]

theorem summable_expSeriesCoeff_mul_level
    {α : Type*} [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    {x : ℝ} (hx : 0 ≤ x) :
    Summable fun n =>
      expSeriesCoeff x n * poissonCloudLevelIntegral μ f n := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  obtain ⟨C, hC0, hC⟩ := hf.bounded
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (expSeriesCoeff_nonneg hx n)
      (poissonCloudLevelIntegral_nonneg μ hf n))
    (fun n => mul_le_mul_of_nonneg_left
      (poissonCloudLevelIntegral_le μ hf hC0 hC n)
      (expSeriesCoeff_nonneg hx n))
    ((summable_expSeriesCoeff x).mul_right C)

theorem sum_range_choose_level_mul_le
    {α : Type*} [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f g : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    (hg : @AssociatedFunction _ inferInstance cloudPointsPreorder g)
    (k : ℕ) :
    (∑ n ∈ Finset.range (k + 1),
        (Nat.choose k n : ℝ) *
          (poissonCloudLevelIntegral μ f n *
            poissonCloudLevelIntegral μ g (k - n))) ≤
      ∑ n ∈ Finset.range (k + 1),
        (Nat.choose k n : ℝ) *
          poissonCloudLevelIntegral μ (fun ω => f ω * g ω) n := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  have h := sum_level_mul_compl_le_sum_level_mul_self
    (κ := Fin k) μ hf hg
  rw [sum_finset_card_compl, sum_finset_card] at h
  simpa using h

theorem sum_range_expSeriesCoeff_level_mul_le
    {α : Type*} [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f g : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    (hg : @AssociatedFunction _ inferInstance cloudPointsPreorder g)
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (∑ n ∈ Finset.range (k + 1),
        (expSeriesCoeff x n * poissonCloudLevelIntegral μ f n) *
          (expSeriesCoeff x (k - n) *
            poissonCloudLevelIntegral μ g (k - n))) ≤
      ∑ n ∈ Finset.range (k + 1),
        (expSeriesCoeff x n *
          poissonCloudLevelIntegral μ (fun ω => f ω * g ω) n) *
            expSeriesCoeff x (k - n) := by
  calc
    (∑ n ∈ Finset.range (k + 1),
        (expSeriesCoeff x n * poissonCloudLevelIntegral μ f n) *
          (expSeriesCoeff x (k - n) *
            poissonCloudLevelIntegral μ g (k - n))) =
        expSeriesCoeff x k *
          ∑ n ∈ Finset.range (k + 1),
            (Nat.choose k n : ℝ) *
              (poissonCloudLevelIntegral μ f n *
                poissonCloudLevelIntegral μ g (k - n)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnk : n ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      calc
        (expSeriesCoeff x n * poissonCloudLevelIntegral μ f n) *
            (expSeriesCoeff x (k - n) *
              poissonCloudLevelIntegral μ g (k - n)) =
            (expSeriesCoeff x n * expSeriesCoeff x (k - n)) *
              (poissonCloudLevelIntegral μ f n *
                poissonCloudLevelIntegral μ g (k - n)) := by ring
        _ = ((Nat.choose k n : ℝ) * expSeriesCoeff x k) *
              (poissonCloudLevelIntegral μ f n *
                poissonCloudLevelIntegral μ g (k - n)) := by
              rw [choose_mul_expSeriesCoeff hnk x]
        _ = expSeriesCoeff x k *
              ((Nat.choose k n : ℝ) *
                (poissonCloudLevelIntegral μ f n *
                  poissonCloudLevelIntegral μ g (k - n))) := by ring
    _ ≤ expSeriesCoeff x k *
          ∑ n ∈ Finset.range (k + 1),
            (Nat.choose k n : ℝ) *
              poissonCloudLevelIntegral μ (fun ω => f ω * g ω) n :=
      mul_le_mul_of_nonneg_left
        (sum_range_choose_level_mul_le μ hf hg k)
        (expSeriesCoeff_nonneg hx k)
    _ = ∑ n ∈ Finset.range (k + 1),
        (expSeriesCoeff x n *
          poissonCloudLevelIntegral μ (fun ω => f ω * g ω) n) *
            expSeriesCoeff x (k - n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnk : n ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      calc
        expSeriesCoeff x k *
            ((Nat.choose k n : ℝ) *
              poissonCloudLevelIntegral μ (fun ω => f ω * g ω) n) =
            ((Nat.choose k n : ℝ) * expSeriesCoeff x k) *
              poissonCloudLevelIntegral μ (fun ω => f ω * g ω) n := by ring
        _ = (expSeriesCoeff x n * expSeriesCoeff x (k - n)) *
              poissonCloudLevelIntegral μ (fun ω => f ω * g ω) n := by
              rw [choose_mul_expSeriesCoeff hnk x]
        _ = (expSeriesCoeff x n *
              poissonCloudLevelIntegral μ (fun ω => f ω * g ω) n) *
                expSeriesCoeff x (k - n) := by ring

theorem tsum_expSeriesCoeff_level_mul_le
    {α : Type*} [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f g : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f)
    (hg : @AssociatedFunction _ inferInstance cloudPointsPreorder g)
    {x : ℝ} (hx : 0 ≤ x) :
    ((∑' n, expSeriesCoeff x n * poissonCloudLevelIntegral μ f n) *
        ∑' n, expSeriesCoeff x n * poissonCloudLevelIntegral μ g n) ≤
      (∑' n, expSeriesCoeff x n *
          poissonCloudLevelIntegral μ (fun ω => f ω * g ω) n) *
        ∑' n, expSeriesCoeff x n := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  let a : ℕ → ℝ := fun n =>
    expSeriesCoeff x n * poissonCloudLevelIntegral μ f n
  let b : ℕ → ℝ := fun n =>
    expSeriesCoeff x n * poissonCloudLevelIntegral μ g n
  let c : ℕ → ℝ := fun n =>
    expSeriesCoeff x n *
      poissonCloudLevelIntegral μ (fun ω => f ω * g ω) n
  let e : ℕ → ℝ := expSeriesCoeff x
  let ab : ℕ → ℝ := fun k =>
    ∑ n ∈ Finset.range (k + 1), a n * b (k - n)
  let ce : ℕ → ℝ := fun k =>
    ∑ n ∈ Finset.range (k + 1), c n * e (k - n)
  have ha : Summable a := by
    simpa only [a] using summable_expSeriesCoeff_mul_level μ hf hx
  have hb : Summable b := by
    simpa only [b] using summable_expSeriesCoeff_mul_level μ hg hx
  have hc : Summable c := by
    simpa only [c] using
      summable_expSeriesCoeff_mul_level μ (hf.mul hg) hx
  have he : Summable e := by
    simpa only [e] using summable_expSeriesCoeff x
  have ha0 : ∀ n, 0 ≤ a n := by
    intro n
    exact mul_nonneg (expSeriesCoeff_nonneg hx n)
      (poissonCloudLevelIntegral_nonneg μ hf n)
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    exact mul_nonneg (expSeriesCoeff_nonneg hx n)
      (poissonCloudLevelIntegral_nonneg μ hg n)
  have hc0 : ∀ n, 0 ≤ c n := by
    intro n
    exact mul_nonneg (expSeriesCoeff_nonneg hx n)
      (poissonCloudLevelIntegral_nonneg μ (hf.mul hg) n)
  have he0 : ∀ n, 0 ≤ e n := expSeriesCoeff_nonneg hx
  have haNorm : Summable fun n => ‖a n‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (ha0 _)] using ha
  have hbNorm : Summable fun n => ‖b n‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hb0 _)] using hb
  have hcNorm : Summable fun n => ‖c n‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hc0 _)] using hc
  have heNorm : Summable fun n => ‖e n‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (he0 _)] using he
  have habNorm : Summable fun k => ‖ab k‖ :=
    summable_norm_sum_mul_range_of_summable_norm haNorm hbNorm
  have hceNorm : Summable fun k => ‖ce k‖ :=
    summable_norm_sum_mul_range_of_summable_norm hcNorm heNorm
  have hab : Summable ab := habNorm.of_norm
  have hce : Summable ce := hceNorm.of_norm
  have hpoint : ∀ k, ab k ≤ ce k := by
    intro k
    change
      (∑ n ∈ Finset.range (k + 1),
          (expSeriesCoeff x n * poissonCloudLevelIntegral μ f n) *
            (expSeriesCoeff x (k - n) *
              poissonCloudLevelIntegral μ g (k - n))) ≤
        ∑ n ∈ Finset.range (k + 1),
          (expSeriesCoeff x n *
            poissonCloudLevelIntegral μ (fun ω => f ω * g ω) n) *
              expSeriesCoeff x (k - n)
    exact sum_range_expSeriesCoeff_level_mul_le μ hf hg hx k
  have hcauchyAB :
      (∑' n, a n) * (∑' n, b n) = ∑' k, ab k :=
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm haNorm hbNorm
  have hcauchyCE :
      (∑' n, c n) * (∑' n, e n) = ∑' k, ce k :=
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hcNorm heNorm
  have hseries :
      (∑' n, a n) * (∑' n, b n) ≤
        (∑' n, c n) * (∑' n, e n) := by
    rw [hcauchyAB, hcauchyCE]
    exact hab.tsum_le_tsum hpoint hce
  simpa only [a, b, c, e] using hseries

theorem integral_poissonCloudMeasure_eq_exp_mul_tsum_level
    {α : Type*} [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    {f : PoissonCloudSample α → ℝ}
    (hf : @AssociatedFunction _ inferInstance cloudPointsPreorder f) :
    (∫ ω, f ω ∂poissonCloudMeasure μ rate) =
      Real.exp (-(rate : ℝ)) *
        ∑' n, expSeriesCoeff (rate : ℝ) n *
          poissonCloudLevelIntegral μ f n := by
  calc
    (∫ ω, f ω ∂poissonCloudMeasure μ rate) =
        ∑' n : ℕ,
          (Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ n / n.factorial) *
            poissonCloudLevelIntegral μ f n :=
      integral_poissonCloudMeasure_eq_tsum_level μ rate hf
    _ = ∑' n : ℕ, Real.exp (-(rate : ℝ)) *
          (expSeriesCoeff (rate : ℝ) n *
            poissonCloudLevelIntegral μ f n) := by
      apply tsum_congr
      intro n
      unfold expSeriesCoeff
      ring
    _ = Real.exp (-(rate : ℝ)) *
          ∑' n, expSeriesCoeff (rate : ℝ) n *
            poissonCloudLevelIntegral μ f n := tsum_mul_left

theorem positivelyAssociated_poissonCloudMeasure
    {α : Type*} [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ℝ≥0) :
    @PositivelyAssociated _ inferInstance cloudPointsPreorder
      (poissonCloudMeasure μ rate) := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  intro f g hf hg
  rw [integral_poissonCloudMeasure_eq_exp_mul_tsum_level μ rate hf,
    integral_poissonCloudMeasure_eq_exp_mul_tsum_level μ rate hg,
    integral_poissonCloudMeasure_eq_exp_mul_tsum_level μ rate (hf.mul hg)]
  let A : ℝ := ∑' n, expSeriesCoeff (rate : ℝ) n *
    poissonCloudLevelIntegral μ f n
  let B : ℝ := ∑' n, expSeriesCoeff (rate : ℝ) n *
    poissonCloudLevelIntegral μ g n
  let C : ℝ := ∑' n, expSeriesCoeff (rate : ℝ) n *
    poissonCloudLevelIntegral μ (fun ω => f ω * g ω) n
  let p : ℝ := Real.exp (-(rate : ℝ))
  let q : ℝ := Real.exp (rate : ℝ)
  change (p * A) * (p * B) ≤ p * C
  have hseries : A * B ≤ C * q := by
    simpa only [A, B, C, q, tsum_expSeriesCoeff] using
      tsum_expSeriesCoeff_level_mul_le μ hf hg rate.coe_nonneg
  have hp0 : 0 ≤ p := Real.exp_nonneg _
  have hpq : p * q = 1 := by
    dsimp [p, q]
    rw [← Real.exp_add]
    simp
  calc
    (p * A) * (p * B) = (p * p) * (A * B) := by ring
    _ ≤ (p * p) * (C * q) :=
      mul_le_mul_of_nonneg_left hseries (mul_nonneg hp0 hp0)
    _ = (p * C) * (p * q) := by ring
    _ = p * C := by rw [hpq, mul_one]

theorem positivelyAssociated_finiteCloudMeasure
    {ι α : Type*} [Fintype ι]
    [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ] (rate : ι → ℝ≥0) :
    @PositivelyAssociated _ inferInstance finiteCloudPointsPreorder
      (finiteCloudMeasure μ rate) := by
  letI : Preorder (PoissonCloudSample α) := cloudPointsPreorder
  change PositivelyAssociated
    (Measure.pi fun i : ι => poissonCloudMeasure μ (rate i))
  exact positivelyAssociated_pi_finite
    (fun i : ι => poissonCloudMeasure μ (rate i))
    (fun i => positivelyAssociated_poissonCloudMeasure μ (rate i))

theorem positivelyAssociated_packetSubblockMeasure
    {d : ℕ} {r : ℕ → ℝ} {α : Type*}
    [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (P : GeometricPacketInterface d r) (k : ℕ)
    (p : Fin (subblockCount P k)) :
    @PositivelyAssociated _ inferInstance finiteCloudPointsPreorder
      (packetSubblockMeasure μ P k p) := by
  unfold packetSubblockMeasure
  exact positivelyAssociated_finiteCloudMeasure μ
    (fractionalRate P k · p)

end Shepp.Section5
end SheppFlattenedModule049

section SheppFlattenedModule050
open scoped ENNReal Topology
open MeasureTheory Set

namespace Shepp.Section5

open ProbabilityTheory
open Shepp.Section2 Shepp.Section3 Shepp.Section4 TopologicalSpace

abbrev PacketInnovation
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :=
  PacketSubblockSample P k (FlatTorus d)

abbrev SpatialInnovation
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :=
  PacketInnovation P (spatialLevel P j)

noncomputable def emptyPacketInnovation
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    PacketInnovation P k :=
  fun _ => (0, fun _ => 0)

noncomputable def spatialInnovationMeasure
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    Measure (SpatialInnovation P j) := by
  classical
  exact if h : SpatialDeletionTime P j then
      packetSubblockMeasure (flatTorusVolume d) P (spatialLevel P j)
        ⟨spatialOffset P j, h⟩
    else Measure.dirac (emptyPacketInnovation P (spatialLevel P j))

noncomputable instance spatialInnovationMeasure_isProbabilityMeasure
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    IsProbabilityMeasure (spatialInnovationMeasure P j) := by
  classical
  unfold spatialInnovationMeasure
  split_ifs <;> infer_instance

abbrev SpatialSlotBits (d : ℕ) := Fin d → Fin 2

abbrev spatialSlotCount (d : ℕ) : ℕ := Fintype.card (SpatialSlotBits d)

@[simp] theorem spatialSlotCount_eq_pow (d : ℕ) :
    spatialSlotCount d = 2 ^ d := by
  simp [spatialSlotCount, SpatialSlotBits]

noncomputable def spatialSlotBitsEquiv (d : ℕ) :
    Fin (spatialSlotCount d) ≃ SpatialSlotBits d :=
  (Fintype.equivFin (SpatialSlotBits d)).symm

noncomputable def spatialPrimarySlot (d : ℕ) : Fin (spatialSlotCount d) :=
  Fintype.equivFin (SpatialSlotBits d) (fun _ => 0)

theorem finiteCloudCovered_mono_points
    {ι K : Type*} [Fintype ι] [PseudoMetricSpace K]
    (radius : ι → ℝ) {ω ω' : FiniteCloudSample ι K}
    (hω : finiteCloudPointsLE ω ω') :
    finiteCloudCovered radius ω ⊆ finiteCloudCovered radius ω' := by
  intro x hx
  simp only [finiteCloudCovered, Set.mem_iUnion] at hx ⊢
  obtain ⟨i, j, hxBall⟩ := hx
  have hcenter : (ω i).2 j ∈ cloudPoints (ω i) :=
    ⟨j, j.isLt, rfl⟩
  obtain ⟨j', hj', heq⟩ := hω i hcenter
  let jNew : Fin (ω' i).1 := ⟨j', hj'⟩
  refine ⟨i, jNew, ?_⟩
  simpa only [jNew, heq] using hxBall

def finiteCloudCoveredLE
    {ι K : Type*} [Fintype ι] [PseudoMetricSpace K]
    (radius : ι → ℝ) (ω ω' : FiniteCloudSample ι K) : Prop :=
  finiteCloudCovered radius ω ⊆ finiteCloudCovered radius ω'

noncomputable abbrev spatialInnovationPreorder
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    Preorder (SpatialInnovation P j) :=
  finiteCloudPointsPreorder

theorem positivelyAssociated_spatialInnovationMeasure
    {d : ℕ} {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (j : ℕ) :
    @PositivelyAssociated _ inferInstance (spatialInnovationPreorder P j)
      (spatialInnovationMeasure P j) := by
  classical
  letI : Preorder (SpatialInnovation P j) := spatialInnovationPreorder P j
  by_cases hdelete : SpatialDeletionTime P j
  · simp only [spatialInnovationMeasure, hdelete, dif_pos]
    exact positivelyAssociated_packetSubblockMeasure
      (flatTorusVolume d) P (spatialLevel P j)
        ⟨spatialOffset P j, hdelete⟩
  · simp only [spatialInnovationMeasure, hdelete]
    exact positivelyAssociated_dirac
      (emptyPacketInnovation P (spatialLevel P j))

noncomputable def packetDeleteResidual
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (A : CompactResidual (FlatTorus d)) (w : PacketInnovation P k) :
    CompactResidual (FlatTorus d) :=
  compactDeleteFiniteCloud (fun n : PacketMark P k => r n) A w

theorem packetDeleteResidual_le
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (A : CompactResidual (FlatTorus d)) (w : PacketInnovation P k) :
    packetDeleteResidual P k A w ≤ A :=
  compactDeleteFiniteCloud_le _ _ _

theorem packetDeleteResidual_antitone
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (A : CompactResidual (FlatTorus d)) {w w' : PacketInnovation P k}
    (hww' : finiteCloudPointsLE w w') :
    packetDeleteResidual P k A w' ≤ packetDeleteResidual P k A w := by
  intro x hx
  exact ⟨hx.1, fun hxCovered =>
    hx.2 (finiteCloudCovered_mono_points
      (fun n : PacketMark P k => r n) hww' hxCovered)⟩

noncomputable def spatialDeletionLive
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (x : SpatialParticle P) (w : PacketInnovation P k) :
    AugmentedState (SpatialParticle P) :=
  if x.level = k then
    spatialState P x.level x.label (packetDeleteResidual P k x.residual w)
  else cemetery

noncomputable def spatialDeletionSlot
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (z : AugmentedState (SpatialParticle P)) (w : PacketInnovation P k)
    (i : Fin (spatialSlotCount d)) : AugmentedState (SpatialParticle P) :=
  if i = spatialPrimarySlot d then
    match z with
    | Sum.inl x => spatialDeletionLive P k x w
    | Sum.inr _ => cemetery
  else cemetery

noncomputable def spatialRefinementLive
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (x : SpatialParticle P) (i : Fin (spatialSlotCount d)) :
    AugmentedState (SpatialParticle P) :=
  if x.level = k then
    let β := gridChild P x.level x.label (spatialSlotBitsEquiv d i)
    spatialState P (x.level + 1) β x.residual
  else cemetery

noncomputable def spatialRefinementSlot
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (z : AugmentedState (SpatialParticle P))
    (i : Fin (spatialSlotCount d)) : AugmentedState (SpatialParticle P) :=
  match z with
  | Sum.inl x => spatialRefinementLive P k x i
  | Sum.inr _ => cemetery

noncomputable def spatialTransition
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ)
    (z : AugmentedState (SpatialParticle P)) (w : SpatialInnovation P j)
    (i : Fin (spatialSlotCount d)) : AugmentedState (SpatialParticle P) := by
  classical
  exact if SpatialDeletionTime P j then
      spatialDeletionSlot P (spatialLevel P j) z w i
    else spatialRefinementSlot P (spatialLevel P j) z i

theorem flatTorusCompactSpaceOfInterface
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    CompactSpace (FlatTorus d) where
  isCompact_univ := by
    rw [← iUnion_gridCell_eq_univ P 0]
    exact isCompact_iUnion fun α => isCompact_gridCell P 0 α

theorem measurable_packetDeleteResidual
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    Measurable fun p : CompactResidual (FlatTorus d) × PacketInnovation P k =>
      packetDeleteResidual P k p.1 p.2 := by
  letI : CompactSpace (FlatTorus d) := flatTorusCompactSpaceOfInterface P
  exact measurable_compactDeleteFiniteCloud (fun n : PacketMark P k => r n)

theorem measurable_spatialDeletionLive
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    Measurable fun p : SpatialParticle P × PacketInnovation P k =>
      spatialDeletionLive P k p.1 p.2 := by
  apply measurable_sigmaProdElim
  intro label
  by_cases hlevel : label.1 = k
  · have hdelete : Measurable fun p : SpatialFiber P label × PacketInnovation P k =>
        packetDeleteResidual P k p.1.1 p.2 :=
      (measurable_packetDeleteResidual P k).comp
        ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
    simp only [spatialDeletionLive, SpatialParticle.level,
      SpatialParticle.label, SpatialParticle.residual, hlevel, if_true]
    change Measurable
      ((fun A => spatialState P label.1 label.2 A) ∘
        fun p : SpatialFiber P label × PacketInnovation P k =>
          packetDeleteResidual P k p.1.1 p.2)
    exact (measurable_spatialState P label.1 label.2).comp hdelete
  · simp only [spatialDeletionLive, SpatialParticle.level, hlevel, if_false]
    exact measurable_const

theorem measurable_spatialDeletionSlot
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (i : Fin (spatialSlotCount d)) :
    Measurable fun p : AugmentedState (SpatialParticle P) × PacketInnovation P k =>
      spatialDeletionSlot P k p.1 p.2 i := by
  by_cases hi : i = spatialPrimarySlot d
  · apply measurable_sumProdElim
    · simpa only [spatialDeletionSlot, hi, if_true] using
        measurable_spatialDeletionLive P k
    · simp only [spatialDeletionSlot, hi, if_true]
      exact measurable_const
  · simp only [spatialDeletionSlot, hi, if_false]
    exact measurable_const

theorem measurable_spatialRefinementLive
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (i : Fin (spatialSlotCount d)) :
    Measurable fun x : SpatialParticle P => spatialRefinementLive P k x i := by
  apply measurable_sigmaElim
  intro label
  by_cases hlevel : label.1 = k
  · let β := gridChild P label.1 label.2 (spatialSlotBitsEquiv d i)
    have hresidual : Measurable fun A : SpatialFiber P label =>
        (A.1 : CompactResidual (FlatTorus d)) := measurable_subtype_coe
    simp only [spatialRefinementLive, SpatialParticle.level,
      SpatialParticle.label, SpatialParticle.residual, hlevel, if_true]
    change Measurable
      ((fun A => spatialState P (label.1 + 1) β A) ∘
        fun A : SpatialFiber P label => A.1)
    exact (measurable_spatialState P (label.1 + 1) β).comp hresidual
  · simp only [spatialRefinementLive, SpatialParticle.level, hlevel, if_false]
    exact measurable_const

theorem measurable_spatialRefinementSlot
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (i : Fin (spatialSlotCount d)) :
    Measurable fun z : AugmentedState (SpatialParticle P) =>
      spatialRefinementSlot P k z i := by
  apply Measurable.sumElim
  · exact measurable_spatialRefinementLive P k i
  · exact measurable_const

theorem measurable_spatialTransition
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ)
    (i : Fin (spatialSlotCount d)) :
    Measurable fun p : AugmentedState (SpatialParticle P) × SpatialInnovation P j =>
      spatialTransition P j p.1 p.2 i := by
  classical
  by_cases hdelete : SpatialDeletionTime P j
  · simpa only [spatialTransition, hdelete, if_true] using
      measurable_spatialDeletionSlot P (spatialLevel P j) i
  · simp only [spatialTransition, hdelete, if_false]
    exact (measurable_spatialRefinementSlot P (spatialLevel P j) i).comp
      measurable_fst

@[simp] theorem spatialDeletionSlot_cemetery
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (w : PacketInnovation P k) (i : Fin (spatialSlotCount d)) :
    spatialDeletionSlot P k cemetery w i = cemetery := by
  classical
  simp [spatialDeletionSlot, cemetery]

@[simp] theorem spatialRefinementSlot_cemetery
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (i : Fin (spatialSlotCount d)) :
    spatialRefinementSlot P k cemetery i = cemetery := by
  rfl

@[simp] theorem spatialTransition_cemetery
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ)
    (w : SpatialInnovation P j) (i : Fin (spatialSlotCount d)) :
    spatialTransition P j cemetery w i = cemetery := by
  classical
  by_cases hdelete : SpatialDeletionTime P j
  · simp [spatialTransition, hdelete]
  · simp [spatialTransition, hdelete]

theorem packetDeleteResidual_mono
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    {A B : CompactResidual (FlatTorus d)} (hAB : A ≤ B)
    (w : PacketInnovation P k) :
    packetDeleteResidual P k A w ≤ packetDeleteResidual P k B w := by
  intro x hx
  exact ⟨hAB hx.1, hx.2⟩

theorem spatialDeletionLive_mono
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (w : PacketInnovation P k) {x y : SpatialParticle P}
    (hxy : spatialParticleLE x y) :
    @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE
      (spatialDeletionLive P k x w) (spatialDeletionLive P k y w) := by
  rcases x with ⟨xLabel, xResidual⟩
  rcases y with ⟨yLabel, yResidual⟩
  have hLabel : xLabel = yLabel := hxy.1
  subst yLabel
  by_cases hlevel : xLabel.1 = k
  · simp only [spatialDeletionLive, SpatialParticle.level,
      SpatialParticle.label, SpatialParticle.residual, hlevel, if_true]
    exact spatialState_mono P xLabel.1 xLabel.2
      (packetDeleteResidual_mono P k hxy.2 w)
  · simp [spatialDeletionLive, SpatialParticle.level, hlevel]

theorem spatialDeletionSlot_state_mono
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (w : PacketInnovation P k) (i : Fin (spatialSlotCount d))
    {x y : AugmentedState (SpatialParticle P)}
    (hxy : @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE x y) :
    @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE
      (spatialDeletionSlot P k x w i) (spatialDeletionSlot P k y w i) := by
  classical
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          by_cases hi : i = spatialPrimarySlot d
          · simpa [spatialDeletionSlot, hi] using
              spatialDeletionLive_mono P k w hxy
          · simp [spatialDeletionSlot, hi]
      | inr _ => exact hxy.elim
  | inr u =>
      cases u
      have hleft : spatialDeletionSlot P k
          (Sum.inr () : AugmentedState (SpatialParticle P)) w i = cemetery := by
        simp [spatialDeletionSlot, cemetery]
      rw [hleft]
      exact cemetery_le_spatialState _

theorem spatialRefinementLive_mono
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (i : Fin (spatialSlotCount d)) {x y : SpatialParticle P}
    (hxy : spatialParticleLE x y) :
    @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE
      (spatialRefinementLive P k x i) (spatialRefinementLive P k y i) := by
  rcases x with ⟨xLabel, xResidual⟩
  rcases y with ⟨yLabel, yResidual⟩
  have hLabel : xLabel = yLabel := hxy.1
  subst yLabel
  by_cases hlevel : xLabel.1 = k
  · simp only [spatialRefinementLive, SpatialParticle.level,
      SpatialParticle.label, SpatialParticle.residual, hlevel, if_true]
    exact spatialState_mono P (xLabel.1 + 1)
      (gridChild P xLabel.1 xLabel.2 (spatialSlotBitsEquiv d i)) hxy.2
  · simp [spatialRefinementLive, SpatialParticle.level, hlevel]

theorem spatialRefinementSlot_state_mono
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (i : Fin (spatialSlotCount d))
    {x y : AugmentedState (SpatialParticle P)}
    (hxy : @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE x y) :
    @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE
      (spatialRefinementSlot P k x i) (spatialRefinementSlot P k y i) := by
  cases x with
  | inl x =>
      cases y with
      | inl y => exact spatialRefinementLive_mono P k i hxy
      | inr _ => exact hxy.elim
  | inr u =>
      cases u
      have hleft : spatialRefinementSlot P k
          (Sum.inr () : AugmentedState (SpatialParticle P)) i = cemetery := rfl
      rw [hleft]
      exact cemetery_le_spatialState _

theorem spatialTransition_state_mono
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ)
    (w : SpatialInnovation P j) (i : Fin (spatialSlotCount d))
    {x y : AugmentedState (SpatialParticle P)}
    (hxy : @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE x y) :
    @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE
      (spatialTransition P j x w i) (spatialTransition P j y w i) := by
  classical
  by_cases hdelete : SpatialDeletionTime P j
  · simp only [spatialTransition, hdelete, if_true]
    exact spatialDeletionSlot_state_mono P (spatialLevel P j) w i hxy
  · simp only [spatialTransition, hdelete, if_false]
    exact spatialRefinementSlot_state_mono P (spatialLevel P j) i hxy

theorem spatialDeletionLive_antitone
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (x : SpatialParticle P) {w w' : PacketInnovation P k}
    (hww' : finiteCloudPointsLE w w') :
    @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE
      (spatialDeletionLive P k x w') (spatialDeletionLive P k x w) := by
  by_cases hlevel : x.level = k
  · simp only [spatialDeletionLive, hlevel, if_true]
    exact spatialState_mono P x.level x.label
      (packetDeleteResidual_antitone P k x.residual hww')
  · simp [spatialDeletionLive, hlevel]

theorem spatialDeletionSlot_antitone
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (z : AugmentedState (SpatialParticle P)) (i : Fin (spatialSlotCount d))
    {w w' : PacketInnovation P k}
    (hww' : finiteCloudPointsLE w w') :
    @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE
      (spatialDeletionSlot P k z w' i) (spatialDeletionSlot P k z w i) := by
  classical
  by_cases hi : i = spatialPrimarySlot d
  · cases z with
    | inl x =>
        simpa [spatialDeletionSlot, hi] using
          spatialDeletionLive_antitone P k x hww'
    | inr _ =>
        simp [spatialDeletionSlot, hi]
  · simp [spatialDeletionSlot, hi]

theorem spatialTransition_destructive
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ)
    (z : AugmentedState (SpatialParticle P)) (i : Fin (spatialSlotCount d))
    {w w' : SpatialInnovation P j}
    (hww' : @LE.le _ (spatialInnovationPreorder P j).toLE w w') :
    @LE.le _ (spatialAugmentedPartialOrder P).toPreorder.toLE
      (spatialTransition P j z w' i) (spatialTransition P j z w i) := by
  classical
  by_cases hdelete : SpatialDeletionTime P j
  · simp only [spatialTransition, hdelete, if_true]
    exact spatialDeletionSlot_antitone P (spatialLevel P j) z i hww'
  · simp only [spatialTransition, hdelete, if_false]
    exact (spatialAugmentedPartialOrder P).le_refl _

theorem measurable_spatialTransitionVector
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    Measurable fun p : AugmentedState (SpatialParticle P) × SpatialInnovation P j =>
      fun i : Fin (spatialSlotCount d) => spatialTransition P j p.1 p.2 i := by
  apply measurable_pi_lambda
  intro i
  exact measurable_spatialTransition P j i

noncomputable def spatialOneParticleKernel
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    Kernel (AugmentedState (SpatialParticle P))
      (Fin (spatialSlotCount d) → AugmentedState (SpatialParticle P)) :=
  (branchInnovationKernel
    (A := AugmentedState (SpatialParticle P)) (spatialInnovationMeasure P j)).map
      (fun p i => spatialTransition P j p.1 p.2 i)

noncomputable instance spatialOneParticleKernel_isMarkov
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    IsMarkovKernel (spatialOneParticleKernel P j) := by
  unfold spatialOneParticleKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_spatialTransitionVector P j)

theorem spatialOneParticleKernel_apply
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ)
    (z : AugmentedState (SpatialParticle P)) :
    spatialOneParticleKernel P j z =
      Measure.map (fun w i => spatialTransition P j z w i)
        (spatialInnovationMeasure P j) := by
  rw [spatialOneParticleKernel,
    Kernel.map_apply _ (measurable_spatialTransitionVector P j),
    branchInnovationKernel_apply]
  rw [Measure.map_map]
  · rfl
  · exact measurable_spatialTransitionVector P j
  · exact measurable_const.prodMk measurable_id

theorem spatialOneParticleKernel_cemetery
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    spatialOneParticleKernel P j cemetery
      (allCemetery (spatialSlotCount d)) = 1 := by
  rw [spatialOneParticleKernel_apply]
  rw [Measure.map_apply]
  · have heq :
        (fun w i => spatialTransition P j cemetery w i) ⁻¹'
            allCemetery (spatialSlotCount d) = Set.univ := by
      ext w
      simp [allCemetery]
    rw [heq]
    exact measure_univ
  · exact (measurable_spatialTransitionVector P j).comp
      (measurable_const.prodMk measurable_id)
  · exact measurableSet_allCemetery _

noncomputable def spatialKillingDelta
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) : ℝ := by
  classical
  exact if h : SpatialDeletionTime P j then
      subblockKillingDelta P (spatialLevel P j) ⟨spatialOffset P j, h⟩
    else 0

theorem spatialKillingDelta_nonneg
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    0 ≤ spatialKillingDelta P j := by
  classical
  by_cases hdelete : SpatialDeletionTime P j
  · simp only [spatialKillingDelta, hdelete, dif_pos]
    exact (subblockKillingDelta_pos P _ _).le
  · simp [spatialKillingDelta, hdelete]

theorem spatialKillingDelta_le_one
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    spatialKillingDelta P j ≤ 1 := by
  classical
  by_cases hdelete : SpatialDeletionTime P j
  · simp only [spatialKillingDelta, hdelete, dif_pos]
    unfold subblockKillingDelta
    linarith [Real.exp_pos
      (-(killingFraction d *
        subblockMass P (spatialLevel P j) ⟨spatialOffset P j, hdelete⟩))]
  · simp [spatialKillingDelta, hdelete]

theorem packetDeleteResidual_eq_bot_of_mem_coverEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (A : CompactResidual (FlatTorus d))
    (hA : (A : Set (FlatTorus d)) ⊆ gridCell P k α)
    {w : PacketInnovation P k} (hw : w ∈ subblockCellCoverEvent P k α) :
    packetDeleteResidual P k A w = ⊥ := by
  rw [← Compacts.coe_eq_empty]
  exact subset_diff_finiteCloudCovered_eq_empty_of_mem_coverEvent
    P k α hA hw

theorem subblockCellCoverEvent_subset_deletion_allCemetery
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (A : SpatialFiber P ⟨k, α⟩) :
    subblockCellCoverEvent P k α ⊆
      (fun w i => spatialDeletionSlot P k
        (Sum.inl (⟨⟨k, α⟩, A⟩ : SpatialParticle P)) w i) ⁻¹'
          allCemetery (spatialSlotCount d) := by
  intro w hw
  intro i
  have hbot : packetDeleteResidual P k A.1 w = ⊥ :=
    packetDeleteResidual_eq_bot_of_mem_coverEvent P k α A.1 A.2 hw
  classical
  change spatialDeletionSlot P k
    (Sum.inl (⟨⟨k, α⟩, A⟩ : SpatialParticle P)) w i = cemetery
  by_cases hi : i = spatialPrimarySlot d
  · rw [spatialDeletionSlot.eq_def, if_pos hi]
    change spatialDeletionLive P k
      (⟨⟨k, α⟩, A⟩ : SpatialParticle P) w = cemetery
    simp only [spatialDeletionLive, SpatialParticle.level,
      SpatialParticle.label, SpatialParticle.residual]
    apply (spatialState_eq_cemetery_iff P k α _).2
    rw [hbot]
    simp [compactIntersection]
  · simp [spatialDeletionSlot, hi]

theorem subblockKillingDelta_le_deletion_map_allCemetery
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (p : Fin (subblockCount P k)) (α : GridLabel P k)
    (A : SpatialFiber P ⟨k, α⟩) :
    subblockKillingDelta P k p ≤
      (Measure.map
        (fun w i => spatialDeletionSlot P k
          (Sum.inl (⟨⟨k, α⟩, A⟩ : SpatialParticle P)) w i)
        (packetSubblockMeasure (flatTorusVolume d) P k p)).real
          (allCemetery (spatialSlotCount d)) := by
  let ν := packetSubblockMeasure (flatTorusVolume d) P k p
  let f := fun w : PacketInnovation P k => fun i =>
    spatialDeletionSlot P k
      (Sum.inl (⟨⟨k, α⟩, A⟩ : SpatialParticle P)) w i
  have hf : Measurable f := by
    apply measurable_pi_lambda
    intro i
    have hpair : Measurable fun w : PacketInnovation P k =>
        ((Sum.inl (⟨⟨k, α⟩, A⟩ : SpatialParticle P) :
          AugmentedState (SpatialParticle P)), w) :=
      measurable_const.prodMk measurable_id
    change Measurable fun w : PacketInnovation P k =>
      spatialDeletionSlot P k
        (Sum.inl (⟨⟨k, α⟩, A⟩ : SpatialParticle P)) w i
    change Measurable
      ((fun q => spatialDeletionSlot P k q.1 q.2 i) ∘
        fun w : PacketInnovation P k =>
          ((Sum.inl (⟨⟨k, α⟩, A⟩ : SpatialParticle P) :
            AugmentedState (SpatialParticle P)), w))
    exact (measurable_spatialDeletionSlot P k i).comp hpair
  calc
    subblockKillingDelta P k p ≤
        ν.real (subblockCellCoverEvent P k α) :=
      packetSubblockMeasureReal_coverEvent_ge_delta hd P k p α
    _ ≤ ν.real (f ⁻¹' allCemetery (spatialSlotCount d)) :=
      measureReal_mono
        (subblockCellCoverEvent_subset_deletion_allCemetery P k α A)
    _ = (Measure.map f ν).real (allCemetery (spatialSlotCount d)) :=
      (map_measureReal_apply hf (measurableSet_allCemetery _)).symm

theorem subblockKillingDelta_le_deletion_map_allCemetery_of_level_eq
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ)
    (p : Fin (subblockCount P k)) (x : SpatialParticle P)
    (hlevel : x.level = k) :
    subblockKillingDelta P k p ≤
      (Measure.map
        (fun w i => spatialDeletionSlot P k (Sum.inl x) w i)
        (packetSubblockMeasure (flatTorusVolume d) P k p)).real
          (allCemetery (spatialSlotCount d)) := by
  rcases x with ⟨label, A⟩
  change label.1 = k at hlevel
  subst k
  exact subblockKillingDelta_le_deletion_map_allCemetery
    hd P label.1 p label.2 A

theorem deletion_map_allCemetery_eq_one_of_level_ne
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (p : Fin (subblockCount P k)) (x : SpatialParticle P)
    (hlevel : x.level ≠ k) :
    (Measure.map
      (fun w i => spatialDeletionSlot P k (Sum.inl x) w i)
      (packetSubblockMeasure (flatTorusVolume d) P k p)).real
        (allCemetery (spatialSlotCount d)) = 1 := by
  let ν := packetSubblockMeasure (flatTorusVolume d) P k p
  let f := fun w : PacketInnovation P k => fun i =>
    spatialDeletionSlot P k (Sum.inl x) w i
  have hf : Measurable f := by
    apply measurable_pi_lambda
    intro i
    have hpair : Measurable fun w : PacketInnovation P k =>
        ((Sum.inl x : AugmentedState (SpatialParticle P)), w) :=
      measurable_const.prodMk measurable_id
    change Measurable fun w : PacketInnovation P k =>
      spatialDeletionSlot P k (Sum.inl x) w i
    change Measurable
      ((fun q => spatialDeletionSlot P k q.1 q.2 i) ∘
        fun w : PacketInnovation P k =>
          ((Sum.inl x : AugmentedState (SpatialParticle P)), w))
    exact (measurable_spatialDeletionSlot P k i).comp hpair
  rw [map_measureReal_apply hf (measurableSet_allCemetery _)]
  have heq : f ⁻¹' allCemetery (spatialSlotCount d) = Set.univ := by
    ext w
    simp [f, allCemetery, spatialDeletionSlot, spatialDeletionLive, hlevel]
  rw [heq]
  exact probReal_univ

theorem spatialOneParticleKernel_killing
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (j : ℕ) (x : SpatialParticle P) :
    spatialKillingDelta P j ≤
      (spatialOneParticleKernel P j (Sum.inl x)).real
        (allCemetery (spatialSlotCount d)) := by
  rw [spatialOneParticleKernel_apply]
  classical
  by_cases hdelete : SpatialDeletionTime P j
  · simp only [spatialKillingDelta, hdelete, dif_pos,
      spatialInnovationMeasure, spatialTransition, if_true]
    by_cases hlevel : x.level = spatialLevel P j
    · exact subblockKillingDelta_le_deletion_map_allCemetery_of_level_eq
        hd P (spatialLevel P j) ⟨spatialOffset P j, hdelete⟩ x hlevel
    · rw [deletion_map_allCemetery_eq_one_of_level_ne P
        (spatialLevel P j) ⟨spatialOffset P j, hdelete⟩ x hlevel]
      unfold subblockKillingDelta
      linarith [Real.exp_pos
        (-(killingFraction d * subblockMass P (spatialLevel P j)
          ⟨spatialOffset P j, hdelete⟩))]
  · simp [spatialKillingDelta, hdelete]

end Shepp.Section5
end SheppFlattenedModule050

section SheppFlattenedModule051
open scoped ENNReal ProbabilityTheory Topology
open MeasureTheory Set

namespace Shepp.Section5

open ProbabilityTheory
open Shepp.Section2 Shepp.Section3 Shepp.Section4

abbrev SpatialPath
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :=
  (j : ℕ) → SpatialInnovation P j

noncomputable def spatialPathMeasure
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    Measure (SpatialPath P) :=
  Measure.infinitePi fun j => spatialInnovationMeasure P j

noncomputable instance spatialPathMeasure_isProbabilityMeasure
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    IsProbabilityMeasure (spatialPathMeasure P) := by
  unfold spatialPathMeasure
  infer_instance

theorem measurable_spatialPath_eval
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    Measurable fun ω : SpatialPath P => ω j :=
  measurable_pi_apply j

theorem spatialPath_eval_hasLaw
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    HasLaw (fun ω : SpatialPath P => ω j)
      (spatialInnovationMeasure P j) (spatialPathMeasure P) := by
  exact (measurePreserving_eval_infinitePi
    (fun i => spatialInnovationMeasure P i) j).hasLaw

theorem spatialPath_coordinates_iIndepFun
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    iIndepFun (fun j (ω : SpatialPath P) => ω j) (spatialPathMeasure P) := by
  unfold spatialPathMeasure
  exact iIndepFun_infinitePi (X := fun _ w => w) (by fun_prop)

noncomputable def fullSpatialResidual
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    CompactResidual (FlatTorus d) := by
  letI : CompactSpace (FlatTorus d) := flatTorusCompactSpaceOfInterface P
  exact ⊤

@[simp] theorem coe_fullSpatialResidual
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ((fullSpatialResidual P : CompactResidual (FlatTorus d)) :
      Set (FlatTorus d)) = Set.univ := by
  letI : CompactSpace (FlatTorus d) := flatTorusCompactSpaceOfInterface P
  simp [fullSpatialResidual]

noncomputable def spatialResidual
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ℕ → SpatialPath P → CompactResidual (FlatTorus d)
  | 0, _ω => fullSpatialResidual P
  | j + 1, ω => by
      classical
      exact if SpatialDeletionTime P j then
          packetDeleteResidual P (spatialLevel P j)
            (spatialResidual P j ω) (ω j)
        else spatialResidual P j ω

@[simp] theorem spatialResidual_zero
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (ω : SpatialPath P) :
    spatialResidual P 0 ω = fullSpatialResidual P :=
  rfl

theorem spatialResidual_succ_of_deletion
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (ω : SpatialPath P) (h : SpatialDeletionTime P j) :
    spatialResidual P (j + 1) ω =
      packetDeleteResidual P (spatialLevel P j) (spatialResidual P j ω) (ω j) := by
  simp [spatialResidual, h]

theorem spatialResidual_succ_of_refinement
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (ω : SpatialPath P) (h : ¬ SpatialDeletionTime P j) :
    spatialResidual P (j + 1) ω = spatialResidual P j ω := by
  simp [spatialResidual, h]

theorem measurable_spatialResidual
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ∀ j, Measurable (spatialResidual P j) := by
  intro j
  induction j with
  | zero =>
      exact measurable_const
  | succ j ih =>
      classical
      by_cases h : SpatialDeletionTime P j
      · rw [show spatialResidual P (j + 1) = fun ω =>
            packetDeleteResidual P (spatialLevel P j)
              (spatialResidual P j ω) (ω j) by
          funext ω
          exact spatialResidual_succ_of_deletion P j ω h]
        exact (measurable_packetDeleteResidual P (spatialLevel P j)).comp
          (ih.prodMk (measurable_spatialPath_eval P j))
      · rw [show spatialResidual P (j + 1) = spatialResidual P j by
          funext ω
          exact spatialResidual_succ_of_refinement P j ω h]
        exact ih

theorem spatialResidual_succ_le
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (ω : SpatialPath P) :
    spatialResidual P (j + 1) ω ≤ spatialResidual P j ω := by
  classical
  by_cases h : SpatialDeletionTime P j
  · rw [spatialResidual_succ_of_deletion P j ω h]
    exact packetDeleteResidual_le P (spatialLevel P j)
      (spatialResidual P j ω) (ω j)
  · rw [spatialResidual_succ_of_refinement P j ω h]

theorem spatialResidual_antitone
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (ω : SpatialPath P) :
    Antitone fun j => spatialResidual P j ω :=
  antitone_nat_of_succ_le fun j => spatialResidual_succ_le P j ω

noncomputable def spatialGridLabelEquiv
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    Fin (Fintype.card (GridLabel P k)) ≃ GridLabel P k :=
  (Fintype.equivFin (GridLabel P k)).symm

noncomputable def spatialInitialPopulation
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    FinitePopulation (AugmentedState (SpatialParticle P)) :=
  ⟨Fintype.card (GridLabel P 0), fun i =>
    spatialState P 0 (spatialGridLabelEquiv P 0 i) (fullSpatialResidual P)⟩

theorem measurable_spatialFinitePopulationUpdate
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    Measurable fun p :
        FinitePopulation (AugmentedState (SpatialParticle P)) ×
          SpatialInnovation P j =>
      sharedFinitePopulationUpdate (spatialTransition P j) p.1 p.2 := by
  apply measurable_sigmaProdElim
  intro q
  exact measurable_sharedFinitePopulationUpdate_branch
    (spatialTransition P j) (fun i => measurable_spatialTransition P j i) q

noncomputable def spatialPopulationPath
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ℕ → SpatialPath P → FinitePopulation (AugmentedState (SpatialParticle P))
  | 0, _ω => spatialInitialPopulation P
  | j + 1, ω =>
      sharedFinitePopulationUpdate (spatialTransition P j)
        (spatialPopulationPath P j ω) (ω j)

@[simp] theorem spatialPopulationPath_zero
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (ω : SpatialPath P) :
    spatialPopulationPath P 0 ω = spatialInitialPopulation P :=
  rfl

@[simp] theorem spatialPopulationPath_succ
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (ω : SpatialPath P) :
    spatialPopulationPath P (j + 1) ω =
      sharedFinitePopulationUpdate (spatialTransition P j)
        (spatialPopulationPath P j ω) (ω j) :=
  rfl

theorem measurable_spatialPopulationPath
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ∀ j, Measurable (spatialPopulationPath P j) := by
  intro j
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
      exact (measurable_spatialFinitePopulationUpdate P j).comp
        (ih.prodMk (measurable_spatialPath_eval P j))

abbrev SpatialPrefix
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :=
  (i : Fin j) → SpatialInnovation P i.1

def spatialPathPrefix
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ)
    (ω : SpatialPath P) : SpatialPrefix P j :=
  fun i => ω i.1

theorem measurable_spatialPathPrefix
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    Measurable (spatialPathPrefix P j) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_spatialPath_eval P i.1

def spatialPrefixInit
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r} {j : ℕ}
    (u : SpatialPrefix P (j + 1)) : SpatialPrefix P j :=
  fun i => u i.castSucc

def spatialPrefixLast
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r} {j : ℕ}
    (u : SpatialPrefix P (j + 1)) : SpatialInnovation P j :=
  u (Fin.last j)

theorem measurable_spatialPrefixInit
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r} (j : ℕ) :
    Measurable (spatialPrefixInit (P := P) (j := j)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.castSucc

theorem measurable_spatialPrefixLast
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r} (j : ℕ) :
    Measurable (spatialPrefixLast (P := P) (j := j)) :=
  measurable_pi_apply (Fin.last j)

noncomputable def spatialPopulationOfPrefix
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    (j : ℕ) → SpatialPrefix P j →
      FinitePopulation (AugmentedState (SpatialParticle P))
  | 0, _u => spatialInitialPopulation P
  | j + 1, u =>
      sharedFinitePopulationUpdate (spatialTransition P j)
        (spatialPopulationOfPrefix P j (spatialPrefixInit u))
        (spatialPrefixLast u)

theorem measurable_spatialPopulationOfPrefix
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ∀ j, Measurable (spatialPopulationOfPrefix P j) := by
  intro j
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
      exact (measurable_spatialFinitePopulationUpdate P j).comp
        ((ih.comp (measurable_spatialPrefixInit j)).prodMk
          (measurable_spatialPrefixLast j))

theorem spatialPopulationPath_eq_ofPrefix
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (ω : SpatialPath P) :
    spatialPopulationPath P j ω =
      spatialPopulationOfPrefix P j (spatialPathPrefix P j ω) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [spatialPopulationPath_succ]
      simp only [spatialPopulationOfPrefix]
      rw [ih]
      rfl

theorem spatialPopulationPath_indepFun_next
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    IndepFun (spatialPopulationPath P j)
      (fun ω : SpatialPath P => ω j) (spatialPathMeasure P) := by
  let S : Finset ℕ := Finset.range j
  let T : Finset ℕ := {j}
  have hdisjoint : Disjoint S T := by
    simp [S, T]
  have hraw : IndepFun
      (fun (ω : SpatialPath P) (i : S) => ω i.1)
      (fun (ω : SpatialPath P) (i : T) => ω i.1)
      (spatialPathMeasure P) :=
    iIndepFun.indepFun_finset S T hdisjoint
      (spatialPath_coordinates_iIndepFun P)
      (fun i => measurable_spatialPath_eval P i)
  let reindex : ((i : S) → SpatialInnovation P i.1) → SpatialPrefix P j :=
    fun u i => u ⟨i.1, by simpa [S] using i.2⟩
  have hreindex : Measurable reindex := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply
      (⟨i.1, by simpa [S] using i.2⟩ : S)
  let pastToPopulation : ((i : S) → SpatialInnovation P i.1) →
      FinitePopulation (AugmentedState (SpatialParticle P)) :=
    fun u => spatialPopulationOfPrefix P j (reindex u)
  have hpast : Measurable pastToPopulation :=
    (measurable_spatialPopulationOfPrefix P j).comp hreindex
  let singletonToInnovation : ((i : T) → SpatialInnovation P i.1) →
      SpatialInnovation P j :=
    fun u => u ⟨j, by simp [T]⟩
  have hsingleton : Measurable singletonToInnovation :=
    measurable_pi_apply (⟨j, by simp [T]⟩ : T)
  have hcomp := hraw.comp hpast hsingleton
  have hleft :
      pastToPopulation ∘
          (fun (ω : SpatialPath P) (i : S) => ω i.1) =
        spatialPopulationPath P j := by
    funext ω
    rw [spatialPopulationPath_eq_ofPrefix P j ω]
    rfl
  have hright :
      singletonToInnovation ∘
          (fun (ω : SpatialPath P) (i : T) => ω i.1) =
        fun ω : SpatialPath P => ω j := by
    rfl
  rw [hleft, hright] at hcomp
  exact hcomp

theorem map_spatialFinitePopulationUpdate_prod
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ)
    (ρ : Measure (FinitePopulation (AugmentedState (SpatialParticle P)))) :
    Measure.map
        (fun p : FinitePopulation (AugmentedState (SpatialParticle P)) ×
            SpatialInnovation P j =>
          sharedFinitePopulationUpdate (spatialTransition P j) p.1 p.2)
        (ρ.prod (spatialInnovationMeasure P j)) =
      ρ.bind
        (sharedPopulationKernel (spatialInnovationMeasure P j)
          (spatialTransition P j)
          (fun i => measurable_spatialTransition P j i)) := by
  let U := fun p : FinitePopulation (AugmentedState (SpatialParticle P)) ×
      SpatialInnovation P j =>
    sharedFinitePopulationUpdate (spatialTransition P j) p.1 p.2
  have hU : Measurable U := measurable_spatialFinitePopulationUpdate P j
  ext s hs
  rw [Measure.map_apply hU hs, Measure.prod_apply (hU hs)]
  rw [Measure.bind_apply hs
    (sharedPopulationKernel (spatialInnovationMeasure P j)
      (spatialTransition P j)
      (fun i => measurable_spatialTransition P j i)).aemeasurable]
  apply lintegral_congr
  rintro ⟨q, xs⟩
  change spatialInnovationMeasure P j
      ((fun w => sharedFinitePopulationUpdate (spatialTransition P j)
        ⟨q, xs⟩ w) ⁻¹' s) =
    sharedPopulationBranchKernel (spatialInnovationMeasure P j)
      (spatialTransition P j)
      (fun i => measurable_spatialTransition P j i) q xs s
  rw [sharedPopulationBranchKernel_apply]
  have hfixed : Measurable fun w =>
      sharedFinitePopulationUpdate (spatialTransition P j) ⟨q, xs⟩ w :=
    (measurable_sharedFinitePopulationUpdate_branch
      (spatialTransition P j)
      (fun i => measurable_spatialTransition P j i) q).comp
        (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hfixed hs]

noncomputable def spatialRecursivePopulationLaw
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ℕ → Measure (FinitePopulation (AugmentedState (SpatialParticle P)))
  | 0 => Measure.dirac (spatialInitialPopulation P)
  | j + 1 =>
      (spatialRecursivePopulationLaw P j).bind
        (sharedPopulationKernel (spatialInnovationMeasure P j)
          (spatialTransition P j)
          (fun i => measurable_spatialTransition P j i))

noncomputable instance spatialRecursivePopulationLaw_isProbabilityMeasure
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    IsProbabilityMeasure (spatialRecursivePopulationLaw P j) := by
  induction j with
  | zero =>
      simp only [spatialRecursivePopulationLaw]
      infer_instance
  | succ j ih =>
      simp only [spatialRecursivePopulationLaw]
      apply isProbabilityMeasure_bind
        (sharedPopulationKernel (spatialInnovationMeasure P j)
          (spatialTransition P j)
          (fun i => measurable_spatialTransition P j i)).aemeasurable
      filter_upwards with ξ
      infer_instance

theorem spatialPopulationPath_hasLaw_recursive
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ∀ j, HasLaw (spatialPopulationPath P j)
      (spatialRecursivePopulationLaw P j) (spatialPathMeasure P) := by
  intro j
  induction j with
  | zero =>
      apply hasLaw_dirac_of_ae_eq
      exact Filter.Eventually.of_forall fun _ => rfl
  | succ j ih =>
      have hpair : HasLaw
          (fun ω : SpatialPath P =>
            (spatialPopulationPath P j ω, ω j))
          ((spatialRecursivePopulationLaw P j).prod
            (spatialInnovationMeasure P j))
          (spatialPathMeasure P) :=
        (spatialPopulationPath_indepFun_next P j).hasLaw_prod ih
          (spatialPath_eval_hasLaw P j)
      have hmap : HasLaw
          (fun p : FinitePopulation (AugmentedState (SpatialParticle P)) ×
              SpatialInnovation P j =>
            sharedFinitePopulationUpdate (spatialTransition P j) p.1 p.2)
          (spatialRecursivePopulationLaw P (j + 1))
          ((spatialRecursivePopulationLaw P j).prod
            (spatialInnovationMeasure P j)) := by
        refine ⟨(measurable_spatialFinitePopulationUpdate P j).aemeasurable, ?_⟩
        rw [spatialRecursivePopulationLaw]
        exact map_spatialFinitePopulationUpdate_prod P j
          (spatialRecursivePopulationLaw P j)
      have hcomp := hmap.comp hpair
      have heq :
          (fun p : FinitePopulation (AugmentedState (SpatialParticle P)) ×
                SpatialInnovation P j =>
              sharedFinitePopulationUpdate (spatialTransition P j) p.1 p.2) ∘
              (fun ω : SpatialPath P =>
                (spatialPopulationPath P j ω, ω j)) =
            spatialPopulationPath P (j + 1) := by
        funext ω
        rfl
      rw [heq] at hcomp
      exact hcomp

noncomputable abbrev spatialPopulationKernel
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    Kernel (FinitePopulation (AugmentedState (SpatialParticle P)))
      (FinitePopulation (AugmentedState (SpatialParticle P))) :=
  sharedPopulationKernel (spatialInnovationMeasure P j)
    (spatialTransition P j) (fun i => measurable_spatialTransition P j i)

noncomputable abbrev spatialEvolutionKernel
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j steps : ℕ) :
    Kernel (FinitePopulation (AugmentedState (SpatialParticle P)))
      (FinitePopulation (AugmentedState (SpatialParticle P))) :=
  sharedEvolutionKernel (fun _ => spatialSlotCount d)
    (fun t => spatialInnovationMeasure P t)
    (fun t => spatialTransition P t)
    (fun t i => measurable_spatialTransition P t i) j steps

theorem spatialEvolutionKernel_append_one
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j steps : ℕ) :
    spatialEvolutionKernel P j (steps + 1) =
      Kernel.comp (spatialPopulationKernel P (j + steps))
        (spatialEvolutionKernel P j steps) := by
  induction steps generalizing j with
  | zero =>
      change Kernel.comp
          (Kernel.id : Kernel
            (FinitePopulation (AugmentedState (SpatialParticle P)))
            (FinitePopulation (AugmentedState (SpatialParticle P))))
          (spatialPopulationKernel P j) =
        Kernel.comp (spatialPopulationKernel P j)
          (Kernel.id : Kernel
            (FinitePopulation (AugmentedState (SpatialParticle P)))
            (FinitePopulation (AugmentedState (SpatialParticle P))))
      simp
  | succ steps ih =>
      calc
        spatialEvolutionKernel P j ((steps + 1) + 1) =
            Kernel.comp (spatialEvolutionKernel P (j + 1) (steps + 1))
              (spatialPopulationKernel P j) := rfl
        _ = Kernel.comp
              (Kernel.comp (spatialPopulationKernel P ((j + 1) + steps))
                (spatialEvolutionKernel P (j + 1) steps))
              (spatialPopulationKernel P j) := by
                rw [ih (j + 1)]
        _ = Kernel.comp (spatialPopulationKernel P (j + (steps + 1)))
              (Kernel.comp (spatialEvolutionKernel P (j + 1) steps)
                (spatialPopulationKernel P j)) := by
                rw [Kernel.comp_assoc]
                congr 2
                omega
        _ = Kernel.comp (spatialPopulationKernel P (j + (steps + 1)))
              (spatialEvolutionKernel P j (steps + 1)) := rfl

noncomputable abbrev spatialSharedPopulationLaw
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (steps : ℕ) :
    Measure (FinitePopulation (AugmentedState (SpatialParticle P))) :=
  sharedPopulationLaw (fun _ => spatialSlotCount d)
    (fun t => spatialInnovationMeasure P t)
    (fun t => spatialTransition P t)
    (fun t i => measurable_spatialTransition P t i)
    (Measure.dirac (spatialInitialPopulation P)) steps

@[simp] theorem spatialSharedPopulationLaw_zero
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    spatialSharedPopulationLaw P 0 =
      Measure.dirac (spatialInitialPopulation P) := by
  simp [spatialSharedPopulationLaw, sharedPopulationLaw]

theorem spatialSharedPopulationLaw_succ
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (steps : ℕ) :
    spatialSharedPopulationLaw P (steps + 1) =
      (spatialSharedPopulationLaw P steps).bind
        (spatialPopulationKernel P steps) := by
  change (Measure.dirac (spatialInitialPopulation P)).bind
      (spatialEvolutionKernel P 0 (steps + 1)) =
    ((Measure.dirac (spatialInitialPopulation P)).bind
      (spatialEvolutionKernel P 0 steps)).bind
        (spatialPopulationKernel P steps)
  rw [spatialEvolutionKernel_append_one P 0 steps]
  simp only [Nat.zero_add]
  change (Measure.dirac (spatialInitialPopulation P)).bind
      (fun ξ => (spatialEvolutionKernel P 0 steps ξ).bind
        (spatialPopulationKernel P steps)) =
    ((Measure.dirac (spatialInitialPopulation P)).bind
      (spatialEvolutionKernel P 0 steps)).bind
        (spatialPopulationKernel P steps)
  exact (Measure.bind_bind (spatialEvolutionKernel P 0 steps).aemeasurable
    (spatialPopulationKernel P steps).aemeasurable).symm

theorem spatialRecursivePopulationLaw_eq_shared
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ∀ steps, spatialRecursivePopulationLaw P steps =
      spatialSharedPopulationLaw P steps := by
  intro steps
  induction steps with
  | zero =>
      simp [spatialRecursivePopulationLaw]
  | succ steps ih =>
      rw [spatialRecursivePopulationLaw, ih,
        spatialSharedPopulationLaw_succ]

theorem spatialPopulationPath_hasLaw_shared
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (steps : ℕ) :
    HasLaw (spatialPopulationPath P steps)
      (spatialSharedPopulationLaw P steps) (spatialPathMeasure P) := by
  rw [← spatialRecursivePopulationLaw_eq_shared P steps]
  exact spatialPopulationPath_hasLaw_recursive P steps

end Shepp.Section5
end SheppFlattenedModule051

section SheppFlattenedModule052
open scoped ENNReal ProbabilityTheory Topology
open MeasureTheory Set

namespace Shepp.Section5

open ProbabilityTheory
open Shepp.Section2 Shepp.Section3 Shepp.Section4

theorem gridLower_child
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (ε : SpatialSlotBits d) (i : Fin d) :
    gridLower P (k + 1) (gridChild P k α ε) i =
      ((α i : ℝ) + (ε i : ℝ) / 2) * gridMesh P k := by
  change ((2 * (α i : ℕ) + (ε i : ℕ) : ℕ) : ℝ) *
      gridMesh P (k + 1) = _
  rw [gridMesh_succ]
  push_cast
  ring

theorem gridUpper_child
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (ε : SpatialSlotBits d) (i : Fin d) :
    gridUpper P (k + 1) (gridChild P k α ε) i =
      ((α i : ℝ) + ((ε i : ℝ) + 1) / 2) * gridMesh P k := by
  change (((2 * (α i : ℕ) + (ε i : ℕ) : ℕ) : ℝ) + 1) *
      gridMesh P (k + 1) = _
  rw [gridMesh_succ]
  push_cast
  ring

theorem exists_mem_gridChild_of_mem_gridCell
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) {z : FlatTorus d}
    (hz : z ∈ gridCell P k α) :
    ∃ ε : SpatialSlotBits d, z ∈ gridCell P (k + 1) (gridChild P k α ε) := by
  rcases hz with ⟨x, hx, rfl⟩
  let ε : SpatialSlotBits d := fun i =>
    if x i ≤ ((α i : ℝ) + 1 / 2) * gridMesh P k then 0 else 1
  refine ⟨ε, x, ?_, rfl⟩
  intro i
  have hi := hx i
  rw [gridLower_child, gridUpper_child]
  dsimp only [ε]
  split_ifs with hmid
  · norm_num
    constructor
    · simpa only [gridLower] using hi.1
    · exact hmid
  · have hmid' : ((α i : ℝ) + 1 / 2) * gridMesh P k < x i :=
      lt_of_not_ge hmid
    norm_num
    constructor
    · exact hmid'.le
    · simpa only [gridUpper] using hi.2

theorem spatialState_live_facts
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (A : CompactResidual (FlatTorus d))
    {x : SpatialParticle P} (hx : spatialState P k α A = Sum.inl x) :
    x.level = k ∧
      x.residual = compactIntersection A (compactGridCell P k α) ∧
      x.residual ≠ ⊥ := by
  have hnonempty :
      compactIntersection A (compactGridCell P k α) ≠ ⊥ := by
    intro hempty
    have hcemetery := (spatialState_eq_cemetery_iff P k α A).2 hempty
    rw [hcemetery] at hx
    cases hx
  rw [spatialState_eq_live_of_nonempty P k α A hnonempty] at hx
  cases hx
  exact ⟨rfl, rfl, hnonempty⟩

theorem exists_live_spatialState_iff
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (A : CompactResidual (FlatTorus d))
    (z : FlatTorus d) :
    (∃ x : SpatialParticle P,
        spatialState P k α A = Sum.inl x ∧ z ∈ x.residual) ↔
      z ∈ A ∧ z ∈ gridCell P k α := by
  constructor
  · rintro ⟨x, hx, hzx⟩
    have hfacts := spatialState_live_facts P k α A hx
    rw [hfacts.2.1] at hzx
    exact hzx
  · rintro ⟨hzA, hzcell⟩
    have hnonempty :
        compactIntersection A (compactGridCell P k α) ≠ ⊥ := by
      intro hempty
      exact (compactIntersection_eq_bot_iff A (compactGridCell P k α)).mp
        hempty ⟨z, hzA, hzcell⟩
    rw [spatialState_eq_live_of_nonempty P k α A hnonempty]
    refine ⟨_, rfl, ?_⟩
    exact ⟨hzA, hzcell⟩

noncomputable def spatialPopulationSupport
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P))) :
    Set (FlatTorus d) :=
  {z | ∃ i, ∃ x : SpatialParticle P,
    ξ.2 i = Sum.inl x ∧ z ∈ x.residual}

theorem mem_spatialPopulationSupport_iff
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (z : FlatTorus d) :
    z ∈ spatialPopulationSupport ξ ↔
      ∃ i, ∃ x : SpatialParticle P,
        ξ.2 i = Sum.inl x ∧ z ∈ x.residual :=
  Iff.rfl

theorem mem_spatialPopulationSupport_sharedUpdate_iff
    {d n q : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    {W : Type*}
    (T : AugmentedState (SpatialParticle P) → W → Fin n →
      AugmentedState (SpatialParticle P))
    (xs : Fin q → AugmentedState (SpatialParticle P)) (w : W)
    (z : FlatTorus d) :
    z ∈ spatialPopulationSupport
        (sharedFinitePopulationUpdate T ⟨q, xs⟩ w) ↔
      ∃ i : Fin q, ∃ l : Fin n, ∃ x : SpatialParticle P,
        T (xs i) w l = Sum.inl x ∧ z ∈ x.residual := by
  constructor
  · rintro ⟨m, x, hmx, hzx⟩
    let il : Fin q × Fin n := finProdFinEquiv.symm m
    refine ⟨il.1, il.2, x, ?_, hzx⟩
    exact hmx
  · rintro ⟨i, l, x, hx, hzx⟩
    refine ⟨finProdFinEquiv (i, l), x, ?_, hzx⟩
    simpa [sharedFinitePopulationUpdate] using hx

def SpatialPopulationValid
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P))) : Prop :=
  ∀ i x, ξ.2 i = Sum.inl x → x.level = k ∧ x.residual ≠ ⊥

def SpatialPopulationRep
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (A : CompactResidual (FlatTorus d)) : Prop :=
  SpatialPopulationValid P k ξ ∧ spatialPopulationSupport ξ = (A : Set _)

theorem exists_live_spatialTransition_of_deletion_iff
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (hdelete : SpatialDeletionTime P j)
    (x : SpatialParticle P) (hxlevel : x.level = spatialLevel P j)
    (w : SpatialInnovation P j) (z : FlatTorus d) :
    (∃ l : Fin (spatialSlotCount d), ∃ y : SpatialParticle P,
        spatialTransition P j (Sum.inl x) w l = Sum.inl y ∧
          z ∈ y.residual) ↔
      z ∈ packetDeleteResidual P (spatialLevel P j) x.residual w := by
  constructor
  · rintro ⟨l, y, hly, hzy⟩
    by_cases hl : l = spatialPrimarySlot d
    · have hstate :
          spatialState P x.level x.label
              (packetDeleteResidual P (spatialLevel P j) x.residual w) =
            Sum.inl y := by
          simpa [spatialTransition, hdelete, spatialDeletionSlot, hl,
            spatialDeletionLive, hxlevel] using hly
      exact ((exists_live_spatialState_iff P x.level x.label
        (packetDeleteResidual P (spatialLevel P j) x.residual w) z).1
          ⟨y, hstate, hzy⟩).1
    · simp [spatialTransition, hdelete, spatialDeletionSlot, hl] at hly
      change (Sum.inr () : AugmentedState (SpatialParticle P)) = Sum.inl y at hly
      cases hly
  · intro hz
    have hzcell : z ∈ gridCell P x.level x.label :=
      x.residual_subset_cell hz.1
    rcases (exists_live_spatialState_iff P x.level x.label
      (packetDeleteResidual P (spatialLevel P j) x.residual w) z).2
        ⟨hz, hzcell⟩ with ⟨y, hy, hzy⟩
    refine ⟨spatialPrimarySlot d, y, ?_, hzy⟩
    simpa [spatialTransition, hdelete, spatialDeletionSlot,
      spatialDeletionLive, hxlevel] using hy

theorem exists_live_spatialTransition_of_refinement_iff
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (hrefine : ¬SpatialDeletionTime P j)
    (x : SpatialParticle P) (hxlevel : x.level = spatialLevel P j)
    (w : SpatialInnovation P j) (z : FlatTorus d) :
    (∃ l : Fin (spatialSlotCount d), ∃ y : SpatialParticle P,
        spatialTransition P j (Sum.inl x) w l = Sum.inl y ∧
          z ∈ y.residual) ↔
      z ∈ x.residual := by
  constructor
  · rintro ⟨l, y, hly, hzy⟩
    have hstate :
        spatialState P (x.level + 1)
            (gridChild P x.level x.label (spatialSlotBitsEquiv d l))
            x.residual = Sum.inl y := by
      simpa [spatialTransition, hrefine, spatialRefinementSlot,
        spatialRefinementLive, hxlevel] using hly
    exact ((exists_live_spatialState_iff P (x.level + 1)
      (gridChild P x.level x.label (spatialSlotBitsEquiv d l))
      x.residual z).1 ⟨y, hstate, hzy⟩).1
  · intro hz
    rcases exists_mem_gridChild_of_mem_gridCell P x.level x.label
        (x.residual_subset_cell hz) with ⟨ε, hzε⟩
    let l : Fin (spatialSlotCount d) := (spatialSlotBitsEquiv d).symm ε
    have hzchild : z ∈ gridCell P (x.level + 1)
        (gridChild P x.level x.label (spatialSlotBitsEquiv d l)) := by
      simpa [l] using hzε
    rcases (exists_live_spatialState_iff P (x.level + 1)
      (gridChild P x.level x.label (spatialSlotBitsEquiv d l))
      x.residual z).2 ⟨hz, hzchild⟩ with ⟨y, hy, hzy⟩
    refine ⟨l, y, ?_, hzy⟩
    simpa [spatialTransition, hrefine, spatialRefinementSlot,
      spatialRefinementLive, hxlevel] using hy

theorem spatialPopulationSupport_update_of_deletion
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (hdelete : SpatialDeletionTime P j)
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (hvalid : SpatialPopulationValid P (spatialLevel P j) ξ)
    (A : CompactResidual (FlatTorus d))
    (hsupport : spatialPopulationSupport ξ = (A : Set _))
    (w : SpatialInnovation P j) :
    spatialPopulationSupport
        (sharedFinitePopulationUpdate (spatialTransition P j) ξ w) =
      (packetDeleteResidual P (spatialLevel P j) A w : Set _) := by
  rcases ξ with ⟨q, xs⟩
  ext z
  rw [mem_spatialPopulationSupport_sharedUpdate_iff]
  constructor
  · rintro ⟨i, l, y, hly, hzy⟩
    cases hxi : xs i with
    | inl x =>
        have hxlevel := (hvalid i x hxi).1
        rw [hxi] at hly
        have hzdelete :=
          (exists_live_spatialTransition_of_deletion_iff
            P j hdelete x hxlevel w z).1 ⟨l, y, hly, hzy⟩
        change z ∈ x.residual ∧
          z ∉ finiteCloudCovered
            (fun n : PacketMark P (spatialLevel P j) => r n) w at hzdelete
        change z ∈ A ∧
          z ∉ finiteCloudCovered
            (fun n : PacketMark P (spatialLevel P j) => r n) w
        have hzglobal : z ∈ spatialPopulationSupport ⟨q, xs⟩ :=
          ⟨i, x, hxi, hzdelete.1⟩
        rw [hsupport] at hzglobal
        exact ⟨hzglobal, hzdelete.2⟩
    | inr u =>
        cases u
        rw [hxi] at hly
        change spatialTransition P j cemetery w l = Sum.inl y at hly
        rw [spatialTransition_cemetery] at hly
        change (Sum.inr () : AugmentedState (SpatialParticle P)) = Sum.inl y at hly
        cases hly
  · intro hz
    change z ∈ A ∧
      z ∉ finiteCloudCovered
        (fun n : PacketMark P (spatialLevel P j) => r n) w at hz
    have hzsupport : z ∈ spatialPopulationSupport ⟨q, xs⟩ := by
      rw [hsupport]
      exact hz.1
    rcases hzsupport with ⟨i, x, hxi, hzx⟩
    change xs i = Sum.inl x at hxi
    have hxlevel := (hvalid i x hxi).1
    have hzdelete :
        z ∈ packetDeleteResidual P (spatialLevel P j) x.residual w := by
      exact ⟨hzx, hz.2⟩
    rcases (exists_live_spatialTransition_of_deletion_iff
      P j hdelete x hxlevel w z).2 hzdelete with ⟨l, y, hly, hzy⟩
    refine ⟨i, l, y, ?_, hzy⟩
    rw [hxi]
    exact hly

theorem spatialPopulationSupport_update_of_refinement
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (hrefine : ¬SpatialDeletionTime P j)
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (hvalid : SpatialPopulationValid P (spatialLevel P j) ξ)
    (w : SpatialInnovation P j) :
    spatialPopulationSupport
        (sharedFinitePopulationUpdate (spatialTransition P j) ξ w) =
      spatialPopulationSupport ξ := by
  rcases ξ with ⟨q, xs⟩
  ext z
  rw [mem_spatialPopulationSupport_sharedUpdate_iff]
  constructor
  · rintro ⟨i, l, y, hly, hzy⟩
    cases hxi : xs i with
    | inl x =>
        have hxlevel := (hvalid i x hxi).1
        rw [hxi] at hly
        have hzx :=
          (exists_live_spatialTransition_of_refinement_iff
            P j hrefine x hxlevel w z).1 ⟨l, y, hly, hzy⟩
        exact ⟨i, x, hxi, hzx⟩
    | inr u =>
        cases u
        rw [hxi] at hly
        change spatialTransition P j cemetery w l = Sum.inl y at hly
        rw [spatialTransition_cemetery] at hly
        change (Sum.inr () : AugmentedState (SpatialParticle P)) = Sum.inl y at hly
        cases hly
  · rintro ⟨i, x, hxi, hzx⟩
    change xs i = Sum.inl x at hxi
    have hxlevel := (hvalid i x hxi).1
    rcases (exists_live_spatialTransition_of_refinement_iff
      P j hrefine x hxlevel w z).2 hzx with ⟨l, y, hly, hzy⟩
    refine ⟨i, l, y, ?_, hzy⟩
    rw [hxi]
    exact hly

theorem spatialPopulationValid_update
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ)
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (hvalid : SpatialPopulationValid P (spatialLevel P j) ξ)
    (w : SpatialInnovation P j) :
    SpatialPopulationValid P (spatialLevel P (j + 1))
      (sharedFinitePopulationUpdate (spatialTransition P j) ξ w) := by
  rcases ξ with ⟨q, xs⟩
  intro m y hmy
  let il : Fin q × Fin (spatialSlotCount d) := finProdFinEquiv.symm m
  change spatialTransition P j (xs il.1) w il.2 = Sum.inl y at hmy
  cases hxi : xs il.1 with
  | inr u =>
      cases u
      rw [hxi] at hmy
      change spatialTransition P j cemetery w il.2 = Sum.inl y at hmy
      rw [spatialTransition_cemetery] at hmy
      change (Sum.inr () : AugmentedState (SpatialParticle P)) = Sum.inl y at hmy
      cases hmy
  | inl x =>
      have hxlevel := (hvalid il.1 x hxi).1
      rw [hxi] at hmy
      by_cases hdelete : SpatialDeletionTime P j
      · by_cases hl : il.2 = spatialPrimarySlot d
        · have hstate :
              spatialState P x.level x.label
                  (packetDeleteResidual P (spatialLevel P j) x.residual w) =
                Sum.inl y := by
              simpa [spatialTransition, hdelete, spatialDeletionSlot, hl,
                spatialDeletionLive, hxlevel] using hmy
          have hfacts := spatialState_live_facts P x.level x.label
            (packetDeleteResidual P (spatialLevel P j) x.residual w) hstate
          refine ⟨?_, hfacts.2.2⟩
          calc
            y.level = x.level := hfacts.1
            _ = spatialLevel P j := hxlevel
            _ = spatialLevel P (j + 1) :=
              (blockIndex_succ_of_deletion (subblockCount P) j hdelete).symm
        · simp [spatialTransition, hdelete, spatialDeletionSlot, hl] at hmy
          change (Sum.inr () : AugmentedState (SpatialParticle P)) = Sum.inl y at hmy
          cases hmy
      · have hstate :
            spatialState P (x.level + 1)
                (gridChild P x.level x.label (spatialSlotBitsEquiv d il.2))
                x.residual = Sum.inl y := by
            simpa [spatialTransition, hdelete, spatialRefinementSlot,
              spatialRefinementLive, hxlevel] using hmy
        have hfacts := spatialState_live_facts P (x.level + 1)
          (gridChild P x.level x.label (spatialSlotBitsEquiv d il.2))
          x.residual hstate
        refine ⟨?_, hfacts.2.2⟩
        calc
          y.level = x.level + 1 := hfacts.1
          _ = spatialLevel P j + 1 := congrArg (fun t => t + 1) hxlevel
          _ = spatialLevel P (j + 1) :=
            (blockIndex_succ_of_refinement (subblockCount P) j hdelete).symm

theorem spatialInitialPopulation_rep
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    SpatialPopulationRep P (spatialLevel P 0)
      (spatialInitialPopulation P) (fullSpatialResidual P) := by
  have hlevel0 : spatialLevel P 0 = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact (self_le_blockStart (subblockCount P)
      (blockIndex (subblockCount P) 0)).trans
        (blockIndex_lower (subblockCount P) 0)
  constructor
  · intro i x hix
    have hfacts := spatialState_live_facts P 0
      (spatialGridLabelEquiv P 0 i) (fullSpatialResidual P) hix
    exact ⟨hfacts.1.trans hlevel0.symm, hfacts.2.2⟩
  · ext z
    constructor
    · rintro ⟨i, x, hix, hzx⟩
      have hzfull := (exists_live_spatialState_iff P 0
        (spatialGridLabelEquiv P 0 i) (fullSpatialResidual P) z).1
          ⟨x, hix, hzx⟩
      exact hzfull.1
    · intro hzfull
      rcases exists_mem_gridCell P 0 z with ⟨α, hzα⟩
      let i : Fin (Fintype.card (GridLabel P 0)) :=
        (spatialGridLabelEquiv P 0).symm α
      have hzstate := (exists_live_spatialState_iff P 0 α
        (fullSpatialResidual P) z).2 ⟨hzfull, hzα⟩
      rcases hzstate with ⟨x, hx, hzx⟩
      refine ⟨i, x, ?_, hzx⟩
      simpa [spatialInitialPopulation, i] using hx

theorem spatialPopulationPath_rep
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ∀ j (ω : SpatialPath P),
      SpatialPopulationRep P (spatialLevel P j)
        (spatialPopulationPath P j ω) (spatialResidual P j ω) := by
  intro j
  induction j with
  | zero =>
      intro ω
      exact spatialInitialPopulation_rep P
  | succ j ih =>
      intro ω
      have hprev := ih ω
      constructor
      · exact spatialPopulationValid_update P j
          (spatialPopulationPath P j ω) hprev.1 (ω j)
      · by_cases hdelete : SpatialDeletionTime P j
        · rw [spatialResidual_succ_of_deletion P j ω hdelete]
          exact spatialPopulationSupport_update_of_deletion P j hdelete
            (spatialPopulationPath P j ω) hprev.1
            (spatialResidual P j ω) hprev.2 (ω j)
        · rw [spatialResidual_succ_of_refinement P j ω hdelete]
          calc
            spatialPopulationSupport (spatialPopulationPath P (j + 1) ω) =
                spatialPopulationSupport
                  (sharedFinitePopulationUpdate (spatialTransition P j)
                    (spatialPopulationPath P j ω) (ω j)) := rfl
            _ = spatialPopulationSupport (spatialPopulationPath P j ω) :=
              spatialPopulationSupport_update_of_refinement P j hdelete
                (spatialPopulationPath P j ω) hprev.1 (ω j)
            _ = (spatialResidual P j ω : Set _) := hprev.2

theorem mem_livePopulationEvent_iff_of_spatialPopulationRep
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (A : CompactResidual (FlatTorus d))
    (hrep : SpatialPopulationRep P k ξ A) :
    ξ ∈ livePopulationEvent ↔ A ≠ ⊥ := by
  constructor
  · rintro ⟨i, x, hix⟩
    have hxnonempty := (hrep.1 i x hix).2
    rcases TopologicalSpace.Compacts.coe_nonempty.mpr hxnonempty with ⟨z, hzx⟩
    apply TopologicalSpace.Compacts.coe_nonempty.mp
    rw [← hrep.2]
    exact ⟨z, i, x, hix, hzx⟩
  · intro hAnonempty
    rcases TopologicalSpace.Compacts.coe_nonempty.mpr hAnonempty with ⟨z, hzA⟩
    have hzsupport : z ∈ spatialPopulationSupport ξ := by
      rw [hrep.2]
      exact hzA
    rcases hzsupport with ⟨i, x, hix, _hzx⟩
    exact ⟨i, x, hix⟩

theorem spatialPopulationPath_preimage_live_eq_residualNonemptyEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    (spatialPopulationPath P j) ⁻¹'
        (livePopulationEvent (X := SpatialParticle P)) =
      residualNonemptyEvent (spatialResidual P) j := by
  ext ω
  exact mem_livePopulationEvent_iff_of_spatialPopulationRep P
    (spatialLevel P j) (spatialPopulationPath P j ω)
    (spatialResidual P j ω) (spatialPopulationPath_rep P j ω)

end Shepp.Section5
end SheppFlattenedModule052

section SheppFlattenedModule053
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators
open MeasureTheory Set

namespace Shepp.Section5

open ProbabilityTheory
open Shepp.Section2 Shepp.Section3 Shepp.Section4

theorem spatialState_live_label
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (A : CompactResidual (FlatTorus d))
    {x : SpatialParticle P} (hx : spatialState P k α A = Sum.inl x) :
    x.1 = ⟨k, α⟩ := by
  have hne : spatialState P k α A ≠ cemetery := by
    rw [hx]
    simp [cemetery]
  have hnonempty := (spatialState_ne_cemetery_iff P k α A).1 hne
  rw [spatialState_eq_live_of_nonempty P k α A hnonempty] at hx
  cases hx
  rfl

def SpatialPopulationLabelInjective
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P))) : Prop :=
  ∀ ⦃i i' : Fin ξ.1⦄ ⦃x x' : SpatialParticle P⦄,
    ξ.2 i = Sum.inl x → ξ.2 i' = Sum.inl x' → x.1 = x'.1 → i = i'

theorem spatialInitialPopulation_labelInjective
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    SpatialPopulationLabelInjective P (spatialInitialPopulation P) := by
  intro i i' x x' hix hix' hlabel
  have hxlabel := spatialState_live_label P 0
    (spatialGridLabelEquiv P 0 i) (fullSpatialResidual P) hix
  have hxlabel' := spatialState_live_label P 0
    (spatialGridLabelEquiv P 0 i') (fullSpatialResidual P) hix'
  have hgrid : spatialGridLabelEquiv P 0 i = spatialGridLabelEquiv P 0 i' := by
    rw [hxlabel, hxlabel'] at hlabel
    exact eq_of_heq (Sigma.mk.inj_iff.mp hlabel).2
  exact (spatialGridLabelEquiv P 0).injective hgrid

theorem spatialTransition_live_label_of_deletion
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (hdelete : SpatialDeletionTime P j)
    (x y : SpatialParticle P) (hxlevel : x.level = spatialLevel P j)
    (w : SpatialInnovation P j) (l : Fin (spatialSlotCount d))
    (hxy : spatialTransition P j (Sum.inl x) w l = Sum.inl y) :
    l = spatialPrimarySlot d ∧ y.1 = x.1 := by
  classical
  by_cases hl : l = spatialPrimarySlot d
  · refine ⟨hl, ?_⟩
    have hstate :
        spatialState P x.level x.label
            (packetDeleteResidual P (spatialLevel P j) x.residual w) =
          Sum.inl y := by
      simpa [spatialTransition, hdelete, spatialDeletionSlot, hl,
        spatialDeletionLive, hxlevel] using hxy
    have hylabel := spatialState_live_label P x.level x.label
      (packetDeleteResidual P (spatialLevel P j) x.residual w) hstate
    calc
      y.1 = ⟨x.level, x.label⟩ := hylabel
      _ = x.1 := by
        rcases x with ⟨⟨level, label⟩, residual⟩
        rfl
  · simp only [spatialTransition, hdelete, if_true, spatialDeletionSlot, hl,
      if_false] at hxy
    change (Sum.inr () : AugmentedState (SpatialParticle P)) = Sum.inl y at hxy
    cases hxy

theorem spatialTransition_live_label_of_refinement
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (hrefine : ¬ SpatialDeletionTime P j)
    (x y : SpatialParticle P) (hxlevel : x.level = spatialLevel P j)
    (w : SpatialInnovation P j) (l : Fin (spatialSlotCount d))
    (hxy : spatialTransition P j (Sum.inl x) w l = Sum.inl y) :
    y.1 = ⟨x.level + 1,
      gridChild P x.level x.label (spatialSlotBitsEquiv d l)⟩ := by
  have hstate :
      spatialState P (x.level + 1)
          (gridChild P x.level x.label (spatialSlotBitsEquiv d l))
          x.residual = Sum.inl y := by
    simpa [spatialTransition, hrefine, spatialRefinementSlot,
      spatialRefinementLive, hxlevel] using hxy
  exact spatialState_live_label P (x.level + 1)
    (gridChild P x.level x.label (spatialSlotBitsEquiv d l))
    x.residual hstate

theorem spatialPopulationLabelInjective_update
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ)
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (hvalid : SpatialPopulationValid P (spatialLevel P j) ξ)
    (hinj : SpatialPopulationLabelInjective P ξ)
    (w : SpatialInnovation P j) :
    SpatialPopulationLabelInjective P
      (sharedFinitePopulationUpdate (spatialTransition P j) ξ w) := by
  rcases ξ with ⟨q, xs⟩
  intro m m' y y' hmy hmy' hylabel
  let il : Fin q × Fin (spatialSlotCount d) := finProdFinEquiv.symm m
  let il' : Fin q × Fin (spatialSlotCount d) := finProdFinEquiv.symm m'
  change spatialTransition P j (xs il.1) w il.2 = Sum.inl y at hmy
  change spatialTransition P j (xs il'.1) w il'.2 = Sum.inl y' at hmy'
  cases hxi : xs il.1 with
  | inr u =>
      cases u
      rw [hxi] at hmy
      change spatialTransition P j cemetery w il.2 = Sum.inl y at hmy
      rw [spatialTransition_cemetery] at hmy
      cases hmy
  | inl x =>
      cases hxi' : xs il'.1 with
      | inr u =>
          cases u
          rw [hxi'] at hmy'
          change spatialTransition P j cemetery w il'.2 = Sum.inl y' at hmy'
          rw [spatialTransition_cemetery] at hmy'
          cases hmy'
      | inl x' =>
          have hxlevel := (hvalid il.1 x hxi).1
          have hxlevel' := (hvalid il'.1 x' hxi').1
          rw [hxi] at hmy
          rw [hxi'] at hmy'
          have hpair : il = il' := by
            by_cases hdelete : SpatialDeletionTime P j
            · have hy := spatialTransition_live_label_of_deletion
                P j hdelete x y hxlevel w il.2 hmy
              have hy' := spatialTransition_live_label_of_deletion
                P j hdelete x' y' hxlevel' w il'.2 hmy'
              have hparentLabel : x.1 = x'.1 := by
                rw [hy.2, hy'.2] at hylabel
                exact hylabel
              have hparent : il.1 = il'.1 := hinj hxi hxi' hparentLabel
              exact Prod.ext hparent (hy.1.trans hy'.1.symm)
            · have hy := spatialTransition_live_label_of_refinement
                P j hdelete x y hxlevel w il.2 hmy
              have hy' := spatialTransition_live_label_of_refinement
                P j hdelete x' y' hxlevel' w il'.2 hmy'
              rcases x with ⟨⟨level, label⟩, residual⟩
              rcases x' with ⟨⟨level', label'⟩, residual'⟩
              simp only [SpatialParticle.level, SpatialParticle.label] at hxlevel hxlevel' hy hy'
              subst level
              subst level'
              rw [hy, hy'] at hylabel
              have hchild :
                  gridChild P (spatialLevel P j) label
                      (spatialSlotBitsEquiv d il.2) =
                    gridChild P (spatialLevel P j) label'
                      (spatialSlotBitsEquiv d il'.2) :=
                eq_of_heq (Sigma.mk.inj_iff.mp hylabel).2
              have hlabel := congrArg (gridParent P (spatialLevel P j)) hchild
              simp only [gridParent_gridChild] at hlabel
              have hparentLabel :
                  (⟨spatialLevel P j, label⟩ : SpatialLabel P) =
                    ⟨spatialLevel P j, label'⟩ := by
                subst label'
                rfl
              have hparent : il.1 = il'.1 := hinj hxi hxi' hparentLabel
              have hslot : il.2 = il'.2 := by
                have hbits := congrArg
                  (gridChildBits P (spatialLevel P j)) hchild
                simp only [gridChildBits_gridChild] at hbits
                exact (spatialSlotBitsEquiv d).injective hbits
              exact Prod.ext hparent hslot
          change finProdFinEquiv.symm m = finProdFinEquiv.symm m' at hpair
          exact finProdFinEquiv.symm.injective hpair

theorem spatialPopulationPath_labelInjective
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ∀ j (ω : SpatialPath P),
      SpatialPopulationLabelInjective P (spatialPopulationPath P j ω) := by
  intro j
  induction j with
  | zero =>
      intro ω
      exact spatialInitialPopulation_labelInjective P
  | succ j ih =>
      intro ω
      exact spatialPopulationLabelInjective_update P j
        (spatialPopulationPath P j ω) (spatialPopulationPath_rep P j ω).1
        (ih ω) (ω j)

abbrev SpatialLiveIndex
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P))) :=
  {i : Fin ξ.1 // ξ.2 i ≠ cemetery}

theorem exists_spatialLiveParticle
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (i : SpatialLiveIndex ξ) :
    ∃ x : SpatialParticle P, ξ.2 i.1 = Sum.inl x := by
  cases hstate : ξ.2 i.1 with
  | inl x => exact ⟨x, rfl⟩
  | inr u =>
      cases u
      exfalso
      apply i.2
      simpa [cemetery] using hstate

noncomputable def spatialLiveParticle
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (i : SpatialLiveIndex ξ) : SpatialParticle P :=
  Classical.choose (exists_spatialLiveParticle ξ i)

theorem spatialLiveParticle_spec
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (i : SpatialLiveIndex ξ) :
    ξ.2 i.1 = Sum.inl (spatialLiveParticle ξ i) :=
  Classical.choose_spec (exists_spatialLiveParticle ξ i)

noncomputable instance spatialLiveIndexFintype
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P))) :
    Fintype (SpatialLiveIndex ξ) := Fintype.ofFinite _

abbrev SpatialActiveLabel
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (A : CompactResidual (FlatTorus d)) :=
  {α : GridLabel P k //
    compactIntersection A (compactGridCell P k α) ≠ ⊥}

noncomputable instance spatialActiveLabelFintype
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (A : CompactResidual (FlatTorus d)) :
    Fintype (SpatialActiveLabel P k A) := Fintype.ofFinite _

noncomputable def spatialLiveIndexToActiveLabel
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (A : CompactResidual (FlatTorus d))
    (hrep : SpatialPopulationRep P k ξ A) :
    SpatialLiveIndex ξ → SpatialActiveLabel P k A := by
  intro i
  let x := spatialLiveParticle ξ i
  have hxstate : ξ.2 i.1 = Sum.inl x := spatialLiveParticle_spec ξ i
  have hxvalid := hrep.1 i.1 x hxstate
  let α : GridLabel P k := hxvalid.1 ▸ x.label
  refine ⟨α, ?_⟩
  rcases TopologicalSpace.Compacts.coe_nonempty.mpr hxvalid.2 with ⟨z, hzx⟩
  have hzA : z ∈ A := by
    have hzsupport : z ∈ spatialPopulationSupport ξ := ⟨i.1, x, hxstate, hzx⟩
    rwa [hrep.2] at hzsupport
  have hzcell : z ∈ gridCell P k α := by
    have hzcell' := x.residual_subset_cell hzx
    dsimp only [α]
    cases hxvalid.1
    exact hzcell'
  intro hbot
  exact (compactIntersection_eq_bot_iff A (compactGridCell P k α)).mp
    hbot ⟨z, hzA, hzcell⟩

theorem spatialLiveIndexToActiveLabel_injective
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (A : CompactResidual (FlatTorus d))
    (hrep : SpatialPopulationRep P k ξ A)
    (hinj : SpatialPopulationLabelInjective P ξ) :
    Function.Injective (spatialLiveIndexToActiveLabel P k ξ A hrep) := by
  intro i i' hii'
  apply Subtype.ext
  let x := spatialLiveParticle ξ i
  let x' := spatialLiveParticle ξ i'
  have hxstate : ξ.2 i.1 = Sum.inl x := spatialLiveParticle_spec ξ i
  have hxstate' : ξ.2 i'.1 = Sum.inl x' := spatialLiveParticle_spec ξ i'
  have hxlevel := (hrep.1 i.1 x hxstate).1
  have hxlevel' := (hrep.1 i'.1 x' hxstate').1
  have hlabelCast : (hxlevel ▸ x.label) = (hxlevel' ▸ x'.label) := by
    exact congrArg Subtype.val hii'
  have hlabel : x.1 = x'.1 := by
    rcases x with ⟨⟨level, label⟩, residual⟩
    rcases x' with ⟨⟨level', label'⟩, residual'⟩
    simp only [SpatialParticle.level, SpatialParticle.label] at hxlevel hxlevel' hlabelCast ⊢
    subst level
    subst level'
    have hlabelValue : label = label' := by
      simpa using hlabelCast
    subst label'
    rfl
  exact hinj hxstate hxstate' hlabel

theorem spatialLiveIndex_card_le_activeLabel_card
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (A : CompactResidual (FlatTorus d))
    (hrep : SpatialPopulationRep P k ξ A)
    (hinj : SpatialPopulationLabelInjective P ξ) :
    Fintype.card (SpatialLiveIndex ξ) ≤
      Fintype.card (SpatialActiveLabel P k A) := by
  classical
  exact Fintype.card_le_of_injective
    (spatialLiveIndexToActiveLabel P k ξ A hrep)
    (spatialLiveIndexToActiveLabel_injective P k ξ A hrep hinj)

theorem finitePopulationLiveMeasure_univ_eq_card_liveIndex
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (ξ : FinitePopulation (AugmentedState (SpatialParticle P))) :
    finitePopulationLiveMeasure ξ Set.univ =
      (Fintype.card (SpatialLiveIndex ξ) : ℝ≥0∞) := by
  classical
  rcases ξ with ⟨q, xs⟩
  rw [finitePopulationLiveMeasure_mk, Measure.finsetSum_apply]
  rw [Fintype.card_subtype]
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _hi
  cases hstate : xs i with
  | inl x => simp [liveDirac, cemetery]
  | inr u =>
      cases u
      simp [liveDirac, cemetery]

noncomputable def spatialActiveCellCountENN
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (A : CompactResidual (FlatTorus d)) : ℝ≥0∞ := by
  classical
  exact ∑ α : GridLabel P k,
    if compactIntersection A (compactGridCell P k α) ≠ ⊥ then 1 else 0

theorem activeLabel_card_eq_sum
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (A : CompactResidual (FlatTorus d)) :
    (Fintype.card (SpatialActiveLabel P k A) : ℝ≥0∞) =
      spatialActiveCellCountENN P k A := by
  classical
  unfold spatialActiveCellCountENN
  rw [Fintype.card_subtype, Finset.card_filter]
  push_cast
  rfl

theorem finitePopulationLiveMeasure_le_activeCellSum
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (ξ : FinitePopulation (AugmentedState (SpatialParticle P)))
    (A : CompactResidual (FlatTorus d))
    (hrep : SpatialPopulationRep P k ξ A)
    (hinj : SpatialPopulationLabelInjective P ξ) :
    finitePopulationLiveMeasure ξ Set.univ ≤
      spatialActiveCellCountENN P k A := by
  rw [finitePopulationLiveMeasure_univ_eq_card_liveIndex ξ,
    ← activeLabel_card_eq_sum P k A]
  exact_mod_cast spatialLiveIndex_card_le_activeLabel_card
    P k ξ A hrep hinj

theorem measurable_spatialActiveCellCountENN_comp
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    {Ω : Type*} [MeasurableSpace Ω]
    (k : ℕ) {R : Ω → CompactResidual (FlatTorus d)}
    (hR : Measurable R) :
    Measurable fun ω => spatialActiveCellCountENN P k (R ω) := by
  classical
  unfold spatialActiveCellCountENN
  apply Finset.measurable_fun_sum
  intro α _hα
  have hinter : Measurable fun ω =>
      compactIntersection (R ω) (compactGridCell P k α) :=
    (measurable_compactIntersection_right (compactGridCell P k α)).comp hR
  have hactive : MeasurableSet {ω |
      compactIntersection (R ω) (compactGridCell P k α) ≠ ⊥} :=
    measurableSet_compactResidualNonemptySet.preimage hinter
  exact Measurable.ite hactive measurable_const measurable_const

theorem spatialPopulationMeanMass_eq_pathLiveMass
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    populationMeanMeasure (spatialSharedPopulationLaw P j) Set.univ =
      ∫⁻ ω, finitePopulationLiveMeasure (spatialPopulationPath P j ω) Set.univ
        ∂spatialPathMeasure P := by
  let f : FinitePopulation (AugmentedState (SpatialParticle P)) → ℝ≥0∞ :=
    fun ξ => finitePopulationLiveMeasure ξ Set.univ
  have hf : Measurable f :=
    Measure.measurable_measure.1 measurable_finitePopulationLiveMeasure
      Set.univ MeasurableSet.univ
  have hmean := lintegral_populationMeanMeasure
    (spatialSharedPopulationLaw P j) (f := fun _ : SpatialParticle P => 1)
      measurable_const
  simp only [lintegral_const, one_mul] at hmean
  rw [hmean]
  have hlaw := (spatialPopulationPath_hasLaw_shared P j).map_eq
  rw [← hlaw]
  exact MeasureTheory.lintegral_map'
    hf.aemeasurable (measurable_spatialPopulationPath P j).aemeasurable

theorem spatialPopulationMeanMass_le_activeCellExpectation
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    populationMeanMeasure (spatialSharedPopulationLaw P j) Set.univ ≤
      ∫⁻ ω, spatialActiveCellCountENN P (spatialLevel P j)
          (spatialResidual P j ω) ∂spatialPathMeasure P := by
  rw [spatialPopulationMeanMass_eq_pathLiveMass P j]
  apply lintegral_mono
  intro ω
  exact finitePopulationLiveMeasure_le_activeCellSum P
    (spatialLevel P j) (spatialPopulationPath P j ω)
    (spatialResidual P j ω) (spatialPopulationPath_rep P j ω)
    (spatialPopulationPath_labelInjective P j ω)

@[simp] theorem sharedFinitePopulationUpdate_finProd
    {A W Y : Type*} {n : ℕ} (T : A → W → Fin n → Y)
    (ξ : FinitePopulation A) (w : W) (i : Fin ξ.1) (l : Fin n) :
    (sharedFinitePopulationUpdate T ξ w).2 (finProdFinEquiv (i, l)) =
      T (ξ.2 i) w l := by
  rcases ξ with ⟨q, xs⟩
  simp [sharedFinitePopulationUpdate]

theorem packetDeleteResidual_compactIntersection
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (A Q : CompactResidual (FlatTorus d)) (w : PacketInnovation P k) :
    packetDeleteResidual P k (compactIntersection A Q) w =
      compactIntersection (packetDeleteResidual P k A w) Q := by
  ext z
  simp only [packetDeleteResidual, coe_compactDeleteFiniteCloud,
    coe_compactIntersection, Set.mem_sdiff, Set.mem_inter_iff]
  tauto

theorem compactIntersection_parent_child
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ)
    (A : CompactResidual (FlatTorus d)) (β : GridLabel P (k + 1)) :
    compactIntersection
        (compactIntersection A (compactGridCell P k (gridParent P k β)))
        (compactGridCell P (k + 1) β) =
      compactIntersection A (compactGridCell P (k + 1) β) := by
  ext z
  simp only [coe_compactIntersection, coe_compactGridCell,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hzA, _hzparent⟩, hzchild⟩
    exact ⟨hzA, hzchild⟩
  · rintro ⟨hzA, hzchild⟩
    exact ⟨⟨hzA, gridCell_child_subset_parent P k β hzchild⟩, hzchild⟩

theorem spatialState_eq_of_compactIntersection_eq
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k)
    (A B : CompactResidual (FlatTorus d))
    (hAB : compactIntersection A (compactGridCell P k α) =
      compactIntersection B (compactGridCell P k α)) :
    spatialState P k α A = spatialState P k α B := by
  by_cases hA : compactIntersection A (compactGridCell P k α) = ⊥
  · have hB : compactIntersection B (compactGridCell P k α) = ⊥ := by
      rw [← hAB]
      exact hA
    rw [(spatialState_eq_cemetery_iff P k α A).2 hA,
      (spatialState_eq_cemetery_iff P k α B).2 hB]
  · have hB : compactIntersection B (compactGridCell P k α) ≠ ⊥ := by
      rwa [← hAB]
    rw [spatialState_eq_live_of_nonempty P k α A hA,
      spatialState_eq_live_of_nonempty P k α B hB]
    apply congrArg Sum.inl
    congr 1
    apply Subtype.ext
    exact hAB

theorem spatialState_compactIntersection_cell
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k)
    (A : CompactResidual (FlatTorus d)) :
    spatialState P k α (compactIntersection A (compactGridCell P k α)) =
      spatialState P k α A := by
  apply spatialState_eq_of_compactIntersection_eq
  unfold compactIntersection
  rw [inf_assoc, inf_idem]

theorem spatialTransition_spatialState_of_deletion
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (hdelete : SpatialDeletionTime P j)
    (α : GridLabel P (spatialLevel P j))
    (A : CompactResidual (FlatTorus d))
    (hactive : compactIntersection A
      (compactGridCell P (spatialLevel P j) α) ≠ ⊥)
    (w : SpatialInnovation P j) :
    spatialTransition P j
        (spatialState P (spatialLevel P j) α A) w
        (spatialPrimarySlot d) =
      spatialState P (spatialLevel P j) α
        (packetDeleteResidual P (spatialLevel P j) A w) := by
  rw [spatialState_eq_live_of_nonempty P (spatialLevel P j) α A hactive]
  simp only [spatialTransition, hdelete, if_true, spatialDeletionSlot,
    spatialDeletionLive, SpatialParticle.level, SpatialParticle.label,
    SpatialParticle.residual]
  rw [packetDeleteResidual_compactIntersection]
  exact spatialState_compactIntersection_cell P (spatialLevel P j) α _

theorem spatialTransition_spatialState_of_refinement
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (hrefine : ¬SpatialDeletionTime P j)
    (α : GridLabel P (spatialLevel P j))
    (A : CompactResidual (FlatTorus d))
    (hactive : compactIntersection A
      (compactGridCell P (spatialLevel P j) α) ≠ ⊥)
    (w : SpatialInnovation P j) (l : Fin (spatialSlotCount d)) :
    spatialTransition P j
        (spatialState P (spatialLevel P j) α A) w l =
      spatialState P (spatialLevel P j + 1)
        (gridChild P (spatialLevel P j) α (spatialSlotBitsEquiv d l)) A := by
  rw [spatialState_eq_live_of_nonempty P (spatialLevel P j) α A hactive]
  simp only [spatialTransition, hrefine, if_false, if_true, spatialRefinementSlot,
    spatialRefinementLive, SpatialParticle.level, SpatialParticle.label,
    SpatialParticle.residual]
  apply spatialState_eq_of_compactIntersection_eq
  let β := gridChild P (spatialLevel P j) α (spatialSlotBitsEquiv d l)
  change compactIntersection
      (compactIntersection A (compactGridCell P (spatialLevel P j) α))
        (compactGridCell P (spatialLevel P j + 1) β) =
    compactIntersection A
      (compactGridCell P (spatialLevel P j + 1) β)
  rw [show α = gridParent P (spatialLevel P j) β by
    simp only [β, gridParent_gridChild]]
  exact compactIntersection_parent_child P (spatialLevel P j) A β

theorem spatialLevel_zero
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    spatialLevel P 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (self_le_blockStart (subblockCount P)
    (blockIndex (subblockCount P) 0)).trans
      (blockIndex_lower (subblockCount P) 0)

theorem SpatialParticle.cast_label_eq_of_label_eq
    {d : ℕ} {r : ℕ → ℝ} {P : GeometricPacketInterface d r}
    (x : SpatialParticle P) (k : ℕ) (α : GridLabel P k)
    (hlabel : x.1 = ⟨k, α⟩) (hlevel : x.level = k) :
    hlevel ▸ x.label = α := by
  rcases x with ⟨⟨level, label⟩, residual⟩
  simp only [SpatialParticle.level, SpatialParticle.label] at hlevel ⊢
  subst level
  have hlabelValue : label = α := by
    exact eq_of_heq (Sigma.mk.inj_iff.mp hlabel).2
  subst label
  rfl

theorem exists_spatialPopulationPath_state_atLevel
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ∀ j (ω : SpatialPath P) (k : ℕ), spatialLevel P j = k →
      ∀ α : GridLabel P k,
        compactIntersection (spatialResidual P j ω)
            (compactGridCell P k α) ≠ ⊥ →
          ∃ i : Fin (spatialPopulationPath P j ω).1,
            (spatialPopulationPath P j ω).2 i =
              spatialState P k α (spatialResidual P j ω) := by
  intro j
  induction j with
  | zero =>
      intro ω k hk α _hactive
      have hk0 : k = 0 := hk.symm.trans (spatialLevel_zero P)
      clear hk
      subst k
      refine ⟨(spatialGridLabelEquiv P 0).symm α, ?_⟩
      simp [spatialInitialPopulation]
  | succ j ih =>
      intro ω k hk β hβ
      classical
      by_cases hdelete : SpatialDeletionTime P j
      · have hsucc : spatialLevel P (j + 1) = spatialLevel P j :=
          blockIndex_succ_of_deletion (subblockCount P) j hdelete
        have hkprev : spatialLevel P j = k := hsucc.symm.trans hk
        clear hk
        subst k
        rw [spatialResidual_succ_of_deletion P j ω hdelete] at hβ ⊢
        have hprev : compactIntersection (spatialResidual P j ω)
            (compactGridCell P (spatialLevel P j) β) ≠ ⊥ := by
          intro hbot
          apply hβ
          apply le_antisymm
          · calc
              compactIntersection
                  (packetDeleteResidual P (spatialLevel P j)
                    (spatialResidual P j ω) (ω j))
                  (compactGridCell P (spatialLevel P j) β) ≤
                  compactIntersection (spatialResidual P j ω)
                    (compactGridCell P (spatialLevel P j) β) :=
                compactIntersection_mono_left
                  (packetDeleteResidual_le P (spatialLevel P j)
                    (spatialResidual P j ω) (ω j))
              _ = ⊥ := hbot
          · exact bot_le
        rcases ih ω (spatialLevel P j) rfl β hprev with ⟨i, hi⟩
        let l : Fin (spatialSlotCount d) := spatialPrimarySlot d
        let m : Fin ((spatialPopulationPath P j ω).1 * spatialSlotCount d) :=
          finProdFinEquiv (i, l)
        refine ⟨m, ?_⟩
        change (sharedFinitePopulationUpdate (spatialTransition P j)
            (spatialPopulationPath P j ω) (ω j)).2 m =
          spatialState P (spatialLevel P j) β
            (packetDeleteResidual P (spatialLevel P j)
              (spatialResidual P j ω) (ω j))
        dsimp only [m]
        rw [sharedFinitePopulationUpdate_finProd]
        rw [hi]
        exact spatialTransition_spatialState_of_deletion P j hdelete β
          (spatialResidual P j ω) hprev (ω j)
      · have hsucc : spatialLevel P (j + 1) = spatialLevel P j + 1 :=
          blockIndex_succ_of_refinement (subblockCount P) j hdelete
        have hknext : spatialLevel P j + 1 = k := hsucc.symm.trans hk
        clear hk
        subst k
        rw [spatialResidual_succ_of_refinement P j ω hdelete] at hβ ⊢
        let α : GridLabel P (spatialLevel P j) :=
          gridParent P (spatialLevel P j) β
        have hprev : compactIntersection (spatialResidual P j ω)
            (compactGridCell P (spatialLevel P j) α) ≠ ⊥ := by
          intro hbot
          apply hβ
          apply le_antisymm
          · calc
              compactIntersection (spatialResidual P j ω)
                  (compactGridCell P (spatialLevel P j + 1) β) ≤
                  compactIntersection (spatialResidual P j ω)
                    (compactGridCell P (spatialLevel P j) α) := by
                intro z hz
                exact ⟨hz.1,
                  gridCell_child_subset_parent P (spatialLevel P j) β hz.2⟩
              _ = ⊥ := hbot
          · exact bot_le
        rcases ih ω (spatialLevel P j) rfl α hprev with ⟨i, hi⟩
        let l : Fin (spatialSlotCount d) :=
          (spatialSlotBitsEquiv d).symm
            (gridChildBits P (spatialLevel P j) β)
        let m : Fin ((spatialPopulationPath P j ω).1 * spatialSlotCount d) :=
          finProdFinEquiv (i, l)
        refine ⟨m, ?_⟩
        change (sharedFinitePopulationUpdate (spatialTransition P j)
            (spatialPopulationPath P j ω) (ω j)).2 m =
          spatialState P (spatialLevel P j + 1) β
            (spatialResidual P j ω)
        dsimp only [m]
        rw [sharedFinitePopulationUpdate_finProd]
        rw [hi]
        simpa only [l, Equiv.apply_symm_apply, α, gridChild_parent_bits] using
          spatialTransition_spatialState_of_refinement P j hdelete α
            (spatialResidual P j ω) hprev (ω j) l

theorem exists_spatialPopulationPath_state
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (ω : SpatialPath P)
    (α : GridLabel P (spatialLevel P j))
    (hactive : compactIntersection (spatialResidual P j ω)
      (compactGridCell P (spatialLevel P j) α) ≠ ⊥) :
    ∃ i : Fin (spatialPopulationPath P j ω).1,
      (spatialPopulationPath P j ω).2 i =
        spatialState P (spatialLevel P j) α (spatialResidual P j ω) :=
  exists_spatialPopulationPath_state_atLevel P j ω (spatialLevel P j) rfl
    α hactive

theorem spatialLiveIndexToActiveLabel_surjective_path
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (ω : SpatialPath P) :
    Function.Surjective
      (spatialLiveIndexToActiveLabel P (spatialLevel P j)
        (spatialPopulationPath P j ω) (spatialResidual P j ω)
        (spatialPopulationPath_rep P j ω)) := by
  intro α
  rcases exists_spatialPopulationPath_state P j ω α.1 α.2 with ⟨i, hi⟩
  have hiLive : (spatialPopulationPath P j ω).2 i ≠ cemetery := by
    rw [hi]
    exact (spatialState_ne_cemetery_iff P (spatialLevel P j) α.1
      (spatialResidual P j ω)).2 α.2
  let iLive : SpatialLiveIndex (spatialPopulationPath P j ω) := ⟨i, hiLive⟩
  refine ⟨iLive, ?_⟩
  apply Subtype.ext
  let x := spatialLiveParticle (spatialPopulationPath P j ω) iLive
  have hxstate : (spatialPopulationPath P j ω).2 i = Sum.inl x :=
    spatialLiveParticle_spec (spatialPopulationPath P j ω) iLive
  have halpha := spatialState_eq_live_of_nonempty P (spatialLevel P j) α.1
    (spatialResidual P j ω) α.2
  have hx :
      (⟨⟨spatialLevel P j, α.1⟩,
        ⟨compactIntersection (spatialResidual P j ω)
          (compactGridCell P (spatialLevel P j) α.1), by
            intro z hz
            exact hz.2⟩⟩ : SpatialParticle P) = x := by
    rw [hi, halpha] at hxstate
    exact Sum.inl.inj hxstate
  unfold spatialLiveIndexToActiveLabel
  dsimp only
  change (((spatialPopulationPath_rep P j ω).1 i x hxstate).1 ▸ x.label) = α.1
  apply SpatialParticle.cast_label_eq_of_label_eq
  exact (congrArg Sigma.fst hx).symm

theorem spatialLiveIndex_card_eq_activeLabel_card_path
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (ω : SpatialPath P) :
    Fintype.card (SpatialLiveIndex (spatialPopulationPath P j ω)) =
      Fintype.card (SpatialActiveLabel P (spatialLevel P j)
        (spatialResidual P j ω)) := by
  apply le_antisymm
  · exact spatialLiveIndex_card_le_activeLabel_card P (spatialLevel P j)
      (spatialPopulationPath P j ω) (spatialResidual P j ω)
      (spatialPopulationPath_rep P j ω)
      (spatialPopulationPath_labelInjective P j ω)
  · exact Fintype.card_le_of_surjective _
      (spatialLiveIndexToActiveLabel_surjective_path P j ω)

theorem finitePopulationLiveMeasure_eq_activeCellSum_path
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (ω : SpatialPath P) :
    finitePopulationLiveMeasure (spatialPopulationPath P j ω) Set.univ =
      spatialActiveCellCountENN P (spatialLevel P j)
        (spatialResidual P j ω) := by
  rw [finitePopulationLiveMeasure_univ_eq_card_liveIndex,
    ← activeLabel_card_eq_sum]
  exact_mod_cast spatialLiveIndex_card_eq_activeLabel_card_path P j ω

theorem spatialPopulationMeanMass_eq_activeCellExpectation
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    populationMeanMeasure (spatialSharedPopulationLaw P j) Set.univ =
      ∫⁻ ω, spatialActiveCellCountENN P (spatialLevel P j)
          (spatialResidual P j ω) ∂spatialPathMeasure P := by
  rw [spatialPopulationMeanMass_eq_pathLiveMass P j]
  apply lintegral_congr
  intro ω
  exact finitePopulationLiveMeasure_eq_activeCellSum_path P j ω

end Shepp.Section5
end SheppFlattenedModule053

section SheppFlattenedModule054
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators
open MeasureTheory Set

namespace Shepp.Section5

open ProbabilityTheory
open Shepp.Section2 Shepp.Section3 Shepp.Section4

noncomputable def spatialResidualOfPrefix
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    (j : ℕ) → SpatialPrefix P j → CompactResidual (FlatTorus d)
  | 0, _u => fullSpatialResidual P
  | j + 1, u => by
      classical
      exact if SpatialDeletionTime P j then
        packetDeleteResidual P (spatialLevel P j)
          (spatialResidualOfPrefix P j (spatialPrefixInit u))
          (spatialPrefixLast u)
      else spatialResidualOfPrefix P j (spatialPrefixInit u)

theorem measurable_spatialResidualOfPrefix
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ∀ j, Measurable (spatialResidualOfPrefix P j) := by
  intro j
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
      classical
      by_cases hdelete : SpatialDeletionTime P j
      · simp only [spatialResidualOfPrefix, hdelete, if_true]
        exact (measurable_packetDeleteResidual P (spatialLevel P j)).comp
          ((ih.comp (measurable_spatialPrefixInit j)).prodMk
            (measurable_spatialPrefixLast j))
      · simp only [spatialResidualOfPrefix, hdelete, if_false]
        exact ih.comp (measurable_spatialPrefixInit j)

theorem spatialResidual_eq_ofPrefix
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (ω : SpatialPath P) :
    spatialResidual P j ω =
      spatialResidualOfPrefix P j (spatialPathPrefix P j ω) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      classical
      by_cases hdelete : SpatialDeletionTime P j
      · rw [spatialResidual_succ_of_deletion P j ω hdelete]
        simp only [spatialResidualOfPrefix, hdelete, if_true]
        rw [ih]
        rfl
      · rw [spatialResidual_succ_of_refinement P j ω hdelete]
        simp only [spatialResidualOfPrefix, hdelete, if_false]
        rw [ih]
        rfl

theorem spatialResidual_indepFun_next
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    IndepFun (spatialResidual P j)
      (fun ω : SpatialPath P => ω j) (spatialPathMeasure P) := by
  let S : Finset ℕ := Finset.range j
  let T : Finset ℕ := {j}
  have hdisjoint : Disjoint S T := by simp [S, T]
  have hraw : IndepFun
      (fun (ω : SpatialPath P) (i : S) => ω i.1)
      (fun (ω : SpatialPath P) (i : T) => ω i.1)
      (spatialPathMeasure P) :=
    iIndepFun.indepFun_finset S T hdisjoint
      (spatialPath_coordinates_iIndepFun P)
      (fun i => measurable_spatialPath_eval P i)
  let reindex : ((i : S) → SpatialInnovation P i.1) → SpatialPrefix P j :=
    fun u i => u ⟨i.1, by
      change i.1 ∈ Finset.range j
      exact Finset.mem_range.mpr i.2⟩
  have hreindex : Measurable reindex := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (⟨i.1, by
      change i.1 ∈ Finset.range j
      exact Finset.mem_range.mpr i.2⟩ : S)
  let pastToResidual : ((i : S) → SpatialInnovation P i.1) →
      CompactResidual (FlatTorus d) :=
    fun u => spatialResidualOfPrefix P j (reindex u)
  have hpast : Measurable pastToResidual :=
    (measurable_spatialResidualOfPrefix P j).comp hreindex
  let singletonToInnovation : ((i : T) → SpatialInnovation P i.1) →
      SpatialInnovation P j := fun u => u ⟨j, by simp [T]⟩
  have hsingleton : Measurable singletonToInnovation :=
    measurable_pi_apply (⟨j, by simp [T]⟩ : T)
  have hcomp := hraw.comp hpast hsingleton
  have hleft : pastToResidual ∘
        (fun (ω : SpatialPath P) (i : S) => ω i.1) =
      spatialResidual P j := by
    funext ω
    rw [spatialResidual_eq_ofPrefix P j ω]
    rfl
  have hright : singletonToInnovation ∘
        (fun (ω : SpatialPath P) (i : T) => ω i.1) =
      fun ω : SpatialPath P => ω j := by
    rfl
  rw [hleft, hright] at hcomp
  exact hcomp

noncomputable def spatialCellActiveSet
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) : Set (CompactResidual (FlatTorus d)) :=
  {A | compactIntersection A (compactGridCell P k α) ≠ ⊥}

theorem measurableSet_spatialCellActiveSet
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) :
    MeasurableSet (spatialCellActiveSet P k α) := by
  change MeasurableSet
    ((fun A => compactIntersection A (compactGridCell P k α)) ⁻¹'
      compactResidualNonemptySet)
  exact measurableSet_compactResidualNonemptySet.preimage
    (measurable_compactIntersection_right (compactGridCell P k α))

noncomputable def spatialInnovationInnerAvoids
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (j : ℕ) : Set (SpatialInnovation P j) :=
  finiteCloudAvoids fun n : PacketMark P (spatialLevel P j) =>
    Metric.ball (gridCenter P k α) (r n - gridCircumradius P k)

theorem measurableSet_spatialInnovationInnerAvoids
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (j : ℕ) :
    MeasurableSet (spatialInnovationInnerAvoids P k α j) :=
  measurableSet_finiteCloudAvoids fun _ => Metric.isOpen_ball.measurableSet

theorem spatialCellActive_succ_subset_inter_avoid
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (j : ℕ)
    (hdelete : SpatialDeletionTime P j) :
    (spatialResidual P (j + 1)) ⁻¹' spatialCellActiveSet P k α ⊆
      (spatialResidual P j) ⁻¹' spatialCellActiveSet P k α ∩
        (fun ω : SpatialPath P => ω j) ⁻¹'
          spatialInnovationInnerAvoids P k α j := by
  intro ω hactive
  change spatialResidual P (j + 1) ω ∈ spatialCellActiveSet P k α at hactive
  rw [spatialResidual_succ_of_deletion P j ω hdelete] at hactive
  rcases TopologicalSpace.Compacts.coe_nonempty.mpr hactive with ⟨z, hz⟩
  have hzprev : z ∈ spatialResidual P j ω := hz.1.1
  have hzcell : z ∈ gridCell P k α := hz.2
  have hprev : spatialResidual P j ω ∈ spatialCellActiveSet P k α := by
    apply TopologicalSpace.Compacts.coe_nonempty.mp
    exact ⟨z, hzprev, hzcell⟩
  have hcurrent :
      ω j ∈ finiteCloudCellActive
        (fun n : PacketMark P (spatialLevel P j) => r n) (gridCell P k α) := by
    exact ⟨z, hz.1.2, hzcell⟩
  have havoid := finiteCloudCellActive_subset_avoids
    (fun n : PacketMark P (spatialLevel P j) => r n)
    (gridCell_subset_closedBall P k α) hcurrent
  exact ⟨hprev, havoid⟩

noncomputable def spatialCellAvoidanceProduct
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (j : ℕ) : ℝ≥0∞ :=
  ∏ t ∈ Finset.range j,
    spatialInnovationMeasure P t (spatialInnovationInnerAvoids P k α t)

theorem spatialInnovationInnerAvoids_measure_refinement
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (j : ℕ)
    (hrefine : ¬ SpatialDeletionTime P j) :
    spatialInnovationMeasure P j (spatialInnovationInnerAvoids P k α j) = 1 := by
  classical
  have hmeasure : spatialInnovationMeasure P j =
      Measure.dirac (emptyPacketInnovation P (spatialLevel P j)) := by
    unfold spatialInnovationMeasure
    exact dif_neg hrefine
  rw [hmeasure]
  rw [Measure.dirac_apply' _ (measurableSet_spatialInnovationInnerAvoids P k α j)]
  simp [spatialInnovationInnerAvoids, emptyPacketInnovation,
    finiteCloudAvoids, cloudAvoids]

theorem spatialCellActive_measure_le_avoidanceProduct
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) :
    ∀ j, spatialPathMeasure P
        ((spatialResidual P j) ⁻¹' spatialCellActiveSet P k α) ≤
      spatialCellAvoidanceProduct P k α j := by
  intro j
  induction j with
  | zero =>
      exact prob_le_one
  | succ j ih =>
      classical
      rw [spatialCellAvoidanceProduct, Finset.prod_range_succ]
      by_cases hdelete : SpatialDeletionTime P j
      · calc
          spatialPathMeasure P
              ((spatialResidual P (j + 1)) ⁻¹' spatialCellActiveSet P k α) ≤
              spatialPathMeasure P
                (((spatialResidual P j) ⁻¹' spatialCellActiveSet P k α) ∩
                  ((fun ω : SpatialPath P => ω j) ⁻¹'
                    spatialInnovationInnerAvoids P k α j)) :=
            measure_mono (spatialCellActive_succ_subset_inter_avoid
              P k α j hdelete)
          _ = spatialPathMeasure P
                ((spatialResidual P j) ⁻¹' spatialCellActiveSet P k α) *
              spatialPathMeasure P
                ((fun ω : SpatialPath P => ω j) ⁻¹'
                  spatialInnovationInnerAvoids P k α j) := by
            exact (spatialResidual_indepFun_next P j).measure_inter_preimage_eq_mul
              (spatialCellActiveSet P k α)
              (spatialInnovationInnerAvoids P k α j)
              (measurableSet_spatialCellActiveSet P k α)
              (measurableSet_spatialInnovationInnerAvoids P k α j)
          _ = spatialPathMeasure P
                ((spatialResidual P j) ⁻¹' spatialCellActiveSet P k α) *
              spatialInnovationMeasure P j
                (spatialInnovationInnerAvoids P k α j) := by
            congr 1
            calc
              spatialPathMeasure P
                  ((fun ω : SpatialPath P => ω j) ⁻¹'
                    spatialInnovationInnerAvoids P k α j) =
                  Measure.map (fun ω : SpatialPath P => ω j)
                    (spatialPathMeasure P)
                    (spatialInnovationInnerAvoids P k α j) :=
                (Measure.map_apply (measurable_spatialPath_eval P j)
                  (measurableSet_spatialInnovationInnerAvoids P k α j)).symm
              _ = spatialInnovationMeasure P j
                    (spatialInnovationInnerAvoids P k α j) := by
                rw [(spatialPath_eval_hasLaw P j).map_eq]
          _ ≤ spatialCellAvoidanceProduct P k α j *
              spatialInnovationMeasure P j
                (spatialInnovationInnerAvoids P k α j) :=
            mul_le_mul' ih le_rfl
      · have hres : spatialResidual P (j + 1) = spatialResidual P j := by
          funext ω
          exact spatialResidual_succ_of_refinement P j ω hdelete
        rw [hres,
          spatialInnovationInnerAvoids_measure_refinement P k α j hdelete,
          mul_one]
        simpa [spatialCellAvoidanceProduct] using ih

noncomputable def packetFractionalRateAt
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) (n : PrefixMark P k) : ℝ≥0 := by
  classical
  exact if hn : (n : ℕ) ∈ packetIndices P k then
    fractionalRate P k ⟨n, hn⟩ p
  else 0

theorem scheduledRate_succ_eq_add_packetFractional
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) (n : PrefixMark P k) :
    scheduledRate P k ((p : ℕ) + 1) n =
      scheduledRate P k p n + packetFractionalRateAt P k p n := by
  classical
  by_cases hn : (n : ℕ) ∈ packetIndices P k
  · let nPacket : PacketMark P k := ⟨n, hn⟩
    have hcurrent := scheduledRate_current_succ P k p nPacket
    have hprefix :
        (⟨nPacket,
          Nat.lt_succ_of_le (mem_packetIndices_le_cutoff P nPacket.property)⟩ :
          PrefixMark P k) = n := by
      apply Fin.ext
      rfl
    simpa [packetFractionalRateAt, hn, nPacket, hprefix] using hcurrent
  · have hold : scheduledRate P k ((p : ℕ) + 1) n = scheduledRate P k p n := by
      cases k with
      | zero =>
          exfalso
          apply hn
          simpa [packetIndices] using n.isLt
      | succ k =>
          have hnle : (n : ℕ) ≤ P.cutoff k := by
            have hnupper : (n : ℕ) ≤ P.cutoff (k + 1) := Nat.lt_succ_iff.mp n.isLt
            have hnotlt : ¬P.cutoff k < (n : ℕ) := by
              intro hlt
              apply hn
              simpa [packetIndices] using And.intro hlt hnupper
            omega
          rw [scheduledRate_old_eq_one P k ((p : ℕ) + 1) n hnle,
            scheduledRate_old_eq_one P k p n hnle]
    simpa [packetFractionalRateAt, hn] using hold

noncomputable def packetMarkPrefixSubtypeEquiv
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    PacketMark P k ≃
      {n : PrefixMark P k // (n : ℕ) ∈ packetIndices P k} where
  toFun n :=
    ⟨⟨n, Nat.lt_succ_of_le (mem_packetIndices_le_cutoff P n.property)⟩,
      n.property⟩
  invFun n := ⟨n.1, n.2⟩
  left_inv n := by apply Subtype.ext; rfl
  right_inv n := by apply Subtype.ext; apply Fin.ext; rfl

theorem sum_packetFractionalRateAt_mul
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) (v : ℕ → ℝ) :
    (∑ n : PrefixMark P k,
      (packetFractionalRateAt P k p n : ℝ) * v n) =
      ∑ n : PacketMark P k, (fractionalRate P k n p : ℝ) * v n := by
  classical
  let pred : PrefixMark P k → Prop := fun n => (n : ℕ) ∈ packetIndices P k
  let f : PrefixMark P k → ℝ := fun n =>
    (packetFractionalRateAt P k p n : ℝ) * v n
  have hsplit := Fintype.sum_subtype_add_sum_subtype pred f
  calc
    (∑ n : PrefixMark P k,
        (packetFractionalRateAt P k p n : ℝ) * v n) =
        (∑ n : {n : PrefixMark P k // pred n}, f n) +
          ∑ n : {n : PrefixMark P k // ¬pred n}, f n := hsplit.symm
    _ = ∑ n : {n : PrefixMark P k // pred n}, f n := by
      have hzero : (∑ n : {n : PrefixMark P k // ¬pred n}, f n) = 0 := by
        apply Finset.sum_eq_zero
        intro n _hn
        simp [f, pred, packetFractionalRateAt, n.property]
      rw [hzero, add_zero]
    _ = ∑ n : PacketMark P k, (fractionalRate P k n p : ℝ) * v n := by
      apply Fintype.sum_equiv (packetMarkPrefixSubtypeEquiv P k).symm
      intro n
      have heq : (⟨n.1, n.2⟩ : PacketMark P k) =
          (packetMarkPrefixSubtypeEquiv P k).symm n := by
        apply Subtype.ext
        rfl
      simp only [f, pred, packetFractionalRateAt]
      rw [dif_pos n.2, ← heq]

noncomputable def scheduledWeightedSum
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (v : ℕ → ℝ) (k p : ℕ) : ℝ :=
  ∑ n : PrefixMark P k, (scheduledRate P k p n : ℝ) * v n

theorem scheduledWeightedSum_succ
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (v : ℕ → ℝ) (k : ℕ) (p : Fin (subblockCount P k)) :
    scheduledWeightedSum P v k ((p : ℕ) + 1) =
      scheduledWeightedSum P v k p +
        ∑ n : PacketMark P k, (fractionalRate P k n p : ℝ) * v n := by
  unfold scheduledWeightedSum
  simp_rw [scheduledRate_succ_eq_add_packetFractional P k p]
  simp only [NNReal.coe_add, add_mul, Finset.sum_add_distrib]
  rw [sum_packetFractionalRateAt_mul P k p v]

theorem scheduledRate_count_eq_one
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (n : PrefixMark P k) :
    scheduledRate P k (subblockCount P k) n = 1 := by
  have hupper : markIntervalUpper P n ≤
      scheduledMass P k (subblockCount P k) := by
    rw [scheduledMass_count, markIntervalUpper, packetEndMass]
    exact prefixMass_mono P.radiusVolume_nonneg (Nat.lt_succ_iff.mp n.isLt)
  apply NNReal.eq
  rw [coe_scheduledRate,
    scheduledOverlap_eq_radiusVolume_of_upper_le P k (subblockCount P k) n hupper,
    div_self (P.radiusVolume_pos n).ne']
  rfl

noncomputable def previousPacketIndicatorRate
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (n : PrefixMark P (k + 1)) : ℝ≥0 := by
  classical
  exact if (n : ℕ) ≤ P.cutoff k then 1 else 0

theorem scheduledRate_next_zero_eq_previousIndicator
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (n : PrefixMark P (k + 1)) :
    scheduledRate P (k + 1) 0 n = previousPacketIndicatorRate P k n := by
  classical
  by_cases hnold : (n : ℕ) ≤ P.cutoff k
  · rw [scheduledRate_old_eq_one P k 0 n hnold]
    simp [previousPacketIndicatorRate, hnold]
  · have hnupper : (n : ℕ) ≤ P.cutoff (k + 1) := Nat.lt_succ_iff.mp n.isLt
    have hnpacket : (n : ℕ) ∈ packetIndices P (k + 1) := by
      simpa [packetIndices] using And.intro (Nat.lt_of_not_ge hnold) hnupper
    let nPacket : PacketMark P (k + 1) := ⟨n, hnpacket⟩
    have hzero := scheduledRate_current_zero P (k + 1) nPacket
    have hprefix :
        (⟨nPacket,
          Nat.lt_succ_of_le (mem_packetIndices_le_cutoff P nPacket.property)⟩ :
          PrefixMark P (k + 1)) = n := by
      apply Fin.ext
      rfl
    simpa [previousPacketIndicatorRate, hnold, nPacket, hprefix] using hzero

theorem scheduledWeightedSum_boundary
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (v : ℕ → ℝ) (k : ℕ) :
    scheduledWeightedSum P v (k + 1) 0 =
      scheduledWeightedSum P v k (subblockCount P k) := by
  classical
  unfold scheduledWeightedSum
  simp_rw [scheduledRate_next_zero_eq_previousIndicator P k,
    scheduledRate_count_eq_one P k]
  simp only [NNReal.coe_one, one_mul]
  have hcut : P.cutoff k ≤ P.cutoff (k + 1) :=
    P.cutoff_monotone (Nat.le_succ k)
  simp only [previousPacketIndicatorRate]
  change (∑ n : Fin (P.cutoff (k + 1) + 1),
      (((if (n : ℕ) ≤ P.cutoff k then (1 : ℝ≥0) else 0) : ℝ≥0) : ℝ) * v n) =
    ∑ n : Fin (P.cutoff k + 1), v n
  rw [Fin.sum_univ_eq_sum_range
    (fun n : ℕ =>
      ((((if n ≤ P.cutoff k then (1 : ℝ≥0) else 0) : ℝ≥0) : ℝ) * v n))
      (P.cutoff (k + 1) + 1)]
  rw [Fin.sum_univ_eq_sum_range v (P.cutoff k + 1)]
  have hsubset : Finset.range (P.cutoff k + 1) ⊆
      Finset.range (P.cutoff (k + 1) + 1) := by
    exact Finset.range_mono (Nat.add_le_add_right hcut 1)
  calc
    (∑ n ∈ Finset.range (P.cutoff (k + 1) + 1),
        ((((if n ≤ P.cutoff k then (1 : ℝ≥0) else 0) : ℝ≥0) : ℝ) * v n)) =
        ∑ n ∈ Finset.range (P.cutoff k + 1),
          ((((if n ≤ P.cutoff k then (1 : ℝ≥0) else 0) : ℝ≥0) : ℝ) * v n) := by
      symm
      apply Finset.sum_subset hsubset
      intro n hnlarge hnsmall
      have hnnotle : ¬n ≤ P.cutoff k := by
        simpa [Finset.mem_range, Nat.lt_succ_iff] using hnsmall
      simp [hnnotle]
    _ = ∑ n ∈ Finset.range (P.cutoff k + 1), v n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnle : n ≤ P.cutoff k := by
        simpa [Finset.mem_range, Nat.lt_succ_iff] using hn
      simp [hnle]

theorem blockOffset_succ_of_deletion
    (J : ℕ → ℕ) (j : ℕ) (hdelete : IsDeletionTime J j) :
    blockOffset J (j + 1) = blockOffset J j + 1 := by
  unfold blockOffset
  rw [blockIndex_succ_of_deletion J j hdelete]
  have hlo := blockIndex_lower J j
  omega

theorem blockOffset_succ_of_refinement
    (J : ℕ → ℕ) (j : ℕ) (hrefine : ¬IsDeletionTime J j) :
    blockOffset J (j + 1) = 0 := by
  unfold blockOffset
  rw [blockIndex_succ_of_refinement J j hrefine, blockStart_succ]
  have hoff := blockOffset_eq_count_of_not_deletion J j hrefine
  have hj := blockStart_add_offset J j
  omega

noncomputable def spatialWeightedIncrement
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (v : ℕ → ℝ) (j : ℕ) : ℝ := by
  classical
  exact if hdelete : SpatialDeletionTime P j then
    ∑ n : PacketMark P (spatialLevel P j),
      (fractionalRate P (spatialLevel P j) n
        ⟨spatialOffset P j, hdelete⟩ : ℝ) * v n
  else 0

noncomputable def spatialAccumulatedWeight
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ t ∈ Finset.range j, spatialWeightedIncrement P v t

theorem spatialAccumulatedWeight_succ
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (v : ℕ → ℝ) (j : ℕ) :
    spatialAccumulatedWeight P v (j + 1) =
      spatialAccumulatedWeight P v j + spatialWeightedIncrement P v j := by
  simp [spatialAccumulatedWeight, Finset.sum_range_succ]

theorem scheduledRate_zero_zero
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (n : PrefixMark P 0) : scheduledRate P 0 0 n = 0 := by
  have hn : (n : ℕ) ∈ packetIndices P 0 := by
    simpa [packetIndices] using n.isLt
  let nPacket : PacketMark P 0 := ⟨n, hn⟩
  have hzero := scheduledRate_current_zero P 0 nPacket
  have hprefix :
      (⟨nPacket,
        Nat.lt_succ_of_le (mem_packetIndices_le_cutoff P nPacket.property)⟩ :
        PrefixMark P 0) = n := by
    apply Fin.ext
    rfl
  simpa [nPacket, hprefix] using hzero

theorem scheduledWeightedSum_zero_zero
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (v : ℕ → ℝ) : scheduledWeightedSum P v 0 0 = 0 := by
  unfold scheduledWeightedSum
  simp_rw [scheduledRate_zero_zero P]
  simp

theorem spatialAccumulatedWeight_eq_scheduled
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (v : ℕ → ℝ) :
    ∀ j, spatialAccumulatedWeight P v j =
      scheduledWeightedSum P v (spatialLevel P j) (spatialOffset P j) := by
  intro j
  induction j with
  | zero =>
      have hindex : blockIndex (subblockCount P) 0 = 0 := by
        apply Nat.eq_zero_of_le_zero
        exact (self_le_blockStart (subblockCount P)
          (blockIndex (subblockCount P) 0)).trans
            (blockIndex_lower (subblockCount P) 0)
      rw [show spatialAccumulatedWeight P v 0 = 0 by
        simp [spatialAccumulatedWeight]]
      change 0 = scheduledWeightedSum P v
        (blockIndex (subblockCount P) 0)
        (blockOffset (subblockCount P) 0)
      rw [hindex]
      simp only [blockOffset, Nat.zero_sub]
      exact (scheduledWeightedSum_zero_zero P v).symm
  | succ j ih =>
      classical
      rw [spatialAccumulatedWeight_succ P v j, ih]
      by_cases hdelete : SpatialDeletionTime P j
      · have hlevel : spatialLevel P (j + 1) = spatialLevel P j :=
          blockIndex_succ_of_deletion (subblockCount P) j hdelete
        have hoffset : spatialOffset P (j + 1) = spatialOffset P j + 1 :=
          blockOffset_succ_of_deletion (subblockCount P) j hdelete
        rw [hlevel, hoffset]
        simp only [spatialWeightedIncrement, hdelete, dif_pos]
        exact (scheduledWeightedSum_succ P v (spatialLevel P j)
          ⟨spatialOffset P j, hdelete⟩).symm
      · have hlevel : spatialLevel P (j + 1) = spatialLevel P j + 1 :=
          blockIndex_succ_of_refinement (subblockCount P) j hdelete
        have hoffset : spatialOffset P (j + 1) = 0 :=
          blockOffset_succ_of_refinement (subblockCount P) j hdelete
        have hcurrent : spatialOffset P j = subblockCount P (spatialLevel P j) :=
          blockOffset_eq_count_of_not_deletion (subblockCount P) j hdelete
        have hincrement : spatialWeightedIncrement P v j = 0 := by
          unfold spatialWeightedIncrement
          exact dif_neg hdelete
        rw [hlevel, hoffset, hcurrent]
        rw [hincrement, add_zero]
        exact (scheduledWeightedSum_boundary P v (spatialLevel P j)).symm

noncomputable def spatialInnerVolumeWeight
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (n : ℕ) : ℝ :=
  (flatTorusVolume d).real
    (Metric.ball (gridCenter P k α) (r n - gridCircumradius P k))

theorem spatialInnovationInnerAvoids_measure_eq_exp_increment
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (j : ℕ) :
    spatialInnovationMeasure P j (spatialInnovationInnerAvoids P k α j) =
      ENNReal.ofReal (Real.exp
        (-spatialWeightedIncrement P
          (spatialInnerVolumeWeight P k α) j)) := by
  classical
  by_cases hdelete : SpatialDeletionTime P j
  · have hmeasure : spatialInnovationMeasure P j =
        packetSubblockMeasure (flatTorusVolume d) P (spatialLevel P j)
          ⟨spatialOffset P j, hdelete⟩ := by
      unfold spatialInnovationMeasure
      exact dif_pos hdelete
    rw [hmeasure]
    change finiteCloudMeasure (flatTorusVolume d)
        (fractionalRate P (spatialLevel P j) ·
          ⟨spatialOffset P j, hdelete⟩)
        (finiteCloudAvoids fun n : PacketMark P (spatialLevel P j) =>
          Metric.ball (gridCenter P k α) (r n - gridCircumradius P k)) = _
    rw [finiteCloudMeasure_avoids (flatTorusVolume d)
      (fractionalRate P (spatialLevel P j) ·
        ⟨spatialOffset P j, hdelete⟩) _
      (fun _ => Metric.isOpen_ball.measurableSet)]
    congr 3
    unfold spatialWeightedIncrement spatialInnerVolumeWeight
    rw [dif_pos hdelete]
  · rw [spatialInnovationInnerAvoids_measure_refinement P k α j hdelete]
    have hincrement : spatialWeightedIncrement P
        (spatialInnerVolumeWeight P k α) j = 0 := by
      unfold spatialWeightedIncrement
      exact dif_neg hdelete
    rw [hincrement]
    simp

theorem spatialCellAvoidanceProduct_eq_exp_accumulated
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) :
    ∀ j, spatialCellAvoidanceProduct P k α j =
      ENNReal.ofReal (Real.exp
        (-spatialAccumulatedWeight P
          (spatialInnerVolumeWeight P k α) j)) := by
  intro j
  induction j with
  | zero =>
      simp [spatialCellAvoidanceProduct, spatialAccumulatedWeight]
  | succ j ih =>
      rw [spatialCellAvoidanceProduct, Finset.prod_range_succ]
      change spatialCellAvoidanceProduct P k α j *
          spatialInnovationMeasure P j
            (spatialInnovationInnerAvoids P k α j) = _
      rw [ih, spatialInnovationInnerAvoids_measure_eq_exp_increment]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      apply congrArg ENNReal.ofReal
      rw [← Real.exp_add]
      rw [spatialAccumulatedWeight_succ]
      congr 1
      ring

theorem spatialCellAvoidanceProduct_eq_exp_scheduled
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (α : GridLabel P k) (j : ℕ) :
    spatialCellAvoidanceProduct P k α j =
      ENNReal.ofReal (Real.exp
        (-scheduledWeightedSum P (spatialInnerVolumeWeight P k α)
          (spatialLevel P j) (spatialOffset P j))) := by
  rw [spatialCellAvoidanceProduct_eq_exp_accumulated,
    spatialAccumulatedWeight_eq_scheduled]

theorem spatialInnerVolumeWeight_eq
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k : ℕ) (α : GridLabel P k)
    (n : PrefixMark P k) :
    spatialInnerVolumeWeight P k α n =
      euclideanUnitBallVolume d * (r n - gridCircumradius P k) ^ d := by
  unfold spatialInnerVolumeWeight
  have hρ : 0 ≤ gridCircumradius P k := gridCircumradius_nonneg P k
  have hρlevel : gridCircumradius P k ≤ P.level k := by
    have hquarter := gridCircumradius_le_level_div_four P k
    have hlevelPos : 0 < P.level k := test_dyadicLevel_pos (P.K + k)
    linarith
  have hlevelRadius : P.level k ≤ r n :=
    P.level_le_radius k n (Nat.lt_succ_iff.mp n.isLt)
  apply flatTorusVolumeReal_ball_gridCenter hd P k α
  · exact sub_nonneg.mpr (hρlevel.trans hlevelRadius)
  · exact lt_of_le_of_lt (sub_le_self _ hρ) (P.radius_lt_quarter n)

theorem scheduledWeightedInner_ge
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (k p : ℕ) (α : GridLabel P k) :
    scheduledMass P k p - (d : ℝ) ^ 2 / 4 ≤
      scheduledWeightedSum P (spatialInnerVolumeWeight P k α) k p := by
  have h := weighted_inner_volume_ge hd P k (scheduledRate P k p)
    (scheduledRate_le_one P k p) (scheduledMass P k p)
    (sum_scheduledRate_mul_radiusVolume P k p)
  unfold scheduledWeightedSum
  simp_rw [spatialInnerVolumeWeight_eq hd P k α]
  simpa only [mul_assoc] using h

theorem spatialCellActive_measure_le_exp
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (j : ℕ)
    (α : GridLabel P (spatialLevel P j)) :
    spatialPathMeasure P
        ((spatialResidual P j) ⁻¹'
          spatialCellActiveSet P (spatialLevel P j) α) ≤
      ENNReal.ofReal (Real.exp
        (-scheduledMass P (spatialLevel P j) (spatialOffset P j) +
          (d : ℝ) ^ 2 / 4)) := by
  calc
    spatialPathMeasure P
        ((spatialResidual P j) ⁻¹'
          spatialCellActiveSet P (spatialLevel P j) α) ≤
        spatialCellAvoidanceProduct P (spatialLevel P j) α j :=
      spatialCellActive_measure_le_avoidanceProduct P
        (spatialLevel P j) α j
    _ = ENNReal.ofReal (Real.exp
          (-scheduledWeightedSum P
            (spatialInnerVolumeWeight P (spatialLevel P j) α)
            (spatialLevel P j) (spatialOffset P j))) :=
      spatialCellAvoidanceProduct_eq_exp_scheduled P
        (spatialLevel P j) α j
    _ ≤ ENNReal.ofReal (Real.exp
        (-scheduledMass P (spatialLevel P j) (spatialOffset P j) +
          (d : ℝ) ^ 2 / 4)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hinner := scheduledWeightedInner_ge hd P
        (spatialLevel P j) (spatialOffset P j) α
      linarith

theorem spatialActiveCellCount_lintegral_eq_sum_measure
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k j : ℕ) :
    (∫⁻ ω, spatialActiveCellCountENN P k (spatialResidual P j ω)
        ∂spatialPathMeasure P) =
      ∑ α : GridLabel P k,
        spatialPathMeasure P
          ((spatialResidual P j) ⁻¹' spatialCellActiveSet P k α) := by
  classical
  unfold spatialActiveCellCountENN
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro α _hα
    let E : Set (SpatialPath P) :=
      (spatialResidual P j) ⁻¹' spatialCellActiveSet P k α
    have hE : MeasurableSet E :=
      (measurableSet_spatialCellActiveSet P k α).preimage
        (measurable_spatialResidual P j)
    have hfun : (fun ω : SpatialPath P =>
        if compactIntersection (spatialResidual P j ω) (compactGridCell P k α) ≠ ⊥
          then (1 : ℝ≥0∞) else 0) = E.indicator (fun _ => 1) := by
      funext ω
      simp only [E, spatialCellActiveSet, Set.mem_preimage,
        Set.mem_setOf_eq, Set.indicator_apply]
    rw [hfun]
    exact lintegral_indicator_one hE
  · intro α _hα
    have hinter : Measurable fun ω =>
        compactIntersection (spatialResidual P j ω) (compactGridCell P k α) :=
      (measurable_compactIntersection_right (compactGridCell P k α)).comp
        (measurable_spatialResidual P j)
    have hactive : MeasurableSet {ω |
        compactIntersection (spatialResidual P j ω) (compactGridCell P k α) ≠ ⊥} :=
      measurableSet_compactResidualNonemptySet.preimage hinter
    exact Measurable.ite hactive measurable_const measurable_const

theorem spatialActiveCellExpectation_le_card_mul_exp
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (j : ℕ) :
    (∫⁻ ω, spatialActiveCellCountENN P (spatialLevel P j)
        (spatialResidual P j ω) ∂spatialPathMeasure P) ≤
      (Fintype.card (GridLabel P (spatialLevel P j)) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp
          (-scheduledMass P (spatialLevel P j) (spatialOffset P j) +
            (d : ℝ) ^ 2 / 4)) := by
  rw [spatialActiveCellCount_lintegral_eq_sum_measure P
    (spatialLevel P j) j]
  calc
    (∑ α : GridLabel P (spatialLevel P j),
        spatialPathMeasure P
          ((spatialResidual P j) ⁻¹'
            spatialCellActiveSet P (spatialLevel P j) α)) ≤
        ∑ _α : GridLabel P (spatialLevel P j),
          ENNReal.ofReal (Real.exp
            (-scheduledMass P (spatialLevel P j) (spatialOffset P j) +
              (d : ℝ) ^ 2 / 4)) := by
      apply Finset.sum_le_sum
      intro α _hα
      exact spatialCellActive_measure_le_exp hd P j α
    _ = (Fintype.card (GridLabel P (spatialLevel P j)) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp
          (-scheduledMass P (spatialLevel P j) (spatialOffset P j) +
            (d : ℝ) ^ 2 / 4)) := by simp

theorem spatialPopulationMeanMass_le_card_mul_exp
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (j : ℕ) :
    populationMeanMeasure (spatialSharedPopulationLaw P j) Set.univ ≤
      (Fintype.card (GridLabel P (spatialLevel P j)) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp
          (-scheduledMass P (spatialLevel P j) (spatialOffset P j) +
            (d : ℝ) ^ 2 / 4)) :=
  (spatialPopulationMeanMass_le_activeCellExpectation P j).trans
    (spatialActiveCellExpectation_le_card_mul_exp hd P j)

theorem spatialPopulationMeanMass_le_closedForm
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (j : ℕ) :
    populationMeanMeasure (spatialSharedPopulationLaw P j) Set.univ ≤
      ENNReal.ofReal
        (firstMomentConstant d * (P.level (spatialLevel P j))⁻¹ ^ d *
          Real.exp (-scheduledMass P (spatialLevel P j) (spatialOffset P j))) := by
  refine (spatialPopulationMeanMass_le_card_mul_exp hd P j).trans_eq ?_
  rw [← ENNReal.ofReal_natCast
    (Fintype.card (GridLabel P (spatialLevel P j)))]
  rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply congrArg ENNReal.ofReal
  rw [card_gridLabel_real P (spatialLevel P j), Real.exp_add]
  unfold firstMomentConstant
  ring

noncomputable instance spatialInitialPopulationMeanFinite
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    IsFiniteMeasure
      (populationMeanMeasure (Measure.dirac (spatialInitialPopulation P))) := by
  unfold populationMeanMeasure
  rw [Measure.dirac_bind measurable_finitePopulationLiveMeasure]
  infer_instance

theorem spatialSharedPopulationLaw_meanPopulation
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    (populationMeanMeasure (spatialSharedPopulationLaw P j)).real Set.univ =
      meanPopulation
        (meanFlow (fun _ => spatialSlotCount d)
          (fun t => spatialOneParticleKernel P t)
          (initialMeanFiniteMeasure
            (Measure.dirac (spatialInitialPopulation P))) j) := by
  have h := sharedPopulationLaw_meanPopulation
    (fun _ => spatialSlotCount d)
    (fun t => spatialOneParticleKernel P t)
    (fun t => spatialInnovationMeasure P t)
    (fun t => spatialTransition P t)
    (fun t i => measurable_spatialTransition P t i)
    (fun t z => (spatialOneParticleKernel_apply P t z).symm)
    (fun t => spatialOneParticleKernel_cemetery P t)
    (Measure.dirac (spatialInitialPopulation P)) j
  rw [generationAfter_eq_add, Nat.zero_add] at h
  exact h

theorem spatialMeanPopulation_le_closedForm
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (j : ℕ) :
    meanPopulation
        (meanFlow (fun _ => spatialSlotCount d)
          (fun t => spatialOneParticleKernel P t)
          (initialMeanFiniteMeasure
            (Measure.dirac (spatialInitialPopulation P))) j) ≤
      firstMomentConstant d * (P.level (spatialLevel P j))⁻¹ ^ d *
        Real.exp (-scheduledMass P (spatialLevel P j) (spatialOffset P j)) := by
  let B : ℝ := firstMomentConstant d * (P.level (spatialLevel P j))⁻¹ ^ d *
    Real.exp (-scheduledMass P (spatialLevel P j) (spatialOffset P j))
  have hBpos : 0 < B := by
    exact mul_pos
      (mul_pos (firstMomentConstant_pos d)
        (pow_pos (inv_pos.mpr (test_dyadicLevel_pos
          (P.K + spatialLevel P j))) d))
      (Real.exp_pos _)
  have hmass :
      populationMeanMeasure (spatialSharedPopulationLaw P j) Set.univ ≤
        ENNReal.ofReal B := by
    exact spatialPopulationMeanMass_le_closedForm hd P j
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  rw [ENNReal.toReal_ofReal hBpos.le] at hreal
  change (populationMeanMeasure (spatialSharedPopulationLaw P j)).real Set.univ ≤ B
    at hreal
  rw [spatialSharedPopulationLaw_meanPopulation P j] at hreal
  exact hreal

end Shepp.Section5
end SheppFlattenedModule054

section SheppFlattenedModule055
open scoped BigOperators ENNReal NNReal ProbabilityTheory
open MeasureTheory Set

namespace Shepp.Section5

open ProbabilityTheory
open Shepp.Section2 Shepp.Section3 Shepp.Section4

noncomputable def spatialMeanSize
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) : ℝ :=
  meanPopulation
    (meanFlow (fun _ => spatialSlotCount d)
      (fun t => spatialOneParticleKernel P t)
      (initialMeanFiniteMeasure
        (Measure.dirac (spatialInitialPopulation P))) j)

theorem spatialMeanSize_nonneg
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    0 ≤ spatialMeanSize P j := by
  unfold spatialMeanSize meanPopulation
  positivity

theorem spatialMeanSize_le_closedForm
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (j : ℕ) :
    spatialMeanSize P j ≤
      firstMomentConstant d * (P.level (spatialLevel P j))⁻¹ ^ d *
        Real.exp (-scheduledMass P (spatialLevel P j) (spatialOffset P j)) :=
  spatialMeanPopulation_le_closedForm hd P j

theorem spatialMeanSize_inv_ge
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (j : ℕ) :
    ENNReal.ofReal
        (reciprocalFirstMomentConstant d *
          (P.level (spatialLevel P j)) ^ d *
          Real.exp
            (scheduledMass P (spatialLevel P j) (spatialOffset P j))) ≤
      (ENNReal.ofReal (spatialMeanSize P j))⁻¹ := by
  let B : ℝ :=
    firstMomentConstant d * (P.level (spatialLevel P j))⁻¹ ^ d *
      Real.exp (-scheduledMass P (spatialLevel P j) (spatialOffset P j))
  have hC : 0 < firstMomentConstant d := firstMomentConstant_pos d
  have hlevel : 0 < P.level (spatialLevel P j) :=
    test_dyadicLevel_pos (P.K + spatialLevel P j)
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hreal :
      reciprocalFirstMomentConstant d *
          (P.level (spatialLevel P j)) ^ d *
          Real.exp
            (scheduledMass P (spatialLevel P j) (spatialOffset P j)) =
        B⁻¹ := by
    dsimp only [B, reciprocalFirstMomentConstant]
    rw [Real.exp_neg, inv_pow]
    field_simp [hC.ne', hlevel.ne', Real.exp_ne_zero]
  calc
    ENNReal.ofReal
        (reciprocalFirstMomentConstant d *
          (P.level (spatialLevel P j)) ^ d *
          Real.exp
            (scheduledMass P (spatialLevel P j) (spatialOffset P j))) =
        ENNReal.ofReal B⁻¹ := by rw [hreal]
    _ = (ENNReal.ofReal B)⁻¹ := ENNReal.ofReal_inv_of_pos hB
    _ ≤ (ENNReal.ofReal (spatialMeanSize P j))⁻¹ := by
      apply ENNReal.inv_le_inv'
      exact ENNReal.ofReal_le_ofReal
        (spatialMeanSize_le_closedForm hd P j)

noncomputable def spatialSubblockResistanceLower
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) : ℝ≥0∞ :=
  ENNReal.ofReal
    (baseResistanceConstant d * (P.level k) ^ d *
      subblockMass P k p * Real.exp (scheduledMass P k p))

noncomputable def spatialPacketResistanceLower
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) : ℝ≥0∞ :=
  ∑ p : Fin (subblockCount P k), spatialSubblockResistanceLower P k p

theorem spatialPacketResistanceLower_ge_increment
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    ENNReal.ofReal
        (geometricResistanceConstant d * (P.level k) ^ d * P.increment k) ≤
      spatialPacketResistanceLower P k := by
  let S : ℝ := ∑ p : Fin (subblockCount P k),
    subblockMass P k p * Real.exp (scheduledMass P k p)
  have hchord : exponentialChordReciprocal * P.increment k ≤ S :=
    exponentialChordReciprocal_mul_increment_le P k
  have hscaleNonneg :
      0 ≤ baseResistanceConstant d * (P.level k) ^ d :=
    mul_nonneg (baseResistanceConstant_pos d).le
      (pow_nonneg (test_dyadicLevel_pos (P.K + k)).le d)
  have hreal :
      geometricResistanceConstant d * (P.level k) ^ d * P.increment k ≤
        baseResistanceConstant d * (P.level k) ^ d * S := by
    calc
      geometricResistanceConstant d * (P.level k) ^ d * P.increment k =
          (baseResistanceConstant d * (P.level k) ^ d) *
            (exponentialChordReciprocal * P.increment k) := by
        unfold geometricResistanceConstant
        ring
      _ ≤ (baseResistanceConstant d * (P.level k) ^ d) * S :=
        mul_le_mul_of_nonneg_left hchord hscaleNonneg
  calc
    ENNReal.ofReal
        (geometricResistanceConstant d * (P.level k) ^ d * P.increment k) ≤
        ENNReal.ofReal
          (baseResistanceConstant d * (P.level k) ^ d * S) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ∑ p : Fin (subblockCount P k),
        spatialSubblockResistanceLower P k p := by
      rw [show baseResistanceConstant d * (P.level k) ^ d * S =
          ∑ p : Fin (subblockCount P k),
            baseResistanceConstant d * (P.level k) ^ d *
              subblockMass P k p * Real.exp (scheduledMass P k p) by
        dsimp only [S]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring]
      rw [ENNReal.ofReal_sum_of_nonneg]
      · rfl
      · intro p _
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (baseResistanceConstant_pos d).le
              (pow_nonneg (test_dyadicLevel_pos (P.K + k)).le d))
            (subblockMass_pos P k p).le)
          (Real.exp_pos (scheduledMass P k p)).le
    _ = spatialPacketResistanceLower P k := rfl

noncomputable def spatialResistanceLowerMass
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) : ℝ≥0∞ :=
  ∑' k : ℕ, spatialPacketResistanceLower P k

theorem spatialResistanceLowerMass_eq_top
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    spatialResistanceLowerMass P = ∞ := by
  have hle :
      (∑' k : ℕ,
        ENNReal.ofReal
          (geometricResistanceConstant d * (P.level k) ^ d * P.increment k)) ≤
        ∑' k : ℕ, spatialPacketResistanceLower P k :=
    ENNReal.tsum_le_tsum fun k =>
      spatialPacketResistanceLower_ge_increment P k
  rw [scaled_packet_increment_tsum_eq_top P] at hle
  unfold spatialResistanceLowerMass
  exact top_unique hle

noncomputable def spatialResistanceLowerTerm
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) : ℝ≥0∞ :=
  blockScheduledTerm (subblockCount P)
    (fun k p => spatialSubblockResistanceLower P k p) j

theorem tsum_spatialResistanceLowerTerm_eq_top
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    (∑' j : ℕ, spatialResistanceLowerTerm P j) = ∞ := by
  rw [show (∑' j : ℕ, spatialResistanceLowerTerm P j) =
      spatialResistanceLowerMass P by
    unfold spatialResistanceLowerTerm spatialResistanceLowerMass
      spatialPacketResistanceLower
    exact tsum_blockScheduledTerm (subblockCount P)
      (fun k p => spatialSubblockResistanceLower P k p)]
  exact spatialResistanceLowerMass_eq_top P

theorem spatialSubblockResistanceLower_le_resistanceTerm
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (j : ℕ)
    (hdelete : SpatialDeletionTime P j) (hm : 0 < spatialMeanSize P j) :
    spatialSubblockResistanceLower P (spatialLevel P j)
        ⟨spatialOffset P j, hdelete⟩ ≤
      resistanceTermENN (spatialKillingDelta P) (spatialMeanSize P) j := by
  let p : Fin (subblockCount P (spatialLevel P j)) :=
    ⟨spatialOffset P j, hdelete⟩
  have hdelta :
      ENNReal.ofReal
          (killingLinearConstant d *
            subblockMass P (spatialLevel P j) p) ≤
        ENNReal.ofReal (subblockKillingDelta P (spatialLevel P j) p) :=
    ENNReal.ofReal_le_ofReal
      (subblockKillingDelta_ge_linear P (spatialLevel P j) p)
  have hmean := spatialMeanSize_inv_ge hd P j
  have hproduct := mul_le_mul' hdelta hmean
  calc
    spatialSubblockResistanceLower P (spatialLevel P j) p =
        ENNReal.ofReal
            ((killingLinearConstant d *
                subblockMass P (spatialLevel P j) p) *
              (reciprocalFirstMomentConstant d *
                (P.level (spatialLevel P j)) ^ d *
                Real.exp
                  (scheduledMass P (spatialLevel P j)
                    (spatialOffset P j)))) := by
      unfold spatialSubblockResistanceLower baseResistanceConstant
      apply congrArg ENNReal.ofReal
      ring
    _ = ENNReal.ofReal
          (killingLinearConstant d *
            subblockMass P (spatialLevel P j) p) *
        ENNReal.ofReal
          (reciprocalFirstMomentConstant d *
            (P.level (spatialLevel P j)) ^ d *
            Real.exp
              (scheduledMass P (spatialLevel P j) (spatialOffset P j))) := by
      rw [ENNReal.ofReal_mul]
      exact mul_nonneg (killingLinearConstant_pos d).le
        (subblockMass_pos P (spatialLevel P j) p).le
    _ ≤ ENNReal.ofReal (subblockKillingDelta P (spatialLevel P j) p) *
        (ENNReal.ofReal (spatialMeanSize P j))⁻¹ := hproduct
    _ = resistanceTermENN (spatialKillingDelta P) (spatialMeanSize P) j := by
      unfold resistanceTermENN
      rw [ENNReal.ofReal_div_of_pos hm]
      simp only [spatialKillingDelta, hdelete, dif_pos, div_eq_mul_inv, p]

theorem spatialResistanceLowerTerm_le_resistanceTerm
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r)
    (hm : ∀ j, 0 < spatialMeanSize P j) (j : ℕ) :
    spatialResistanceLowerTerm P j ≤
      resistanceTermENN (spatialKillingDelta P) (spatialMeanSize P) j := by
  classical
  by_cases hdelete : SpatialDeletionTime P j
  · change blockOffset (subblockCount P) j <
      subblockCount P (blockIndex (subblockCount P) j) at hdelete
    unfold spatialResistanceLowerTerm blockScheduledTerm
    rw [dif_pos hdelete]
    exact spatialSubblockResistanceLower_le_resistanceTerm
      hd P j hdelete (hm j)
  · change ¬blockOffset (subblockCount P) j <
      subblockCount P (blockIndex (subblockCount P) j) at hdelete
    unfold spatialResistanceLowerTerm blockScheduledTerm
    rw [dif_neg hdelete]
    exact bot_le

theorem spatialDivergentResistance
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r)
    (hm : ∀ j, 0 < spatialMeanSize P j) :
    DivergentResistance (spatialKillingDelta P) (spatialMeanSize P) := by
  unfold DivergentResistance
  have hle := ENNReal.tsum_le_tsum fun j =>
    spatialResistanceLowerTerm_le_resistanceTerm hd P hm j
  rw [tsum_spatialResistanceLowerTerm_eq_top P] at hle
  exact top_unique hle

end Shepp.Section5
end SheppFlattenedModule055

section SheppFlattenedModule056
open scoped BigOperators ENNReal ProbabilityTheory
open MeasureTheory Set

namespace Shepp.Section4

open ProbabilityTheory

noncomputable def unionPotential (u : ℝ) : ℝ :=
  u + (1 / 2 : ℝ) * u ^ 2

theorem unionPotential_eq_quadraticPotential_one (u : ℝ) :
    unionPotential u = quadraticPotential 1 u := by
  simp [unionPotential, quadraticPotential, resistanceLambda]

@[simp] theorem quadraticPotential_one_eq_unionPotential (u : ℝ) :
    quadraticPotential 1 u = unionPotential u :=
  (unionPotential_eq_quadraticPotential_one u).symm

theorem measurable_unionPotential : Measurable unionPotential := by
  unfold unionPotential
  fun_prop

theorem unionPotential_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ unionPotential u := by
  unfold unionPotential
  positivity

theorem unionPotential_ge_self {u : ℝ} (_hu : 0 ≤ u) :
    u ≤ unionPotential u := by
  unfold unionPotential
  nlinarith [sq_nonneg u]

theorem unionPotential_le_three_halves_mul {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    unionPotential u ≤ (3 / 2 : ℝ) * u := by
  unfold unionPotential
  nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]

theorem unionPotential_le_three_halves {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    unionPotential u ≤ (3 / 2 : ℝ) := by
  calc
    unionPotential u ≤ (3 / 2 : ℝ) * u :=
      unionPotential_le_three_halves_mul hu0 hu1
    _ ≤ 3 / 2 := by nlinarith

theorem unionPotential_binary {a b : ℝ}
    (ha0 : 0 ≤ a) (_ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    unionPotential (a + (1 - a) * b) ≤
      unionPotential a + unionPotential b := by
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hab_le_a : a * b ≤ a := by
    exact mul_le_of_le_one_right ha0 hb1
  have hinner : 0 ≤ a + b - (1 / 2 : ℝ) * (a * b) := by
    nlinarith
  have hprod : 0 ≤ a * b * (a + b - (1 / 2 : ℝ) * (a * b)) :=
    mul_nonneg hab0 hinner
  have hid :
      unionPotential a + unionPotential b -
          unionPotential (a + (1 - a) * b) =
        a * b * (a + b - (1 / 2 : ℝ) * (a * b)) := by
    unfold unionPotential
    ring
  have hnonneg :
      0 ≤ unionPotential a + unionPotential b -
        unionPotential (a + (1 - a) * b) := by
    rw [hid]
    exact hprod
  exact sub_nonneg.mp hnonneg

theorem unionPotential_slotSurvival_le_slotMass
    {us : List ℝ} (h : ValidSlotProbabilities us) :
    unionPotential (slotSurvival us) ≤
      slotMass (us.map unionPotential) := by
  induction us with
  | nil => simp [unionPotential, slotSurvival, slotMass]
  | cons u us ih =>
      have hu := h.head
      have ht := h.tail
      have hp0 := slotSurvival_nonneg ht
      have hp1 := slotSurvival_le_one ht
      have hbinary := unionPotential_binary hu.1 hu.2 hp0 hp1
      have htail := ih ht
      simp only [slotMass] at htail
      simp only [slotSurvival, List.map_cons, slotMass, List.sum_cons]
      exact hbinary.trans (by
        simpa only [add_comm] using
          add_le_add_right htail (unionPotential u))

end Shepp.Section4
end SheppFlattenedModule056

section SheppFlattenedModule057
open scoped BigOperators
open MeasureTheory Set

namespace Shepp.Section4

open ProbabilityTheory

theorem slotMass_unionPotential_slotParameterList
    {Y : Type*} {n : ℕ} (s : Y → ℝ) (y : Fin n → Y) :
    slotMass (slotParameterList n (unionPotential ∘ s) y) =
      slotMass ((slotParameterList n s y).map unionPotential) := by
  simp only [slotParameterList, slotMass,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply]

theorem kernelUnionPotentialKilling
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {n : ℕ} (Q : Kernel X (Fin n → AugmentedState Y)) [IsMarkovKernel Q]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (_hδ1 : δ ≤ 1)
    {s : AugmentedState Y → ℝ} (hs : Measurable s)
    (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1)
    (hcem : s cemetery = 0) (x : X)
    (hkill : δ ≤ (Q x).real (allCemetery n)) :
    slotMean Q (unionPotential ∘ s) x -
        unionPotential (bellmanStep Q s x) ≥
      (δ / 2) * (bellmanStep Q s x) ^ 2 := by
  let R : (Fin n → AugmentedState Y) → ℝ :=
    fun y => slotSurvival (slotParameterList n s y)
  let P : (Fin n → AugmentedState Y) → ℝ :=
    fun y => slotMass (slotParameterList n (unionPotential ∘ s) y)
  let μ : Measure (Fin n → AugmentedState Y) := Q x
  have hvalid : ∀ y, ValidSlotProbabilities (slotParameterList n s y) :=
    fun y => valid_slotParameterList hs0 hs1 y
  have hR0 : ∀ y, 0 ≤ R y :=
    fun y => slotSurvival_nonneg (hvalid y)
  have hR1 : ∀ y, R y ≤ 1 :=
    fun y => slotSurvival_le_one (hvalid y)
  have hRMeas : Measurable R := by
    exact measurable_slotSurvival_slotParameterList hs
  have hRInt : Integrable R μ :=
    integrable_slotSurvival_slotParameterList μ hs hs0 hs1
  have hR2Int : Integrable (fun y => R y ^ 2) μ := by
    apply Integrable.of_bound (hRMeas.pow_const 2).aestronglyMeasurable 1
    filter_upwards with y
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [hR0 y, hR1 y]
  have hPhiRInt : Integrable (fun y => unionPotential (R y)) μ := by
    have hEq : (fun y => unionPotential (R y)) =
        fun y => R y + (1 / 2 : ℝ) * R y ^ 2 := by
      funext y
      rfl
    rw [hEq]
    exact hRInt.add (hR2Int.const_mul (1 / 2 : ℝ))
  have hPMeas : Measurable P := by
    exact measurable_slotMass_slotParameterList
      (measurable_unionPotential.comp hs)
  have hPInt : Integrable P μ := by
    apply Integrable.of_bound hPMeas.aestronglyMeasurable
      ((n : ℝ) * (3 / 2 : ℝ))
    filter_upwards with y
    have hnonneg : 0 ≤ P y := by
      dsimp only [P]
      rw [slotMass_slotParameterList]
      exact Finset.sum_nonneg fun i _ =>
        unionPotential_nonneg (hs0 (y i))
    rw [Real.norm_of_nonneg hnonneg]
    dsimp only [P]
    rw [slotMass_slotParameterList]
    calc
      (∑ i, unionPotential (s (y i))) ≤
          ∑ _i : Fin n, (3 / 2 : ℝ) := by
        exact Finset.sum_le_sum fun i _ =>
          unionPotential_le_three_halves (hs0 (y i)) (hs1 (y i))
      _ = (n : ℝ) * (3 / 2 : ℝ) := by simp
  have hpoint : ∀ y, unionPotential (R y) ≤ P y := by
    intro y
    dsimp only [R, P]
    rw [slotMass_unionPotential_slotParameterList]
    exact unionPotential_slotSurvival_le_slotMass (hvalid y)
  have hIntegratedUnion :
      (∫ y, unionPotential (R y) ∂μ) ≤ ∫ y, P y ∂μ :=
    integral_mono hPhiRInt hPInt hpoint
  have hzero : ∀ y ∈ allCemetery n, R y = 0 := by
    intro y hy
    exact slotSurvival_eq_zero_of_mem_allCemetery hcem hy
  have hCauchy :
      (∫ y, R y ∂μ) ^ 2 ≤
        μ.real (allCemetery n)ᶜ * ∫ y, R y ^ 2 ∂μ :=
    integral_sq_le_measure_compl_mul_integral_sq μ hR0 hRInt hR2Int hzero
  have hcomp : μ.real (allCemetery n)ᶜ ≤ 1 - δ := by
    rw [measureReal_compl (measurableSet_allCemetery n), probReal_univ]
    dsimp only [μ]
    linarith
  have hsecond0 : 0 ≤ ∫ y, R y ^ 2 ∂μ :=
    integral_nonneg fun y => sq_nonneg (R y)
  have hCauchy' :
      (∫ y, R y ∂μ) ^ 2 ≤
        (1 - δ) * ∫ y, R y ^ 2 ∂μ :=
    hCauchy.trans (mul_le_mul_of_nonneg_right hcomp hsecond0)
  have hfactorLe : 1 - δ ≤ 1 := by linarith
  have hfirstSecond :
      (∫ y, R y ∂μ) ^ 2 ≤ ∫ y, R y ^ 2 ∂μ := by
    calc
      (∫ y, R y ∂μ) ^ 2 ≤
          (1 - δ) * ∫ y, R y ^ 2 ∂μ := hCauchy'
      _ ≤ 1 * ∫ y, R y ^ 2 ∂μ :=
        mul_le_mul_of_nonneg_right hfactorLe hsecond0
      _ = ∫ y, R y ^ 2 ∂μ := one_mul _
  have hgapUpper :
      δ * (∫ y, R y ^ 2 ∂μ) ≤
        (∫ y, R y ^ 2 ∂μ) - (∫ y, R y ∂μ) ^ 2 := by
    nlinarith [hCauchy']
  have hgapLower :
      δ * (∫ y, R y ∂μ) ^ 2 ≤
        δ * (∫ y, R y ^ 2 ∂μ) :=
    mul_le_mul_of_nonneg_left hfirstSecond hδ0
  have hvariance :
      δ * (∫ y, R y ∂μ) ^ 2 ≤
        (∫ y, R y ^ 2 ∂μ) - (∫ y, R y ∂μ) ^ 2 :=
    hgapLower.trans hgapUpper
  have hPhiIntegral :
      (∫ y, unionPotential (R y) ∂μ) =
        (∫ y, R y ∂μ) +
          (1 / 2 : ℝ) * ∫ y, R y ^ 2 ∂μ := by
    have hEq : (fun y => unionPotential (R y)) =
        fun y => R y + (1 / 2 : ℝ) * R y ^ 2 := by
      funext y
      rfl
    rw [hEq, integral_add hRInt (hR2Int.const_mul (1 / 2 : ℝ)),
      integral_const_mul]
  have hBellman : bellmanStep Q s x = ∫ y, R y ∂μ := by
    rfl
  have hSlotMean : slotMean Q (unionPotential ∘ s) x = ∫ y, P y ∂μ := by
    rfl
  rw [hBellman, hSlotMean]
  rw [hPhiIntegral] at hIntegratedUnion
  unfold unionPotential
  nlinarith [hvariance]

end Shepp.Section4
end SheppFlattenedModule057

section SheppFlattenedModule058
open MeasureTheory

namespace Shepp.Section4

open ProbabilityTheory

theorem bellmanFrom_unionPotentialKilling
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (δ : ℕ → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (hkill : ∀ j (x : X j),
      δ j ≤ (Q j (Sum.inl x)).real (allCemetery (n j)))
    (j steps : ℕ) (x : X j) :
    slotMean (Q j) (unionPotential ∘ bellmanFrom n Q (j + 1) steps)
        (Sum.inl x) -
      unionPotential (bellmanFrom n Q j (steps + 1) (Sum.inl x)) ≥
        (δ j / 2) *
          (bellmanFrom n Q j (steps + 1) (Sum.inl x)) ^ 2 := by
  rw [bellmanFrom_succ]
  exact kernelUnionPotentialKilling (Q j) (hδ0 j) (hδ1 j)
    (measurable_bellmanFrom n Q (j + 1) steps)
    (fun y => (bellmanFrom_mem_Icc n Q (j + 1) steps y).1)
    (fun y => (bellmanFrom_mem_Icc n Q (j + 1) steps y).2)
    (bellmanFrom_cemetery n Q hAbsorb (j + 1) steps)
    (Sum.inl x) (hkill j x)

theorem bellmanTo_unionPotentialKilling
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (δ : ℕ → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (hkill : ∀ j (x : X j),
      δ j ≤ (Q j (Sum.inl x)).real (allCemetery (n j)))
    {j N : ℕ} (hjN : j < N) (x : X j) :
    slotMean (Q j) (unionPotential ∘ bellmanTo n Q (j + 1) N)
        (Sum.inl x) -
      unionPotential (bellmanTo n Q j N (Sum.inl x)) ≥
        (δ j / 2) * (bellmanTo n Q j N (Sum.inl x)) ^ 2 := by
  have hsub : N - j = (N - (j + 1)) + 1 := by omega
  simpa only [bellmanTo, hsub] using
    bellmanFrom_unionPotentialKilling n Q δ hδ0 hδ1 hAbsorb hkill
      j (N - (j + 1)) x

end Shepp.Section4
end SheppFlattenedModule058

section SheppFlattenedModule059
open scoped BigOperators ENNReal ProbabilityTheory
open MeasureTheory Set

namespace Shepp.Section4

open ProbabilityTheory

@[simp] theorem resistanceLambda_one : resistanceLambda 1 = (1 / 2 : ℝ) := by
  norm_num [resistanceLambda]

@[simp] theorem conductanceEta_one : conductanceEta 1 = (2 / 9 : ℝ) := by
  norm_num [conductanceEta, resistanceLambda]

@[simp] theorem resistanceConstant_one :
    resistanceConstant 1 = (1 / 6 : ℝ) := by
  norm_num [resistanceConstant, conductanceEta, resistanceLambda]

theorem unionHorizonConductance_growth_square
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (δ : ℕ → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (hkill : ∀ j (x : X j),
      δ j ≤ (Q j (Sum.inl x)).real (allCemetery (n j)))
    (μ0 : FiniteMeasure (X 0)) {j N : ℕ} (hjN : j < N) :
    horizonConductance 1 n Q μ0 (j + 1) N -
        horizonConductance 1 n Q μ0 j N ≥
      (δ j / 2) * horizonSquareIntegral n Q μ0 j N := by
  let sNow := bellmanTo n Q j N
  let sNext := bellmanTo n Q (j + 1) N
  let μj := meanFlow n Q μ0 j
  let coeff := δ j / 2
  let g : X j → ℝ := fun x =>
    slotMean (Q j) (unionPotential ∘ sNext) (Sum.inl x)
  let q : X j → ℝ := fun x => unionPotential (sNow (Sum.inl x))
  let sq : X j → ℝ := fun x => (sNow (Sum.inl x)) ^ 2
  have hsNowMeas : Measurable sNow := measurable_bellmanTo n Q j N
  have hsNextMeas : Measurable sNext := measurable_bellmanTo n Q (j + 1) N
  have hsNow0 : ∀ z, 0 ≤ sNow z :=
    fun z => (bellmanTo_mem_Icc n Q j N z).1
  have hsNow1 : ∀ z, sNow z ≤ 1 :=
    fun z => (bellmanTo_mem_Icc n Q j N z).2
  have hsNext0 : ∀ z, 0 ≤ sNext z :=
    fun z => (bellmanTo_mem_Icc n Q (j + 1) N z).1
  have hsNext1 : ∀ z, sNext z ≤ 1 :=
    fun z => (bellmanTo_mem_Icc n Q (j + 1) N z).2
  have hPotentialMeas : Measurable (unionPotential ∘ sNext) :=
    measurable_unionPotential.comp hsNextMeas
  have hgMeas : Measurable g :=
    (measurable_slotMean (Q j) hPotentialMeas).comp measurable_inl
  have hPotential0 : ∀ z, 0 ≤ unionPotential (sNext z) :=
    fun z => unionPotential_nonneg (hsNext0 z)
  have hPotentialBound : ∀ z, unionPotential (sNext z) ≤ (3 / 2 : ℝ) :=
    fun z => unionPotential_le_three_halves (hsNext0 z) (hsNext1 z)
  have hgInt : Integrable g (μj : Measure (X j)) := by
    apply Integrable.of_bound hgMeas.aestronglyMeasurable
      ((n j : ℝ) * (3 / 2 : ℝ))
    filter_upwards with x
    exact slotMean_norm_le_bound_mul (Q j) (le_rfl) hPotentialMeas
      (by norm_num) hPotential0 hPotentialBound (Sum.inl x)
  have hqMeas : Measurable q :=
    measurable_unionPotential.comp (hsNowMeas.comp measurable_inl)
  have hqInt : Integrable q (μj : Measure (X j)) := by
    apply Integrable.of_bound hqMeas.aestronglyMeasurable (3 / 2 : ℝ)
    filter_upwards with x
    rw [Real.norm_of_nonneg (unionPotential_nonneg (hsNow0 _))]
    exact unionPotential_le_three_halves (hsNow0 _) (hsNow1 _)
  have hsqMeas : Measurable sq :=
    (hsNowMeas.comp measurable_inl).pow_const 2
  have hsqInt : Integrable sq (μj : Measure (X j)) := by
    apply Integrable.of_bound hsqMeas.aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [hsNow0 (Sum.inl x), hsNow1 (Sum.inl x)]
  have hcoeff0 : 0 ≤ coeff := div_nonneg (hδ0 j) (by norm_num)
  have hpoint : ∀ x, q x + coeff * sq x ≤ g x := by
    intro x
    have hk := bellmanTo_unionPotentialKilling n Q δ hδ0 hδ1
      hAbsorb hkill hjN x
    dsimp only [g, q, sq, coeff, sNow, sNext]
    linarith
  have hle := integral_mono (hqInt.add (hsqInt.const_mul coeff)) hgInt hpoint
  change (∫ x, q x + coeff * sq x ∂(μj : Measure (X j))) ≤
    ∫ x, g x ∂(μj : Measure (X j)) at hle
  rw [integral_add hqInt (hsqInt.const_mul coeff), integral_const_mul] at hle
  have hle' :
      horizonConductance 1 n Q μ0 j N +
          coeff * horizonSquareIntegral n Q μ0 j N ≤
        ∫ x, g x ∂(μj : Measure (X j)) := by
    simpa only [horizonConductance, conductance, horizonSquareIntegral,
      squareSurvivalIntegral, quadraticPotential_one_eq_unionPotential,
      q, sq, μj] using hle
  have hnext := horizonConductance_succ_eq_slotMean
    1 (by norm_num) n Q hAbsorb μ0 j N
  have hPotentialEq :
      quadraticPotential 1 ∘ sNext = unionPotential ∘ sNext := by
    funext z
    exact quadraticPotential_one_eq_unionPotential (sNext z)
  rw [hPotentialEq] at hnext
  have hnext' : horizonConductance 1 n Q μ0 (j + 1) N =
      ∫ x, g x ∂(μj : Measure (X j)) := by
    simpa only [g, sNext, μj] using hnext
  dsimp only [coeff] at hle' ⊢
  rw [hnext']
  linarith

theorem unionHorizonConductance_growth
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (δ : ℕ → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (hkill : ∀ j (x : X j),
      δ j ≤ (Q j (Sum.inl x)).real (allCemetery (n j)))
    (μ0 : FiniteMeasure (X 0)) {j N : ℕ} (hjN : j < N)
    (hmj : 0 < meanPopulation (meanFlow n Q μ0 j)) :
    horizonConductance 1 n Q μ0 (j + 1) N -
        horizonConductance 1 n Q μ0 j N ≥
      (2 / 9 : ℝ) *
        (δ j / meanPopulation (meanFlow n Q μ0 j)) *
          horizonConductance 1 n Q μ0 j N ^ 2 := by
  let m := meanPopulation (meanFlow n Q μ0 j)
  let A := horizonSurvivalIntegral n Q μ0 j N
  let C := horizonConductance 1 n Q μ0 j N
  let S := horizonSquareIntegral n Q μ0 j N
  let factor : ℝ := 3 / 2
  have hfactor : 0 < factor := by norm_num [factor]
  have hA0 : 0 ≤ A := horizonSurvival_nonneg n Q μ0 j N
  have hAC : A ≤ C := by
    have h := survivalIntegral_le_conductance (B := 1) (by norm_num)
      (meanFlow n Q μ0 j) (measurable_bellmanTo n Q j N)
      (fun z => (bellmanTo_mem_Icc n Q j N z).1)
      (fun z => (bellmanTo_mem_Icc n Q j N z).2)
    simpa only [A, C, horizonSurvivalIntegral, horizonConductance] using h
  have hC0 : 0 ≤ C := hA0.trans hAC
  have hCA : C ≤ factor * A := by
    have h := conductance_le_linear_survivalIntegral (B := 1) (by norm_num)
      (meanFlow n Q μ0 j) (measurable_bellmanTo n Q j N)
      (fun z => (bellmanTo_mem_Icc n Q j N z).1)
      (fun z => (bellmanTo_mem_Icc n Q j N z).2)
    have h' : C ≤ (1 + (1 / 2 : ℝ)) * A := by
      simpa only [A, C, horizonSurvivalIntegral, horizonConductance,
        resistanceLambda_one] using h
    norm_num at h'
    exact h'
  have hAS : A ^ 2 ≤ m * S := by
    have h := survivalIntegral_sq_le_population_mul_square (meanFlow n Q μ0 j)
      (measurable_bellmanTo n Q j N)
      (fun z => (bellmanTo_mem_Icc n Q j N z).1)
      (fun z => (bellmanTo_mem_Icc n Q j N z).2)
    simpa only [A, m, S, horizonSurvivalIntegral, horizonSquareIntegral] using h
  have hCfactorSq : C ^ 2 ≤ (factor * A) ^ 2 := by
    have hfactorA : 0 ≤ factor * A := mul_nonneg hfactor.le hA0
    nlinarith
  have hCS : C ^ 2 ≤ factor ^ 2 * m * S := by
    calc
      C ^ 2 ≤ (factor * A) ^ 2 := hCfactorSq
      _ = factor ^ 2 * A ^ 2 := by ring
      _ ≤ factor ^ 2 * (m * S) :=
        mul_le_mul_of_nonneg_left hAS (sq_nonneg factor)
      _ = factor ^ 2 * m * S := by ring
  have hdenom : 0 < factor ^ 2 * m :=
    mul_pos (sq_pos_of_pos hfactor) hmj
  have hratio : C ^ 2 / (factor ^ 2 * m) ≤ S := by
    apply (div_le_iff₀ hdenom).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hCS
  have hscale0 : 0 ≤ δ j / 2 := div_nonneg (hδ0 j) (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hratio hscale0
  have hidentity :
      (2 / 9 : ℝ) * (δ j / m) * C ^ 2 =
        (δ j / 2) * (C ^ 2 / (factor ^ 2 * m)) := by
    dsimp only [factor]
    field_simp [ne_of_gt hmj]
    ring
  have hcoercive := unionHorizonConductance_growth_square
    n Q δ hδ0 hδ1 hAbsorb hkill μ0 hjN
  dsimp only [m, A, C, S] at hidentity hscaled ⊢
  rw [hidentity]
  exact hscaled.trans hcoercive

theorem unionHorizonConductance_mono_step
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (δ : ℕ → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (hkill : ∀ j (x : X j),
      δ j ≤ (Q j (Sum.inl x)).real (allCemetery (n j)))
    (μ0 : FiniteMeasure (X 0)) {j N : ℕ} (hjN : j < N) :
    horizonConductance 1 n Q μ0 j N ≤
      horizonConductance 1 n Q μ0 (j + 1) N := by
  have hS0 : 0 ≤ horizonSquareIntegral n Q μ0 j N := by
    rw [horizonSquareIntegral, squareSurvivalIntegral]
    exact integral_nonneg fun x => sq_nonneg _
  have hcoeff0 : 0 ≤ δ j / 2 := div_nonneg (hδ0 j) (by norm_num)
  have h := unionHorizonConductance_growth_square
    n Q δ hδ0 hδ1 hAbsorb hkill μ0 hjN
  nlinarith [mul_nonneg hcoeff0 hS0]

theorem unionHorizonConductance_nonneg
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (μ0 : FiniteMeasure (X 0)) (j N : ℕ) :
    0 ≤ horizonConductance 1 n Q μ0 j N := by
  have hA0 := horizonSurvival_nonneg n Q μ0 j N
  have hAC := survivalIntegral_le_conductance (B := 1) (by norm_num)
    (meanFlow n Q μ0 j) (measurable_bellmanTo n Q j N)
    (fun z => (bellmanTo_mem_Icc n Q j N z).1)
    (fun z => (bellmanTo_mem_Icc n Q j N z).2)
  exact hA0.trans (by
    simpa only [horizonSurvivalIntegral, horizonConductance] using hAC)

@[simp] theorem unionHorizonConductance_terminal
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (μ0 : FiniteMeasure (X 0)) (N : ℕ) :
    horizonConductance 1 n Q μ0 N N =
      (3 / 2 : ℝ) * meanPopulation (meanFlow n Q μ0 N) := by
  rw [horizonConductance_terminal, resistanceLambda_one]
  norm_num

theorem unionHorizonConductance_reciprocal_step
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (δ : ℕ → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (hkill : ∀ j (x : X j),
      δ j ≤ (Q j (Sum.inl x)).real (allCemetery (n j)))
    (μ0 : FiniteMeasure (X 0)) {j N : ℕ} (hjN : j < N)
    (hmj : 0 < meanPopulation (meanFlow n Q μ0 j))
    (hCj : 0 < horizonConductance 1 n Q μ0 j N) :
    1 / horizonConductance 1 n Q μ0 j N -
        1 / horizonConductance 1 n Q μ0 (j + 1) N ≥
      (1 / 6 : ℝ) *
        (δ j / meanPopulation (meanFlow n Q μ0 j)) := by
  let m := meanPopulation (meanFlow n Q μ0 j)
  let C := horizonConductance 1 n Q μ0 j N
  let D := horizonConductance 1 n Q μ0 (j + 1) N
  let r := δ j / m
  have hC : 0 < C := by simpa only [C] using hCj
  have hr : 0 ≤ r := div_nonneg (hδ0 j) hmj.le
  have hgrowth : D - C ≥ conductanceEta 1 * r * C ^ 2 := by
    have h := unionHorizonConductance_growth
      n Q δ hδ0 hδ1 hAbsorb hkill μ0 hjN hmj
    simpa only [C, D, r, m, conductanceEta_one] using h
  have hCm : C ≤ (1 + resistanceLambda 1) * m := by
    have h := conductance_le_one_add_mul_population (B := 1) (by norm_num)
      (meanFlow n Q μ0 j) (measurable_bellmanTo n Q j N)
      (fun z => (bellmanTo_mem_Icc n Q j N z).1)
      (fun z => (bellmanTo_mem_Icc n Q j N z).2)
    simpa only [C, m, horizonConductance] using h
  have hCdiv : C / m ≤ 1 + resistanceLambda 1 :=
    (div_le_iff₀ hmj).2 hCm
  have hCdiv0 : 0 ≤ C / m := div_nonneg hC.le hmj.le
  have hrC' : δ j * (C / m) ≤ 1 + resistanceLambda 1 := by
    calc
      δ j * (C / m) ≤ 1 * (C / m) :=
        mul_le_mul_of_nonneg_right (hδ1 j) hCdiv0
      _ ≤ 1 + resistanceLambda 1 := by simpa using hCdiv
  have hrC : r * C ≤ 1 + resistanceLambda 1 := by
    have hid : r * C = δ j * (C / m) := by
      dsimp only [r]
      field_simp [ne_of_gt hmj]
    rw [hid]
    exact hrC'
  have hstep := reciprocal_resistance_step (B := 1) (by norm_num)
    hC hr hgrowth hrC
  simpa only [C, D, r, m, resistanceConstant_one] using hstep

theorem unionHorizon_finite_reciprocal_resistance
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (δ : ℕ → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (hkill : ∀ j (x : X j),
      δ j ≤ (Q j (Sum.inl x)).real (allCemetery (n j)))
    (μ0 : FiniteMeasure (X 0)) (N : ℕ)
    (hm : ∀ j ≤ N, 0 < meanPopulation (meanFlow n Q μ0 j))
    (hC0 : 0 < horizonConductance 1 n Q μ0 0 N) :
    (1 / 6 : ℝ) *
        ∑ j ∈ Finset.range N,
          δ j / meanPopulation (meanFlow n Q μ0 j) ≤
      1 / horizonConductance 1 n Q μ0 0 N -
        1 / horizonConductance 1 n Q μ0 N N := by
  let C : ℕ → ℝ := fun k => horizonConductance 1 n Q μ0 k N
  have hCpos : ∀ k ≤ N, 0 < C k := by
    intro k hkN
    induction k with
    | zero => simpa only [C] using hC0
    | succ k ih =>
        have hkN : k < N := Nat.lt_of_succ_le hkN
        have hkpos : 0 < C k := ih (Nat.le_of_lt hkN)
        have hmono := unionHorizonConductance_mono_step
          n Q δ hδ0 hδ1 hAbsorb hkill μ0 hkN
        exact hkpos.trans_le (by simpa only [C] using hmono)
  have htel :
      (1 / 6 : ℝ) *
          ∑ j ∈ Finset.range N,
            δ j / meanPopulation (meanFlow n Q μ0 j) ≤
        1 / C 0 - 1 / C N := by
    apply finite_reciprocal_resistance
      (N := N) (C := C)
      (r := fun k => δ k / meanPopulation (meanFlow n Q μ0 k))
      (c := (1 / 6 : ℝ))
    intro j hjN
    have hstep := unionHorizonConductance_reciprocal_step
      n Q δ hδ0 hδ1 hAbsorb hkill μ0 hjN
      (hm j (Nat.le_of_lt hjN)) (hCpos j (Nat.le_of_lt hjN))
    simpa only [C] using hstep
  simpa only [C] using htel

theorem unionHorizonConductance_initial_bound
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (δ : ℕ → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (hkill : ∀ j (x : X j),
      δ j ≤ (Q j (Sum.inl x)).real (allCemetery (n j)))
    (μ0 : FiniteMeasure (X 0)) (N : ℕ)
    (hm : ∀ j ≤ N, 0 < meanPopulation (meanFlow n Q μ0 j)) :
    horizonConductance 1 n Q μ0 0 N ≤
      (2 / (3 * meanPopulation (meanFlow n Q μ0 N)) +
        (1 / 6 : ℝ) *
          ∑ j ∈ Finset.range N,
            δ j / meanPopulation (meanFlow n Q μ0 j))⁻¹ := by
  let C0 := horizonConductance 1 n Q μ0 0 N
  let mN := meanPopulation (meanFlow n Q μ0 N)
  let S := ∑ j ∈ Finset.range N,
    δ j / meanPopulation (meanFlow n Q μ0 j)
  let R := 2 / (3 * mN) + (1 / 6 : ℝ) * S
  change C0 ≤ R⁻¹
  have hmN : 0 < mN := hm N le_rfl
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    apply Finset.sum_nonneg
    intro j hj
    exact div_nonneg (hδ0 j)
      (hm j (Nat.le_of_lt (Finset.mem_range.mp hj))).le
  have hR : 0 < R := by
    have hfirst : 0 < 2 / (3 * mN) := by positivity
    have hsecond : 0 ≤ (1 / 6 : ℝ) * S := mul_nonneg (by norm_num) hS0
    exact add_pos_of_pos_of_nonneg hfirst hsecond
  have hC0nonneg : 0 ≤ C0 := by
    simpa only [C0] using unionHorizonConductance_nonneg n Q μ0 0 N
  by_cases hC0pos : 0 < C0
  · have hsum := unionHorizon_finite_reciprocal_resistance
      n Q δ hδ0 hδ1 hAbsorb hkill μ0 N hm
      (by simpa only [C0] using hC0pos)
    rw [unionHorizonConductance_terminal] at hsum
    have hfirstEq :
        1 / ((3 / 2 : ℝ) * mN) = 2 / (3 * mN) := by
      field_simp [ne_of_gt hmN]
    have hRle : R ≤ 1 / C0 := by
      dsimp only [R, S, C0, mN]
      rw [hfirstEq] at hsum
      linarith
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hR).2
    calc
      C0 * R ≤ C0 * (1 / C0) :=
        mul_le_mul_of_nonneg_left hRle hC0pos.le
      _ = 1 := by field_simp [ne_of_gt hC0pos]
  · have hC0zero : C0 = 0 := le_antisymm (le_of_not_gt hC0pos) hC0nonneg
    rw [hC0zero]
    exact inv_nonneg.mpr hR.le

theorem paperSharedNoiseResistance_bound
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    [∀ j, PartialOrder (AugmentedState (X j))] [∀ j, Preorder (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (δ : ℕ → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (hkill : ∀ j (x : X j),
      δ j ≤ (Q j (Sum.inl x)).real (allCemetery (n j)))
    (ν : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (ν j)]
    (hassoc : ∀ j, PositivelyAssociated (ν j))
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (hLeast : ∀ j z, cemetery ≤ (z : AugmentedState (X j)))
    (hStateMono : ∀ j w i, Monotone fun x => T j x w i)
    (hDestructive : ∀ j x i, Antitone fun w => T j x w i)
    (hLaw : ∀ j x, Measure.map (fun w i => T j x w i) (ν j) = Q j x)
    (ρ0 : Measure (FinitePopulation (AugmentedState (X 0))))
    [IsProbabilityMeasure ρ0]
    [IsFiniteMeasure (populationMeanMeasure ρ0)]
    (N : ℕ)
    (hm : ∀ j ≤ N, 0 < meanPopulation
      (meanFlow n Q (initialMeanFiniteMeasure ρ0) j)) :
    sharedPopulationLaw n ν T hTJoint ρ0 N livePopulationEvent ≤
      ENNReal.ofReal
        ((2 / (3 * meanPopulation
            (meanFlow n Q (initialMeanFiniteMeasure ρ0) N)) +
          (1 / 6 : ℝ) *
            ∑ j ∈ Finset.range N,
              δ j / meanPopulation
                (meanFlow n Q (initialMeanFiniteMeasure ρ0) j))⁻¹) := by
  have hDecouple := association_decoupling_probability
    n Q ν hassoc T hTJoint hLeast hStateMono hDestructive hLaw ρ0 N
  have hPotential := initialBellmanPotential_le_horizonConductance
    1 (by norm_num) n Q hAbsorb ρ0 N
  have hConductance := unionHorizonConductance_initial_bound
    n Q δ hδ0 hδ1 hAbsorb hkill
      (initialMeanFiniteMeasure ρ0) N hm
  exact hDecouple.trans <| hPotential.trans <|
    ENNReal.ofReal_le_ofReal hConductance

end Shepp.Section4
end SheppFlattenedModule059

section SheppFlattenedModule060
open scoped BigOperators ENNReal ProbabilityTheory Topology
open MeasureTheory Set Filter

namespace Shepp.Section4

open ProbabilityTheory

theorem paperSharedNonextinction_tendsto_zero
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    [∀ j, PartialOrder (AugmentedState (X j))] [∀ j, Preorder (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (δ : ℕ → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (hkill : ∀ j (x : X j),
      δ j ≤ (Q j (Sum.inl x)).real (allCemetery (n j)))
    (ν : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (ν j)]
    (hassoc : ∀ j, PositivelyAssociated (ν j))
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (hLeast : ∀ j z, cemetery ≤ (z : AugmentedState (X j)))
    (hStateMono : ∀ j w i, Monotone fun x => T j x w i)
    (hDestructive : ∀ j x i, Antitone fun w => T j x w i)
    (hLaw : ∀ j x, Measure.map (fun w i => T j x w i) (ν j) = Q j x)
    (ρ0 : Measure (FinitePopulation (AugmentedState (X 0))))
    [IsProbabilityMeasure ρ0]
    [IsFiniteMeasure (populationMeanMeasure ρ0)]
    (hm : ∀ j, 0 < meanPopulation
      (meanFlow n Q (initialMeanFiniteMeasure ρ0) j))
    (hdiv : DivergentResistance δ (fun j =>
      meanPopulation (meanFlow n Q (initialMeanFiniteMeasure ρ0) j))) :
    Tendsto (fun N =>
      sharedPopulationLaw n ν T hTJoint ρ0 N
        (livePopulationEvent (X := X (generationAfter 0 N))))
      atTop (𝓝 0) := by
  let m : ℕ → ℝ := fun j =>
    meanPopulation (meanFlow n Q (initialMeanFiniteMeasure ρ0) j)
  let c : ℝ := 1 / 6
  have hc : 0 < c := by norm_num [c]
  have hUpper : ∀ N,
      sharedPopulationLaw n ν T hTJoint ρ0 N
          (livePopulationEvent (X := X (generationAfter 0 N))) ≤
        (ENNReal.ofReal c * resistancePartialENN δ m N)⁻¹ := by
    intro N
    have hFinite := paperSharedNoiseResistance_bound
      n Q δ hδ0 hδ1 hAbsorb hkill ν hassoc T hTJoint
      hLeast hStateMono hDestructive hLaw ρ0 N
      (fun j _hj => hm j)
    have ha : 0 < 2 / (3 * m N) := by
      have hmN : 0 < m N := by simpa only [m] using hm N
      positivity
    have hDrop := ofReal_inverse_add_mul_sum_le
      (Finset.range N)
      (a := 2 / (3 * m N))
      (c := c) (r := fun j => δ j / m j)
      ha hc (fun j _hj => div_nonneg (hδ0 j) (by
        simpa only [m] using (hm j).le))
    exact hFinite.trans (by
      simpa only [m, c, resistancePartialENN, resistanceTermENN] using hDrop)
  have hInv : Tendsto
      (fun N => (ENNReal.ofReal c * resistancePartialENN δ m N)⁻¹)
      atTop (𝓝 0) := by
    apply resistanceInverse_tendsto_zero hc
    simpa only [m] using hdiv
  exact Filter.Tendsto.squeeze tendsto_const_nhds hInv
    (fun _N => bot_le) hUpper

theorem paperSharedFiniteTimeExtinction_of_divergentResistance
    {K Ω : Type*} [MetricSpace K] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : ℕ → Ω → CompactResidual K)
    (hR : ∀ N, Measurable (R N))
    (hRdec : ∀ ω, Antitone fun N => R N ω)
    {X W : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (W j)]
    [∀ j, PartialOrder (AugmentedState (X j))] [∀ j, Preorder (W j)]
    (n : ℕ → ℕ)
    (Q : (j : ℕ) → Kernel (AugmentedState (X j))
      (Fin (n j) → AugmentedState (X (j + 1))))
    [∀ j, IsMarkovKernel (Q j)]
    (delta : ℕ → ℝ) (hdelta0 : ∀ j, 0 ≤ delta j)
    (hdelta1 : ∀ j, delta j ≤ 1)
    (hAbsorb : ∀ j, Q j cemetery (allCemetery (n j)) = 1)
    (hkill : ∀ j (x : X j),
      delta j ≤ (Q j (Sum.inl x)).real (allCemetery (n j)))
    (nu : (j : ℕ) → Measure (W j)) [∀ j, IsProbabilityMeasure (nu j)]
    (hassoc : ∀ j, PositivelyAssociated (nu j))
    (T : (j : ℕ) → AugmentedState (X j) → W j →
      Fin (n j) → AugmentedState (X (j + 1)))
    (hTJoint : ∀ j i, Measurable fun p : AugmentedState (X j) × W j =>
      T j p.1 p.2 i)
    (hLeast : ∀ j z, cemetery ≤ (z : AugmentedState (X j)))
    (hStateMono : ∀ j w i, Monotone fun x => T j x w i)
    (hDestructive : ∀ j x i, Antitone fun w => T j x w i)
    (hLaw : ∀ j x, Measure.map (fun w i => T j x w i) (nu j) = Q j x)
    (rho0 : Measure (FinitePopulation (AugmentedState (X 0))))
    [IsProbabilityMeasure rho0]
    [IsFiniteMeasure (populationMeanMeasure rho0)]
    (Xi : (N : ℕ) → Ω →
      FinitePopulation (AugmentedState (X (generationAfter 0 N))))
    (hXiMeas : ∀ N, Measurable (Xi N))
    (hXiLaw : ∀ N, Measure.map (Xi N) μ =
      sharedPopulationLaw n nu T hTJoint rho0 N)
    (hEvent : ∀ N, (Xi N) ⁻¹'
      (livePopulationEvent (X := X (generationAfter 0 N))) =
        residualNonemptyEvent R N)
    (hm : ∀ j, 0 < meanPopulation
      (meanFlow n Q (initialMeanFiniteMeasure rho0) j))
    (hdiv : DivergentResistance delta (fun j =>
      meanPopulation (meanFlow n Q (initialMeanFiniteMeasure rho0) j))) :
    μ (residualFiniteTimeExtinctionEvent R) = 1 := by
  apply residualFiniteTimeExtinction_of_nonempty_tendsto_zero R hR hRdec μ
  have hshared := paperSharedNonextinction_tendsto_zero
    n Q delta hdelta0 hdelta1 hAbsorb hkill nu hassoc T hTJoint
      hLeast hStateMono hDestructive hLaw rho0 hm hdiv
  have hprob : (fun N => μ (residualNonemptyEvent R N)) =
      (fun N => sharedPopulationLaw n nu T hTJoint rho0 N
        (livePopulationEvent (X := X (generationAfter 0 N)))) := by
    funext N
    exact residualNonempty_measure_eq_sharedPopulationLaw_of_pathwise_identification
      n nu T hTJoint rho0 μ Xi hXiMeas hXiLaw R hEvent N
  rw [hprob]
  exact hshared

end Shepp.Section4
end SheppFlattenedModule060

section SheppFlattenedModule061
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology
open MeasureTheory Set

namespace Shepp.Section5

open ProbabilityTheory
open Shepp.Section2 Shepp.Section3 Shepp.Section4

theorem spatialResidual_finiteTimeExtinction
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) :
    spatialPathMeasure P
        (residualFiniteTimeExtinctionEvent (spatialResidual P)) = 1 := by
  classical
  letI : PartialOrder (AugmentedState (SpatialParticle P)) :=
    spatialAugmentedPartialOrder P
  letI (j : ℕ) : Preorder (SpatialInnovation P j) :=
    spatialInnovationPreorder P j
  have hlaw : ∀ j (x : AugmentedState (SpatialParticle P)),
      Measure.map (fun w i => spatialTransition P j x w i)
          (spatialInnovationMeasure P j) =
        spatialOneParticleKernel P j x := by
    intro j x
    exact (spatialOneParticleKernel_apply P j x).symm
  have hXiLaw : ∀ N,
      Measure.map (spatialPopulationPath P N) (spatialPathMeasure P) =
        spatialSharedPopulationLaw P N := by
    intro N
    exact (spatialPopulationPath_hasLaw_shared P N).map_eq
  by_cases hzero : ∃ j, spatialMeanSize P j = 0
  · obtain ⟨j, hj⟩ := hzero
    apply sharedFiniteTimeExtinction_of_meanPopulation_eq_zero
      (K := FlatTorus d) (Ω := SpatialPath P)
      (X := fun _ => SpatialParticle P)
      (W := fun t => SpatialInnovation P t)
      (μ := spatialPathMeasure P)
      (R := spatialResidual P)
      (hR := measurable_spatialResidual P)
      (hRdec := spatialResidual_antitone P)
      (n := fun _ => spatialSlotCount d)
      (Q := fun t => spatialOneParticleKernel P t)
      (nu := fun t => spatialInnovationMeasure P t)
      (T := fun t => spatialTransition P t)
      (hTJoint := fun t i => measurable_spatialTransition P t i)
      (hLaw := hlaw)
      (hAbsorb := fun t => spatialOneParticleKernel_cemetery P t)
      (rho0 := Measure.dirac (spatialInitialPopulation P))
      (Xi := fun N => spatialPopulationPath P N)
      (hXiMeas := measurable_spatialPopulationPath P)
      (hXiLaw := hXiLaw)
      (hEvent := spatialPopulationPath_preimage_live_eq_residualNonemptyEvent P)
      (steps := j)
    rw [generationAfter_eq_add, Nat.zero_add]
    exact hj
  · have hm : ∀ j, 0 < spatialMeanSize P j := by
      intro j
      have hne : spatialMeanSize P j ≠ 0 := by
        intro hj
        exact hzero ⟨j, hj⟩
      exact lt_of_le_of_ne (spatialMeanSize_nonneg P j) (Ne.symm hne)
    apply paperSharedFiniteTimeExtinction_of_divergentResistance
      (K := FlatTorus d) (Ω := SpatialPath P)
      (X := fun _ => SpatialParticle P)
      (W := fun t => SpatialInnovation P t)
      (μ := spatialPathMeasure P)
      (R := spatialResidual P)
      (hR := measurable_spatialResidual P)
      (hRdec := spatialResidual_antitone P)
      (n := fun _ => spatialSlotCount d)
      (Q := fun t => spatialOneParticleKernel P t)
      (delta := spatialKillingDelta P)
      (hdelta0 := spatialKillingDelta_nonneg P)
      (hdelta1 := spatialKillingDelta_le_one P)
      (hAbsorb := fun t => spatialOneParticleKernel_cemetery P t)
      (hkill := spatialOneParticleKernel_killing hd P)
      (nu := fun t => spatialInnovationMeasure P t)
      (hassoc := positivelyAssociated_spatialInnovationMeasure P)
      (T := fun t => spatialTransition P t)
      (hTJoint := fun t i => measurable_spatialTransition P t i)
      (hLeast := fun _ z => cemetery_le_spatialState z)
      (hStateMono := fun t w i _ _ hxy =>
        spatialTransition_state_mono P t w i hxy)
      (hDestructive := fun t x i _ _ hww =>
        spatialTransition_destructive P t x i hww)
      (hLaw := hlaw)
      (rho0 := Measure.dirac (spatialInitialPopulation P))
      (Xi := fun N => spatialPopulationPath P N)
      (hXiMeas := measurable_spatialPopulationPath P)
      (hXiLaw := hXiLaw)
      (hEvent := spatialPopulationPath_preimage_live_eq_residualNonemptyEvent P)
      (hm := by simpa [spatialMeanSize] using hm)
      (hdiv := by
        change DivergentResistance (spatialKillingDelta P) (spatialMeanSize P)
        exact spatialDivergentResistance hd P hm)

end Shepp.Section5
end SheppFlattenedModule061

section SheppFlattenedModule062
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology
open MeasureTheory Set

namespace Shepp.Section5

open ProbabilityTheory
open Shepp.Section2 Shepp.Section3 Shepp.Section4

theorem map_cast_measure_family
    {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (μ : ∀ i, Measure (β i)) {i i' : ι} (h : i = i') :
    Measure.map (_root_.cast (congrArg β h)) (μ i) = μ i' := by
  cases h
  exact Measure.map_id

theorem measurable_packetInnovation_cast
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    {t k : ℕ} (h : spatialLevel P t = k) :
    Measurable fun w : SpatialInnovation P t =>
      _root_.cast (congrArg (PacketInnovation P) h) w := by
  subst k
  exact measurable_id

theorem spatialLevel_blockStart_add
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) :
    spatialLevel P (spatialBlockStart P k + p) = k := by
  let p' : Fin (subblockCount P k + 1) := ⟨p, by omega⟩
  change blockIndex (subblockCount P)
      (blockStart (subblockCount P) k + p) = k
  change blockIndex (subblockCount P)
      (blockStart (subblockCount P) k + p') = k
  exact blockIndex_start_add (subblockCount P) k p'

noncomputable def spatialPacketCloud
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (ω : SpatialPath P) : PacketCloudSample P k (FlatTorus d) :=
  fun p =>
    _root_.cast
      (congrArg (PacketInnovation P) (spatialLevel_blockStart_add P k p))
      (ω (spatialBlockStart P k + p))

theorem spatialDeletionTime_blockStart_add
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) :
    SpatialDeletionTime P (spatialBlockStart P k + p) := by
  let p' : Fin (subblockCount P k + 1) := ⟨p, by omega⟩
  unfold SpatialDeletionTime IsDeletionTime
  change blockOffset (subblockCount P)
      (blockStart (subblockCount P) k + p') <
    subblockCount P
      (blockIndex (subblockCount P)
        (blockStart (subblockCount P) k + p'))
  rw [blockIndex_start_add, blockOffset_start_add]
  exact p.isLt

theorem measurable_spatialPacketCloud_cast
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) :
    Measurable fun w : SpatialInnovation P (spatialBlockStart P k + p) =>
      _root_.cast
        (congrArg (PacketInnovation P) (spatialLevel_blockStart_add P k p)) w := by
  exact measurable_packetInnovation_cast P
    (spatialLevel_blockStart_add P k p)

theorem measurable_spatialPacketCloud
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    Measurable (spatialPacketCloud P k) := by
  apply measurable_pi_lambda
  intro p
  exact (measurable_spatialPacketCloud_cast P k p).comp
    (measurable_spatialPath_eval P (spatialBlockStart P k + p))

theorem spatialPacketCloud_coordinate_hasLaw
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (p : Fin (subblockCount P k)) :
    HasLaw (fun ω : SpatialPath P => spatialPacketCloud P k ω p)
      (packetSubblockMeasure (flatTorusVolume d) P k p)
      (spatialPathMeasure P) := by
  let t : ℕ := spatialBlockStart P k + p
  let c : SpatialInnovation P t → PacketInnovation P k := fun w =>
    _root_.cast
      (congrArg (PacketInnovation P) (spatialLevel_blockStart_add P k p)) w
  have hc : Measurable c := measurable_spatialPacketCloud_cast P k p
  refine ⟨(hc.comp (measurable_spatialPath_eval P t)).aemeasurable, ?_⟩
  change Measure.map (c ∘ fun ω : SpatialPath P => ω t)
      (spatialPathMeasure P) = _
  rw [← Measure.map_map hc (measurable_spatialPath_eval P t)]
  rw [(spatialPath_eval_hasLaw P t).map_eq]
  have hdelete : SpatialDeletionTime P t :=
    spatialDeletionTime_blockStart_add P k p
  have hlevel : spatialLevel P t = k := spatialLevel_blockStart_add P k p
  have hoffset : spatialOffset P t = p := by
    let p' : Fin (subblockCount P k + 1) := ⟨p, by omega⟩
    change blockOffset (subblockCount P)
        (blockStart (subblockCount P) k + p') = p
    exact blockOffset_start_add (subblockCount P) k p'
  unfold spatialInnovationMeasure
  rw [dif_pos hdelete]
  let z : Σ q : ℕ, Fin (subblockCount P q) :=
    ⟨spatialLevel P t, ⟨spatialOffset P t, hdelete⟩⟩
  let z' : Σ q : ℕ, Fin (subblockCount P q) := ⟨k, p⟩
  have hz : z = z' := by
    apply Sigma.ext hlevel
    exact (Fin.heq_ext_iff (congrArg (subblockCount P) hlevel)).2 hoffset
  have hmap := map_cast_measure_family
    (β := fun q : Σ q : ℕ, Fin (subblockCount P q) => PacketInnovation P q.1)
    (fun q => packetSubblockMeasure (flatTorusVolume d) P q.1 q.2) hz
  simpa only [z, z', c] using hmap

theorem spatialPacketCloud_subblocks_iIndepFun
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    iIndepFun
      (fun p (ω : SpatialPath P) => spatialPacketCloud P k ω p)
      (spatialPathMeasure P) := by
  let time : Fin (subblockCount P k) → ℕ :=
    fun p => spatialBlockStart P k + p
  have htime : Function.Injective time := by
    intro p q hpq
    apply Fin.ext
    dsimp only [time] at hpq
    omega
  have hraw := iIndepFun.precomp htime
    (spatialPath_coordinates_iIndepFun P)
  have hcomp := hraw.comp
    (fun p w =>
      _root_.cast
        (congrArg (PacketInnovation P) (spatialLevel_blockStart_add P k p)) w)
    (fun p => measurable_spatialPacketCloud_cast P k p)
  exact hcomp.congr fun _ => Filter.Eventually.of_forall fun _ => rfl

theorem spatialPacketCloud_hasLaw
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (k : ℕ) :
    HasLaw (spatialPacketCloud P k)
      (packetCloudMeasure (flatTorusVolume d) P k) (spatialPathMeasure P) := by
  exact (spatialPacketCloud_subblocks_iIndepFun P k).hasLaw_pi
    (spatialPacketCloud_coordinate_hasLaw P k)

theorem spatialPacketCloud_at_deletion
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (hdelete : SpatialDeletionTime P j) (ω : SpatialPath P) :
    spatialPacketCloud P (spatialLevel P j) ω
        ⟨spatialOffset P j, hdelete⟩ = ω j := by
  unfold spatialPacketCloud
  have htime :
      spatialBlockStart P (spatialLevel P j) + spatialOffset P j = j :=
    blockStart_add_offset (subblockCount P) j
  rw [cast_eq_iff_heq]
  rw [htime]

noncomputable def spatialPacketCovered
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (ω : SpatialPath P) : Set (FlatTorus d) :=
  ⋃ p : Fin (subblockCount P k),
    finiteCloudCovered (fun n : PacketMark P k => r n)
      (spatialPacketCloud P k ω p)

noncomputable def markedAtomsCovered
    {K : Type*} [PseudoMetricSpace K] (r : ℕ → ℝ)
    (A : Set (K × ℕ)) : Set K :=
  ⋃ a : K × ℕ, ⋃ _h : a ∈ A, Metric.ball a.1 (r a.2)

theorem spatialPacketCovered_eq_markedAtomsCovered_packetFullAtoms
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (ω : SpatialPath P) :
    spatialPacketCovered P k ω =
      markedAtomsCovered r (packetFullAtoms (spatialPacketCloud P k ω)) := by
  rw [packetFullAtoms_eq_iUnion_subblocks]
  ext z
  simp only [spatialPacketCovered, markedAtomsCovered, finiteCloudCovered,
    packetSubblockAtoms, markedCloudPoints, cloudPoints, Set.mem_iUnion,
    Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, n, j, hz⟩
    let a : FlatTorus d × ℕ :=
      ((spatialPacketCloud P k ω p n).2 j, n)
    refine ⟨a, ?_, ?_⟩
    · refine ⟨p, n, (spatialPacketCloud P k ω p n).2 j, ?_, rfl⟩
      exact ⟨j, j.isLt, rfl⟩
    · simpa only [a] using hz
  · rintro ⟨a, ⟨p, n, x, ⟨j, hj, hjx⟩, hxa⟩, hz⟩
    subst a
    subst x
    exact ⟨p, n, ⟨j, hj⟩, hz⟩

noncomputable def spatialFullCoveredThroughPacket
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (K : ℕ) (ω : SpatialPath P) : Set (FlatTorus d) :=
  ⋃ k : Fin (K + 1), spatialPacketCovered P k ω

theorem spatialFullCoveredThroughPacket_mono
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (K : ℕ) (ω : SpatialPath P) :
    spatialFullCoveredThroughPacket P K ω ⊆
      spatialFullCoveredThroughPacket P (K + 1) ω := by
  intro z hz
  simp only [spatialFullCoveredThroughPacket, mem_iUnion] at hz ⊢
  obtain ⟨k, hk⟩ := hz
  exact ⟨⟨k, by omega⟩, hk⟩

theorem spatialLevel_le_time
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (j : ℕ) :
    spatialLevel P j ≤ j :=
  (self_le_blockStart (subblockCount P) (spatialLevel P j)).trans
    (blockIndex_lower (subblockCount P) j)

theorem deletionCovered_subset_spatialFullCoveredThroughPacket
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (j : ℕ) (hdelete : SpatialDeletionTime P j) (ω : SpatialPath P) :
    finiteCloudCovered
        (fun n : PacketMark P (spatialLevel P j) => r n) (ω j) ⊆
      spatialFullCoveredThroughPacket P j ω := by
  intro z hz
  simp only [spatialFullCoveredThroughPacket, spatialPacketCovered,
    mem_iUnion]
  let k : Fin (j + 1) := ⟨spatialLevel P j, by
    exact Nat.lt_succ_of_le (spatialLevel_le_time P j)⟩
  let p : Fin (subblockCount P (spatialLevel P j)) :=
    ⟨spatialOffset P j, hdelete⟩
  refine ⟨k, p, ?_⟩
  rw [spatialPacketCloud_at_deletion P j hdelete ω]
  exact hz

noncomputable def spatialRevealedCovered
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ℕ → SpatialPath P → Set (FlatTorus d)
  | 0, _ω => ∅
  | j + 1, ω => by
      classical
      exact if h : SpatialDeletionTime P j then
        spatialRevealedCovered P j ω ∪
          finiteCloudCovered
            (fun n : PacketMark P (spatialLevel P j) => r n) (ω j)
      else spatialRevealedCovered P j ω

theorem coe_spatialResidual_eq_compl_spatialRevealedCovered
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ∀ N (ω : SpatialPath P),
      ((spatialResidual P N ω : CompactResidual (FlatTorus d)) :
          Set (FlatTorus d)) =
        (spatialRevealedCovered P N ω)ᶜ := by
  intro N
  induction N with
  | zero =>
      intro ω
      simp [spatialRevealedCovered]
  | succ j ih =>
      intro ω
      classical
      by_cases hdelete : SpatialDeletionTime P j
      · rw [spatialResidual_succ_of_deletion P j ω hdelete]
        unfold packetDeleteResidual
        rw [coe_compactDeleteFiniteCloud, ih]
        simp only [spatialRevealedCovered, hdelete, dite_true]
        ext z
        simp only [mem_sdiff, mem_compl_iff, mem_union]
        tauto
      · rw [spatialResidual_succ_of_refinement P j ω hdelete, ih]
        simp only [spatialRevealedCovered, hdelete, dite_false]

theorem spatialRevealedCovered_subset_fullCoveredThroughPacket
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ∀ N (ω : SpatialPath P),
      spatialRevealedCovered P N ω ⊆
        spatialFullCoveredThroughPacket P N ω := by
  intro N
  induction N with
  | zero =>
      intro ω z hz
      simp [spatialRevealedCovered] at hz
  | succ j ih =>
      intro ω
      classical
      by_cases hdelete : SpatialDeletionTime P j
      · simp only [spatialRevealedCovered, hdelete, dite_true]
        intro z hz
        rcases hz with hz | hz
        · exact spatialFullCoveredThroughPacket_mono P j ω (ih ω hz)
        · exact spatialFullCoveredThroughPacket_mono P j ω
            (deletionCovered_subset_spatialFullCoveredThroughPacket
              P j hdelete ω hz)
      · simp only [spatialRevealedCovered, hdelete, dite_false]
        intro z hz
        exact spatialFullCoveredThroughPacket_mono P j ω (ih ω hz)

def spatialFiniteFullPacketCoverEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    Set (SpatialPath P) :=
  {ω | ∃ K, spatialFullCoveredThroughPacket P K ω = Set.univ}

theorem residualFiniteTimeExtinctionEvent_subset_fullPacketCover
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    residualFiniteTimeExtinctionEvent (spatialResidual P) ⊆
      spatialFiniteFullPacketCoverEvent P := by
  intro ω hω
  rcases hω with ⟨N, hN⟩
  refine ⟨N, Set.eq_univ_of_univ_subset ?_⟩
  intro z _hz
  apply spatialRevealedCovered_subset_fullCoveredThroughPacket P N ω
  have hcoe :
      ((spatialResidual P N ω : CompactResidual (FlatTorus d)) :
          Set (FlatTorus d)) = ∅ := by
    rw [hN]
    rfl
  rw [coe_spatialResidual_eq_compl_spatialRevealedCovered P N ω] at hcoe
  by_contra hz
  have : z ∈ (spatialRevealedCovered P N ω)ᶜ := hz
  rw [hcoe] at this
  exact this

theorem spatialFiniteFullPacketCoverEvent_measure_one
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) :
    spatialPathMeasure P (spatialFiniteFullPacketCoverEvent P) = 1 := by
  apply le_antisymm
  · calc
      spatialPathMeasure P (spatialFiniteFullPacketCoverEvent P) ≤
          spatialPathMeasure P Set.univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  calc
    1 = spatialPathMeasure P
        (residualFiniteTimeExtinctionEvent (spatialResidual P)) :=
      (spatialResidual_finiteTimeExtinction hd P).symm
    _ ≤ spatialPathMeasure P (spatialFiniteFullPacketCoverEvent P) :=
      measure_mono (residualFiniteTimeExtinctionEvent_subset_fullPacketCover P)

end Shepp.Section5
end SheppFlattenedModule062

section SheppFlattenedModule063
open scoped ENNReal NNReal ProbabilityTheory Topology
open MeasureTheory Set

namespace Shepp.Section5

open ProbabilityTheory
open Shepp.Section2 Shepp.Section3 Shepp.Section4 TopologicalSpace

theorem cloudPoints_eq_range_fin
    {K : Type*} (w : PoissonCloudSample K) :
    cloudPoints w = Set.range fun i : Fin w.1 => w.2 i := by
  ext x
  simp only [cloudPoints, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩

theorem finite_cloudPoints
    {K : Type*} (w : PoissonCloudSample K) :
    (cloudPoints w).Finite := by
  rw [cloudPoints_eq_range_fin]
  exact Set.finite_range _

noncomputable def cloudSupport
    {K : Type*} [MetricSpace K]
    (w : PoissonCloudSample K) : CompactResidual K :=
  ⟨cloudPoints w, (finite_cloudPoints w).isCompact⟩

@[simp]
theorem coe_cloudSupport
    {K : Type*} [MetricSpace K]
    (w : PoissonCloudSample K) :
    ((cloudSupport w : CompactResidual K) : Set K) = cloudPoints w :=
  rfl

noncomputable def packetFullMarkSupport
    {d : ℕ} {r : ℕ → ℝ} {K : Type*} [MetricSpace K]
    {P : GeometricPacketInterface d r} {k : ℕ}
    (w : PacketCloudSample P k K) (n : PacketMark P k) :
    CompactResidual K :=
  ⟨⋃ p : Fin (subblockCount P k), cloudPoints (w p n),
    (Set.finite_iUnion fun p => finite_cloudPoints (w p n)).isCompact⟩

@[simp]
theorem coe_packetFullMarkSupport
    {d : ℕ} {r : ℕ → ℝ} {K : Type*} [MetricSpace K]
    {P : GeometricPacketInterface d r} {k : ℕ}
    (w : PacketCloudSample P k K) (n : PacketMark P k) :
    ((packetFullMarkSupport w n : CompactResidual K) : Set K) =
      ⋃ p : Fin (subblockCount P k), cloudPoints (w p n) :=
  rfl

def compactMisses
    {K : Type*} [TopologicalSpace K] (E : Set K) :
    Set (CompactResidual K) :=
  {A | Disjoint (A : Set K) E}

theorem compactMisses_inter
    {K : Type*} [TopologicalSpace K] (E F : Set K) :
    compactMisses E ∩ compactMisses F = compactMisses (E ∪ F) := by
  ext A
  simp only [compactMisses, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.disjoint_left, Set.mem_union]
  constructor
  · rintro ⟨hE, hF⟩ x hxA hx
    rcases hx with hxE | hxF
    · exact hE hxA hxE
    · exact hF hxA hxF
  · intro h
    exact ⟨fun x hxA hxE => h hxA (Or.inl hxE),
      fun x hxA hxF => h hxA (Or.inr hxF)⟩

@[simp]
theorem compactMisses_empty
    {K : Type*} [TopologicalSpace K] :
    compactMisses (∅ : Set K) = Set.univ := by
  ext A
  simp [compactMisses]

def compactMissGenerator
    (K : Type*) [TopologicalSpace K] :
    Set (Set (CompactResidual K)) :=
  {S | ∃ F : Set K, IsClosed F ∧ S = compactMisses F}

theorem isPiSystem_compactMissGenerator
    (K : Type*) [TopologicalSpace K] :
    IsPiSystem (compactMissGenerator K) := by
  intro S hS T hT _hST
  rcases hS with ⟨E, hE, rfl⟩
  rcases hT with ⟨F, hF, rfl⟩
  exact ⟨E ∪ F, hE.union hF, compactMisses_inter E F⟩

theorem measurableSet_compactMisses_of_isClosed
    {K : Type*} [MetricSpace K]
    {F : Set K} (hF : IsClosed F) :
    MeasurableSet (compactMisses F) := by
  have hhit : IsClosed
      {A : CompactResidual K | ((A : Set K) ∩ F).Nonempty} :=
    Compacts.isClosed_inter_nonempty_of_isClosed hF
  have heq :
      compactMisses F =
        {A : CompactResidual K | ((A : Set K) ∩ F).Nonempty}ᶜ := by
    ext A
    simp only [compactMisses, Set.mem_setOf_eq, Set.mem_compl_iff,
      Set.disjoint_left]
    constructor
    · intro h hnonempty
      rcases hnonempty with ⟨x, hxA, hxF⟩
      exact h hxA hxF
    · intro h x hxA hxF
      exact h ⟨x, hxA, hxF⟩
  rw [heq]
  exact hhit.measurableSet.compl

private theorem measurableSet_compactMisses_open_generate
    {K : Type*} [MetricSpace K] [CompactSpace K]
    {U : Set K} (hU : IsOpen U) :
    MeasurableSet[MeasurableSpace.generateFrom (compactMissGenerator K)]
      (compactMisses U) := by
  by_cases htop : U = Set.univ
  · subst U
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨Set.univ, isClosed_univ, rfl⟩
  · let F : ℕ → Set K := fun n =>
      compactOpenCore (⊤ : CompactResidual K) U n
    have hFclosed : ∀ n, IsClosed (F n) := fun n =>
      isClosed_compactOpenCore (⊤ : CompactResidual K) U n
    have hUnion : ⋃ n : ℕ, F n = U := by
      simpa only [F, Compacts.coe_top, Set.univ_inter] using
        iUnion_compactOpenCore (⊤ : CompactResidual K) hU
          (Set.nonempty_compl.2 htop)
    have heq : compactMisses U = ⋂ n : ℕ, compactMisses (F n) := by
      ext A
      simp only [compactMisses, Set.mem_setOf_eq, Set.mem_iInter,
        Set.disjoint_left]
      constructor
      · intro h n x hxA hxF
        exact h hxA (hUnion ▸ Set.mem_iUnion.2 ⟨n, hxF⟩)
      · intro h x hxA hxU
        have hxUnion : x ∈ ⋃ n : ℕ, F n := hUnion.symm ▸ hxU
        obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hxUnion
        exact h n hxA hxn
    rw [heq]
    exact MeasurableSet.iInter fun n =>
      MeasurableSpace.measurableSet_generateFrom
        ⟨F n, hFclosed n, rfl⟩

theorem borel_compactResidual_eq_generateFrom_misses
    (K : Type*) [MetricSpace K] [CompactSpace K]
    [SecondCountableTopology K] :
    borel (CompactResidual K) =
      MeasurableSpace.generateFrom (compactMissGenerator K) := by
  let basis : Set (Set (CompactResidual K)) :=
    (fun u : Set (Set K) =>
      {A : CompactResidual K |
        (A : Set K) ⊆ ⋃₀ u ∧
          ∀ U ∈ u, ((A : Set K) ∩ U).Nonempty}) ''
      {u : Set (Set K) | u.Finite ∧ u ⊆ {U | IsOpen U}}
  have hbasis : IsTopologicalBasis basis := by
    simpa only [basis] using
      (isTopologicalBasis_opens.compacts (α := K))
  apply le_antisymm
  · rw [hbasis.borel_eq_generateFrom]
    apply MeasurableSpace.generateFrom_le
    intro V hV
    rcases hV with ⟨u, ⟨huFinite, huOpen⟩, rfl⟩
    let Uall : Set K := ⋃₀ u
    have hUall : IsOpen Uall :=
      isOpen_sUnion fun U hU => huOpen hU
    have hupper :
        MeasurableSet[MeasurableSpace.generateFrom
          (compactMissGenerator K)]
          (compactMisses Uallᶜ) :=
      MeasurableSpace.measurableSet_generateFrom
        ⟨Uallᶜ, hUall.isClosed_compl, rfl⟩
    have hhits :
        MeasurableSet[MeasurableSpace.generateFrom
          (compactMissGenerator K)]
          (⋂ U ∈ u, (compactMisses U)ᶜ) :=
      huFinite.measurableSet_biInter fun U hU =>
        (measurableSet_compactMisses_open_generate (huOpen hU)).compl
    have heq :
        {A : CompactResidual K |
          (A : Set K) ⊆ ⋃₀ u ∧
            ∀ U ∈ u, ((A : Set K) ∩ U).Nonempty} =
          compactMisses Uallᶜ ∩
            ⋂ U ∈ u, (compactMisses U)ᶜ := by
      ext A
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, compactMisses, Set.disjoint_left, Uall]
      constructor
      · rintro ⟨hsub, hhit⟩
        refine ⟨?_, ?_⟩
        · intro x hxA hxcompl
          exact hxcompl (hsub hxA)
        · intro U hU hmiss
          rcases hhit U hU with ⟨x, hxA, hxU⟩
          exact hmiss hxA hxU
      · rintro ⟨hupper', hhits'⟩
        refine ⟨?_, ?_⟩
        · intro x hxA
          by_contra hxUall
          exact hupper' hxA hxUall
        · intro U hU
          by_contra hnonempty
          apply hhits' U hU
          intro x hxA hxU
          exact hnonempty ⟨x, hxA, hxU⟩
    change MeasurableSet[MeasurableSpace.generateFrom
      (compactMissGenerator K)]
        {A : CompactResidual K |
          (A : Set K) ⊆ ⋃₀ u ∧
            ∀ U ∈ u, ((A : Set K) ∩ U).Nonempty}
    rw [heq]
    exact hupper.inter hhits
  · apply MeasurableSpace.generateFrom_le
    intro V hV
    rcases hV with ⟨F, hF, rfl⟩
    exact measurableSet_compactMisses_of_isClosed hF

theorem measurable_compactSupport_of_misses
    {Ω K : Type*} [MeasurableSpace Ω]
    [MetricSpace K] [CompactSpace K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K]
    (S : Ω → CompactResidual K)
    (hmiss : ∀ E : Set K, MeasurableSet E →
      MeasurableSet (S ⁻¹' compactMisses E)) :
    Measurable S := by
  rw [show CompactResidual.instMeasurableSpace K =
      MeasurableSpace.generateFrom (compactMissGenerator K) by
    exact borel_compactResidual_eq_generateFrom_misses K]
  apply measurable_generateFrom
  intro V hV
  rcases hV with ⟨F, hF, rfl⟩
  exact hmiss F hF.measurableSet

theorem cloudSupport_mem_compactMisses_iff
    {K : Type*} [MetricSpace K]
    (w : PoissonCloudSample K) (E : Set K) :
    cloudSupport w ∈ compactMisses E ↔ w ∈ cloudAvoids E := by
  simp only [compactMisses, Set.mem_setOf_eq, coe_cloudSupport,
    Set.disjoint_left, cloudPoints, cloudAvoids]
  constructor
  · intro h i hi hiE
    exact h ⟨i, hi, rfl⟩ hiE
  · intro h x hx hiE
    rcases hx with ⟨i, hi, rfl⟩
    exact h i hi hiE

theorem packetFullMarkSupport_mem_compactMisses_iff
    {d : ℕ} {r : ℕ → ℝ} {K : Type*} [MetricSpace K]
    {P : GeometricPacketInterface d r} {k : ℕ}
    (w : PacketCloudSample P k K) (n : PacketMark P k) (E : Set K) :
    packetFullMarkSupport w n ∈ compactMisses E ↔
      w ∈ packetFullMarkAvoids n E := by
  simp only [compactMisses, Set.mem_setOf_eq,
    coe_packetFullMarkSupport, Set.disjoint_left,
    packetFullMarkAvoids, Set.mem_pi, Set.mem_univ, forall_const,
    Set.mem_preimage, cloudAvoids, cloudPoints, Set.mem_iUnion]
  constructor
  · intro h p i hi hiE
    exact h ⟨p, i, hi, rfl⟩ hiE
  · intro h x hx hiE
    rcases hx with ⟨p, i, hi, rfl⟩
    exact h p i hi hiE

theorem measurable_cloudSupport
    {K : Type*} [MetricSpace K] [CompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] :
    Measurable (cloudSupport : PoissonCloudSample K → CompactResidual K) := by
  apply measurable_compactSupport_of_misses cloudSupport
  intro E hE
  have heq : cloudSupport ⁻¹' compactMisses E = cloudAvoids E := by
    ext w
    exact cloudSupport_mem_compactMisses_iff w E
  rw [heq]
  exact measurableSet_cloudAvoids hE

theorem measurable_packetFullMarkSupport
    {d : ℕ} {r : ℕ → ℝ} {K : Type*}
    [MetricSpace K] [CompactSpace K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K]
    (P : GeometricPacketInterface d r) (k : ℕ)
    (n : PacketMark P k) :
    Measurable fun w : PacketCloudSample P k K =>
      packetFullMarkSupport w n := by
  apply measurable_compactSupport_of_misses
    (fun w : PacketCloudSample P k K => packetFullMarkSupport w n)
  intro E hE
  have heq :
      (fun w : PacketCloudSample P k K => packetFullMarkSupport w n) ⁻¹'
          compactMisses E =
        packetFullMarkAvoids n E := by
    ext w
    exact packetFullMarkSupport_mem_compactMisses_iff w n E
  rw [heq]
  exact measurableSet_packetFullMarkAvoids n hE

noncomputable def poissonSupportMeasure
    {K : Type*} [MetricSpace K] [CompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsProbabilityMeasure μ] (rate : ℝ≥0) :
    Measure (CompactResidual K) :=
  Measure.map cloudSupport (poissonCloudMeasure μ rate)

noncomputable instance poissonSupportMeasure_isProbabilityMeasure
    {K : Type*} [MetricSpace K] [CompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsProbabilityMeasure μ] (rate : ℝ≥0) :
    IsProbabilityMeasure (poissonSupportMeasure μ rate) := by
  unfold poissonSupportMeasure
  constructor
  rw [Measure.map_apply measurable_cloudSupport MeasurableSet.univ]
  simp

theorem poissonSupportMeasure_compactMisses
    {K : Type*} [MetricSpace K] [CompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    {E : Set K} (hE : IsClosed E) :
    poissonSupportMeasure μ rate (compactMisses E) =
      ENNReal.ofReal
        (Real.exp (-(rate : ℝ) * μ.real E)) := by
  rw [poissonSupportMeasure, Measure.map_apply measurable_cloudSupport]
  · have heq : cloudSupport ⁻¹' compactMisses E = cloudAvoids E := by
      ext w
      exact cloudSupport_mem_compactMisses_iff w E
    rw [heq]
    exact poissonCloudMeasure_cloudAvoids μ rate hE.measurableSet
  · apply measurableSet_compactMisses_of_isClosed
    exact hE

theorem packetFullMarkSupport_hasLaw_poissonSupport_one
    {d : ℕ} {r : ℕ → ℝ} {K : Type*}
    [MetricSpace K] [CompactSpace K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsProbabilityMeasure μ]
    (P : GeometricPacketInterface d r) (k : ℕ)
    (n : PacketMark P k) :
    HasLaw (fun w : PacketCloudSample P k K =>
        packetFullMarkSupport w n)
      (poissonSupportMeasure μ 1) (packetCloudMeasure μ P k) := by
  refine ⟨(measurable_packetFullMarkSupport P k n).aemeasurable, ?_⟩
  apply ext_of_generate_finite
    (compactMissGenerator K)
    (borel_compactResidual_eq_generateFrom_misses K)
    (isPiSystem_compactMissGenerator K)
  · intro S hS
    rcases hS with ⟨E, hE, rfl⟩
    rw [Measure.map_apply (measurable_packetFullMarkSupport P k n)
      (measurableSet_compactMisses_of_isClosed hE)]
    have hpre :
        (fun w : PacketCloudSample P k K =>
          packetFullMarkSupport w n) ⁻¹' compactMisses E =
          packetFullMarkAvoids n E := by
      ext w
      exact packetFullMarkSupport_mem_compactMisses_iff w n E
    rw [hpre, packetCloudMeasure_fullMarkAvoids μ P k n hE.measurableSet]
    simpa using
      (poissonSupportMeasure_compactMisses μ 1 hE).symm
  · rw [Measure.map_apply (measurable_packetFullMarkSupport P k n)
      MeasurableSet.univ]
    simp

def packetAllFullMarksAvoids
    {d : ℕ} {r : ℕ → ℝ} {K : Type*}
    {P : GeometricPacketInterface d r} {k : ℕ}
    (E : PacketMark P k → Set K) :
    Set (PacketCloudSample P k K) :=
  Set.univ.pi fun _p => finiteCloudAvoids E

theorem measurableSet_packetAllFullMarksAvoids
    {d : ℕ} {r : ℕ → ℝ} {K : Type*} [MeasurableSpace K]
    {P : GeometricPacketInterface d r} {k : ℕ}
    {E : PacketMark P k → Set K}
    (hE : ∀ n, MeasurableSet (E n)) :
    MeasurableSet (packetAllFullMarksAvoids E) := by
  exact MeasurableSet.univ_pi fun _p =>
    measurableSet_finiteCloudAvoids hE

theorem packetFullSupportVector_preimage_pi_compactMisses
    {d : ℕ} {r : ℕ → ℝ} {K : Type*} [MetricSpace K]
    {P : GeometricPacketInterface d r} {k : ℕ}
    (E : PacketMark P k → Set K) :
    (fun w : PacketCloudSample P k K =>
        fun n => packetFullMarkSupport w n) ⁻¹'
      (Set.univ.pi fun n => compactMisses (E n)) =
        packetAllFullMarksAvoids E := by
  ext w
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
    packetAllFullMarksAvoids, finiteCloudAvoids]
  constructor
  · intro h p n
    have hn :=
      (packetFullMarkSupport_mem_compactMisses_iff w n (E n)).1 (h n)
    simpa only [packetFullMarkAvoids, Set.mem_pi, Set.mem_univ,
      forall_const, Set.mem_preimage] using hn p
  · intro h n
    apply (packetFullMarkSupport_mem_compactMisses_iff w n (E n)).2
    simp only [packetFullMarkAvoids, Set.mem_pi, Set.mem_univ,
      forall_const, Set.mem_preimage]
    exact fun p => h p n

theorem packetCloudMeasure_allFullMarksAvoids
    {d : ℕ} {r : ℕ → ℝ} {K : Type*} [MeasurableSpace K]
    (μ : Measure K) [IsProbabilityMeasure μ]
    (P : GeometricPacketInterface d r) (k : ℕ)
    (E : PacketMark P k → Set K)
    (hE : ∀ n, MeasurableSet (E n)) :
    packetCloudMeasure μ P k (packetAllFullMarksAvoids E) =
      ∏ n : PacketMark P k,
        ENNReal.ofReal (Real.exp (-μ.real (E n))) := by
  rw [packetCloudMeasure, packetAllFullMarksAvoids, Measure.pi_pi]
  simp_rw [packetSubblockMeasure,
    finiteCloudMeasure_avoids μ (fractionalRate P k · _) E hE]
  rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
    (fun _ _ => Real.exp_nonneg _)]
  rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
    (fun _ _ => Real.exp_nonneg _)]
  rw [← Real.exp_sum, ← Real.exp_sum]
  congr 2
  have hrate : ∀ n : PacketMark P k,
      (∑ p : Fin (subblockCount P k),
        (fractionalRate P k n p : ℝ)) = 1 := by
    intro n
    exact_mod_cast sum_fractionalRate P k n
  calc
    (∑ p : Fin (subblockCount P k),
        -∑ n : PacketMark P k,
          (fractionalRate P k n p : ℝ) * μ.real (E n)) =
        -∑ p : Fin (subblockCount P k),
          ∑ n : PacketMark P k,
            (fractionalRate P k n p : ℝ) * μ.real (E n) := by
      rw [Finset.sum_neg_distrib]
    _ = -∑ n : PacketMark P k,
          ∑ p : Fin (subblockCount P k),
            (fractionalRate P k n p : ℝ) * μ.real (E n) := by
      congr 1
      exact Finset.sum_comm
    _ = -∑ n : PacketMark P k, μ.real (E n) := by
      congr 1
      apply Finset.sum_congr rfl
      intro n _hn
      rw [← Finset.sum_mul, hrate n, one_mul]
    _ = ∑ n : PacketMark P k, -μ.real (E n) := by
      rw [Finset.sum_neg_distrib]

theorem measurable_packetFullSupportVector
    {d : ℕ} {r : ℕ → ℝ} {K : Type*}
    [MetricSpace K] [CompactSpace K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K]
    (P : GeometricPacketInterface d r) (k : ℕ) :
    Measurable fun w : PacketCloudSample P k K =>
      fun n : PacketMark P k => packetFullMarkSupport w n := by
  apply measurable_pi_lambda
  intro n
  exact measurable_packetFullMarkSupport P k n

private noncomputable def poissonSupportFiniteSpanning
    {K : Type*} [MetricSpace K] [CompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsProbabilityMeasure μ] :
    (poissonSupportMeasure μ 1).FiniteSpanningSetsIn
      (compactMissGenerator K) where
  set := fun _ => Set.univ
  set_mem := fun _ =>
    ⟨∅, isClosed_empty, compactMisses_empty.symm⟩
  finite := fun _ => by simp
  spanning := by
    apply Set.eq_univ_of_forall
    intro A
    exact Set.mem_iUnion.2 ⟨0, Set.mem_univ A⟩

theorem packetFullSupportVector_hasLaw
    {d : ℕ} {r : ℕ → ℝ} {K : Type*}
    [MetricSpace K] [CompactSpace K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsProbabilityMeasure μ]
    (P : GeometricPacketInterface d r) (k : ℕ) :
    HasLaw
      (fun w : PacketCloudSample P k K =>
        fun n : PacketMark P k => packetFullMarkSupport w n)
      (Measure.pi fun _n : PacketMark P k => poissonSupportMeasure μ 1)
      (packetCloudMeasure μ P k) := by
  refine ⟨(measurable_packetFullSupportVector P k).aemeasurable, ?_⟩
  symm
  apply Measure.pi_eq_generateFrom
    (fun _n => by
      exact (borel_compactResidual_eq_generateFrom_misses K).symm)
    (fun _n => isPiSystem_compactMissGenerator K)
    (fun _n => poissonSupportFiniteSpanning μ)
  intro s hs
  choose E hE hsE using fun n => hs n
  have hsEq : s = fun n => compactMisses (E n) := funext hsE
  subst s
  rw [Measure.map_apply (measurable_packetFullSupportVector P k)
    (MeasurableSet.univ_pi fun n =>
      measurableSet_compactMisses_of_isClosed (hE n))]
  rw [packetFullSupportVector_preimage_pi_compactMisses]
  rw [packetCloudMeasure_allFullMarksAvoids μ P k E
    (fun n => (hE n).measurableSet)]
  apply Finset.prod_congr rfl
  intro n _hn
  simpa using (poissonSupportMeasure_compactMisses μ 1 (hE n)).symm

abbrev SpatialPacketSubblockIndex
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :=
  (k : ℕ) × Fin (subblockCount P k)

noncomputable def spatialPacketSubblockTime
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    SpatialPacketSubblockIndex P → ℕ :=
  fun q => spatialBlockStart P q.1 + q.2

theorem spatialPacketSubblockTime_injective
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    Function.Injective (spatialPacketSubblockTime P) := by
  intro a b hab
  have hk : a.1 = b.1 := by
    have hlevel := congrArg (spatialLevel P) hab
    simpa only [spatialPacketSubblockTime,
      spatialLevel_blockStart_add] using hlevel
  cases a with
  | mk ak ap =>
      cases b with
      | mk bk bp =>
          dsimp only at hk
          subst bk
          have hp : ap = bp := by
            apply Fin.ext
            dsimp only [spatialPacketSubblockTime] at hab
            omega
          subst bp
          rfl

theorem spatialPacketSubblocks_all_iIndepFun
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    iIndepFun
      (fun q : SpatialPacketSubblockIndex P =>
        fun ω : SpatialPath P => spatialPacketCloud P q.1 ω q.2)
      (spatialPathMeasure P) := by
  have hraw := iIndepFun.precomp
    (spatialPacketSubblockTime_injective P)
    (spatialPath_coordinates_iIndepFun P)
  have hcomp := hraw.comp
    (fun q w =>
      _root_.cast
        (congrArg (PacketInnovation P)
          (spatialLevel_blockStart_add P q.1 q.2)) w)
    (fun q => measurable_spatialPacketCloud_cast P q.1 q.2)
  exact hcomp.congr fun _ => Filter.Eventually.of_forall fun _ => rfl

theorem spatialPacketSubblocks_all_hasLaw
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    HasLaw
      (fun ω : SpatialPath P =>
        fun q : SpatialPacketSubblockIndex P =>
          spatialPacketCloud P q.1 ω q.2)
      (Measure.infinitePi fun q : SpatialPacketSubblockIndex P =>
        packetSubblockMeasure (flatTorusVolume d) P q.1 q.2)
      (spatialPathMeasure P) := by
  exact (spatialPacketSubblocks_all_iIndepFun P).hasLaw_infinitePi
    (fun q => spatialPacketCloud_coordinate_hasLaw P q.1 q.2)
    ((by
      apply measurable_pi_lambda
      intro q
      exact (measurable_pi_apply q.2).comp
        (measurable_spatialPacketCloud P q.1) :
      Measurable fun ω : SpatialPath P =>
        fun q : SpatialPacketSubblockIndex P =>
          spatialPacketCloud P q.1 ω q.2)).aemeasurable

theorem measurable_spatialAllPacketClouds
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    Measurable fun ω : SpatialPath P =>
      fun k : ℕ => spatialPacketCloud P k ω := by
  apply measurable_pi_lambda
  intro k
  exact measurable_spatialPacketCloud P k

theorem spatialAllPacketClouds_hasLaw
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    HasLaw
      (fun ω : SpatialPath P =>
        fun k : ℕ => spatialPacketCloud P k ω)
      (Measure.infinitePi fun k : ℕ =>
        packetCloudMeasure (flatTorusVolume d) P k)
      (spatialPathMeasure P) := by
  let X : (k : ℕ) → Fin (subblockCount P k) → Type :=
    fun k _p => PacketSubblockSample P k (FlatTorus d)
  let flat : SpatialPath P →
      ((q : SpatialPacketSubblockIndex P) → X q.1 q.2) :=
    fun ω q => spatialPacketCloud P q.1 ω q.2
  let curry :
      ((q : SpatialPacketSubblockIndex P) → X q.1 q.2) →
        ((k : ℕ) → (p : Fin (subblockCount P k)) → X k p) :=
    MeasurableEquiv.piCurry X
  have hflatMeas : Measurable flat := by
    apply measurable_pi_lambda
    intro q
    exact (measurable_pi_apply q.2).comp
      (measurable_spatialPacketCloud P q.1)
  have hcurryMeas : Measurable curry :=
    (MeasurableEquiv.piCurry X).measurable
  refine ⟨(measurable_spatialAllPacketClouds P).aemeasurable, ?_⟩
  change Measure.map (curry ∘ flat) (spatialPathMeasure P) = _
  rw [← Measure.map_map hcurryMeas hflatMeas]
  rw [(spatialPacketSubblocks_all_hasLaw P).map_eq]
  change Measure.map (MeasurableEquiv.piCurry X)
      (Measure.infinitePi fun q : SpatialPacketSubblockIndex P =>
        packetSubblockMeasure (flatTorusVolume d) P q.1 q.2) = _
  rw [Measure.infinitePi_map_piCurry]
  congr 1
  funext k
  rw [Measure.infinitePi_eq_pi]
  rfl

theorem spatialPacketClouds_iIndepFun
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    iIndepFun
      (fun k : ℕ => fun ω : SpatialPath P => spatialPacketCloud P k ω)
      (spatialPathMeasure P) := by
  apply (iIndepFun_iff_hasLaw_Pi_infinitePi
    (fun k => spatialPacketCloud_hasLaw P k)
    (measurable_spatialAllPacketClouds P).aemeasurable).2
  exact spatialAllPacketClouds_hasLaw P

noncomputable def spatialFullMarkSupport
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (ω : SpatialPath P) (n : PacketMark P k) :
    CompactResidual (FlatTorus d) :=
  packetFullMarkSupport (spatialPacketCloud P k ω) n

theorem measurable_spatialAllFullMarkSupports
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    Measurable fun ω : SpatialPath P =>
      fun k : ℕ => fun n : PacketMark P k =>
        spatialFullMarkSupport P k ω n := by
  letI : CompactSpace (FlatTorus d) :=
    flatTorusCompactSpaceOfInterface P
  apply measurable_pi_lambda
  intro k
  exact (measurable_packetFullSupportVector P k).comp
    (measurable_spatialPacketCloud P k)

noncomputable def spatialFullMarkSupportMeasure
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    Measure ((k : ℕ) →
      (n : PacketMark P k) → CompactResidual (FlatTorus d)) := by
  letI : CompactSpace (FlatTorus d) :=
    flatTorusCompactSpaceOfInterface P
  exact Measure.infinitePi fun k : ℕ =>
    Measure.pi fun _n : PacketMark P k =>
      poissonSupportMeasure (flatTorusVolume d) 1

theorem spatialAllFullMarkSupports_hasLaw
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    HasLaw
      (fun ω : SpatialPath P =>
        fun k : ℕ => fun n : PacketMark P k =>
          spatialFullMarkSupport P k ω n)
      (spatialFullMarkSupportMeasure P)
      (spatialPathMeasure P) := by
  letI : CompactSpace (FlatTorus d) :=
    flatTorusCompactSpaceOfInterface P
  let X : (k : ℕ) → Type :=
    fun k => PacketCloudSample P k (FlatTorus d)
  let Y : (k : ℕ) → Type :=
    fun k => (n : PacketMark P k) → CompactResidual (FlatTorus d)
  let f : (k : ℕ) → X k → Y k :=
    fun _k w n => packetFullMarkSupport w n
  have hf : ∀ k, Measurable (f k) := fun k =>
    measurable_packetFullSupportVector P k
  have hcloudMeas : Measurable fun ω : SpatialPath P =>
      fun k : ℕ => spatialPacketCloud P k ω :=
    measurable_spatialAllPacketClouds P
  have hcoordinateMeas : Measurable fun w : ((k : ℕ) → X k) =>
      fun k => f k (w k) := by
    apply measurable_pi_lambda
    intro k
    exact (hf k).comp (measurable_pi_apply k)
  refine ⟨(measurable_spatialAllFullMarkSupports P).aemeasurable, ?_⟩
  unfold spatialFullMarkSupportMeasure
  change Measure.map
      ((fun w : ((k : ℕ) → X k) => fun k => f k (w k)) ∘
        (fun ω : SpatialPath P => fun k => spatialPacketCloud P k ω))
      (spatialPathMeasure P) = _
  rw [← Measure.map_map hcoordinateMeas hcloudMeas]
  rw [(spatialAllPacketClouds_hasLaw P).map_eq]
  have hmap := Measure.infinitePi_map_pi
    (μ := fun k : ℕ => packetCloudMeasure (flatTorusVolume d) P k) hf
  rw [hmap]
  congr 1
  funext k
  exact (packetFullSupportVector_hasLaw
    (flatTorusVolume d) P k).map_eq

end Shepp.Section5
end SheppFlattenedModule063

section SheppFlattenedModule064
open scoped ENNReal NNReal ProbabilityTheory Topology
open MeasureTheory Set

namespace Shepp.Section5

open ProbabilityTheory
open Shepp.Section2 Shepp.Section3 Shepp.Section4 TopologicalSpace

def compactSupportPointCovered
    {K : Type*} [PseudoMetricSpace K] (ρ : ℝ) :
    Set (CompactResidual K × K) :=
  {p | ∃ x ∈ (p.1 : Set K), p.2 ∈ Metric.ball x ρ}

theorem isOpen_compactSupportPointCovered
    {K : Type*} [PseudoMetricSpace K] (ρ : ℝ) :
    IsOpen (compactSupportPointCovered (K := K) ρ) := by
  let U : Set (K × K) := {p | dist p.2 p.1 < ρ}
  have hU : IsOpen U := by
    exact isOpen_lt (continuous_dist.comp
      (continuous_snd.prodMk continuous_fst)) continuous_const
  let embed : CompactResidual K × K → CompactResidual (K × K) :=
    fun p => p.1 ×ˢ ({p.2} : CompactResidual K)
  have hembed : Continuous embed := by
    change Continuous
      ((fun q : CompactResidual K × CompactResidual K => q.1 ×ˢ q.2) ∘
        fun p : CompactResidual K × K =>
          (p.1, ({p.2} : CompactResidual K)))
    exact Compacts.continuous_prod.comp
      (continuous_fst.prodMk
        (Compacts.continuous_singleton.comp continuous_snd))
  have hopen : IsOpen
      (embed ⁻¹' {C : CompactResidual (K × K) |
        ((C : Set (K × K)) ∩ U).Nonempty}) :=
    (Compacts.isOpen_inter_nonempty_of_isOpen hU).preimage hembed
  convert hopen using 1
  ext p
  simp only [compactSupportPointCovered, Set.mem_setOf_eq,
    Set.mem_preimage, embed, U]
  constructor
  · rintro ⟨x, hx, hball⟩
    exact ⟨(x, p.2), ⟨hx, rfl⟩, by simpa using hball⟩
  · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, hdist⟩
    have hz' : z = p.2 := by simpa using hz
    subst z
    exact ⟨x, hx, by simpa using hdist⟩

noncomputable def compactSupportsCovered
    {ι K : Type*} [PseudoMetricSpace K]
    (radius : ι → ℝ) (A : ι → CompactResidual K) : Set K :=
  ⋃ i : ι, ⋃ x : K, ⋃ _hx : x ∈ (A i : Set K),
    Metric.ball x (radius i)

def compactSupportCoverEvent
    {ι K : Type*} [PseudoMetricSpace K]
    (radius : ι → ℝ) : Set (ι → CompactResidual K) :=
  {A | compactSupportsCovered radius A = Set.univ}

theorem isOpen_setOf_mem_compactSupportsCovered
    {ι K : Type*} [PseudoMetricSpace K] (radius : ι → ℝ) :
    IsOpen {p : (ι → CompactResidual K) × K |
      p.2 ∈ compactSupportsCovered radius p.1} := by
  have heq :
      {p : (ι → CompactResidual K) × K |
        p.2 ∈ compactSupportsCovered radius p.1} =
      ⋃ i : ι, (fun p : (ι → CompactResidual K) × K =>
        (p.1 i, p.2)) ⁻¹' compactSupportPointCovered (radius i) := by
    ext p
    simp only [compactSupportsCovered, compactSupportPointCovered,
      Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨i, x, hx, hball⟩
      exact ⟨i, x, hx, hball⟩
    · rintro ⟨i, x, hx, hball⟩
      exact ⟨i, x, hx, hball⟩
  rw [heq]
  apply isOpen_iUnion
  intro i
  exact (isOpen_compactSupportPointCovered (radius i)).preimage
    (((continuous_apply i).comp continuous_fst).prodMk continuous_snd)

theorem isOpen_compactSupportCoverEvent
    {ι K : Type*} [PseudoMetricSpace K] [CompactSpace K]
    (radius : ι → ℝ) :
    IsOpen (compactSupportCoverEvent (K := K) radius) := by
  let V : Set ((ι → CompactResidual K) × K) :=
    {p | p.2 ∈ compactSupportsCovered radius p.1}
  have hV : IsOpen V :=
    isOpen_setOf_mem_compactSupportsCovered radius
  have hcompl :
      (compactSupportCoverEvent (K := K) radius)ᶜ = Prod.fst '' Vᶜ := by
    ext A
    constructor
    · intro hA
      have hne : compactSupportsCovered radius A ≠ Set.univ := by
        simpa only [compactSupportCoverEvent, Set.mem_compl_iff,
          Set.mem_setOf_eq] using hA
      obtain ⟨z, hz⟩ :=
        (Set.ne_univ_iff_exists_notMem
          (compactSupportsCovered radius A)).1 hne
      exact ⟨(A, z), by simpa only [V, Set.mem_compl_iff,
        Set.mem_setOf_eq], rfl⟩
    · rintro ⟨⟨B, z⟩, hz, hBA⟩
      dsimp only at hBA
      subst B
      simp only [compactSupportCoverEvent, Set.mem_compl_iff,
        Set.mem_setOf_eq]
      intro hEq
      have hzmem : z ∈ compactSupportsCovered radius A := by
        rw [hEq]
        exact Set.mem_univ z
      have hznmem : z ∉ compactSupportsCovered radius A := by
        simpa only [V, Set.mem_compl_iff,
          Set.mem_setOf_eq] using hz
      exact hznmem hzmem
  have hclosed :
      IsClosed ((compactSupportCoverEvent (K := K) radius)ᶜ) := by
    rw [hcompl]
    exact isClosedMap_fst_of_compactSpace Vᶜ hV.isClosed_compl
  simpa only [compl_compl] using hclosed.isOpen_compl

theorem measurableSet_compactSupportCoverEvent
    {ι K : Type*} [Fintype ι] [MetricSpace K]
    [CompactSpace K] [SecondCountableTopology K]
    (radius : ι → ℝ) :
    MeasurableSet (compactSupportCoverEvent (K := K) radius) :=
  (isOpen_compactSupportCoverEvent radius).measurableSet

abbrev PacketPrefixFullMarkIndex
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (K : ℕ) :=
  (k : Fin (K + 1)) × PacketMark P k

abbrev SpatialFullMarkSupportSample
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :=
  (k : ℕ) → (n : PacketMark P k) →
    CompactResidual (FlatTorus d)

def spatialFullMarkSupportRestriction
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (K : ℕ) (S : SpatialFullMarkSupportSample P) :
    PacketPrefixFullMarkIndex P K → CompactResidual (FlatTorus d) :=
  fun q => S q.1 q.2

theorem measurable_spatialFullMarkSupportRestriction
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (K : ℕ) :
    Measurable (spatialFullMarkSupportRestriction P K) := by
  apply measurable_pi_lambda
  intro q
  change Measurable fun S : SpatialFullMarkSupportSample P =>
    S (q.1 : ℕ) q.2
  fun_prop

def spatialFullMarkSupportCoverThroughPacketEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (K : ℕ) : Set (SpatialFullMarkSupportSample P) :=
  spatialFullMarkSupportRestriction P K ⁻¹'
    compactSupportCoverEvent
      (fun q : PacketPrefixFullMarkIndex P K => r q.2)

theorem measurableSet_spatialFullMarkSupportCoverThroughPacketEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (K : ℕ) :
    MeasurableSet (spatialFullMarkSupportCoverThroughPacketEvent P K) := by
  letI : CompactSpace (FlatTorus d) :=
    flatTorusCompactSpaceOfInterface P
  exact (measurableSet_compactSupportCoverEvent
    (fun q : PacketPrefixFullMarkIndex P K => r q.2)).preimage
      (measurable_spatialFullMarkSupportRestriction P K)

theorem compactSupportsCovered_spatialFullMarkSupport
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (k : ℕ) (ω : SpatialPath P) :
    compactSupportsCovered (fun n : PacketMark P k => r n)
        (fun n => spatialFullMarkSupport P k ω n) =
      spatialPacketCovered P k ω := by
  ext z
  simp only [compactSupportsCovered, spatialFullMarkSupport,
    coe_packetFullMarkSupport, spatialPacketCovered, finiteCloudCovered,
    cloudPoints, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, x, ⟨p, j, hj, hjx⟩, hz⟩
    subst x
    exact ⟨p, n, ⟨j, hj⟩, hz⟩
  · rintro ⟨p, n, j, hz⟩
    exact ⟨n, (spatialPacketCloud P k ω p n).2 j,
      ⟨p, j, j.isLt, rfl⟩, hz⟩

theorem compactSupportsCovered_spatialRestriction_eq
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (K : ℕ) (ω : SpatialPath P) :
    compactSupportsCovered
        (fun q : PacketPrefixFullMarkIndex P K => r q.2)
        (spatialFullMarkSupportRestriction P K
          (fun k n => spatialFullMarkSupport P k ω n)) =
      spatialFullCoveredThroughPacket P K ω := by
  calc
    compactSupportsCovered
        (fun q : PacketPrefixFullMarkIndex P K => r q.2)
        (spatialFullMarkSupportRestriction P K
          (fun k n => spatialFullMarkSupport P k ω n)) =
        ⋃ k : Fin (K + 1),
          compactSupportsCovered (fun n : PacketMark P k => r n)
            (fun n => spatialFullMarkSupport P k ω n) := by
      simp only [compactSupportsCovered,
        spatialFullMarkSupportRestriction, Set.iUnion_sigma]
    _ = ⋃ k : Fin (K + 1), spatialPacketCovered P k ω := by
      congr 1
      funext k
      exact compactSupportsCovered_spatialFullMarkSupport P k ω
    _ = spatialFullCoveredThroughPacket P K ω := rfl

theorem spatialSupports_mem_coverThroughPacket_iff
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (K : ℕ) (ω : SpatialPath P) :
    (fun k n => spatialFullMarkSupport P k ω n) ∈
        spatialFullMarkSupportCoverThroughPacketEvent P K ↔
      spatialFullCoveredThroughPacket P K ω = Set.univ := by
  change compactSupportsCovered
      (fun q : PacketPrefixFullMarkIndex P K => r q.2)
      (spatialFullMarkSupportRestriction P K
        (fun k n => spatialFullMarkSupport P k ω n)) = Set.univ ↔ _
  rw [compactSupportsCovered_spatialRestriction_eq]

def spatialFullMarkSupportFiniteCoverEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    Set (SpatialFullMarkSupportSample P) :=
  ⋃ K : ℕ, spatialFullMarkSupportCoverThroughPacketEvent P K

theorem measurableSet_spatialFullMarkSupportFiniteCoverEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    MeasurableSet (spatialFullMarkSupportFiniteCoverEvent P) :=
  MeasurableSet.iUnion fun K =>
    measurableSet_spatialFullMarkSupportCoverThroughPacketEvent P K

theorem spatialAllFullMarkSupports_preimage_finiteCoverEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    (fun ω : SpatialPath P =>
      fun k n => spatialFullMarkSupport P k ω n) ⁻¹'
        spatialFullMarkSupportFiniteCoverEvent P =
      spatialFiniteFullPacketCoverEvent P := by
  ext ω
  simp only [Set.mem_preimage, spatialFullMarkSupportFiniteCoverEvent,
    Set.mem_iUnion, spatialFiniteFullPacketCoverEvent, Set.mem_setOf_eq]
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K, (spatialSupports_mem_coverThroughPacket_iff P K ω).1 hK⟩
  · rintro ⟨K, hK⟩
    exact ⟨K, (spatialSupports_mem_coverThroughPacket_iff P K ω).2 hK⟩

theorem spatialFullMarkSupportMeasure_finiteCoverEvent_measure_one
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) :
    spatialFullMarkSupportMeasure P
        (spatialFullMarkSupportFiniteCoverEvent P) = 1 := by
  have hmeasure := (spatialAllFullMarkSupports_hasLaw P).measure_eq
    (p := fun S => S ∈ spatialFullMarkSupportFiniteCoverEvent P)
    (measurableSet_spatialFullMarkSupportFiniteCoverEvent P)
  have hpre :
      {ω : SpatialPath P |
        (fun k n => spatialFullMarkSupport P k ω n) ∈
          spatialFullMarkSupportFiniteCoverEvent P} =
        (fun ω : SpatialPath P =>
          fun k n => spatialFullMarkSupport P k ω n) ⁻¹'
            spatialFullMarkSupportFiniteCoverEvent P := rfl
  rw [hpre] at hmeasure
  calc
    spatialFullMarkSupportMeasure P
        (spatialFullMarkSupportFiniteCoverEvent P) =
        spatialPathMeasure P
          ((fun ω : SpatialPath P =>
            fun k n => spatialFullMarkSupport P k ω n) ⁻¹'
              spatialFullMarkSupportFiniteCoverEvent P) := by
      simpa only [Set.setOf_mem_eq] using hmeasure.symm
    _ = spatialPathMeasure P (spatialFiniteFullPacketCoverEvent P) := by
      rw [spatialAllFullMarkSupports_preimage_finiteCoverEvent]
    _ = 1 := spatialFiniteFullPacketCoverEvent_measure_one hd P

end Shepp.Section5
end SheppFlattenedModule064

section SheppFlattenedModule065
open scoped ENNReal NNReal ProbabilityTheory Topology
open MeasureTheory Set

namespace Shepp.Section5

open ProbabilityTheory
open Shepp.Section2 Shepp.Section3 Shepp.Section4 TopologicalSpace
open Filter

theorem exists_le_packetCutoff
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (n : ℕ) : ∃ k, n ≤ P.cutoff k := by
  exact ((tendsto_atTop.1 P.cutoff_tendsto) n).exists

noncomputable def packetIndexOf
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (n : ℕ) : ℕ :=
  Nat.find (exists_le_packetCutoff P n)

theorem le_cutoff_packetIndexOf
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (n : ℕ) : n ≤ P.cutoff (packetIndexOf P n) := by
  exact Nat.find_spec (exists_le_packetCutoff P n)

theorem mem_packetIndices_packetIndexOf
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (n : ℕ) : n ∈ packetIndices P (packetIndexOf P n) := by
  have hupper := le_cutoff_packetIndexOf P n
  cases hidx : packetIndexOf P n with
  | zero =>
      simpa [packetIndices, hidx] using hupper
  | succ k =>
      rw [hidx] at hupper
      have hnot : ¬n ≤ P.cutoff k := by
        have hfind : Nat.find (exists_le_packetCutoff P n) = k + 1 := by
          simpa only [packetIndexOf] using hidx
        have hmin := Nat.find_min (exists_le_packetCutoff P n)
          (show k < Nat.find (exists_le_packetCutoff P n) by
            omega)
        exact hmin
      simpa [packetIndices, hidx] using
        (show P.cutoff k < n ∧ n ≤ P.cutoff (k + 1) by omega)

theorem packetIndices_unique
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    {k l n : ℕ} (hk : n ∈ packetIndices P k)
    (hl : n ∈ packetIndices P l) : k = l := by
  wlog hkl : k ≤ l generalizing k l
  · exact (this hl hk (Nat.le_of_not_ge hkl)).symm
  rcases hkl.eq_or_lt with hEq | hlt
  · exact hEq
  · cases l with
    | zero => omega
    | succ j =>
        have hnle : n ≤ P.cutoff k :=
          mem_packetIndices_le_cutoff P hk
        have hnlow : P.cutoff j < n := by
          exact (Finset.mem_Ioc.mp (by simpa [packetIndices] using hl)).1
        have hkj : k ≤ j := by omega
        have hcut : P.cutoff k ≤ P.cutoff j :=
          P.cutoff_monotone hkj
        omega

theorem packetIndexOf_eq_of_mem
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    {k n : ℕ} (hn : n ∈ packetIndices P k) :
    packetIndexOf P n = k :=
  packetIndices_unique P (mem_packetIndices_packetIndexOf P n) hn

noncomputable def packetMarkEquivIndexFiber
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ∀ k : ℕ, PacketMark P k ≃ {n : ℕ // packetIndexOf P n = k} :=
  fun k =>
    { toFun := fun n => ⟨n, packetIndexOf_eq_of_mem P n.property⟩
      invFun := fun n => ⟨n, by
        have hmem := mem_packetIndices_packetIndexOf P (n : ℕ)
        rw [n.property] at hmem
        exact hmem⟩
      left_inv := fun n => by apply Subtype.ext; rfl
      right_inv := fun n => by apply Subtype.ext; rfl }

noncomputable def allPacketMarksEquivNat
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    ((k : ℕ) × PacketMark P k) ≃ ℕ :=
  (Equiv.sigmaCongrRight (packetMarkEquivIndexFiber P)).trans
    (Equiv.sigmaFiberEquiv (packetIndexOf P))

abbrev FullPoissonSupportSample (d : ℕ) :=
  ℕ → CompactResidual (FlatTorus d)

noncomputable def packetSupportsToNat
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    SpatialFullMarkSupportSample P → FullPoissonSupportSample d :=
  (MeasurableEquiv.piCongrLeft
    (fun _n : ℕ => CompactResidual (FlatTorus d))
    (allPacketMarksEquivNat P)) ∘
  (MeasurableEquiv.piCurry
    (fun k : ℕ => fun _n : PacketMark P k =>
      CompactResidual (FlatTorus d))).symm

theorem measurable_packetSupportsToNat
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    Measurable (packetSupportsToNat P) :=
  (MeasurableEquiv.piCongrLeft
    (fun _n : ℕ => CompactResidual (FlatTorus d))
    (allPacketMarksEquivNat P)).measurable.comp
  (MeasurableEquiv.piCurry
    (fun k : ℕ => fun _n : PacketMark P k =>
      CompactResidual (FlatTorus d))).symm.measurable

noncomputable def fullPoissonSupportMeasure
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    Measure (FullPoissonSupportSample d) := by
  letI : CompactSpace (FlatTorus d) :=
    flatTorusCompactSpaceOfInterface P
  exact Measure.infinitePi fun _n : ℕ =>
    poissonSupportMeasure (flatTorusVolume d) 1

theorem packetSupportsToNat_hasLaw
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    HasLaw (packetSupportsToNat P)
      (fullPoissonSupportMeasure P)
      (spatialFullMarkSupportMeasure P) := by
  letI : CompactSpace (FlatTorus d) :=
    flatTorusCompactSpaceOfInterface P
  let X : (k : ℕ) → PacketMark P k → Type :=
    fun _k _n => CompactResidual (FlatTorus d)
  let uncurry : SpatialFullMarkSupportSample P →
      ((q : (k : ℕ) × PacketMark P k) → X q.1 q.2) :=
    (MeasurableEquiv.piCurry X).symm
  let reindex :
      ((q : (k : ℕ) × PacketMark P k) → X q.1 q.2) →
        FullPoissonSupportSample d :=
    MeasurableEquiv.piCongrLeft
      (fun _n : ℕ => CompactResidual (FlatTorus d))
      (allPacketMarksEquivNat P)
  have huncurry : Measurable uncurry :=
    (MeasurableEquiv.piCurry X).symm.measurable
  have hreindex : Measurable reindex :=
    (MeasurableEquiv.piCongrLeft
      (fun _n : ℕ => CompactResidual (FlatTorus d))
      (allPacketMarksEquivNat P)).measurable
  refine ⟨(measurable_packetSupportsToNat P).aemeasurable, ?_⟩
  unfold fullPoissonSupportMeasure spatialFullMarkSupportMeasure
  change Measure.map (reindex ∘ uncurry)
      (Measure.infinitePi fun k : ℕ =>
        Measure.pi fun _n : PacketMark P k =>
          poissonSupportMeasure (flatTorusVolume d) 1) = _
  rw [← Measure.map_map hreindex huncurry]
  have hinner :
      (fun k : ℕ =>
        Measure.pi fun _n : PacketMark P k =>
          poissonSupportMeasure (flatTorusVolume d) 1) =
      (fun k : ℕ =>
        Measure.infinitePi fun _n : PacketMark P k =>
          poissonSupportMeasure (flatTorusVolume d) 1) := by
    funext k
    exact (Measure.infinitePi_eq_pi
      (μ := fun _n : PacketMark P k =>
        poissonSupportMeasure (flatTorusVolume d) 1)).symm
  rw [hinner]
  change Measure.map reindex
      (Measure.map (MeasurableEquiv.piCurry X).symm
        (Measure.infinitePi fun k : ℕ =>
          Measure.infinitePi fun _n : PacketMark P k =>
            poissonSupportMeasure (flatTorusVolume d) 1)) = _
  rw [Measure.infinitePi_map_piCurry_symm]
  change Measure.map
      (MeasurableEquiv.piCongrLeft
        (fun _n : ℕ => CompactResidual (FlatTorus d))
        (allPacketMarksEquivNat P))
      (Measure.infinitePi fun _q : (k : ℕ) × PacketMark P k =>
        poissonSupportMeasure (flatTorusVolume d) 1) = _
  exact Measure.infinitePi_map_piCongrLeft
    (fun _n : ℕ => poissonSupportMeasure (flatTorusVolume d) 1)
    (allPacketMarksEquivNat P)

theorem packetSupportsToNat_apply_packetMark
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (S : SpatialFullMarkSupportSample P) (k : ℕ)
    (n : PacketMark P k) :
    packetSupportsToNat P S n = S k n := by
  let e := allPacketMarksEquivNat P
  have he : e ⟨k, n⟩ = (n : ℕ) := rfl
  have hsymm : e.symm (n : ℕ) = ⟨k, n⟩ := by
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using he.symm
  unfold packetSupportsToNat
  change S (e.symm (n : ℕ)).1 (e.symm (n : ℕ)).2 = S k n
  rw [hsymm]

noncomputable def spatialFullMarkSupportByNat
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (ω : SpatialPath P) : FullPoissonSupportSample d :=
  packetSupportsToNat P
    (fun k n => spatialFullMarkSupport P k ω n)

theorem spatialFullMarkSupportByNat_hasLaw
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    HasLaw (spatialFullMarkSupportByNat P)
      (fullPoissonSupportMeasure P) (spatialPathMeasure P) :=
  (packetSupportsToNat_hasLaw P).fun_comp
    (spatialAllFullMarkSupports_hasLaw P)

noncomputable def fullPoissonSupportsCoveredThrough
    {d : ℕ} (r : ℕ → ℝ) (N : ℕ)
    (S : FullPoissonSupportSample d) : Set (FlatTorus d) :=
  compactSupportsCovered (fun n : Fin (N + 1) => r n)
    (fun n => S n)

def fullPoissonSupportCoverThroughEvent
    {d : ℕ} (r : ℕ → ℝ) (N : ℕ) :
    Set (FullPoissonSupportSample d) :=
  {S | fullPoissonSupportsCoveredThrough r N S = Set.univ}

theorem measurableSet_fullPoissonSupportCoverThroughEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (N : ℕ) :
    MeasurableSet (fullPoissonSupportCoverThroughEvent (d := d) r N) := by
  letI : CompactSpace (FlatTorus d) :=
    flatTorusCompactSpaceOfInterface P
  let restrict : FullPoissonSupportSample d →
      (Fin (N + 1) → CompactResidual (FlatTorus d)) :=
    fun S n => S n
  have hrestrict : Measurable restrict := by
    apply measurable_pi_lambda
    intro n
    exact measurable_pi_apply (n : ℕ)
  change MeasurableSet
    (restrict ⁻¹' compactSupportCoverEvent
      (fun n : Fin (N + 1) => r n))
  exact (measurableSet_compactSupportCoverEvent
    (fun n : Fin (N + 1) => r n)).preimage hrestrict

def fullPoissonSupportFiniteCoverEvent
    {d : ℕ} (r : ℕ → ℝ) : Set (FullPoissonSupportSample d) :=
  ⋃ N : ℕ, fullPoissonSupportCoverThroughEvent (d := d) r N

theorem measurableSet_fullPoissonSupportFiniteCoverEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    MeasurableSet (fullPoissonSupportFiniteCoverEvent (d := d) r) :=
  MeasurableSet.iUnion fun N =>
    measurableSet_fullPoissonSupportCoverThroughEvent P N

theorem packetPrefixCovered_subset_fullPoissonCutoffCovered
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (K : ℕ) (S : SpatialFullMarkSupportSample P) :
    compactSupportsCovered
        (fun q : PacketPrefixFullMarkIndex P K => r q.2)
        (spatialFullMarkSupportRestriction P K S) ⊆
      fullPoissonSupportsCoveredThrough r (P.cutoff K)
        (packetSupportsToNat P S) := by
  intro z hz
  simp only [compactSupportsCovered,
    spatialFullMarkSupportRestriction, Set.mem_iUnion] at hz
  obtain ⟨q, x, hx, hball⟩ := hz
  have hnpacket : (q.2 : ℕ) ≤ P.cutoff (q.1 : ℕ) :=
    mem_packetIndices_le_cutoff P q.2.property
  have hk : (q.1 : ℕ) ≤ K := Nat.le_of_lt_succ q.1.isLt
  have hncut : (q.2 : ℕ) ≤ P.cutoff K :=
    hnpacket.trans (P.cutoff_monotone hk)
  let nPrefix : Fin (P.cutoff K + 1) :=
    ⟨q.2, Nat.lt_succ_of_le hncut⟩
  simp only [fullPoissonSupportsCoveredThrough,
    compactSupportsCovered, Set.mem_iUnion]
  refine ⟨nPrefix, x, ?_, ?_⟩
  · rw [packetSupportsToNat_apply_packetMark P S (q.1 : ℕ) q.2]
    exact hx
  · simpa only [nPrefix] using hball

theorem packetFiniteCoverEvent_subset_natFiniteCover_preimage
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    spatialFullMarkSupportFiniteCoverEvent P ⊆
      packetSupportsToNat P ⁻¹'
        fullPoissonSupportFiniteCoverEvent (d := d) r := by
  intro S hS
  obtain ⟨K, hK⟩ := Set.mem_iUnion.1 hS
  apply Set.mem_preimage.2
  apply Set.mem_iUnion.2
  refine ⟨P.cutoff K, ?_⟩
  change fullPoissonSupportsCoveredThrough r (P.cutoff K)
      (packetSupportsToNat P S) = Set.univ
  apply Set.eq_univ_of_univ_subset
  intro z _hz
  apply packetPrefixCovered_subset_fullPoissonCutoffCovered P K S
  change compactSupportsCovered
      (fun q : PacketPrefixFullMarkIndex P K => r q.2)
      (spatialFullMarkSupportRestriction P K S) = Set.univ at hK
  rw [hK]
  exact Set.mem_univ z

theorem fullPoissonSupportMeasure_finiteCoverEvent_measure_one
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) :
    fullPoissonSupportMeasure P
        (fullPoissonSupportFiniteCoverEvent (d := d) r) = 1 := by
  letI : CompactSpace (FlatTorus d) :=
    flatTorusCompactSpaceOfInterface P
  letI : IsProbabilityMeasure (spatialFullMarkSupportMeasure P) :=
    (spatialAllFullMarkSupports_hasLaw P).isProbabilityMeasure_iff.mp
      inferInstance
  let E := fullPoissonSupportFiniteCoverEvent (d := d) r
  have hmono :
      spatialFullMarkSupportMeasure P
          (spatialFullMarkSupportFiniteCoverEvent P) ≤
        spatialFullMarkSupportMeasure P (packetSupportsToNat P ⁻¹' E) :=
    measure_mono
      (packetFiniteCoverEvent_subset_natFiniteCover_preimage P)
  have hpre :
      spatialFullMarkSupportMeasure P (packetSupportsToNat P ⁻¹' E) = 1 := by
    apply le_antisymm
    · calc
        spatialFullMarkSupportMeasure P (packetSupportsToNat P ⁻¹' E) ≤
            spatialFullMarkSupportMeasure P Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    · rw [spatialFullMarkSupportMeasure_finiteCoverEvent_measure_one hd P]
        at hmono
      exact hmono
  have hmeasure := (packetSupportsToNat_hasLaw P).measure_eq
    (p := fun S => S ∈ E)
    (measurableSet_fullPoissonSupportFiniteCoverEvent P)
  have hpreSet :
      {S : SpatialFullMarkSupportSample P | packetSupportsToNat P S ∈ E} =
        packetSupportsToNat P ⁻¹' E := rfl
  rw [hpreSet] at hmeasure
  calc
    fullPoissonSupportMeasure P
        (fullPoissonSupportFiniteCoverEvent (d := d) r) =
        spatialFullMarkSupportMeasure P (packetSupportsToNat P ⁻¹' E) := by
      simpa only [E, Set.setOf_mem_eq] using hmeasure.symm
    _ = 1 := hpre

def tailRadius (r : ℕ → ℝ) (n₀ : ℕ) : ℕ → ℝ :=
  fun n => r (n₀ + n)

theorem tailRadius_pos {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (n₀ n : ℕ) : 0 < tailRadius r n₀ n :=
  hr (n₀ + n)

theorem tailRadius_lt_quarter {r : ℕ → ℝ}
    (hrsmall : ∀ n, r n < 1 / 4) (n₀ n : ℕ) :
    tailRadius r n₀ n < 1 / 4 :=
  hrsmall (n₀ + n)

theorem tailRadius_antitone {r : ℕ → ℝ} (hmono : Antitone r)
    (n₀ : ℕ) : Antitone (tailRadius r n₀) := by
  intro a b hab
  exact hmono (Nat.add_le_add_left hab n₀)

theorem tailRadius_tendsto_zero {r : ℕ → ℝ}
    (hrlim : Tendsto r atTop (nhds 0)) (n₀ : ℕ) :
    Tendsto (tailRadius r n₀) atTop (nhds 0) := by
  have heq : tailRadius r n₀ = r ∘ fun n => n + n₀ := by
    funext n
    simp only [tailRadius, Function.comp_apply, Nat.add_comm]
  rw [heq]
  exact hrlim.comp (tendsto_add_atTop_nat n₀)

theorem flatTorusOverlapTerm_le_one
    (d : ℕ) (r : ℕ → ℝ) (n : ℕ) (z : FlatTorus d) :
    flatTorusOverlapTerm d r n z ≤ 1 := by
  unfold flatTorusOverlapTerm
  exact measureReal_le_one

@[simp] theorem flatTorusOverlapTerm_tailRadius
    (d : ℕ) (r : ℕ → ℝ) (n₀ n : ℕ) (z : FlatTorus d) :
    flatTorusOverlapTerm d (tailRadius r n₀) n z =
      flatTorusOverlapTerm d r (n₀ + n) z := by
  rfl

theorem flatTorusOverlapEnergy_tail_decomposition
    (d : ℕ) (r : ℕ → ℝ) (n₀ : ℕ) (z : FlatTorus d) :
    (∑ n ∈ Finset.range n₀,
        ENNReal.ofReal (flatTorusOverlapTerm d r n z)) +
      flatTorusOverlapEnergy d (tailRadius r n₀) z =
        flatTorusOverlapEnergy d r z := by
  let f : ℕ → ℝ≥0∞ :=
    fun n => ENNReal.ofReal (flatTorusOverlapTerm d r n z)
  let g : ℕ → ℝ≥0∞ :=
    fun n => ENNReal.ofReal
      (flatTorusOverlapTerm d (tailRadius r n₀) n z)
  change (∑ n ∈ Finset.range n₀, f n) + (∑' n, g n) = ∑' n, f n
  have hg : g = fun n => f (n + n₀) := by
    funext n
    dsimp only [g, f]
    rw [flatTorusOverlapTerm_tailRadius]
    rw [Nat.add_comm n₀ n]
  rw [hg]
  have htail : Summable (fun n => f (n + n₀)) := ENNReal.summable
  exact htail.sum_add_tsum_nat_add'

theorem flatTorusOverlapEnergy_le_nat_add_tail
    (d : ℕ) (r : ℕ → ℝ) (n₀ : ℕ) (z : FlatTorus d) :
    flatTorusOverlapEnergy d r z ≤
      (n₀ : ℝ≥0∞) + flatTorusOverlapEnergy d (tailRadius r n₀) z := by
  rw [← flatTorusOverlapEnergy_tail_decomposition d r n₀ z]
  gcongr
  calc
    (∑ n ∈ Finset.range n₀,
        ENNReal.ofReal (flatTorusOverlapTerm d r n z)) ≤
        ∑ _n ∈ Finset.range n₀, (1 : ℝ≥0∞) := by
      gcongr with n hn
      exact ENNReal.ofReal_le_one.2
        (flatTorusOverlapTerm_le_one d r n z)
    _ = n₀ := by simp

theorem flatTorusOverlapEnergyExp_le_exp_nat_mul_tail
    (d : ℕ) (r : ℕ → ℝ) (n₀ : ℕ) (z : FlatTorus d) :
    flatTorusOverlapEnergyExp d r z ≤
      EReal.exp (n₀ : EReal) *
        flatTorusOverlapEnergyExp d (tailRadius r n₀) z := by
  rw [flatTorusOverlapEnergyExp, flatTorusOverlapEnergyExp,
    ← EReal.exp_add]
  apply EReal.exp_monotone
  have hcoe :
      (flatTorusOverlapEnergy d r z : EReal) ≤
        (((n₀ : ℝ≥0∞) +
          flatTorusOverlapEnergy d (tailRadius r n₀) z : ℝ≥0∞) : EReal) :=
    EReal.coe_ennreal_le_coe_ennreal_iff.2
      (flatTorusOverlapEnergy_le_nat_add_tail d r n₀ z)
  rw [EReal.coe_ennreal_add] at hcoe
  have hnat : (((n₀ : ℝ≥0∞) : EReal)) = (n₀ : EReal) := by
    rw [← ENNReal.coe_natCast n₀, EReal.coe_nnreal_eq_coe_real]
    rfl
  rwa [hnat] at hcoe

theorem lintegral_flatTorusOverlapEnergyExp_tail_eq_top
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (htop :
      (∫⁻ z : FlatTorus d,
        flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) = ∞)
    (n₀ : ℕ) :
    (∫⁻ z : FlatTorus d,
      flatTorusOverlapEnergyExp d (tailRadius r n₀) z
        ∂(flatTorusVolume d)) = ∞ := by
  let c : ℝ≥0∞ := EReal.exp (n₀ : EReal)
  have hmono :
      (∫⁻ z : FlatTorus d,
        flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) ≤
      ∫⁻ z : FlatTorus d,
        c * flatTorusOverlapEnergyExp d (tailRadius r n₀) z
          ∂(flatTorusVolume d) := by
    apply lintegral_mono
    intro z
    exact flatTorusOverlapEnergyExp_le_exp_nat_mul_tail d r n₀ z
  rw [htop] at hmono
  have hprodInt :
      (∫⁻ z : FlatTorus d,
        c * flatTorusOverlapEnergyExp d (tailRadius r n₀) z
          ∂(flatTorusVolume d)) = ∞ :=
    top_unique hmono
  have hmeas :
      Measurable (flatTorusOverlapEnergyExp d (tailRadius r n₀)) :=
    measurable_flatTorusOverlapEnergyExp d hd
      (tailRadius_pos hr n₀) (tailRadius_lt_quarter hrsmall n₀)
  rw [lintegral_const_mul c hmeas] at hprodInt
  have hc : c ≠ ∞ := by
    intro h
    exact EReal.natCast_ne_top n₀ (EReal.exp_eq_top_iff.mp h)
  rcases ENNReal.mul_eq_top.mp hprodInt with htail | hconst
  · exact htail.2
  · exact (hc hconst.1).elim

theorem lintegral_flatTorusOverlapSumExp_tail_eq_top
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (nhds 0))
    (htop :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞)
    (n₀ : ℕ) :
    (∫⁻ z : FlatTorus d,
      ENNReal.ofReal (Real.exp
        (flatTorusOverlapSum d (tailRadius r n₀) z))
        ∂(flatTorusVolume d)) = ∞ := by
  have hbase :
      (∫⁻ z : FlatTorus d,
        flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) = ∞ := by
    rw [lintegral_flatTorusOverlapEnergyExp_eq_real d hd hr hrsmall hrlim]
    exact htop
  have htail := lintegral_flatTorusOverlapEnergyExp_tail_eq_top
    d hd hr hrsmall hbase n₀
  rw [lintegral_flatTorusOverlapEnergyExp_eq_real d hd
    (tailRadius_pos hr n₀) (tailRadius_lt_quarter hrsmall n₀)
    (tailRadius_tendsto_zero hrlim n₀)] at htail
  exact htail

theorem exists_geometricPacketInterface_tail_of_torus_overlap
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (htorus :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞)
    (n₀ : ℕ) :
    Nonempty (GeometricPacketInterface d (tailRadius r n₀)) := by
  apply exists_geometricPacketInterface_of_torus_overlap
    d hd (tailRadius_pos hr n₀) (tailRadius_lt_quarter hrsmall n₀)
      (tailRadius_antitone hmono n₀) (tailRadius_tendsto_zero hrlim n₀)
      (t₀ := 1) (by norm_num)
  exact lintegral_flatTorusOverlapSumExp_tail_eq_top
    d hd hr hrsmall hrlim htorus n₀

def fullPoissonSupportShift
    {d : ℕ} (n₀ : ℕ) (S : FullPoissonSupportSample d) :
    FullPoissonSupportSample d :=
  fun n => S (n₀ + n)

theorem measurable_fullPoissonSupportShift
    {d : ℕ} (n₀ : ℕ) :
    Measurable (fullPoissonSupportShift (d := d) n₀) := by
  apply measurable_pi_lambda
  intro n
  exact measurable_pi_apply (n₀ + n)

theorem fullPoissonSupportShift_hasLaw
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (n₀ : ℕ) :
    HasLaw (fullPoissonSupportShift (d := d) n₀)
      (fullPoissonSupportMeasure P) (fullPoissonSupportMeasure P) := by
  letI : CompactSpace (FlatTorus d) :=
    flatTorusCompactSpaceOfInterface P
  refine ⟨(measurable_fullPoissonSupportShift (d := d) n₀).aemeasurable, ?_⟩
  unfold fullPoissonSupportMeasure
  have hinj : Function.Injective (fun n : ℕ => n₀ + n) := by
    intro a b hab
    exact Nat.add_left_cancel hab
  exact Measure.map_infinitePi_infinitePi_of_inj hinj

theorem fullPoissonSupportMeasure_eq
    {d : ℕ} {r s : ℕ → ℝ}
    (P : GeometricPacketInterface d r)
    (Q : GeometricPacketInterface d s) :
    fullPoissonSupportMeasure P = fullPoissonSupportMeasure Q := by
  unfold fullPoissonSupportMeasure
  congr 1

noncomputable instance fullPoissonSupportMeasure_isProbabilityMeasure
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) :
    IsProbabilityMeasure (fullPoissonSupportMeasure P) := by
  letI : CompactSpace (FlatTorus d) :=
    flatTorusCompactSpaceOfInterface P
  unfold fullPoissonSupportMeasure
  infer_instance

def fullPoissonSupportTailFiniteCoverEvent
    {d : ℕ} (r : ℕ → ℝ) (n₀ : ℕ) :
    Set (FullPoissonSupportSample d) :=
  fullPoissonSupportShift (d := d) n₀ ⁻¹'
    fullPoissonSupportFiniteCoverEvent (d := d) (tailRadius r n₀)

theorem measurableSet_fullPoissonSupportTailFiniteCoverEvent
    {d : ℕ} {r : ℕ → ℝ} {n₀ : ℕ}
    (Q : GeometricPacketInterface d (tailRadius r n₀)) :
    MeasurableSet (fullPoissonSupportTailFiniteCoverEvent (d := d) r n₀) := by
  exact (measurableSet_fullPoissonSupportFiniteCoverEvent Q).preimage
    (measurable_fullPoissonSupportShift (d := d) n₀)

theorem fullPoissonSupportMeasure_tailFiniteCoverEvent_measure_one
    {d : ℕ} (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (htorus :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞)
    (P : GeometricPacketInterface d r) (n₀ : ℕ) :
    fullPoissonSupportMeasure P
      (fullPoissonSupportTailFiniteCoverEvent (d := d) r n₀) = 1 := by
  obtain ⟨Q⟩ := exists_geometricPacketInterface_tail_of_torus_overlap
    d hd hr hrsmall hmono hrlim htorus n₀
  let E := fullPoissonSupportFiniteCoverEvent (d := d) (tailRadius r n₀)
  have hE : MeasurableSet E :=
    measurableSet_fullPoissonSupportFiniteCoverEvent Q
  have hone : fullPoissonSupportMeasure P E = 1 := by
    rw [fullPoissonSupportMeasure_eq P Q]
    exact fullPoissonSupportMeasure_finiteCoverEvent_measure_one
      (by omega) Q
  have hlaw := (fullPoissonSupportShift_hasLaw P n₀).measure_eq
    (p := fun S => S ∈ E) hE
  have hpreSet :
      {S : FullPoissonSupportSample d |
        fullPoissonSupportShift n₀ S ∈ E} =
        fullPoissonSupportShift n₀ ⁻¹' E := rfl
  rw [hpreSet] at hlaw
  have hESet : {S : FullPoissonSupportSample d | S ∈ E} = E :=
    Set.setOf_mem_eq
  rw [hESet] at hlaw
  calc
    fullPoissonSupportMeasure P
        (fullPoissonSupportTailFiniteCoverEvent (d := d) r n₀) =
        fullPoissonSupportMeasure P E := by
      simpa only [fullPoissonSupportTailFiniteCoverEvent, E] using hlaw
    _ = 1 := hone

def fullPoissonSupportAllTailsCoverEvent
    {d : ℕ} (r : ℕ → ℝ) : Set (FullPoissonSupportSample d) :=
  ⋂ n₀ : ℕ, fullPoissonSupportTailFiniteCoverEvent (d := d) r n₀

theorem measurableSet_fullPoissonSupportAllTailsCoverEvent
    {d : ℕ} (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (htorus :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞) :
    MeasurableSet (fullPoissonSupportAllTailsCoverEvent (d := d) r) := by
  apply MeasurableSet.iInter
  intro n₀
  obtain ⟨Q⟩ := exists_geometricPacketInterface_tail_of_torus_overlap
    d hd hr hrsmall hmono hrlim htorus n₀
  exact measurableSet_fullPoissonSupportTailFiniteCoverEvent Q

theorem fullPoissonSupportMeasure_allTailsCoverEvent_measure_one
    {d : ℕ} (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (htorus :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞)
    (P : GeometricPacketInterface d r) :
    fullPoissonSupportMeasure P
      (fullPoissonSupportAllTailsCoverEvent (d := d) r) = 1 := by
  let μ := fullPoissonSupportMeasure P
  have haeEach : ∀ n₀ : ℕ,
      ∀ᵐ S : FullPoissonSupportSample d ∂μ,
        S ∈ fullPoissonSupportTailFiniteCoverEvent (d := d) r n₀ := by
    intro n₀
    obtain ⟨Q⟩ := exists_geometricPacketInterface_tail_of_torus_overlap
      d hd hr hrsmall hmono hrlim htorus n₀
    have hmeas := measurableSet_fullPoissonSupportTailFiniteCoverEvent Q
    have hone := fullPoissonSupportMeasure_tailFiniteCoverEvent_measure_one
      hd hr hrsmall hmono hrlim htorus P n₀
    apply ae_iff.2
    change μ (fullPoissonSupportTailFiniteCoverEvent (d := d) r n₀)ᶜ = 0
    rw [measure_compl hmeas]
    · rw [show μ = fullPoissonSupportMeasure P by rfl, hone]
      simp
    · rw [show μ = fullPoissonSupportMeasure P by rfl, hone]
      simp
  have haeAll :
      ∀ᵐ S : FullPoissonSupportSample d ∂μ,
        ∀ n₀ : ℕ,
          S ∈ fullPoissonSupportTailFiniteCoverEvent (d := d) r n₀ :=
    ae_all_iff.2 haeEach
  have haeEvent :
      ∀ᵐ S : FullPoissonSupportSample d ∂μ,
        S ∈ fullPoissonSupportAllTailsCoverEvent (d := d) r := by
    filter_upwards [haeAll] with S hS
    exact Set.mem_iInter.2 hS
  have hcompl :
      μ (fullPoissonSupportAllTailsCoverEvent (d := d) r)ᶜ = 0 :=
    ae_iff.1 haeEvent
  have hfull := measure_of_measure_compl_eq_zero hcompl
  simpa only [μ, measure_univ] using hfull

noncomputable def fullPoissonSupportsCoveredBetween
    {d : ℕ} (r : ℕ → ℝ) (n₀ n₁ : ℕ)
    (S : FullPoissonSupportSample d) : Set (FlatTorus d) :=
  compactSupportsCovered
    (fun n : {m : ℕ // m ∈ Finset.Icc n₀ n₁} => r n)
    (fun n => S n)

theorem fullPoissonSupportsCoveredThrough_tailShift_eq_between
    {d : ℕ} (r : ℕ → ℝ) (n₀ N : ℕ)
    (S : FullPoissonSupportSample d) :
    fullPoissonSupportsCoveredThrough (tailRadius r n₀) N
        (fullPoissonSupportShift n₀ S) =
      fullPoissonSupportsCoveredBetween r n₀ (n₀ + N) S := by
  apply Set.Subset.antisymm
  · intro z hz
    simp only [fullPoissonSupportsCoveredThrough,
      fullPoissonSupportsCoveredBetween, compactSupportsCovered,
      Set.mem_iUnion] at hz ⊢
    obtain ⟨n, x, hx, hball⟩ := hz
    let m : {q : ℕ // q ∈ Finset.Icc n₀ (n₀ + N)} :=
      ⟨n₀ + n, by
        simp only [Finset.mem_Icc]
        constructor
        · omega
        · exact Nat.add_le_add_left (Nat.le_of_lt_succ n.isLt) n₀⟩
    refine ⟨m, x, ?_, ?_⟩
    · simpa only [m, fullPoissonSupportShift] using hx
    · simpa only [m, tailRadius] using hball
  · intro z hz
    simp only [fullPoissonSupportsCoveredThrough,
      fullPoissonSupportsCoveredBetween, compactSupportsCovered,
      Set.mem_iUnion] at hz ⊢
    obtain ⟨m, x, hx, hball⟩ := hz
    have hm : n₀ ≤ (m : ℕ) ∧ (m : ℕ) ≤ n₀ + N := by
      simpa only [Finset.mem_Icc] using m.property
    let n : Fin (N + 1) :=
      ⟨(m : ℕ) - n₀, by omega⟩
    refine ⟨n, x, ?_, ?_⟩
    · simpa only [n, fullPoissonSupportShift, Nat.add_sub_of_le hm.1] using hx
    · simpa only [n, tailRadius, Nat.add_sub_of_le hm.1] using hball

def fullPoissonSupportPaperTailCoverEvent
    {d : ℕ} (r : ℕ → ℝ) : Set (FullPoissonSupportSample d) :=
  {S | ∀ n₀ : ℕ, ∃ n₁ : ℕ, n₀ ≤ n₁ ∧
    fullPoissonSupportsCoveredBetween r n₀ n₁ S = Set.univ}

theorem allTailsCoverEvent_subset_paperTailCoverEvent
    {d : ℕ} (r : ℕ → ℝ) :
    fullPoissonSupportAllTailsCoverEvent (d := d) r ⊆
      fullPoissonSupportPaperTailCoverEvent (d := d) r := by
  intro S hS n₀
  have htail := Set.mem_iInter.1 hS n₀
  change fullPoissonSupportShift n₀ S ∈
    fullPoissonSupportFiniteCoverEvent (d := d) (tailRadius r n₀) at htail
  obtain ⟨N, hN⟩ := Set.mem_iUnion.1 htail
  refine ⟨n₀ + N, Nat.le_add_right n₀ N, ?_⟩
  change fullPoissonSupportsCoveredThrough (tailRadius r n₀) N
      (fullPoissonSupportShift n₀ S) = Set.univ at hN
  rw [fullPoissonSupportsCoveredThrough_tailShift_eq_between] at hN
  exact hN

theorem fullPoissonSupportMeasure_paperTailCoverEvent_measure_one
    {d : ℕ} (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (htorus :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞)
    (P : GeometricPacketInterface d r) :
    fullPoissonSupportMeasure P
      (fullPoissonSupportPaperTailCoverEvent (d := d) r) = 1 := by
  have hmonoMeasure :
      fullPoissonSupportMeasure P
          (fullPoissonSupportAllTailsCoverEvent (d := d) r) ≤
        fullPoissonSupportMeasure P
          (fullPoissonSupportPaperTailCoverEvent (d := d) r) :=
    measure_mono (allTailsCoverEvent_subset_paperTailCoverEvent (d := d) r)
  rw [fullPoissonSupportMeasure_allTailsCoverEvent_measure_one
    hd hr hrsmall hmono hrlim htorus P] at hmonoMeasure
  apply le_antisymm
  · calc
      fullPoissonSupportMeasure P
          (fullPoissonSupportPaperTailCoverEvent (d := d) r) ≤
          fullPoissonSupportMeasure P Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · exact hmonoMeasure

noncomputable def fullPoissonSupportsCoveredFrom
    {d : ℕ} (r : ℕ → ℝ) (n₀ : ℕ)
    (S : FullPoissonSupportSample d) : Set (FlatTorus d) :=
  compactSupportsCovered
    (fun n : {m : ℕ // n₀ ≤ m} => r n)
    (fun n => S n)

noncomputable def fullPoissonSupportLimsupSet
    {d : ℕ} (r : ℕ → ℝ)
    (S : FullPoissonSupportSample d) : Set (FlatTorus d) :=
  ⋂ n₀ : ℕ, fullPoissonSupportsCoveredFrom r n₀ S

def fullPoissonSupportLimsupCoverEvent
    {d : ℕ} (r : ℕ → ℝ) : Set (FullPoissonSupportSample d) :=
  {S | fullPoissonSupportLimsupSet r S = Set.univ}

theorem fullPoissonSupportsCoveredBetween_subset_coveredFrom
    {d : ℕ} (r : ℕ → ℝ) (n₀ n₁ : ℕ)
    (S : FullPoissonSupportSample d) :
    fullPoissonSupportsCoveredBetween r n₀ n₁ S ⊆
      fullPoissonSupportsCoveredFrom r n₀ S := by
  intro z hz
  simp only [fullPoissonSupportsCoveredBetween,
    fullPoissonSupportsCoveredFrom, compactSupportsCovered,
    Set.mem_iUnion] at hz ⊢
  obtain ⟨m, x, hx, hball⟩ := hz
  have hm : n₀ ≤ (m : ℕ) := (Finset.mem_Icc.mp m.property).1
  let n : {q : ℕ // n₀ ≤ q} := ⟨m, hm⟩
  refine ⟨n, x, ?_, ?_⟩
  · simpa only [n] using hx
  · simpa only [n] using hball

theorem allTailsCoverEvent_subset_limsupCoverEvent
    {d : ℕ} (r : ℕ → ℝ) :
    fullPoissonSupportAllTailsCoverEvent (d := d) r ⊆
      fullPoissonSupportLimsupCoverEvent (d := d) r := by
  intro S hS
  change fullPoissonSupportLimsupSet r S = Set.univ
  apply Set.eq_univ_of_univ_subset
  intro z _hz
  apply Set.mem_iInter.2
  intro n₀
  have htail := Set.mem_iInter.1 hS n₀
  change fullPoissonSupportShift n₀ S ∈
    fullPoissonSupportFiniteCoverEvent (d := d) (tailRadius r n₀) at htail
  obtain ⟨N, hN⟩ := Set.mem_iUnion.1 htail
  change fullPoissonSupportsCoveredThrough (tailRadius r n₀) N
      (fullPoissonSupportShift n₀ S) = Set.univ at hN
  rw [fullPoissonSupportsCoveredThrough_tailShift_eq_between] at hN
  apply fullPoissonSupportsCoveredBetween_subset_coveredFrom
    r n₀ (n₀ + N) S
  rw [hN]
  exact Set.mem_univ z

theorem fullPoissonSupportMeasure_limsupCoverEvent_measure_one
    {d : ℕ} (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (htorus :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞)
    (P : GeometricPacketInterface d r) :
    fullPoissonSupportMeasure P
      (fullPoissonSupportLimsupCoverEvent (d := d) r) = 1 := by
  have hmonoMeasure :
      fullPoissonSupportMeasure P
          (fullPoissonSupportAllTailsCoverEvent (d := d) r) ≤
        fullPoissonSupportMeasure P
          (fullPoissonSupportLimsupCoverEvent (d := d) r) :=
    measure_mono (allTailsCoverEvent_subset_limsupCoverEvent (d := d) r)
  rw [fullPoissonSupportMeasure_allTailsCoverEvent_measure_one
    hd hr hrsmall hmono hrlim htorus P] at hmonoMeasure
  apply le_antisymm
  · calc
      fullPoissonSupportMeasure P
          (fullPoissonSupportLimsupCoverEvent (d := d) r) ≤
          fullPoissonSupportMeasure P Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · exact hmonoMeasure

theorem poissonizedSufficiency
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (htorus :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞) :
    Nonempty (GeometricPacketInterface d r) ∧
      ∀ P : GeometricPacketInterface d r,
        fullPoissonSupportMeasure P
            (fullPoissonSupportPaperTailCoverEvent (d := d) r) = 1 ∧
          fullPoissonSupportMeasure P
            (fullPoissonSupportLimsupCoverEvent (d := d) r) = 1 := by
  constructor
  · exact exists_geometricPacketInterface_of_torus_overlap
      d hd hr hrsmall hmono hrlim (t₀ := 1) (by norm_num) htorus
  · intro P
    exact ⟨
      fullPoissonSupportMeasure_paperTailCoverEvent_measure_one
        hd hr hrsmall hmono hrlim htorus P,
      fullPoissonSupportMeasure_limsupCoverEvent_measure_one
        hd hr hrsmall hmono hrlim htorus P⟩

end Shepp.Section5
end SheppFlattenedModule065

section SheppFlattenedModule066
open scoped ENNReal ProbabilityTheory Topology
open Filter MeasureTheory Set

namespace Shepp.Section6

open ProbabilityTheory
open Shepp.Section2 Shepp.Section3 Shepp.Section4 Shepp.Section5
  TopologicalSpace

abbrev IIDCenterSample (d : ℕ) := ℕ → FlatTorus d

noncomputable def iidCenterMeasure (d : ℕ) :
    Measure (IIDCenterSample d) :=
  Measure.infinitePi fun _n : ℕ => flatTorusVolume d

noncomputable instance iidCenterMeasure_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (iidCenterMeasure d) := by
  unfold iidCenterMeasure
  infer_instance

theorem iidCenterCoordinates_iIndepFun (d : ℕ) :
    iIndepFun (fun n (X : IIDCenterSample d) => X n)
      (iidCenterMeasure d) := by
  unfold iidCenterMeasure
  exact iIndepFun_infinitePi (X := fun _n x => x) (fun _n => measurable_id)

theorem iidCenterCoordinate_hasLaw (d n : ℕ) :
    HasLaw (fun X : IIDCenterSample d => X n)
      (flatTorusVolume d) (iidCenterMeasure d) := by
  refine ⟨(measurable_pi_apply n).aemeasurable, ?_⟩
  unfold iidCenterMeasure
  exact Measure.infinitePi_map_eval (fun _n : ℕ => flatTorusVolume d) n

noncomputable def iidSingletonSupports
    {d : ℕ} (X : IIDCenterSample d) : FullPoissonSupportSample d :=
  fun n => ({X n} : CompactResidual (FlatTorus d))

@[simp]
theorem coe_iidSingletonSupports
    {d : ℕ} (X : IIDCenterSample d) (n : ℕ) :
    (((iidSingletonSupports X) n : CompactResidual (FlatTorus d)) :
        Set (FlatTorus d)) = {X n} :=
  rfl

theorem measurable_iidSingletonSupports {d : ℕ} :
    Measurable (iidSingletonSupports :
      IIDCenterSample d → FullPoissonSupportSample d) := by
  apply measurable_pi_lambda
  intro n
  exact Compacts.continuous_singleton.measurable.comp
    (measurable_pi_apply n)

noncomputable def iidCentersCoveredFrom
    {d : ℕ} (r : ℕ → ℝ) (n₀ : ℕ)
    (X : IIDCenterSample d) : Set (FlatTorus d) :=
  fullPoissonSupportsCoveredFrom r n₀ (iidSingletonSupports X)

theorem mem_iidCentersCoveredFrom_iff
    {d : ℕ} (r : ℕ → ℝ) (n₀ : ℕ)
    (X : IIDCenterSample d) (z : FlatTorus d) :
    z ∈ iidCentersCoveredFrom r n₀ X ↔
      ∃ n : ℕ, n₀ ≤ n ∧ z ∈ Metric.ball (X n) (r n) := by
  simp only [iidCentersCoveredFrom, fullPoissonSupportsCoveredFrom,
    compactSupportsCovered, Set.mem_iUnion,
    coe_iidSingletonSupports, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, x, hx, hz⟩
    exact ⟨n, n.property, hx ▸ hz⟩
  · rintro ⟨n, hn, hz⟩
    let m : {q : ℕ // n₀ ≤ q} := ⟨n, hn⟩
    exact ⟨m, X n, rfl, by simpa only [m] using hz⟩

noncomputable def iidLimsupSet
    {d : ℕ} (r : ℕ → ℝ) (X : IIDCenterSample d) :
    Set (FlatTorus d) :=
  fullPoissonSupportLimsupSet r (iidSingletonSupports X)

theorem iidLimsupSet_eq_iInter_coveredFrom
    {d : ℕ} (r : ℕ → ℝ) (X : IIDCenterSample d) :
    iidLimsupSet r X = ⋂ n₀ : ℕ, iidCentersCoveredFrom r n₀ X :=
  rfl

def iidLimsupCoverEvent
    {d : ℕ} (r : ℕ → ℝ) : Set (IIDCenterSample d) :=
  iidSingletonSupports ⁻¹'
    fullPoissonSupportLimsupCoverEvent (d := d) r

@[simp]
theorem mem_iidLimsupCoverEvent_iff
    {d : ℕ} (r : ℕ → ℝ) (X : IIDCenterSample d) :
    X ∈ iidLimsupCoverEvent (d := d) r ↔
      iidLimsupSet r X = Set.univ :=
  Iff.rfl

def iidAllTailsFiniteCoverEvent
    {d : ℕ} (r : ℕ → ℝ) : Set (IIDCenterSample d) :=
  iidSingletonSupports ⁻¹'
    fullPoissonSupportAllTailsCoverEvent (d := d) r

theorem measurableSet_iidAllTailsFiniteCoverEvent
    {d : ℕ} (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (htorus :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞) :
    MeasurableSet (iidAllTailsFiniteCoverEvent (d := d) r) := by
  exact (measurableSet_fullPoissonSupportAllTailsCoverEvent
    hd hr hrsmall hmono hrlim htorus).preimage
      measurable_iidSingletonSupports

theorem iidAllTailsFiniteCoverEvent_subset_limsupCoverEvent
    {d : ℕ} (r : ℕ → ℝ) :
    iidAllTailsFiniteCoverEvent (d := d) r ⊆
      iidLimsupCoverEvent (d := d) r := by
  exact Set.preimage_mono
    (allTailsCoverEvent_subset_limsupCoverEvent (d := d) r)

def iidPaperTailCoverEvent
    {d : ℕ} (r : ℕ → ℝ) : Set (IIDCenterSample d) :=
  iidSingletonSupports ⁻¹'
    fullPoissonSupportPaperTailCoverEvent (d := d) r

theorem iidAllTailsFiniteCoverEvent_subset_paperTailCoverEvent
    {d : ℕ} (r : ℕ → ℝ) :
    iidAllTailsFiniteCoverEvent (d := d) r ⊆
      iidPaperTailCoverEvent (d := d) r := by
  exact Set.preimage_mono
    (allTailsCoverEvent_subset_paperTailCoverEvent (d := d) r)

end Shepp.Section6
end SheppFlattenedModule066

section SheppFlattenedModule067
open scoped ENNReal NNReal ProbabilityTheory Topology
open Filter MeasureTheory Set

namespace Shepp.Section6

open ProbabilityTheory

theorem integrable_exp_mul_natCast_poissonMeasure
    (rate : NNReal) (t : ℝ) :
    Integrable (fun n : ℕ => Real.exp (t * (n : ℝ)))
      (poissonMeasure rate) := by
  apply integrable_poissonMeasure_iff.mpr
  have h :=
    (Real.summable_pow_div_factorial
      ((rate : ℝ) * Real.exp t)).mul_left (Real.exp (-(rate : ℝ)))
  refine h.congr fun n => ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [show t * (n : ℝ) = (n : ℝ) * t by ring, Real.exp_nat_mul]
  rw [mul_pow]
  ring

theorem poisson_natCast_mgf (rate : NNReal) (t : ℝ) :
    mgf (fun n : ℕ => (n : ℝ)) (poissonMeasure rate) t =
      Real.exp ((rate : ℝ) * (Real.exp t - 1)) := by
  unfold mgf
  rw [integral_poissonMeasure]
  calc
    (∑' n : ℕ,
        (Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ n /
          (n.factorial : ℝ)) • Real.exp (t * (n : ℝ))) =
        Real.exp (-(rate : ℝ)) *
          ∑' n : ℕ,
            (((rate : ℝ) * Real.exp t) ^ n /
              (n.factorial : ℝ)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      simp only [smul_eq_mul]
      rw [show t * (n : ℝ) = (n : ℝ) * t by ring,
        Real.exp_nat_mul, mul_pow]
      ring
    _ = Real.exp (-(rate : ℝ)) *
        Real.exp ((rate : ℝ) * Real.exp t) := by
      have hsum :
          (∑' n : ℕ,
            (((rate : ℝ) * Real.exp t) ^ n /
              (n.factorial : ℝ))) =
            Real.exp ((rate : ℝ) * Real.exp t) := by
        simpa [Shepp.Section5.expSeriesCoeff] using
          (Shepp.Section5.tsum_expSeriesCoeff
            ((rate : ℝ) * Real.exp t))
      rw [hsum]
    _ = Real.exp ((rate : ℝ) * (Real.exp t - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem poisson_natCast_ge_le_exp
    (rate : NNReal) (threshold t : ℝ) (ht : 0 ≤ t) :
    (poissonMeasure rate).real
        {n : ℕ | threshold ≤ (n : ℝ)} ≤
      Real.exp
        (-t * threshold + (rate : ℝ) * (Real.exp t - 1)) := by
  calc
    (poissonMeasure rate).real
        {n : ℕ | threshold ≤ (n : ℝ)} ≤
        Real.exp (-t * threshold) *
          mgf (fun n : ℕ => (n : ℝ)) (poissonMeasure rate) t :=
      measure_ge_le_exp_mul_mgf threshold ht
        (integrable_exp_mul_natCast_poissonMeasure rate t)
    _ = Real.exp
        (-t * threshold + (rate : ℝ) * (Real.exp t - 1)) := by
      rw [poisson_natCast_mgf, ← Real.exp_add]

theorem poisson_deficit_upper_tail
    {N D : ℕ} (hD : 0 < D) (hDN : D ≤ N) :
    (poissonMeasure ((N - D : ℕ) : NNReal)).real
        {k : ℕ | (N : ℝ) ≤ (k : ℝ)} ≤
      Real.exp (-((D : ℝ) ^ 2 / (4 * (N : ℝ)))) := by
  have hN : 0 < N := lt_of_lt_of_le hD hDN
  let t : ℝ := (D : ℝ) / (2 * (N : ℝ))
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one (by positivity : (0 : ℝ) < 2 * (N : ℝ))]
    norm_cast
    omega
  have hone_sub_pos : 0 < 1 - t := sub_pos.mpr ht1
  have hexp : Real.exp t - 1 ≤ t / (1 - t) := by
    calc
      Real.exp t - 1 ≤ 1 / (1 - t) - 1 :=
        sub_le_sub_right
          (Real.exp_bound_div_one_sub_of_interval ht0 ht1) 1
      _ = t / (1 - t) := by
        field_simp
        ring
  have hchernoff := poisson_natCast_ge_le_exp
    (((N - D : ℕ) : NNReal)) (N : ℝ) t ht0
  calc
    (poissonMeasure ((N - D : ℕ) : NNReal)).real
        {k : ℕ | (N : ℝ) ≤ (k : ℝ)} ≤
        Real.exp
          (-t * (N : ℝ) +
            (((N - D : ℕ) : NNReal) : ℝ) *
              (Real.exp t - 1)) := hchernoff
    _ ≤ Real.exp
        (-t * (N : ℝ) +
          (((N - D : ℕ) : NNReal) : ℝ) *
            (t / (1 - t))) := by
      apply Real.exp_le_exp.mpr
      gcongr
    _ ≤ Real.exp (-((D : ℝ) ^ 2 / (4 * (N : ℝ)))) := by
      apply Real.exp_le_exp.mpr
      rw [NNReal.coe_natCast, Nat.cast_sub hDN]
      have hDNreal : (D : ℝ) ≤ (N : ℝ) := by exact_mod_cast hDN
      have hden : 0 < 2 * (N : ℝ) - (D : ℝ) := by
        nlinarith [show (0 : ℝ) < (N : ℝ) by positivity]
      have hfourN : 0 < 4 * (N : ℝ) := by positivity
      have htfrac :
          t / (1 - t) =
            (D : ℝ) / (2 * (N : ℝ) - (D : ℝ)) := by
        dsimp [t]
        field_simp
      have hfrac :
          ((N : ℝ) - (D : ℝ)) *
              ((D : ℝ) / (2 * (N : ℝ) - (D : ℝ))) ≤
            (D : ℝ) / 2 - (D : ℝ) ^ 2 / (4 * (N : ℝ)) := by
        calc
          ((N : ℝ) - (D : ℝ)) *
                ((D : ℝ) / (2 * (N : ℝ) - (D : ℝ))) =
              (((N : ℝ) - (D : ℝ)) * (D : ℝ)) /
                (2 * (N : ℝ) - (D : ℝ)) := by ring
          _ ≤ ((D : ℝ) * (2 * (N : ℝ) - (D : ℝ))) /
                (4 * (N : ℝ)) := by
            rw [div_le_div_iff₀ hden hfourN]
            nlinarith [sq_nonneg (D : ℝ)]
          _ = (D : ℝ) / 2 -
                (D : ℝ) ^ 2 / (4 * (N : ℝ)) := by
            field_simp
            ring
      rw [htfrac]
      calc
        -t * (N : ℝ) +
              ((N : ℝ) - (D : ℝ)) *
                ((D : ℝ) / (2 * (N : ℝ) - (D : ℝ))) =
            -(D : ℝ) / 2 +
              ((N : ℝ) - (D : ℝ)) *
                ((D : ℝ) / (2 * (N : ℝ) - (D : ℝ))) := by
          dsimp [t]
          field_simp
        _ ≤ -(D : ℝ) / 2 +
              ((D : ℝ) / 2 -
                (D : ℝ) ^ 2 / (4 * (N : ℝ))) := by
          gcongr
        _ = -((D : ℝ) ^ 2 / (4 * (N : ℝ))) := by ring

theorem summable_stretched_exponential
    {c p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    Summable (fun n : ℕ =>
      Real.exp (-c * (n : ℝ) ^ p)) := by
  have hlog := (isLittleO_log_rpow_atTop hp).bound
    (show 0 < c / 2 by positivity)
  have hlogNat := tendsto_natCast_atTop_atTop.eventually hlog
  have hdom : ∀ᶠ n : ℕ in atTop,
      ‖Real.exp (-c * (n : ℝ) ^ p)‖ ≤
        (((n : ℝ) ^ 2)⁻¹) := by
    filter_upwards [hlogNat, eventually_ge_atTop 1] with n hnlog hn1
    have hn1real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1real
    have hlognonneg : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg hn1real
    have hrpownonneg : 0 ≤ (n : ℝ) ^ p := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hlognonneg,
      Real.norm_eq_abs, abs_of_nonneg hrpownonneg] at hnlog
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-c * (n : ℝ) ^ p) ≤
          Real.exp (-2 * Real.log (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = (((n : ℝ) ^ 2)⁻¹) := by
        rw [show -2 * Real.log (n : ℝ) =
          -(2 * Real.log (n : ℝ)) by ring]
        rw [Real.exp_neg,
          show 2 * Real.log (n : ℝ) =
            Real.log (n : ℝ) + Real.log (n : ℝ) by ring,
          Real.exp_add, Real.exp_log hnpos]
        ring
  exact Summable.of_norm_bounded_eventually_nat
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))) hdom

end Shepp.Section6
end SheppFlattenedModule067

section SheppFlattenedModule068
open scoped ENNReal ProbabilityTheory Topology BigOperators
open Filter Set MeasureTheory

namespace Shepp.Section6

open ProbabilityTheory Shepp.Section2 Shepp.Section3 Shepp.Section4
  Shepp.Section5 TopologicalSpace

private theorem exists_iidGridLevel
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (n : ℕ) :
    ∃ q : ℕ, P.level q ≤ r n := by
  have hevent := test_dyadicLevel_tendsto_zero.eventually_lt_const
    (P.radius_pos n)
  obtain ⟨M, hM⟩ := hevent.exists
  refine ⟨M + 1, ?_⟩
  exact (test_dyadicLevel_antitone (by omega)).trans hM.le

noncomputable def iidGridLevel
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (n : ℕ) : ℕ :=
  Nat.find (exists_iidGridLevel P n)

theorem iidGridLevel_spec
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (n : ℕ) :
    P.level (iidGridLevel P n) ≤ r n :=
  Nat.find_spec (exists_iidGridLevel P n)

theorem radius_lt_two_iidGridLevel
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (n : ℕ)
    (hsmall : r n < P.level 0) :
    r n < 2 * P.level (iidGridLevel P n) := by
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero
    (by
      intro hzero
      have hspec := iidGridLevel_spec P n
      rw [hzero] at hspec
      exact (not_le_of_gt hsmall) hspec : iidGridLevel P n ≠ 0)
  have hnot : ¬P.level q ≤ r n := by
    intro hqr
    have hmin := Nat.find_min' (exists_iidGridLevel P n)
      hqr
    change iidGridLevel P n ≤ q at hmin
    rw [hq] at hmin
    omega
  have hlt : r n < P.level q := lt_of_not_ge hnot
  calc
    r n < P.level q := hlt
    _ = 2 * P.level (q + 1) := by
      simpa only [Nat.add_assoc] using
        test_dyadicLevel_succ (P.K + q)
    _ = 2 * P.level (iidGridLevel P n) := by rw [hq]

noncomputable def iidGridCardConstant (d : ℕ) : ℝ :=
  (gridEta d)⁻¹ ^ d * euclideanUnitBallVolume d * (2 : ℝ) ^ d

theorem iidGridCardConstant_pos (d : ℕ) :
    0 < iidGridCardConstant d := by
  unfold iidGridCardConstant
  exact mul_pos
    (mul_pos (pow_pos (inv_pos.mpr (gridEta_pos d)) d)
      (euclideanUnitBallVolume_pos d))
    (pow_pos (by norm_num) d)

theorem iid_grid_card_mul_radiusVolume_le
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r) (n : ℕ)
    (hsmall : r n < P.level 0) :
    (Fintype.card (GridLabel P (iidGridLevel P n)) : ℝ) *
        radiusVolume d r n ≤ iidGridCardConstant d := by
  have hlpos : 0 < P.level (iidGridLevel P n) :=
    test_dyadicLevel_pos _
  have hrpos : 0 < r n := P.radius_pos n
  have hratio : (P.level (iidGridLevel P n))⁻¹ * r n ≤ 2 := by
    rw [inv_mul_le_iff₀ hlpos]
    simpa [mul_comm] using (radius_lt_two_iidGridLevel P n hsmall).le
  have hratio0 : 0 ≤ (P.level (iidGridLevel P n))⁻¹ * r n := by
    positivity
  have hp : ((P.level (iidGridLevel P n))⁻¹ * r n) ^ d ≤
      (2 : ℝ) ^ d := by
    gcongr
  rw [card_gridLabel_real]
  unfold radiusVolume iidGridCardConstant
  calc
    (gridEta d)⁻¹ ^ d * (P.level (iidGridLevel P n))⁻¹ ^ d *
          (euclideanUnitBallVolume d * r n ^ d) =
        ((gridEta d)⁻¹ ^ d * euclideanUnitBallVolume d) *
          (((P.level (iidGridLevel P n))⁻¹ * r n) ^ d) := by
      rw [mul_pow]
      ring
    _ ≤ ((gridEta d)⁻¹ ^ d * euclideanUnitBallVolume d) *
          (2 : ℝ) ^ d := by
      exact mul_le_mul_of_nonneg_left hp
        (mul_nonneg (pow_nonneg (inv_nonneg.mpr (gridEta_pos d).le) d)
          (euclideanUnitBallVolume_pos d).le)
    _ = (gridEta d)⁻¹ ^ d * euclideanUnitBallVolume d *
          (2 : ℝ) ^ d := by ring

def highMomentQualifies (v : ℕ → ℝ) (n : ℕ) : Prop :=
  1 / (((n + 1 : ℕ) : ℝ) ^ (7 / 8 : ℝ)) ≤ v n

theorem threshold_four_thirds (n : ℕ) :
    (1 / (((n + 1 : ℕ) : ℝ) ^ (7 / 8 : ℝ))) ^ (4 / 3 : ℝ) =
      1 / (((n + 1 : ℕ) : ℝ) ^ (7 / 6 : ℝ)) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [Real.div_rpow (by norm_num) (Real.rpow_nonneg hn.le _)]
  norm_num
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  norm_num

theorem highMomentQualifies_unbounded {v : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (hdiv : ¬Summable (fun n => v n ^ (4 / 3 : ℝ))) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ highMomentQualifies v n := by
  intro N
  by_contra hnone
  push Not at hnone
  have hmajor : Summable (fun n : ℕ =>
      1 / (((n + 1 : ℕ) : ℝ) ^ (7 / 6 : ℝ))) := by
    have hp : Summable (fun n : ℕ =>
        1 / (n : ℝ) ^ (7 / 6 : ℝ)) :=
      Real.summable_one_div_nat_rpow.mpr (by norm_num)
    have hshift := (summable_nat_add_iff 1).mpr hp
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  apply hdiv
  apply Summable.of_norm_bounded_eventually_nat hmajor
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hv n).le _)]
  have hbase : v n ≤
      1 / (((n + 1 : ℕ) : ℝ) ^ (7 / 8 : ℝ)) :=
    (lt_of_not_ge (hnone n hn)).le
  have hp := Real.rpow_le_rpow (hv n).le hbase
    (by norm_num : (0 : ℝ) ≤ 4 / 3)
  simpa only [threshold_four_thirds] using hp

theorem summable_seven_eighths_mul_stretched_eighth
    {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ =>
      (n : ℝ) ^ (7 / 8 : ℝ) *
        Real.exp (-c * (n : ℝ) ^ (1 / 8 : ℝ))) := by
  have hlog := (isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 8)).bound
      (show 0 < c / 2 by positivity)
  have hlogNat := tendsto_natCast_atTop_atTop.eventually hlog
  have hdom : ∀ᶠ n : ℕ in atTop,
      ‖(n : ℝ) ^ (7 / 8 : ℝ) *
          Real.exp (-c * (n : ℝ) ^ (1 / 8 : ℝ))‖ ≤
        Real.exp (-(c / 2) * (n : ℝ) ^ (1 / 8 : ℝ)) := by
    filter_upwards [hlogNat, eventually_ge_atTop 1] with n hnlog hn1
    have hn1real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1real
    have hlognonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1real
    have hrpownonneg : 0 ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hlognonneg,
      Real.norm_eq_abs, abs_of_nonneg hrpownonneg] at hnlog
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (by positivity)
      (Real.exp_pos _))]
    calc
      (n : ℝ) ^ (7 / 8 : ℝ) *
            Real.exp (-c * (n : ℝ) ^ (1 / 8 : ℝ)) =
          Real.exp ((7 / 8 : ℝ) * Real.log (n : ℝ) -
            c * (n : ℝ) ^ (1 / 8 : ℝ)) := by
        rw [Real.rpow_def_of_pos hnpos, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(c / 2) *
          (n : ℝ) ^ (1 / 8 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  exact Summable.of_norm_bounded_eventually_nat
    (summable_stretched_exponential
      (show 0 < c / 2 by positivity)
      (by norm_num : (0 : ℝ) < 1 / 8)) hdom

theorem summable_shifted_highMoment_majorant {c C : ℝ}
    (hc : 0 < c) :
    Summable (fun n : ℕ =>
      C * (((n + 1 : ℕ) : ℝ) ^ (7 / 8 : ℝ)) *
        Real.exp (-c * (((n + 1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)))) := by
  have h := summable_seven_eighths_mul_stretched_eighth hc
  have hshift := (summable_nat_add_iff 1).mpr h
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hshift.mul_left C

def iidAvoidEvent {d : ℕ} (s n : ℕ) (y : FlatTorus d) (t : ℝ) :
    Set (IIDCenterSample d) :=
  ⋂ j ∈ Finset.Icc s n,
    (fun X : IIDCenterSample d => X j) ⁻¹' (Metric.ball y t)ᶜ

theorem measurableSet_iidAvoidEvent {d : ℕ} (s n : ℕ)
    (y : FlatTorus d) (t : ℝ) :
    MeasurableSet (iidAvoidEvent s n y t) := by
  apply Finset.measurableSet_biInter
  intro j _hj
  exact Metric.isOpen_ball.measurableSet.compl.preimage
    (measurable_pi_apply j)

theorem iidAvoidEvent_measure_eq {d : ℕ} (s n : ℕ)
    (y : FlatTorus d) (t : ℝ) :
    iidCenterMeasure d (iidAvoidEvent s n y t) =
      ∏ _j ∈ Finset.Icc s n,
        flatTorusVolume d (Metric.ball y t)ᶜ := by
  rw [iidAvoidEvent]
  rw [(iidCenterCoordinates_iIndepFun d).measure_inter_preimage_eq_mul]
  · apply Finset.prod_congr rfl
    intro j _hj
    exact (iidCenterCoordinate_hasLaw d j).measure_eq
      (p := fun z => z ∈ (Metric.ball y t)ᶜ)
      Metric.isOpen_ball.measurableSet.compl
  · intro j _hj
    exact Metric.isOpen_ball.measurableSet.compl

theorem iidAvoidEvent_measureReal_eq {d : ℕ} (s n : ℕ)
    (y : FlatTorus d) (t : ℝ) :
    (iidCenterMeasure d).real (iidAvoidEvent s n y t) =
      (1 - (flatTorusVolume d).real (Metric.ball y t)) ^
        (Finset.Icc s n).card := by
  rw [measureReal_def, iidAvoidEvent_measure_eq, ENNReal.toReal_prod]
  simp_rw [← measureReal_def,
    measureReal_compl Metric.isOpen_ball.measurableSet, probReal_univ]
  exact Finset.prod_const _

theorem halfRadius_ball_volume
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (n : ℕ)
    (α : GridLabel P (iidGridLevel P n)) :
    (flatTorusVolume d).real
        (Metric.ball (gridCenter P (iidGridLevel P n) α) (r n / 2)) =
      radiusVolume d r n / (2 : ℝ) ^ d := by
  rw [flatTorusVolumeReal_ball_gridCenter hd P
    (iidGridLevel P n) α
      (div_nonneg (P.radius_pos n).le (by norm_num)) (by
      have hsmall := P.radius_lt_quarter n
      nlinarith [P.radius_pos n])]
  unfold radiusVolume
  rw [div_pow]
  ring

theorem iidAvoidEvent_measureReal_le_exp
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (s n : ℕ)
    (α : GridLabel P (iidGridLevel P n)) :
    (iidCenterMeasure d).real
        (iidAvoidEvent s n (gridCenter P (iidGridLevel P n) α)
          (r n / 2)) ≤
      Real.exp (-((Finset.Icc s n).card : ℝ) *
        (radiusVolume d r n / (2 : ℝ) ^ d)) := by
  rw [iidAvoidEvent_measureReal_eq,
    halfRadius_ball_volume hd P n α]
  let p : ℝ := radiusVolume d r n / (2 : ℝ) ^ d
  have hp0 : 0 ≤ p := by
    dsimp [p]
    exact div_nonneg (P.radiusVolume_nonneg n) (by positivity)
  have hp1 : p ≤ 1 := by
    dsimp [p]
    rw [← halfRadius_ball_volume hd P n α]
    exact measureReal_le_one
  have hbase0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  calc
    (1 - radiusVolume d r n / (2 : ℝ) ^ d) ^
          (Finset.Icc s n).card =
        (1 - p) ^ (Finset.Icc s n).card := by rfl
    _ ≤ (Real.exp (-p)) ^ (Finset.Icc s n).card := by
      gcongr
      exact Real.one_sub_le_exp_neg p
    _ = Real.exp (-((Finset.Icc s n).card : ℝ) * p) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = Real.exp (-((Finset.Icc s n).card : ℝ) *
        (radiusVolume d r n / (2 : ℝ) ^ d)) := by rfl

noncomputable def iidGridMissEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (s n : ℕ) : Set (IIDCenterSample d) :=
  ⋃ α : GridLabel P (iidGridLevel P n),
    iidAvoidEvent s n (gridCenter P (iidGridLevel P n) α) (r n / 2)

theorem measurableSet_iidGridMissEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (s n : ℕ) : MeasurableSet (iidGridMissEvent P s n) := by
  apply MeasurableSet.iUnion
  intro α
  exact measurableSet_iidAvoidEvent s n _ _

theorem iidGridMissEvent_measureReal_le
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (s n : ℕ) :
    (iidCenterMeasure d).real (iidGridMissEvent P s n) ≤
      (Fintype.card (GridLabel P (iidGridLevel P n)) : ℝ) *
        Real.exp (-((Finset.Icc s n).card : ℝ) *
          (radiusVolume d r n / (2 : ℝ) ^ d)) := by
  calc
    (iidCenterMeasure d).real (iidGridMissEvent P s n) ≤
        ∑ α : GridLabel P (iidGridLevel P n),
          (iidCenterMeasure d).real
            (iidAvoidEvent s n
              (gridCenter P (iidGridLevel P n) α) (r n / 2)) := by
      exact measureReal_iUnion_fintype_le _
    _ ≤ ∑ _α : GridLabel P (iidGridLevel P n),
        Real.exp (-((Finset.Icc s n).card : ℝ) *
          (radiusVolume d r n / (2 : ℝ) ^ d)) := by
      gcongr with α
      exact iidAvoidEvent_measureReal_le_exp hd P s n α
    _ = (Fintype.card (GridLabel P (iidGridLevel P n)) : ℝ) *
        Real.exp (-((Finset.Icc s n).card : ℝ) *
          (radiusVolume d r n / (2 : ℝ) ^ d)) := by simp

theorem half_natCast_mul_threshold (n : ℕ) :
    (((n + 1 : ℕ) : ℝ) / 2) *
        (1 / (((n + 1 : ℕ) : ℝ) ^ (7 / 8 : ℝ))) =
      (1 / 2 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  calc
    (((n + 1 : ℕ) : ℝ) / 2) *
          (1 / (((n + 1 : ℕ) : ℝ) ^ (7 / 8 : ℝ))) =
        (1 / 2 : ℝ) *
          (((n + 1 : ℕ) : ℝ) /
            (((n + 1 : ℕ) : ℝ) ^ (7 / 8 : ℝ))) := by ring
    _ = (1 / 2 : ℝ) *
        ((((n + 1 : ℕ) : ℝ) ^ (1 : ℝ)) /
          (((n + 1 : ℕ) : ℝ) ^ (7 / 8 : ℝ))) := by rw [Real.rpow_one]
    _ = (1 / 2 : ℝ) *
        (((n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) - 7 / 8)) := by
      rw [Real.rpow_sub hn]
    _ = (1 / 2 : ℝ) *
        (((n + 1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by norm_num

noncomputable def highMomentExpConstant (d : ℕ) : ℝ :=
  1 / (2 * (2 : ℝ) ^ d)

theorem highMomentExpConstant_pos (d : ℕ) :
    0 < highMomentExpConstant d := by
  unfold highMomentExpConstant
  positivity

theorem iidGridMiss_majorant
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (s n : ℕ)
    (hsmall : r n < P.level 0) (hqual : highMomentQualifies (radiusVolume d r) n)
    (hfit : 2 * s ≤ n + 1) :
    (iidCenterMeasure d).real (iidGridMissEvent P s n) ≤
      iidGridCardConstant d *
        (((n + 1 : ℕ) : ℝ) ^ (7 / 8 : ℝ)) *
          Real.exp (-highMomentExpConstant d *
            (((n + 1 : ℕ) : ℝ) ^ (1 / 8 : ℝ))) := by
  let card : ℝ :=
    (Fintype.card (GridLabel P (iidGridLevel P n)) : ℝ)
  let v : ℝ := radiusVolume d r n
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hcard0 : 0 ≤ card := by dsimp [card]; positivity
  have hv0 : 0 ≤ v := by exact P.radiusVolume_nonneg n
  have hcardV : card * v ≤ iidGridCardConstant d := by
    exact iid_grid_card_mul_radiusVolume_le P n hsmall
  have hqual' : 1 / N ^ (7 / 8 : ℝ) ≤ v := by
    exact hqual
  have hcard : card ≤ iidGridCardConstant d * N ^ (7 / 8 : ℝ) := by
    rw [← div_le_iff₀ (Real.rpow_pos_of_pos hNpos _)]
    calc
      card / N ^ (7 / 8 : ℝ) =
          card * (1 / N ^ (7 / 8 : ℝ)) := by ring
      _ ≤ card * v := mul_le_mul_of_nonneg_left hqual' hcard0
      _ ≤ iidGridCardConstant d := hcardV
  have hsle : s ≤ n := by omega
  have hmcard : (Finset.Icc s n).card = n + 1 - s := Nat.card_Icc s n
  have hmNat : n + 1 ≤ 2 * (Finset.Icc s n).card := by
    rw [hmcard]
    omega
  have hmReal : N / 2 ≤ ((Finset.Icc s n).card : ℝ) := by
    have hcast : N ≤ 2 * ((Finset.Icc s n).card : ℝ) := by
      dsimp [N]
      exact_mod_cast hmNat
    linarith
  have hmass : (1 / 2 : ℝ) * N ^ (1 / 8 : ℝ) ≤
      ((Finset.Icc s n).card : ℝ) * v := by
    calc
      (1 / 2 : ℝ) * N ^ (1 / 8 : ℝ) =
          (N / 2) * (1 / N ^ (7 / 8 : ℝ)) := by
        simpa only [N] using (half_natCast_mul_threshold n).symm
      _ ≤ ((Finset.Icc s n).card : ℝ) * v := by
        exact mul_le_mul hmReal hqual' (by positivity) (by positivity)
  have hexp :
      Real.exp (-((Finset.Icc s n).card : ℝ) * (v / (2 : ℝ) ^ d)) ≤
        Real.exp (-highMomentExpConstant d * N ^ (1 / 8 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have htwo : 0 < (2 : ℝ) ^ d := pow_pos (by norm_num) d
    have hdiv := div_le_div_of_nonneg_right hmass htwo.le
    have hmag : highMomentExpConstant d * N ^ (1 / 8 : ℝ) ≤
        ((Finset.Icc s n).card : ℝ) * (v / (2 : ℝ) ^ d) := by
      unfold highMomentExpConstant
      calc
        1 / (2 * (2 : ℝ) ^ d) * N ^ (1 / 8 : ℝ) =
            ((1 / 2 : ℝ) * N ^ (1 / 8 : ℝ)) / (2 : ℝ) ^ d := by
          field_simp
        _ ≤ (((Finset.Icc s n).card : ℝ) * v) / (2 : ℝ) ^ d := hdiv
        _ = ((Finset.Icc s n).card : ℝ) * (v / (2 : ℝ) ^ d) := by ring
    linarith
  calc
    (iidCenterMeasure d).real (iidGridMissEvent P s n) ≤
        card * Real.exp (-((Finset.Icc s n).card : ℝ) *
          (v / (2 : ℝ) ^ d)) := iidGridMissEvent_measureReal_le hd P s n
    _ ≤ (iidGridCardConstant d * N ^ (7 / 8 : ℝ)) *
        Real.exp (-((Finset.Icc s n).card : ℝ) *
          (v / (2 : ℝ) ^ d)) := by
      exact mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ ≤ (iidGridCardConstant d * N ^ (7 / 8 : ℝ)) *
        Real.exp (-highMomentExpConstant d * N ^ (1 / 8 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hexp
        (mul_nonneg (iidGridCardConstant_pos d).le (by positivity))
    _ = iidGridCardConstant d *
        (((n + 1 : ℕ) : ℝ) ^ (7 / 8 : ℝ)) *
          Real.exp (-highMomentExpConstant d *
            (((n + 1 : ℕ) : ℝ) ^ (1 / 8 : ℝ))) := by rfl

noncomputable def highMomentBadEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (s n : ℕ) : Set (IIDCenterSample d) := by
  classical
  exact if r n < P.level 0 ∧ highMomentQualifies (radiusVolume d r) n ∧
        2 * s ≤ n + 1 then
      iidGridMissEvent P s n
    else ∅

theorem measurableSet_highMomentBadEvent
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (s n : ℕ) : MeasurableSet (highMomentBadEvent P s n) := by
  unfold highMomentBadEvent
  split_ifs
  · exact measurableSet_iidGridMissEvent P s n
  · exact MeasurableSet.empty

theorem highMomentBadEvent_measureReal_le
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (s n : ℕ) :
    (iidCenterMeasure d).real (highMomentBadEvent P s n) ≤
      iidGridCardConstant d *
        (((n + 1 : ℕ) : ℝ) ^ (7 / 8 : ℝ)) *
          Real.exp (-highMomentExpConstant d *
            (((n + 1 : ℕ) : ℝ) ^ (1 / 8 : ℝ))) := by
  unfold highMomentBadEvent
  split_ifs with h
  · exact iidGridMiss_majorant hd P s n h.1 h.2.1 h.2.2
  · simp only [measureReal_empty]
    exact mul_nonneg
      (mul_nonneg (iidGridCardConstant_pos d).le
        (Real.rpow_nonneg (by positivity) _))
      (Real.exp_pos _).le

theorem highMomentBadEvent_tsum_ne_top
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (s : ℕ) :
    (∑' n : ℕ,
      iidCenterMeasure d (highMomentBadEvent P s n)) ≠ ∞ := by
  let f : ℕ → ℝ := fun n =>
    (iidCenterMeasure d).real (highMomentBadEvent P s n)
  let g : ℕ → ℝ := fun n =>
    iidGridCardConstant d *
      (((n + 1 : ℕ) : ℝ) ^ (7 / 8 : ℝ)) *
        Real.exp (-highMomentExpConstant d *
          (((n + 1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)))
  have hg : Summable g := by
    exact summable_shifted_highMoment_majorant
      (highMomentExpConstant_pos d)
  have hf : Summable f :=
    Summable.of_nonneg_of_le
      (fun n => measureReal_nonneg)
      (fun n => highMomentBadEvent_measureReal_le hd P s n) hg
  have hfnn : ∀ n, 0 ≤ f n := fun _ => measureReal_nonneg
  have heq : (fun n : ℕ =>
      iidCenterMeasure d (highMomentBadEvent P s n)) =
      fun n => ENNReal.ofReal (f n) := by
    funext n
    exact (ofReal_measureReal).symm
  rw [heq, ← ENNReal.ofReal_tsum_of_nonneg hfnn hf]
  exact ENNReal.ofReal_ne_top

theorem ae_eventually_not_highMomentBadEvent
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (s : ℕ) :
    ∀ᵐ X : IIDCenterSample d ∂iidCenterMeasure d,
      ∀ᶠ n : ℕ in atTop, X ∉ highMomentBadEvent P s n :=
  ae_eventually_notMem (highMomentBadEvent_tsum_ne_top hd P s)

theorem not_mem_iidAvoidEvent_iff
    {d : ℕ} (s n : ℕ) (y : FlatTorus d) (t : ℝ)
    (X : IIDCenterSample d) :
    X ∉ iidAvoidEvent s n y t ↔
      ∃ j ∈ Finset.Icc s n, X j ∈ Metric.ball y t := by
  simp [iidAvoidEvent, and_assoc]

theorem coveredFrom_eq_univ_of_not_gridMiss
    {d : ℕ} {r : ℕ → ℝ} (P : GeometricPacketInterface d r)
    (hmono : Antitone r) {s n : ℕ}
    (X : IIDCenterSample d) (hgood : X ∉ iidGridMissEvent P s n) :
    iidCentersCoveredFrom r s X = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  have hzUnion : z ∈ ⋃ α : GridLabel P (iidGridLevel P n),
      gridCell P (iidGridLevel P n) α := by
    rw [iUnion_gridCell_eq_univ]
    exact Set.mem_univ z
  obtain ⟨α, hzcell⟩ := Set.mem_iUnion.1 hzUnion
  have hnotAvoid : X ∉ iidAvoidEvent s n
      (gridCenter P (iidGridLevel P n) α) (r n / 2) := by
    intro havoid
    apply hgood
    exact Set.mem_iUnion.2 ⟨α, havoid⟩
  obtain ⟨j, hjIcc, hjball⟩ :=
    (not_mem_iidAvoidEvent_iff s n _ _ X).1 hnotAvoid
  have hsj : s ≤ j := (Finset.mem_Icc.1 hjIcc).1
  have hjn : j ≤ n := (Finset.mem_Icc.1 hjIcc).2
  have hzclosed := gridCell_subset_closedBall P
    (iidGridLevel P n) α hzcell
  have hzdist : dist z (gridCenter P (iidGridLevel P n) α) ≤
      gridCircumradius P (iidGridLevel P n) := by
    exact Metric.mem_closedBall.1 hzclosed
  have hjdist : dist (gridCenter P (iidGridLevel P n) α) (X j) <
      r n / 2 := by
    rw [dist_comm]
    exact Metric.mem_ball.1 hjball
  have hquarter : gridCircumradius P (iidGridLevel P n) ≤ r n / 4 := by
    exact (gridCircumradius_le_level_div_four P
      (iidGridLevel P n)).trans
        (div_le_div_of_nonneg_right (iidGridLevel_spec P n) (by norm_num))
  have hzballn : z ∈ Metric.ball (X j) (r n) := by
    rw [Metric.mem_ball]
    calc
      dist z (X j) ≤
          dist z (gridCenter P (iidGridLevel P n) α) +
            dist (gridCenter P (iidGridLevel P n) α) (X j) :=
        dist_triangle _ _ _
      _ < gridCircumradius P (iidGridLevel P n) + r n / 2 :=
        add_lt_add_of_le_of_lt hzdist hjdist
      _ < r n := by
        nlinarith [P.radius_pos n]
  apply (mem_iidCentersCoveredFrom_iff r s X z).2
  exact ⟨j, hsj, Metric.ball_subset_ball (hmono hjn) hzballn⟩

theorem ae_coveredFrom_eq_univ_of_highMoment
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (hmono : Antitone r)
    (hrlim : Tendsto r atTop (nhds 0))
    (hdiv : ¬Summable
      (fun n => radiusVolume d r n ^ (4 / 3 : ℝ)))
    (s : ℕ) :
    ∀ᵐ X : IIDCenterSample d ∂iidCenterMeasure d,
      iidCentersCoveredFrom r s X = Set.univ := by
  filter_upwards [ae_eventually_not_highMomentBadEvent hd P s]
    with X hX
  rw [eventually_atTop] at hX
  obtain ⟨Bbad, hBbad⟩ := hX
  have hsmallEv : ∀ᶠ n : ℕ in atTop, r n < P.level 0 :=
    hrlim.eventually_lt_const (test_dyadicLevel_pos P.K)
  rw [eventually_atTop] at hsmallEv
  obtain ⟨Bsmall, hBsmall⟩ := hsmallEv
  let B : ℕ := max (max Bbad Bsmall) (2 * s)
  obtain ⟨n, hnB, hqual⟩ :=
    highMomentQualifies_unbounded P.radiusVolume_pos hdiv B
  have hnBad : Bbad ≤ n :=
    (le_max_left Bbad Bsmall).trans
      ((le_max_left (max Bbad Bsmall) (2 * s)).trans hnB)
  have hnSmall : Bsmall ≤ n :=
    (le_max_right Bbad Bsmall).trans
      ((le_max_left (max Bbad Bsmall) (2 * s)).trans hnB)
  have hnFit : 2 * s ≤ n + 1 := by
    have : 2 * s ≤ B := le_max_right _ _
    omega
  have hsmall := hBsmall n hnSmall
  have hnotBad := hBbad n hnBad
  have hnotMiss : X ∉ iidGridMissEvent P s n := by
    have hcond : r n < P.level 0 ∧
        highMomentQualifies (radiusVolume d r) n ∧ 2 * s ≤ n + 1 :=
      ⟨hsmall, hqual, hnFit⟩
    unfold highMomentBadEvent at hnotBad
    rw [if_pos hcond] at hnotBad
    exact hnotBad
  exact coveredFrom_eq_univ_of_not_gridMiss P hmono X hnotMiss

theorem highMoment_iidLimsupCover_ae_of_interface
    {d : ℕ} (hd : 0 < d) {r : ℕ → ℝ}
    (P : GeometricPacketInterface d r) (hmono : Antitone r)
    (hrlim : Tendsto r atTop (nhds 0))
    (hdiv : ¬Summable
      (fun n => radiusVolume d r n ^ (4 / 3 : ℝ))) :
    ∀ᵐ X : IIDCenterSample d ∂iidCenterMeasure d,
      X ∈ iidLimsupCoverEvent (d := d) r := by
  have haeEach : ∀ s : ℕ,
      ∀ᵐ X : IIDCenterSample d ∂iidCenterMeasure d,
        iidCentersCoveredFrom r s X = Set.univ :=
    fun s => ae_coveredFrom_eq_univ_of_highMoment hd P hmono hrlim hdiv s
  have haeAll :
      ∀ᵐ X : IIDCenterSample d ∂iidCenterMeasure d,
        ∀ s : ℕ, iidCentersCoveredFrom r s X = Set.univ :=
    ae_all_iff.2 haeEach
  filter_upwards [haeAll] with X hX
  change iidLimsupSet r X = Set.univ
  rw [iidLimsupSet_eq_iInter_coveredFrom]
  simp only [hX, iInter_const]

theorem highMoment_dePoissonizedSufficiency
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (hdiv : ¬Summable
      (fun n => radiusVolume d r n ^ (4 / 3 : ℝ)))
    (htop :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞) :
    iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 1 := by
  obtain ⟨P⟩ := exists_geometricPacketInterface_of_torus_overlap
    d hd hr hrsmall hmono hrlim (t₀ := 1) (by norm_num) htop
  have hae := highMoment_iidLimsupCover_ae_of_interface
    (show 0 < d by omega) P hmono hrlim hdiv
  have hcompl : iidCenterMeasure d
      (iidLimsupCoverEvent (d := d) r)ᶜ = 0 := by
    apply ae_iff.1
    simpa only [Set.mem_compl_iff, not_not] using hae
  have hfull := measure_of_measure_compl_eq_zero hcompl
  simpa using hfull

end Shepp.Section6
end SheppFlattenedModule068

section SheppFlattenedModule069
open scoped ENNReal NNReal Topology
open Filter Set

namespace Shepp.Section6

lemma rpow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
  rw [Real.rpow_one_add' hx (by norm_num)]
  rw [← Real.sqrt_eq_rpow]

lemma rpow_three_halves_add_one_le_succ {x : ℝ} (hx : 1 ≤ x) :
    x ^ (3 / 2 : ℝ) + 1 ≤ (x + 1) ^ (3 / 2 : ℝ) := by
  rw [rpow_three_halves_eq_mul_sqrt (zero_le_one.trans hx)]
  rw [rpow_three_halves_eq_mul_sqrt (by positivity : 0 ≤ x + 1)]
  have hsqrt : Real.sqrt x ≤ Real.sqrt (x + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsqrt1 : 1 ≤ Real.sqrt x := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hx
  calc
    x * Real.sqrt x + 1 ≤ x * Real.sqrt x + Real.sqrt x := by
      gcongr
    _ = (x + 1) * Real.sqrt x := by ring
    _ ≤ (x + 1) * Real.sqrt (x + 1) := by
      gcongr

noncomputable def paperReserveIndex (k : ℕ) : ℕ :=
  ⌈((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)⌉₊

lemma paperReserveIndex_succ (k : ℕ) :
    paperReserveIndex k + 1 ≤ paperReserveIndex (k + 1) := by
  rw [paperReserveIndex, paperReserveIndex, Nat.add_one_le_ceil_iff]
  calc
    (⌈((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)⌉₊ : ℝ) <
        ((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    _ ≤ (((k + 1 + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) := by
      rw [show (((k + 1 + 1 : ℕ) : ℝ)) =
        ((k + 1 : ℕ) : ℝ) + 1 by push_cast; ring]
      exact rpow_three_halves_add_one_le_succ
        (show (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) by norm_cast; omega)

lemma paperReserveIndex_pos (k : ℕ) : 0 < paperReserveIndex k := by
  exact Nat.one_le_ceil_iff.mpr (by positivity)

noncomputable def reserveIndex (k : ℕ) : ℕ :=
  paperReserveIndex k - 1

lemma reserveIndex_succ (k : ℕ) :
    reserveIndex k < reserveIndex (k + 1) := by
  unfold reserveIndex
  have hk := paperReserveIndex_pos k
  have hks := paperReserveIndex_pos (k + 1)
  have hstep := paperReserveIndex_succ k
  omega

lemma reserveIndex_strictMono : StrictMono reserveIndex :=
  strictMono_nat_of_lt_succ reserveIndex_succ

lemma rpow_three_halves_le_iff_two_thirds
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (3 / 2 : ℝ) ≤ y ↔ x ≤ y ^ (2 / 3 : ℝ) := by
  constructor
  · intro h
    have hp := Real.rpow_le_rpow (by positivity) h
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
    calc
      x = (x ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_mul hx]
        norm_num
      _ ≤ y ^ (2 / 3 : ℝ) := hp
  · intro h
    have hp := Real.rpow_le_rpow hx h
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
    calc
      x ^ (3 / 2 : ℝ) ≤
          (y ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := hp
      _ = y := by
        rw [← Real.rpow_mul hy]
        norm_num

lemma paperReserveIndex_le_iff (k N : ℕ) :
    paperReserveIndex k ≤ N ↔
      k + 1 ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
  rw [paperReserveIndex, Nat.ceil_le]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (rpow_three_halves_le_iff_two_thirds
      (show 0 ≤ (((k + 1 : ℕ) : ℝ)) by positivity)
      (show 0 ≤ (N : ℝ) by positivity))

lemma reserveIndex_lt_iff (k N : ℕ) :
    reserveIndex k < N ↔
      k + 1 ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
  have hk := paperReserveIndex_pos k
  unfold reserveIndex
  rw [← paperReserveIndex_le_iff]
  omega

lemma reserveIndex_lt_iff_le_floor (k N : ℕ) :
    reserveIndex k < N ↔
      k + 1 ≤ ⌊(N : ℝ) ^ (2 / 3 : ℝ)⌋₊ := by
  rw [reserveIndex_lt_iff]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (Nat.le_floor_iff
      (n := k + 1) (a := (N : ℝ) ^ (2 / 3 : ℝ))
      (by positivity)).symm

def reserveSet : Set ℕ := Set.range reserveIndex

noncomputable def reserveIndicesBelow (N : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range N).filter fun n => n ∈ reserveSet

noncomputable def reserveCount (N : ℕ) : ℕ :=
  (reserveIndicesBelow N).card

lemma reserveIndicesBelow_eq_image (N : ℕ) :
    reserveIndicesBelow N =
      Finset.image reserveIndex
        (Finset.range ⌊(N : ℝ) ^ (2 / 3 : ℝ)⌋₊) := by
  classical
  ext n
  simp only [reserveIndicesBelow, Finset.mem_filter, Finset.mem_range,
    reserveSet, Set.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hn, k, rfl⟩
    refine ⟨k, ?_, rfl⟩
    rw [reserveIndex_lt_iff_le_floor] at hn
    omega
  · rintro ⟨k, hk, rfl⟩
    refine ⟨?_, k, rfl⟩
    rw [reserveIndex_lt_iff_le_floor]
    omega

theorem reserveCount_eq_floor (N : ℕ) :
    reserveCount N = ⌊(N : ℝ) ^ (2 / 3 : ℝ)⌋₊ := by
  classical
  rw [reserveCount, reserveIndicesBelow_eq_image,
    Finset.card_image_of_injective _ reserveIndex_strictMono.injective,
    Finset.card_range]

lemma reserveIndex_add_one (k : ℕ) :
    reserveIndex k + 1 = paperReserveIndex k := by
  unfold reserveIndex
  have hk := paperReserveIndex_pos k
  omega

lemma reserveIndex_add_one_cast_lower (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤
      (reserveIndex k + 1 : ℕ) := by
  rw [reserveIndex_add_one]
  exact Nat.le_ceil _

lemma reserve_denominator_lower (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) ^ (9 / 8 : ℝ) ≤
      ((reserveIndex k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
  have h := Real.rpow_le_rpow (by positivity)
    (reserveIndex_add_one_cast_lower k)
    (by norm_num : (0 : ℝ) ≤ 3 / 4)
  calc
    ((k + 1 : ℕ) : ℝ) ^ (9 / 8 : ℝ) =
        (((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_mul (by positivity)]
      norm_num
    _ ≤ ((reserveIndex k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := h

theorem summable_reserve_cost
    {v : ℕ → ℝ} (hv : ∀ n, 0 ≤ v n) (hanti : Antitone v)
    (hsum : Summable (fun n => v n ^ (4 / 3 : ℝ))) :
    Summable (fun k => v (reserveIndex k)) := by
  let A : ℝ := ∑' n : ℕ, v n ^ (4 / 3 : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact tsum_nonneg fun n => Real.rpow_nonneg (hv n) _
  have hprefix : ∀ n : ℕ,
      ((n + 1 : ℕ) : ℝ) * v n ^ (4 / 3 : ℝ) ≤ A := by
    intro n
    calc
      ((n + 1 : ℕ) : ℝ) * v n ^ (4 / 3 : ℝ) =
          ∑ _i ∈ Finset.range (n + 1), v n ^ (4 / 3 : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range (n + 1), v i ^ (4 / 3 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Real.rpow_le_rpow (hv n)
          (hanti (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
          (by norm_num)
      _ ≤ A := by
        exact hsum.sum_le_tsum _
          (fun i _ => Real.rpow_nonneg (hv i) _)
  have hpoint : ∀ n : ℕ,
      v n ≤ A ^ (3 / 4 : ℝ) /
        ((n + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
    intro n
    have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hdiv : v n ^ (4 / 3 : ℝ) ≤
        A / ((n + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hnpos]
      simpa [mul_comm] using hprefix n
    have hp := Real.rpow_le_rpow
      (Real.rpow_nonneg (hv n) _) hdiv
      (by norm_num : (0 : ℝ) ≤ 3 / 4)
    calc
      v n = (v n ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_mul (hv n)]
        norm_num
      _ ≤ (A / ((n + 1 : ℕ) : ℝ)) ^ (3 / 4 : ℝ) := hp
      _ = A ^ (3 / 4 : ℝ) /
          ((n + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
        rw [Real.div_rpow hA hnpos.le]
  have hbound : ∀ k : ℕ,
      v (reserveIndex k) ≤
        A ^ (3 / 4 : ℝ) /
          ((k + 1 : ℕ) : ℝ) ^ (9 / 8 : ℝ) := by
    intro k
    calc
      v (reserveIndex k) ≤
          A ^ (3 / 4 : ℝ) /
            ((reserveIndex k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) :=
        hpoint (reserveIndex k)
      _ ≤ A ^ (3 / 4 : ℝ) /
          ((k + 1 : ℕ) : ℝ) ^ (9 / 8 : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity)
          (by positivity) (reserve_denominator_lower k)
  have hmajor : Summable (fun k : ℕ =>
      A ^ (3 / 4 : ℝ) /
        ((k + 1 : ℕ) : ℝ) ^ (9 / 8 : ℝ)) := by
    have hp : Summable (fun n : ℕ =>
        1 / (n : ℝ) ^ (9 / 8 : ℝ)) :=
      Real.summable_one_div_nat_rpow.mpr (by norm_num)
    have hshift := (summable_nat_add_iff 1).mpr hp
    simpa only [div_eq_mul_inv, one_mul, Nat.cast_add,
      Nat.cast_one] using hshift.mul_left (A ^ (3 / 4 : ℝ))
  exact Summable.of_nonneg_of_le
    (fun k => hv (reserveIndex k)) hbound hmajor

end Shepp.Section6
end SheppFlattenedModule069

section SheppFlattenedModule070
open scoped ENNReal NNReal Topology
open Filter Set MeasureTheory

namespace Shepp.Section6

open Shepp.Section2

theorem flatTorusOverlapTerm_nonneg
    (d : ℕ) (r : ℕ → ℝ) (n : ℕ) (z : FlatTorus d) :
    0 ≤ flatTorusOverlapTerm d r n z := by
  unfold flatTorusOverlapTerm
  positivity

theorem flatTorusOverlapTerm_le_radiusVolume
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrsmall : ∀ n, r n < 1 / 4)
    (n : ℕ) (z : FlatTorus d) :
    flatTorusOverlapTerm d r n z ≤ radiusVolume d r n := by
  calc
    flatTorusOverlapTerm d r n z ≤
        (flatTorusVolume d).real (Metric.ball (0 : FlatTorus d) (r n)) := by
      unfold flatTorusOverlapTerm flatTorusBallLens
      exact measureReal_mono Set.inter_subset_left
    _ = MeasureTheory.volume.real
        (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r n)) := by
      rw [show (0 : FlatTorus d) =
        flatTorusMk d (0 : EuclideanSpace ℝ (Fin d)) by rfl]
      rw [Measure.real,
        flatTorusVolume_ball_eq_volume
          d (c := (0 : EuclideanSpace ℝ (Fin d))) (hrsmall n)]
      rfl
    _ = radiusVolume d r n := by
      rw [volumeReal_euclideanBall d hd (r n) (hr n)]
      unfold radiusVolume
      ring

theorem radiusVolume_nonneg
    (d : ℕ) {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) (n : ℕ) :
    0 ≤ radiusVolume d r n := by
  unfold radiusVolume
  exact mul_nonneg (euclideanUnitBallVolume_pos d).le
    (pow_nonneg (hr n) d)

theorem radiusVolume_antitone
    (d : ℕ) {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n)
    (hanti : Antitone r) : Antitone (radiusVolume d r) := by
  intro a b hab
  unfold radiusVolume
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (hr b) (hanti hab) d)
    (euclideanUnitBallVolume_pos d).le

noncomputable def reserveCost (d : ℕ) (r : ℕ → ℝ) : ℝ :=
  ∑' k, radiusVolume d r (reserveIndex k)

noncomputable def reserveOverlapEnergy
    (d : ℕ) (r : ℕ → ℝ) (z : FlatTorus d) : ℝ≥0∞ :=
  ∑' k, ENNReal.ofReal
    (flatTorusOverlapTerm d r (reserveIndex k) z)

noncomputable def retainedOverlapEnergy
    (d : ℕ) (r : ℕ → ℝ) (z : FlatTorus d) : ℝ≥0∞ :=
  ∑' n : (reserveSetᶜ : Set ℕ),
    ENNReal.ofReal (flatTorusOverlapTerm d r n z)

noncomputable def retainedOverlapEnergyExp
    (d : ℕ) (r : ℕ → ℝ) (z : FlatTorus d) : ℝ≥0∞ :=
  EReal.exp (retainedOverlapEnergy d r z : EReal)

noncomputable def reserveEquiv : ℕ ≃ reserveSet :=
  Equiv.ofInjective reserveIndex reserveIndex_strictMono.injective

@[simp] theorem reserveEquiv_apply (k : ℕ) :
    (reserveEquiv k : ℕ) = reserveIndex k := by
  rfl

theorem reserveCost_nonneg
    (d : ℕ) {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) :
    0 ≤ reserveCost d r := by
  unfold reserveCost
  exact tsum_nonneg fun k =>
    radiusVolume_nonneg d hr (reserveIndex k)

theorem reserveOverlapEnergy_le_cost
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hsum : Summable (fun n => radiusVolume d r n ^ (4 / 3 : ℝ)))
    (hanti : Antitone r) (z : FlatTorus d) :
    reserveOverlapEnergy d r z ≤ ENNReal.ofReal (reserveCost d r) := by
  have hcost : Summable (fun k => radiusVolume d r (reserveIndex k)) :=
    summable_reserve_cost
      (fun n => radiusVolume_nonneg d hr n)
      (radiusVolume_antitone d hr hanti) hsum
  rw [reserveOverlapEnergy, reserveCost,
    ENNReal.ofReal_tsum_of_nonneg
      (fun k => radiusVolume_nonneg d hr (reserveIndex k)) hcost]
  apply ENNReal.tsum_le_tsum
  intro k
  exact ENNReal.ofReal_le_ofReal
    (flatTorusOverlapTerm_le_radiusVolume
      d hd hr hrsmall (reserveIndex k) z)

set_option maxHeartbeats 800000 in

theorem flatTorusOverlapEnergy_le_reserve_add_retained
    (d : ℕ) (r : ℕ → ℝ) (z : FlatTorus d) :
    flatTorusOverlapEnergy d r z ≤
      reserveOverlapEnergy d r z + retainedOverlapEnergy d r z := by
  let f : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (flatTorusOverlapTerm d r n z)
  have hpartition := ENNReal.tsum_union_le f reserveSet reserveSetᶜ
  have hunion : reserveSet ∪ reserveSetᶜ = Set.univ :=
    Set.union_compl_self reserveSet
  rw [hunion] at hpartition
  change (∑' n : (Set.univ : Set ℕ), f n.1) ≤ _ at hpartition
  have huniv : (∑' n : (Set.univ : Set ℕ), f n.1) =
      ∑' n : ℕ, f n := by
    exact (Equiv.Set.univ ℕ).tsum_eq f
  rw [huniv] at hpartition
  have hreserve : (∑' n : reserveSet, f n) =
      reserveOverlapEnergy d r z := by
    rw [← reserveEquiv.tsum_eq]
    rfl
  simpa only [flatTorusOverlapEnergy, retainedOverlapEnergy,
    hreserve, f] using hpartition

theorem flatTorusOverlapEnergy_le_cost_add_retained
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hsum : Summable (fun n => radiusVolume d r n ^ (4 / 3 : ℝ)))
    (hanti : Antitone r) (z : FlatTorus d) :
    flatTorusOverlapEnergy d r z ≤
      ENNReal.ofReal (reserveCost d r) + retainedOverlapEnergy d r z := by
  calc
    flatTorusOverlapEnergy d r z ≤
        reserveOverlapEnergy d r z + retainedOverlapEnergy d r z :=
      flatTorusOverlapEnergy_le_reserve_add_retained d r z
    _ ≤ ENNReal.ofReal (reserveCost d r) +
        retainedOverlapEnergy d r z := by
      gcongr
      exact reserveOverlapEnergy_le_cost
        d hd hr hrsmall hsum hanti z

theorem measurable_retainedOverlapEnergy
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4) :
    Measurable (retainedOverlapEnergy d r) := by
  apply Measurable.tsum
  intro n
  have heq : flatTorusOverlapTerm d r n =
      fun z => radialOverlapTerm d r n (dist 0 z) := by
    funext z
    exact flatTorusOverlapTerm_eq_radialOverlapTerm
      d hd hr hrsmall n z
  apply ENNReal.measurable_ofReal.comp
  rw [heq]
  exact (measurable_radialOverlapTerm d r n).comp
    (measurable_dist_zero_flatTorus d)

theorem measurable_retainedOverlapEnergyExp
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4) :
    Measurable (retainedOverlapEnergyExp d r) := by
  exact EReal.measurable_exp.comp
    (measurable_coe_ennreal_ereal.comp
      (measurable_retainedOverlapEnergy d hd hr hrsmall))

theorem flatTorusOverlapEnergyExp_le_cost_mul_retained
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hsum : Summable (fun n => radiusVolume d r n ^ (4 / 3 : ℝ)))
    (hanti : Antitone r) (z : FlatTorus d) :
    flatTorusOverlapEnergyExp d r z ≤
      EReal.exp ((ENNReal.ofReal (reserveCost d r) : ℝ≥0∞) : EReal) *
        retainedOverlapEnergyExp d r z := by
  rw [flatTorusOverlapEnergyExp, retainedOverlapEnergyExp,
    ← EReal.exp_add]
  apply EReal.exp_monotone
  rw [← EReal.coe_ennreal_add]
  exact EReal.coe_ennreal_le_coe_ennreal_iff.2
    (flatTorusOverlapEnergy_le_cost_add_retained
      d hd hr hrsmall hsum hanti z)

theorem lintegral_retainedOverlapEnergyExp_eq_top
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hsum : Summable (fun n => radiusVolume d r n ^ (4 / 3 : ℝ)))
    (hanti : Antitone r)
    (htop :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞) :
    (∫⁻ z : FlatTorus d,
      retainedOverlapEnergyExp d r z ∂(flatTorusVolume d)) = ∞ := by
  let c : ℝ≥0∞ :=
    EReal.exp ((ENNReal.ofReal (reserveCost d r) : ℝ≥0∞) : EReal)
  have hfull :
      (∫⁻ z : FlatTorus d,
        flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) = ∞ := by
    rw [lintegral_flatTorusOverlapEnergyExp_eq_real
      d hd hr hrsmall hrlim]
    exact htop
  have hmono :
      (∫⁻ z : FlatTorus d,
        flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)) ≤
      ∫⁻ z : FlatTorus d,
        c * retainedOverlapEnergyExp d r z ∂(flatTorusVolume d) := by
    apply lintegral_mono
    intro z
    exact flatTorusOverlapEnergyExp_le_cost_mul_retained
      d (by omega) (fun n => (hr n).le) hrsmall hsum hanti z
  rw [hfull] at hmono
  have hprod :
      (∫⁻ z : FlatTorus d,
        c * retainedOverlapEnergyExp d r z ∂(flatTorusVolume d)) = ∞ :=
    top_unique hmono
  have hmeas := measurable_retainedOverlapEnergyExp d hd hr hrsmall
  rw [lintegral_const_mul c hmeas] at hprod
  have hc : c ≠ ∞ := by
    intro hcTop
    have harg := EReal.exp_eq_top_iff.mp hcTop
    exact ENNReal.ofReal_ne_top
      (EReal.coe_ennreal_eq_top_iff.mp harg)
  rcases ENNReal.mul_eq_top.mp hprod with hretained | hconstant
  · exact hretained.2
  · exact (hc hconstant.1).elim

end Shepp.Section6
end SheppFlattenedModule070

section SheppFlattenedModule071
open scoped ENNReal NNReal Topology
open Filter Set

namespace Shepp.Section6

open Shepp.Section2

noncomputable def retainedIndicesBelow (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun n => n ∉ reserveSet

theorem retained_reserve_count (N : ℕ) :
    (retainedIndicesBelow N).card + reserveCount N = N := by
  classical
  rw [retainedIndicesBelow, reserveCount, reserveIndicesBelow]
  simpa [Finset.card_range] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.range N) (p := fun n => n ∉ reserveSet))

lemma cube_two_thirds (M : ℕ) :
    (((M ^ 3 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) = (M : ℝ) ^ 2 := by
  push_cast
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ M)]
  norm_num

lemma floor_cube_two_thirds (M : ℕ) :
    ⌊(((M ^ 3 : ℕ) : ℝ) ^ (2 / 3 : ℝ))⌋₊ = M ^ 2 := by
  rw [cube_two_thirds]
  rw [show (M : ℝ) ^ 2 = ((M ^ 2 : ℕ) : ℝ) by norm_cast]
  exact Nat.floor_natCast (M ^ 2)

theorem retained_count_cube (M : ℕ) :
    (retainedIndicesBelow (M ^ 3)).card + M ^ 2 = M ^ 3 := by
  rw [← floor_cube_two_thirds M]
  simpa only [reserveCount_eq_floor] using
    retained_reserve_count (M ^ 3)

lemma cube_gap (B : ℕ) :
    B + 1 < (B + 2) ^ 3 - (B + 2) ^ 2 := by
  have heq : (B + 2) ^ 3 =
      (B + 2) ^ 2 + (B + 2) ^ 2 * (B + 1) := by ring
  rw [heq, Nat.add_sub_cancel_left]
  have hsq : 2 ≤ (B + 2) ^ 2 := by
    calc
      2 ≤ 2 ^ 2 := by norm_num
      _ ≤ (B + 2) ^ 2 := by gcongr <;> omega
  calc
    B + 1 < 2 * (B + 1) := by omega
    _ ≤ (B + 2) ^ 2 * (B + 1) :=
      Nat.mul_le_mul_right (B + 1) hsq

theorem reserve_compl_infinite : reserveSetᶜ.Infinite := by
  classical
  apply Set.infinite_of_forall_exists_gt
  intro B
  let M : ℕ := B + 2
  let N : ℕ := M ^ 3
  have hcount := retained_count_cube M
  have hgap : B + 1 < N - M ^ 2 := by
    simpa only [M, N] using cube_gap B
  have hcard : (retainedIndicesBelow N).card = N - M ^ 2 := by
    have hcountN : (retainedIndicesBelow N).card + M ^ 2 = M ^ 3 := by
      simpa only [N] using hcount
    have hcard' : (retainedIndicesBelow N).card =
        M ^ 3 - M ^ 2 := by omega
    simpa only [N] using hcard'
  have hlarge : B + 1 < (retainedIndicesBelow N).card := by
    rwa [hcard]
  have hex : ∃ n ∈ retainedIndicesBelow N, B < n := by
    by_contra h
    push Not at h
    have hsubset : retainedIndicesBelow N ⊆ Finset.range (B + 1) := by
      intro n hn
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h n hn))
    have hle := Finset.card_le_card hsubset
    simp only [Finset.card_range] at hle
    omega
  obtain ⟨n, hn, hBn⟩ := hex
  refine ⟨n, ?_, hBn⟩
  have hn' := hn
  simp [retainedIndicesBelow] at hn'
  change n ∉ reserveSet
  exact hn'.2

noncomputable def retainedIndex (k : ℕ) : ℕ :=
  Nat.nth (fun n => n ∉ reserveSet) k

theorem retainedIndex_strictMono : StrictMono retainedIndex :=
  Nat.nth_strictMono (by
    simpa [Set.compl_def] using reserve_compl_infinite)

theorem retainedIndex_monotone : Monotone retainedIndex :=
  retainedIndex_strictMono.monotone

theorem retainedIndex_mem (k : ℕ) : retainedIndex k ∉ reserveSet :=
  Nat.nth_mem_of_infinite (by
    simpa [Set.compl_def] using reserve_compl_infinite) k

theorem range_retainedIndex : Set.range retainedIndex = reserveSetᶜ := by
  calc
    Set.range retainedIndex = {n : ℕ | n ∉ reserveSet} :=
      Nat.range_nth_of_infinite (by
        simpa [Set.compl_def] using reserve_compl_infinite)
    _ = reserveSetᶜ := by ext n; simp

theorem retainedIndex_le (k : ℕ) : k ≤ retainedIndex k :=
  retainedIndex_strictMono.id_le k

theorem retainedIndex_tendsto_atTop :
    Tendsto retainedIndex atTop atTop :=
  retainedIndex_strictMono.tendsto_atTop

noncomputable def retainedEquiv : ℕ ≃ (reserveSetᶜ : Set ℕ) :=
  Equiv.ofBijective
    (fun k => ⟨retainedIndex k, by
      change retainedIndex k ∉ reserveSet
      exact retainedIndex_mem k⟩)
    ⟨fun _ _ h => retainedIndex_strictMono.injective
        (Subtype.ext_iff.mp h),
      fun n => by
        have hn : (n : ℕ) ∈ Set.range retainedIndex := by
          rw [range_retainedIndex]
          exact n.property
        obtain ⟨k, hk⟩ := hn
        exact ⟨k, Subtype.ext hk⟩⟩

@[simp] theorem retainedEquiv_apply (k : ℕ) :
    (retainedEquiv k : ℕ) = retainedIndex k := by
  rfl

noncomputable def retainedRadius (r : ℕ → ℝ) (k : ℕ) : ℝ :=
  r (retainedIndex k)

theorem retainedRadius_pos {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (k : ℕ) :
    0 < retainedRadius r k := hr _

theorem retainedRadius_lt_quarter {r : ℕ → ℝ}
    (hrsmall : ∀ n, r n < 1 / 4) (k : ℕ) :
    retainedRadius r k < 1 / 4 := hrsmall _

theorem retainedRadius_antitone {r : ℕ → ℝ}
    (hanti : Antitone r) : Antitone (retainedRadius r) := by
  intro a b hab
  exact hanti (retainedIndex_monotone hab)

theorem retainedRadius_tendsto_zero {r : ℕ → ℝ}
    (hrlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (retainedRadius r) atTop (𝓝 0) :=
  hrlim.comp retainedIndex_tendsto_atTop

theorem flatTorusOverlapEnergy_retainedRadius
    (d : ℕ) (r : ℕ → ℝ) (z : FlatTorus d) :
    flatTorusOverlapEnergy d (retainedRadius r) z =
      retainedOverlapEnergy d r z := by
  unfold flatTorusOverlapEnergy retainedOverlapEnergy
  rw [← retainedEquiv.tsum_eq]
  rfl

theorem flatTorusOverlapSum_retainedRadius
    (d : ℕ) (r : ℕ → ℝ) (z : FlatTorus d) :
    flatTorusOverlapSum d (retainedRadius r) z =
      ∑' n : (reserveSetᶜ : Set ℕ),
        flatTorusOverlapTerm d r n z := by
  unfold flatTorusOverlapSum
  rw [← retainedEquiv.tsum_eq]
  rfl

theorem flatTorusOverlapEnergyExp_retainedRadius
    (d : ℕ) (r : ℕ → ℝ) (z : FlatTorus d) :
    flatTorusOverlapEnergyExp d (retainedRadius r) z =
      retainedOverlapEnergyExp d r z := by
  rw [flatTorusOverlapEnergyExp, retainedOverlapEnergyExp,
    flatTorusOverlapEnergy_retainedRadius]

theorem lintegral_retainedRadius_overlapSumExp_eq_top
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hsum : Summable (fun n => radiusVolume d r n ^ (4 / 3 : ℝ)))
    (hanti : Antitone r)
    (htop :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞) :
    (∫⁻ z : FlatTorus d,
      ENNReal.ofReal (Real.exp
        (flatTorusOverlapSum d (retainedRadius r) z))
        ∂(flatTorusVolume d)) = ∞ := by
  have hretained := lintegral_retainedOverlapEnergyExp_eq_top
    d hd hr hrsmall hrlim hsum hanti htop
  have hext :
      (∫⁻ z : FlatTorus d,
        flatTorusOverlapEnergyExp d (retainedRadius r) z
          ∂(flatTorusVolume d)) = ∞ := by
    simpa only [flatTorusOverlapEnergyExp_retainedRadius] using hretained
  rw [lintegral_flatTorusOverlapEnergyExp_eq_real
    d hd (retainedRadius_pos hr)
    (retainedRadius_lt_quarter hrsmall)
    (retainedRadius_tendsto_zero hrlim)] at hext
  exact hext

end Shepp.Section6
end SheppFlattenedModule071

section SheppFlattenedModule072
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators
open Filter Set MeasureTheory

namespace Shepp.Section6

open ProbabilityTheory Shepp.Section3

noncomputable def retainedCount (N : ℕ) : ℕ := by
  classical
  exact Nat.count (fun n => n ∉ reserveSet) N

theorem retainedCount_eq_card (N : ℕ) :
    retainedCount N = (retainedIndicesBelow N).card := by
  classical
  rw [retainedCount, Nat.count_eq_card_filter_range]
  rfl

theorem retainedCount_add_reserveCount (N : ℕ) :
    retainedCount N + reserveCount N = N := by
  rw [retainedCount_eq_card]
  exact retained_reserve_count N

theorem retainedCount_eq_sub (N : ℕ) :
    retainedCount N = N - reserveCount N := by
  have h := retainedCount_add_reserveCount N
  omega

theorem retainedIndex_lt_iff_count (k N : ℕ) :
    retainedIndex k < N ↔ k < retainedCount N := by
  classical
  have hinf : {n : ℕ | n ∉ reserveSet}.Infinite := by
    simpa [Set.compl_def] using reserve_compl_infinite
  exact (Nat.lt_nth_iff_count_lt hinf).symm

abbrev RetainedPoissonCountSample := ℕ → ℕ

noncomputable def retainedPoissonCountMeasure :
    Measure RetainedPoissonCountSample :=
  Measure.infinitePi fun _ : ℕ => poissonMeasure 1

noncomputable instance retainedPoissonCountMeasure_isProbabilityMeasure :
    IsProbabilityMeasure retainedPoissonCountMeasure := by
  unfold retainedPoissonCountMeasure
  infer_instance

theorem retainedCountCoordinates_iIndepFun :
    iIndepFun (fun k (P : RetainedPoissonCountSample) => P k)
      retainedPoissonCountMeasure := by
  unfold retainedPoissonCountMeasure
  exact iIndepFun_infinitePi (X := fun _n x => x)
    (fun _n => measurable_id)

theorem retainedCountCoordinate_hasLaw (k : ℕ) :
    HasLaw (fun P : RetainedPoissonCountSample => P k)
      (poissonMeasure 1) retainedPoissonCountMeasure := by
  refine ⟨(measurable_pi_apply k).aemeasurable, ?_⟩
  unfold retainedPoissonCountMeasure
  exact Measure.infinitePi_map_eval (fun _ : ℕ => poissonMeasure 1) k

noncomputable def cumulativeRetainedCount
    (N : ℕ) (P : RetainedPoissonCountSample) : ℕ :=
  ∑ k ∈ Finset.range (retainedCount N), P k

theorem cumulativeRetainedCount_hasLaw (N : ℕ) :
    HasLaw (cumulativeRetainedCount N)
      (poissonMeasure ((retainedCount N : ℕ) : NNReal))
      retainedPoissonCountMeasure := by
  have h := hasLaw_finsetSum_poisson
    retainedCountCoordinates_iIndepFun
    (fun k => retainedCountCoordinate_hasLaw k)
    (Finset.range (retainedCount N))
  have h' : HasLaw
      (∑ k ∈ Finset.range (retainedCount N),
        fun P : RetainedPoissonCountSample => P k)
      (poissonMeasure ((retainedCount N : ℕ) : NNReal))
      retainedPoissonCountMeasure := by
    simpa using h
  exact h'.congr (Filter.Eventually.of_forall fun P => by
    simp only [cumulativeRetainedCount, Finset.sum_apply])

theorem reserveCount_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < reserveCount N := by
  rw [reserveCount_eq_floor]
  apply (Nat.one_le_floor_iff
    ((N : ℝ) ^ (2 / 3 : ℝ))).mpr
  calc
    (1 : ℝ) = (1 : ℝ) ^ (2 / 3 : ℝ) := by norm_num
    _ ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
      apply Real.rpow_le_rpow (by norm_num)
        (by exact_mod_cast hN) (by norm_num)

theorem reserveCount_le (N : ℕ) : reserveCount N ≤ N := by
  have h := retained_reserve_count N
  omega

lemma rpow_ratio_two_thirds (N : ℕ) (hN : 0 < N) :
    ((((N : ℝ) ^ (2 / 3 : ℝ) / 2) ^ 2) /
        (4 * (N : ℝ))) =
      (1 / 16 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpow : ((N : ℝ) ^ (2 / 3 : ℝ)) ^ 2 =
      (N : ℝ) ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast hNr.le]
    norm_num
  have hdiv : (N : ℝ) ^ (4 / 3 : ℝ) / (N : ℝ) =
      (N : ℝ) ^ (1 / 3 : ℝ) := by
    calc
      (N : ℝ) ^ (4 / 3 : ℝ) / (N : ℝ) =
          (N : ℝ) ^ (4 / 3 : ℝ) / (N : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((4 / 3 : ℝ) - 1) := by
        rw [Real.rpow_sub hNr]
      _ = (N : ℝ) ^ (1 / 3 : ℝ) := by norm_num
  calc
    ((((N : ℝ) ^ (2 / 3 : ℝ) / 2) ^ 2) /
          (4 * (N : ℝ))) =
        (1 / 16 : ℝ) *
          ((N : ℝ) ^ (4 / 3 : ℝ) / (N : ℝ)) := by
      rw [div_pow, hpow]
      ring
    _ = (1 / 16 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) := by
      rw [hdiv]

theorem reserve_exponent_lower {N : ℕ} (hN : 1 ≤ N) :
    (1 / 16 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) ≤
      (reserveCount N : ℝ) ^ 2 / (4 * (N : ℝ)) := by
  let x : ℝ := (N : ℝ) ^ (2 / 3 : ℝ)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    calc
      (1 : ℝ) = (1 : ℝ) ^ (2 / 3 : ℝ) := by norm_num
      _ ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
        apply Real.rpow_le_rpow (by norm_num)
          (by exact_mod_cast hN) (by norm_num)
  have hD : x / 2 < (reserveCount N : ℝ) := by
    rw [reserveCount_eq_floor]
    exact Nat.div_two_lt_floor hx1
  rw [← rpow_ratio_two_thirds N (by omega)]
  have hx0 : 0 ≤ x / 2 := by
    dsimp [x]
    positivity
  have hsquare : (x / 2) ^ 2 ≤ (reserveCount N : ℝ) ^ 2 := by
    nlinarith
  exact div_le_div_of_nonneg_right hsquare (by positivity)

noncomputable def countOverflowEvent (N : ℕ) :
    Set RetainedPoissonCountSample :=
  {P | N < cumulativeRetainedCount N P}

theorem countOverflow_measure_le (N : ℕ) :
    retainedPoissonCountMeasure (countOverflowEvent N) ≤
      ENNReal.ofReal
        (Real.exp (-(1 / 16 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ))) := by
  by_cases hN0 : N = 0
  · subst N
    have hcount0 : retainedCount 0 = 0 := by
      have h := retainedCount_add_reserveCount 0
      omega
    simp [countOverflowEvent, cumulativeRetainedCount, hcount0]
  · have hN : 1 ≤ N := (Nat.one_le_iff_ne_zero).2 hN0
    let D : ℕ := reserveCount N
    have hD : 0 < D := reserveCount_pos hN
    have hDN : D ≤ N := reserveCount_le N
    have hlaw : HasLaw (cumulativeRetainedCount N)
        (poissonMeasure (((N - D : ℕ) : NNReal)))
        retainedPoissonCountMeasure := by
      simpa only [D, retainedCount_eq_sub] using
        cumulativeRetainedCount_hasLaw N
    let A : Set ℕ := {k | N < k}
    let B : Set ℕ := {k | (N : ℝ) ≤ (k : ℝ)}
    have hmeasure :
        retainedPoissonCountMeasure (countOverflowEvent N) =
          poissonMeasure (((N - D : ℕ) : NNReal)) A := by
      have h := hlaw.measure_eq (p := fun k => k ∈ A)
        MeasurableSet.of_discrete
      simpa only [countOverflowEvent, A, Set.mem_setOf_eq] using h
    have hAB : A ⊆ B := by
      intro k hk
      change N < k at hk
      change (N : ℝ) ≤ (k : ℝ)
      exact_mod_cast hk.le
    have htail := poisson_deficit_upper_tail hD hDN
    change (poissonMeasure (((N - D : ℕ) : NNReal))).real B ≤
      Real.exp (-((D : ℝ) ^ 2 / (4 * (N : ℝ)))) at htail
    calc
      retainedPoissonCountMeasure (countOverflowEvent N) =
          poissonMeasure (((N - D : ℕ) : NNReal)) A := hmeasure
      _ ≤ poissonMeasure (((N - D : ℕ) : NNReal)) B := measure_mono hAB
      _ = ENNReal.ofReal
          ((poissonMeasure (((N - D : ℕ) : NNReal))).real B) :=
        (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (4 * (N : ℝ))))) :=
        ENNReal.ofReal_le_ofReal htail
      _ ≤ ENNReal.ofReal
          (Real.exp (-(1 / 16 : ℝ) *
            (N : ℝ) ^ (1 / 3 : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hlower := reserve_exponent_lower hN
        dsimp [D]
        nlinarith

theorem countOverflow_tsum_ne_top :
    (∑' N : ℕ,
      retainedPoissonCountMeasure (countOverflowEvent N)) ≠ ∞ := by
  let g : ℕ → ℝ := fun N =>
    Real.exp (-(1 / 16 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ))
  have hg : Summable g :=
    summable_stretched_exponential
      (c := (1 / 16 : ℝ)) (p := (1 / 3 : ℝ))
      (by norm_num) (by norm_num)
  have hnonneg : ∀ N, 0 ≤ g N := fun N => (Real.exp_pos _).le
  have hle :
      (∑' N : ℕ,
        retainedPoissonCountMeasure (countOverflowEvent N)) ≤
      ∑' N : ℕ, ENNReal.ofReal (g N) := by
    apply ENNReal.tsum_le_tsum
    intro N
    exact countOverflow_measure_le N
  have hfinite : (∑' N : ℕ, ENNReal.ofReal (g N)) < ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hg]
    exact ENNReal.ofReal_lt_top
  exact (lt_of_le_of_lt hle hfinite).ne

theorem ae_eventually_cumulativeRetainedCount_le :
    ∀ᵐ P : RetainedPoissonCountSample ∂retainedPoissonCountMeasure,
      ∀ᶠ N : ℕ in atTop, cumulativeRetainedCount N P ≤ N := by
  filter_upwards [ae_eventually_notMem countOverflow_tsum_ne_top] with P hP
  filter_upwards [hP] with N hN
  change ¬N < cumulativeRetainedCount N P at hN
  exact Nat.le_of_not_gt hN

end Shepp.Section6
end SheppFlattenedModule072

section SheppFlattenedModule073
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators
open Filter Set MeasureTheory

namespace Shepp.Section6

open ProbabilityTheory Shepp.Section2 Shepp.Section3 Shepp.Section4
  Shepp.Section5 TopologicalSpace

noncomputable def retainedAtomPrefix
    (P : RetainedPoissonCountSample) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, P i

@[simp]
theorem retainedAtomPrefix_zero (P : RetainedPoissonCountSample) :
    retainedAtomPrefix P 0 = 0 := by
  simp [retainedAtomPrefix]

theorem retainedAtomPrefix_succ
    (P : RetainedPoissonCountSample) (k : ℕ) :
    retainedAtomPrefix P (k + 1) = retainedAtomPrefix P k + P k := by
  simp [retainedAtomPrefix, Finset.sum_range_succ]

theorem retainedAtomPrefix_mono (P : RetainedPoissonCountSample) :
    Monotone (retainedAtomPrefix P) := by
  intro k l hkl
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih =>
      rw [retainedAtomPrefix_succ]
      exact ih.trans (Nat.le_add_right _ _)

theorem measurable_retainedAtomPrefix (k : ℕ) :
    Measurable fun P : RetainedPoissonCountSample => retainedAtomPrefix P k := by
  unfold retainedAtomPrefix
  exact Finset.measurable_fun_sum (Finset.range k) fun i _ =>
    measurable_pi_apply i

abbrev RetainedRankAtom
    (P : RetainedPoissonCountSample) (K : ℕ) :=
  (k : Fin K) × Fin (P k)

noncomputable def retainedAtomRank
    (P : RetainedPoissonCountSample) {K : ℕ}
    (a : RetainedRankAtom P K) : ℕ :=
  retainedAtomPrefix P a.1 + a.2

theorem retainedAtomRank_lt_prefix_succ
    (P : RetainedPoissonCountSample) {K : ℕ}
    (a : RetainedRankAtom P K) :
    retainedAtomRank P a < retainedAtomPrefix P (a.1 + 1) := by
  rw [retainedAtomRank, retainedAtomPrefix_succ]
  omega

theorem retainedAtomRank_injective
    (P : RetainedPoissonCountSample) (K : ℕ) :
    Function.Injective (retainedAtomRank P : RetainedRankAtom P K -> ℕ) := by
  rintro ⟨k, i⟩ ⟨l, j⟩ h
  change retainedAtomPrefix P k + i = retainedAtomPrefix P l + j at h
  have hklt : retainedAtomPrefix P k + i < retainedAtomPrefix P (k + 1) := by
    rw [retainedAtomPrefix_succ]
    omega
  have hllt : retainedAtomPrefix P l + j < retainedAtomPrefix P (l + 1) := by
    rw [retainedAtomPrefix_succ]
    omega
  have hkl : k = l := by
    apply le_antisymm
    · by_contra hnot
      have hlk : l < k := by omega
      have hmono : retainedAtomPrefix P (l + 1) ≤
          retainedAtomPrefix P k :=
        retainedAtomPrefix_mono P (by omega)
      omega
    · by_contra hnot
      have hkl' : k < l := by omega
      have hmono : retainedAtomPrefix P (k + 1) ≤
          retainedAtomPrefix P l :=
        retainedAtomPrefix_mono P (by omega)
      omega
  subst l
  have hij : i = j := by
    apply Fin.ext
    omega
  subst j
  rfl

theorem measurable_natSequence_apply
    {α : Type*} [MeasurableSpace α] :
    Measurable fun p : (ℕ -> α) × ℕ => p.1 p.2 := by
  intro E hE
  have heq :
      (fun p : (ℕ -> α) × ℕ => p.1 p.2) ⁻¹' E =
        ⋃ n : ℕ, ((fun X : ℕ -> α => X n) ⁻¹' E) ×ˢ ({n} : Set ℕ) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod,
      Set.mem_singleton_iff]
    constructor
    · intro hp
      exact ⟨p.2, hp, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact hn
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    ((measurable_pi_apply n hE).prod (MeasurableSet.singleton n))

abbrev RankCouplingSample (d : ℕ) :=
  RetainedPoissonCountSample × IIDCenterSample d

noncomputable def rankCouplingMeasure (d : ℕ) :
    Measure (RankCouplingSample d) :=
  retainedPoissonCountMeasure.prod (iidCenterMeasure d)

noncomputable instance rankCouplingMeasure_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (rankCouplingMeasure d) := by
  unfold rankCouplingMeasure
  infer_instance

noncomputable def rankCoupledCloud
    {d : ℕ} (k : ℕ) (ω : RankCouplingSample d) :
    PoissonCloudSample (FlatTorus d) :=
  (ω.1 k, fun i => ω.2 (retainedAtomPrefix ω.1 k + i))

theorem measurable_rankCoupledCloud {d k : ℕ} :
    Measurable (rankCoupledCloud (d := d) k) := by
  apply Measurable.prodMk
  · exact (measurable_pi_apply k).comp measurable_fst
  · apply measurable_pi_lambda
    intro i
    have hpair : Measurable fun c : RankCouplingSample d =>
        (c.2, retainedAtomPrefix c.1 k + i) := by
      apply Measurable.prodMk
      · exact measurable_snd
      · exact (measurable_retainedAtomPrefix k).comp measurable_fst |>.add measurable_const
    change Measurable ((fun p : (ℕ -> FlatTorus d) × ℕ => p.1 p.2) ∘
      fun c : RankCouplingSample d =>
        (c.2, retainedAtomPrefix c.1 k + i))
    exact measurable_natSequence_apply.comp hpair

noncomputable def rankCoupledSupport
    {d : ℕ} (k : ℕ) (ω : RankCouplingSample d) :
    CompactResidual (FlatTorus d) :=
  cloudSupport (rankCoupledCloud k ω)

theorem measurable_rankCoupledSupport
    {d : ℕ} {r : ℕ -> ℝ}
    (Q : GeometricPacketInterface d r) (k : ℕ) :
    Measurable (rankCoupledSupport (d := d) k) := by
  letI : CompactSpace (FlatTorus d) := flatTorusCompactSpaceOfInterface Q
  exact measurable_cloudSupport.comp measurable_rankCoupledCloud

noncomputable def rankCoupledSupports
    {d : ℕ} (ω : RankCouplingSample d) : FullPoissonSupportSample d :=
  fun k => rankCoupledSupport k ω

theorem measurable_rankCoupledSupports
    {d : ℕ} {r : ℕ -> ℝ}
    (Q : GeometricPacketInterface d r) :
    Measurable (rankCoupledSupports (d := d)) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_rankCoupledSupport Q k

abbrev RetainedRankAtomOn
    (P : RetainedPoissonCountSample) (s : Finset ℕ) :=
  (k : s) × Fin (P k)

noncomputable def retainedAtomRankOn
    (P : RetainedPoissonCountSample) {s : Finset ℕ}
    (a : RetainedRankAtomOn P s) : ℕ :=
  retainedAtomPrefix P a.1 + a.2

theorem retainedAtomRankOn_injective
    (P : RetainedPoissonCountSample) (s : Finset ℕ) :
    Function.Injective
      (retainedAtomRankOn P : RetainedRankAtomOn P s -> ℕ) := by
  rintro ⟨k, i⟩ ⟨l, j⟩ h
  change retainedAtomPrefix P k + i = retainedAtomPrefix P l + j at h
  have hklt : retainedAtomPrefix P k + i <
      retainedAtomPrefix P (k + 1) := by
    rw [retainedAtomPrefix_succ]
    omega
  have hllt : retainedAtomPrefix P l + j <
      retainedAtomPrefix P (l + 1) := by
    rw [retainedAtomPrefix_succ]
    omega
  have hkl : (k : ℕ) = l := by
    apply le_antisymm
    · by_contra hnot
      have hlk : (l : ℕ) < k := by omega
      have hmono : retainedAtomPrefix P (l + 1) ≤
          retainedAtomPrefix P k :=
        retainedAtomPrefix_mono P (by omega)
      omega
    · by_contra hnot
      have hkl' : (k : ℕ) < l := by omega
      have hmono : retainedAtomPrefix P (k + 1) ≤
          retainedAtomPrefix P l :=
        retainedAtomPrefix_mono P (by omega)
      omega
  have hksub : k = l := Subtype.ext hkl
  subst l
  have hij : i = j := by
    apply Fin.ext
    omega
  subst j
  rfl

def rankCenterAvoids
    {d : ℕ} (P : RetainedPoissonCountSample) (s : Finset ℕ)
    (E : ℕ -> Set (FlatTorus d)) : Set (IIDCenterSample d) :=
  {X | ∀ a : RetainedRankAtomOn P s,
    X (retainedAtomRankOn P a) ∉ E a.1}

theorem rankCenterAvoids_eq_iInter
    {d : ℕ} (P : RetainedPoissonCountSample) (s : Finset ℕ)
    (E : ℕ -> Set (FlatTorus d)) :
    rankCenterAvoids P s E =
      ⋂ a : RetainedRankAtomOn P s,
        (fun X : IIDCenterSample d => X (retainedAtomRankOn P a)) ⁻¹'
          (E a.1)ᶜ := by
  ext X
  simp [rankCenterAvoids]

theorem measurableSet_rankCenterAvoids
    {d : ℕ} (P : RetainedPoissonCountSample) (s : Finset ℕ)
    {E : ℕ -> Set (FlatTorus d)} (hE : ∀ k, MeasurableSet (E k)) :
    MeasurableSet (rankCenterAvoids P s E) := by
  rw [rankCenterAvoids_eq_iInter]
  exact MeasurableSet.iInter fun a =>
    (hE a.1).compl.preimage (measurable_pi_apply _)

theorem iidCenterMeasure_rankCenterAvoids
    {d : ℕ} (P : RetainedPoissonCountSample) (s : Finset ℕ)
    (E : ℕ -> Set (FlatTorus d)) (hE : ∀ k, MeasurableSet (E k)) :
    iidCenterMeasure d (rankCenterAvoids P s E) =
      ∏ k : s, (flatTorusVolume d (E k)ᶜ) ^ P k := by
  rw [rankCenterAvoids_eq_iInter]
  let atomCoord : RetainedRankAtomOn P s -> IIDCenterSample d -> FlatTorus d :=
    fun a X => X (retainedAtomRankOn P a)
  have hindep : iIndepFun atomCoord (iidCenterMeasure d) := by
    exact (iidCenterCoordinates_iIndepFun d).precomp
      (retainedAtomRankOn_injective P s)
  have hprod := hindep.measure_inter_preimage_eq_mul
    (Finset.univ : Finset (RetainedRankAtomOn P s))
    (sets := fun a => (E a.1)ᶜ)
    (fun a _ => (hE a.1).compl)
  simp only [Finset.mem_univ, Set.iInter_true, atomCoord] at hprod
  rw [hprod]
  have hcoord : ∀ a : RetainedRankAtomOn P s,
      iidCenterMeasure d
          ((fun X : IIDCenterSample d => X (retainedAtomRankOn P a)) ⁻¹'
            (E a.1)ᶜ) =
        flatTorusVolume d (E a.1)ᶜ := by
    intro a
    exact (iidCenterCoordinate_hasLaw d (retainedAtomRankOn P a)).measure_eq
      (p := fun x => x ∈ (E a.1)ᶜ) (hE a.1).compl
  simp_rw [hcoord]
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro k _hk
  simp

def rankCoupledSupportsAvoid
    {d : ℕ} (s : Finset ℕ) (E : ℕ -> Set (FlatTorus d)) :
    Set (RankCouplingSample d) :=
  {ω | ∀ k : s, rankCoupledSupport k ω ∈ compactMisses (E k)}

theorem measurableSet_rankCoupledSupportsAvoid
    {d : ℕ} {r : ℕ -> ℝ}
    (Q : GeometricPacketInterface d r) (s : Finset ℕ)
    {E : ℕ -> Set (FlatTorus d)} (hE : ∀ k, IsClosed (E k)) :
    MeasurableSet (rankCoupledSupportsAvoid (d := d) s E) := by
  letI : CompactSpace (FlatTorus d) := flatTorusCompactSpaceOfInterface Q
  have heq : rankCoupledSupportsAvoid (d := d) s E =
      ⋂ k : s, (rankCoupledSupport (d := d) k) ⁻¹'
        compactMisses (E k) := by
    ext ω
    simp [rankCoupledSupportsAvoid]
  rw [heq]
  exact MeasurableSet.iInter fun k =>
    (measurableSet_compactMisses_of_isClosed (hE k)).preimage
      (measurable_rankCoupledSupport Q k)

theorem rankCoupledSupportsAvoid_mk_preimage
    {d : ℕ} (P : RetainedPoissonCountSample) (s : Finset ℕ)
    (E : ℕ -> Set (FlatTorus d)) :
    Prod.mk P ⁻¹' rankCoupledSupportsAvoid (d := d) s E =
      rankCenterAvoids P s E := by
  ext X
  simp only [Set.mem_preimage, rankCoupledSupportsAvoid,
    Set.mem_setOf_eq, rankCenterAvoids]
  constructor
  · intro h a
    have ha := h a.1
    apply (cloudSupport_mem_compactMisses_iff
      (rankCoupledCloud a.1 (P, X)) (E a.1)).1 ha
    exact a.2.isLt
  · intro h k
    apply (cloudSupport_mem_compactMisses_iff
      (rankCoupledCloud k (P, X)) (E k)).2
    intro i hi
    let a : RetainedRankAtomOn P s := ⟨k, ⟨i, hi⟩⟩
    simpa only [rankCoupledCloud, retainedAtomRankOn, a] using h a

theorem lintegral_countCoordinate_pow
    (k : ℕ) (q : ℝ≥0∞) (hq : q ≠ ∞) :
    (∫⁻ P : RetainedPoissonCountSample, q ^ P k
        ∂retainedPoissonCountMeasure) =
      ENNReal.ofReal (Real.exp (q.toReal - 1)) := by
  have hmeas : AEMeasurable (fun n : ℕ => q ^ n) (poissonMeasure 1) :=
    (measurable_of_countable _).aemeasurable
  rw [(retainedCountCoordinate_hasLaw k).lintegral_comp hmeas]
  simpa using lintegral_pow_poissonMeasure 1 q hq

theorem lintegral_countCoordinate_avoidance
    {d : ℕ} (k : ℕ) {E : Set (FlatTorus d)} (hE : MeasurableSet E) :
    (∫⁻ P : RetainedPoissonCountSample,
        (flatTorusVolume d Eᶜ) ^ P k ∂retainedPoissonCountMeasure) =
      ENNReal.ofReal (Real.exp (-(flatTorusVolume d).real E)) := by
  rw [lintegral_countCoordinate_pow k _
    (measure_ne_top (flatTorusVolume d) Eᶜ)]
  congr 2
  change (flatTorusVolume d).real Eᶜ - 1 =
    -(flatTorusVolume d).real E
  rw [measureReal_compl hE, probReal_univ]
  ring

theorem rankCouplingMeasure_supportsAvoid
    {d : ℕ} {r : ℕ -> ℝ}
    (Q : GeometricPacketInterface d r) (s : Finset ℕ)
    (E : ℕ -> Set (FlatTorus d)) (hE : ∀ k, IsClosed (E k)) :
    rankCouplingMeasure d (rankCoupledSupportsAvoid (d := d) s E) =
      ∏ k : s,
        ENNReal.ofReal (Real.exp (-(flatTorusVolume d).real (E k))) := by
  letI : CompactSpace (FlatTorus d) := flatTorusCompactSpaceOfInterface Q
  rw [rankCouplingMeasure,
    Measure.prod_apply (measurableSet_rankCoupledSupportsAvoid Q s hE)]
  simp_rw [rankCoupledSupportsAvoid_mk_preimage,
    iidCenterMeasure_rankCenterAvoids _ s E (fun k => (hE k).measurableSet)]
  let q : ℕ -> ℝ≥0∞ := fun k => flatTorusVolume d (E k)ᶜ
  have hqmeas : ∀ k, Measurable fun n : ℕ => q k ^ n :=
    fun _ => measurable_of_countable _
  have hindep : iIndepFun
      (fun k : s => fun P : RetainedPoissonCountSample => q k ^ P k)
      retainedPoissonCountMeasure := by
    have hcoords : iIndepFun
        (fun k : s => fun P : RetainedPoissonCountSample => P k)
        retainedPoissonCountMeasure :=
      retainedCountCoordinates_iIndepFun.precomp Subtype.val_injective
    exact hcoords.comp (fun k n => q k ^ n) (fun k => hqmeas k)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun
    Finset.univ _ hindep
      (fun k => (hqmeas k).comp (measurable_pi_apply (k : ℕ)))]
  apply Finset.prod_congr rfl
  intro k _hk
  rw [lintegral_countCoordinate_avoidance k (hE k).measurableSet]

noncomputable def rankUnitPoissonSupportMeasure
    {d : ℕ} {r : ℕ -> ℝ} (Q : GeometricPacketInterface d r) :
    Measure (CompactResidual (FlatTorus d)) := by
  letI : CompactSpace (FlatTorus d) := flatTorusCompactSpaceOfInterface Q
  exact poissonSupportMeasure (flatTorusVolume d) 1

noncomputable instance rankUnitPoissonSupportMeasure_isProbabilityMeasure
    {d : ℕ} {r : ℕ -> ℝ} (Q : GeometricPacketInterface d r) :
    IsProbabilityMeasure (rankUnitPoissonSupportMeasure Q) := by
  unfold rankUnitPoissonSupportMeasure
  infer_instance

theorem rankUnitPoissonSupportMeasure_compactMisses
    {d : ℕ} {r : ℕ -> ℝ} (Q : GeometricPacketInterface d r)
    {E : Set (FlatTorus d)} (hE : IsClosed E) :
    rankUnitPoissonSupportMeasure Q (compactMisses E) =
      ENNReal.ofReal (Real.exp (-(flatTorusVolume d).real E)) := by
  letI : CompactSpace (FlatTorus d) := flatTorusCompactSpaceOfInterface Q
  unfold rankUnitPoissonSupportMeasure
  simpa using poissonSupportMeasure_compactMisses
    (flatTorusVolume d) 1 hE

noncomputable def rankCoupledSupportsOn
    {d : ℕ} (s : Finset ℕ) (ω : RankCouplingSample d) :
    s -> CompactResidual (FlatTorus d) :=
  fun k => rankCoupledSupport k ω

theorem measurable_rankCoupledSupportsOn
    {d : ℕ} {r : ℕ -> ℝ} (Q : GeometricPacketInterface d r)
    (s : Finset ℕ) :
    Measurable (rankCoupledSupportsOn (d := d) s) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_rankCoupledSupport Q k

theorem rankCoupledSupportsOn_preimage_pi_misses
    {d : ℕ} (s : Finset ℕ) (E : s -> Set (FlatTorus d)) :
    rankCoupledSupportsOn (d := d) s ⁻¹'
        (Set.univ.pi fun k => compactMisses (E k)) =
      {ω | ∀ k : s,
        rankCoupledSupport k ω ∈ compactMisses (E k)} := by
  ext ω
  simp [rankCoupledSupportsOn]

theorem rankCouplingMeasure_supportsAvoidOn
    {d : ℕ} {r : ℕ -> ℝ}
    (Q : GeometricPacketInterface d r) (s : Finset ℕ)
    (E : s -> Set (FlatTorus d)) (hE : ∀ k, IsClosed (E k)) :
    rankCouplingMeasure d
        {ω | ∀ k : s,
          rankCoupledSupport k ω ∈ compactMisses (E k)} =
      ∏ k : s,
        rankUnitPoissonSupportMeasure Q (compactMisses (E k)) := by
  classical
  let Efull : ℕ -> Set (FlatTorus d) := fun n =>
    if hn : n ∈ s then E ⟨n, hn⟩ else ∅
  have hEfull : ∀ n, IsClosed (Efull n) := by
    intro n
    dsimp [Efull]
    split_ifs with hn
    · exact hE ⟨n, hn⟩
    · exact isClosed_empty
  have hevent :
      {ω | ∀ k : s,
          rankCoupledSupport k ω ∈ compactMisses (E k)} =
        rankCoupledSupportsAvoid (d := d) s Efull := by
    ext ω
    simp only [rankCoupledSupportsAvoid, Set.mem_setOf_eq]
    constructor <;> intro h k
    · simpa only [Efull, dif_pos k.property] using h k
    · simpa only [Efull, dif_pos k.property] using h k
  rw [hevent, rankCouplingMeasure_supportsAvoid Q s Efull hEfull]
  apply Finset.prod_congr rfl
  intro k _hk
  rw [rankUnitPoissonSupportMeasure_compactMisses Q (hE k)]
  simp only [Efull, dif_pos k.property]

theorem rankCoupledSupportsOn_hasLaw
    {d : ℕ} {r : ℕ -> ℝ} (Q : GeometricPacketInterface d r)
    (s : Finset ℕ) :
    HasLaw (rankCoupledSupportsOn (d := d) s)
      (Measure.pi fun _k : s => rankUnitPoissonSupportMeasure Q)
      (rankCouplingMeasure d) := by
  letI : CompactSpace (FlatTorus d) := flatTorusCompactSpaceOfInterface Q
  refine ⟨(measurable_rankCoupledSupportsOn Q s).aemeasurable, ?_⟩
  symm
  apply Measure.pi_eq_generateFrom
    (fun _k => (borel_compactResidual_eq_generateFrom_misses
      (FlatTorus d)).symm)
    (fun _k => isPiSystem_compactMissGenerator (FlatTorus d))
    (fun _k => by
      refine
        { set := fun _ => Set.univ
          set_mem := fun _ =>
            ⟨∅, isClosed_empty, compactMisses_empty.symm⟩
          finite := fun _ => by simp
          spanning := ?_ }
      apply Set.eq_univ_of_forall
      intro A
      exact Set.mem_iUnion.2 ⟨0, Set.mem_univ A⟩)
  intro t ht
  choose E hE htE using fun k => ht k
  have htEq : t = fun k => compactMisses (E k) := funext htE
  subst t
  rw [Measure.map_apply (measurable_rankCoupledSupportsOn Q s)
    (MeasurableSet.univ_pi fun k =>
      measurableSet_compactMisses_of_isClosed (hE k))]
  rw [rankCoupledSupportsOn_preimage_pi_misses]
  exact rankCouplingMeasure_supportsAvoidOn Q s E hE

theorem rankCoupledSupports_map_eq_infinitePi
    {d : ℕ} {r : ℕ -> ℝ} (Q : GeometricPacketInterface d r) :
    Measure.map (rankCoupledSupports (d := d)) (rankCouplingMeasure d) =
      Measure.infinitePi fun _k : ℕ => rankUnitPoissonSupportMeasure Q := by
  apply Measure.eq_infinitePi
  intro s t ht
  let tOn : s -> Set (CompactResidual (FlatTorus d)) := fun k => t k
  have htOn : ∀ k : s, MeasurableSet (tOn k) := fun k => ht k
  have hbox : MeasurableSet (Set.univ.pi tOn) :=
    MeasurableSet.univ_pi htOn
  have h := (rankCoupledSupportsOn_hasLaw Q s).measure_eq
    (p := fun y => y ∈ Set.univ.pi tOn) hbox
  simp only [Set.setOf_mem_eq] at h
  rw [Measure.pi_pi] at h
  rw [Measure.map_apply (measurable_rankCoupledSupports Q)
    (MeasurableSet.pi s.countable_toSet fun i _hi => ht i)]
  have hevent :
      rankCoupledSupports (d := d) ⁻¹' (s : Set ℕ).pi t =
        {ω | ∀ i : s, rankCoupledSupport i ω ∈ t i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, rankCoupledSupports,
      Set.mem_setOf_eq]
    constructor
    · intro hmem i
      exact hmem i i.property
    · intro hmem i hi
      exact hmem ⟨i, hi⟩
  rw [hevent, ← Finset.prod_coe_sort]
  simpa only [rankCoupledSupportsOn, tOn, Set.mem_setOf_eq,
    Set.mem_pi, Set.mem_univ, forall_const] using h

theorem fullPoissonSupportMeasure_eq_rankInfinitePi
    {d : ℕ} {r : ℕ -> ℝ} (Q : GeometricPacketInterface d r) :
    fullPoissonSupportMeasure Q =
      Measure.infinitePi fun _k : ℕ => rankUnitPoissonSupportMeasure Q := by
  rfl

theorem rankCoupledSupports_hasLaw
    {d : ℕ} {r : ℕ -> ℝ} (Q : GeometricPacketInterface d r) :
    HasLaw (rankCoupledSupports (d := d))
      (fullPoissonSupportMeasure Q) (rankCouplingMeasure d) := by
  refine ⟨(measurable_rankCoupledSupports Q).aemeasurable, ?_⟩
  rw [fullPoissonSupportMeasure_eq_rankInfinitePi Q]
  exact rankCoupledSupports_map_eq_infinitePi Q

end Shepp.Section6
end SheppFlattenedModule073

section SheppFlattenedModule074
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators
open Filter Set MeasureTheory

namespace Shepp.Section6

open ProbabilityTheory Shepp.Section2 Shepp.Section3 Shepp.Section4
  Shepp.Section5 TopologicalSpace

theorem retainedCount_retainedIndex_succ (k : ℕ) :
    retainedCount (retainedIndex k + 1) = k + 1 := by
  classical
  unfold retainedCount retainedIndex
  exact Nat.count_nth_succ_of_infinite
    (by simpa [Set.compl_def] using reserve_compl_infinite) k

theorem cumulativeRetainedCount_retainedIndex_succ
    (P : RetainedPoissonCountSample) (k : ℕ) :
    cumulativeRetainedCount (retainedIndex k + 1) P =
      retainedAtomPrefix P (k + 1) := by
  simp [cumulativeRetainedCount, retainedAtomPrefix,
    retainedCount_retainedIndex_succ]

theorem ae_eventually_retainedAtomPrefix_succ_le :
    ∀ᵐ P : RetainedPoissonCountSample ∂retainedPoissonCountMeasure,
      ∀ᶠ k : ℕ in atTop,
        retainedAtomPrefix P (k + 1) ≤ retainedIndex k + 1 := by
  filter_upwards [ae_eventually_cumulativeRetainedCount_le] with P hP
  rw [eventually_atTop] at hP ⊢
  obtain ⟨N, hN⟩ := hP
  refine ⟨N, ?_⟩
  intro k hk
  have hcut : N ≤ retainedIndex k + 1 := by
    have hkle : k ≤ retainedIndex k := retainedIndex_le k
    omega
  have hfit := hN (retainedIndex k + 1) hcut
  rwa [cumulativeRetainedCount_retainedIndex_succ] at hfit

theorem positive_retained_count_arbitrarily_late_of_allTailsCover
    {d : ℕ} (ρ : ℕ -> ℝ) (ω : RankCouplingSample d)
    (hcover : rankCoupledSupports ω ∈
      fullPoissonSupportAllTailsCoverEvent (d := d) ρ) :
    ∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧ 0 < ω.1 k := by
  intro k₀
  have htail := Set.mem_iInter.1 hcover k₀
  change fullPoissonSupportShift k₀ (rankCoupledSupports ω) ∈
    fullPoissonSupportFiniteCoverEvent (d := d) (tailRadius ρ k₀) at htail
  obtain ⟨N, hN⟩ := Set.mem_iUnion.1 htail
  change fullPoissonSupportsCoveredThrough (tailRadius ρ k₀) N
      (fullPoissonSupportShift k₀ (rankCoupledSupports ω)) = Set.univ at hN
  have hz : (0 : FlatTorus d) ∈
      fullPoissonSupportsCoveredThrough (tailRadius ρ k₀) N
        (fullPoissonSupportShift k₀ (rankCoupledSupports ω)) := by
    rw [hN]
    exact Set.mem_univ _
  simp only [fullPoissonSupportsCoveredThrough, compactSupportsCovered,
    Set.mem_iUnion] at hz
  obtain ⟨n, x, hx, _hzball⟩ := hz
  change x ∈ rankCoupledSupport (k₀ + n) ω at hx
  change x ∈ cloudPoints (rankCoupledCloud (k₀ + n) ω) at hx
  obtain ⟨i, hi, _hxi⟩ := hx
  refine ⟨k₀ + n, Nat.le_add_right k₀ n, ?_⟩
  change i < ω.1 (k₀ + n) at hi
  omega

theorem retainedAtomPrefix_tendsto_atTop_of_positive_arbitrarily_late
    (P : RetainedPoissonCountSample)
    (hpos : ∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧ 0 < P k) :
    Tendsto (retainedAtomPrefix P) atTop atTop := by
  have hex : ∀ B : ℕ, ∃ N : ℕ, B ≤ retainedAtomPrefix P N := by
    intro B
    induction B with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ B ih =>
        obtain ⟨N, hBN⟩ := ih
        obtain ⟨k, hNk, hPk⟩ := hpos N
        refine ⟨k + 1, ?_⟩
        rw [retainedAtomPrefix_succ]
        have hmono : retainedAtomPrefix P N ≤ retainedAtomPrefix P k :=
          retainedAtomPrefix_mono P hNk
        omega
  apply tendsto_atTop.2
  intro B
  obtain ⟨N, hBN⟩ := hex B
  filter_upwards [eventually_ge_atTop N] with M hNM
  exact hBN.trans (retainedAtomPrefix_mono P hNM)

theorem retainedAtomPrefix_tendsto_atTop_of_allTailsCover
    {d : ℕ} (ρ : ℕ -> ℝ) (ω : RankCouplingSample d)
    (hcover : rankCoupledSupports ω ∈
      fullPoissonSupportAllTailsCoverEvent (d := d) ρ) :
    Tendsto (retainedAtomPrefix ω.1) atTop atTop :=
  retainedAtomPrefix_tendsto_atTop_of_positive_arbitrarily_late ω.1
    (positive_retained_count_arbitrarily_late_of_allTailsCover ρ ω hcover)

theorem iidLimsupCover_of_rankCoupled_allTailsCover
    {d : ℕ} {r : ℕ -> ℝ} (hmono : Antitone r)
    (ω : RankCouplingSample d)
    (hfit : ∀ᶠ k : ℕ in atTop,
      retainedAtomPrefix ω.1 (k + 1) ≤ retainedIndex k + 1)
    (hcover : rankCoupledSupports ω ∈
      fullPoissonSupportAllTailsCoverEvent
        (d := d) (retainedRadius r)) :
    ω.2 ∈ iidLimsupCoverEvent (d := d) r := by
  have hpoissonLimsup :=
    allTailsCoverEvent_subset_limsupCoverEvent
      (d := d) (retainedRadius r) hcover
  change iidLimsupSet r ω.2 = Set.univ
  apply Set.eq_univ_of_univ_subset
  intro z _hzuniv
  rw [iidLimsupSet_eq_iInter_coveredFrom]
  apply Set.mem_iInter.2
  intro n₀
  have hprefixTendsto :=
    retainedAtomPrefix_tendsto_atTop_of_allTailsCover
      (retainedRadius r) ω hcover
  have hpref : ∀ᶠ k : ℕ in atTop,
      n₀ ≤ retainedAtomPrefix ω.1 k :=
    (tendsto_atTop.1 hprefixTendsto) n₀
  have hboth := hfit.and hpref
  rw [eventually_atTop] at hboth
  obtain ⟨k₀, hk₀⟩ := hboth
  have hzPoisson : z ∈ fullPoissonSupportLimsupSet
      (retainedRadius r) (rankCoupledSupports ω) := by
    change fullPoissonSupportLimsupSet
      (retainedRadius r) (rankCoupledSupports ω) = Set.univ at hpoissonLimsup
    rw [hpoissonLimsup]
    exact Set.mem_univ z
  have htail := Set.mem_iInter.1 hzPoisson k₀
  simp only [fullPoissonSupportsCoveredFrom, compactSupportsCovered,
    Set.mem_iUnion] at htail
  obtain ⟨k, x, hx, hball⟩ := htail
  have hkdata := hk₀ k k.property
  change x ∈ rankCoupledSupport k ω at hx
  change x ∈ cloudPoints (rankCoupledCloud k ω) at hx
  obtain ⟨i, hi, hxi⟩ := hx
  change i < ω.1 k at hi
  let j : ℕ := retainedAtomPrefix ω.1 k + i
  have hjlower : n₀ ≤ j := by
    dsimp [j]
    exact hkdata.2.trans (Nat.le_add_right _ _)
  have hjlt : j < retainedAtomPrefix ω.1 (k + 1) := by
    dsimp [j]
    rw [retainedAtomPrefix_succ]
    omega
  have hjmark : j ≤ retainedIndex k := by
    have hupper := hkdata.1
    omega
  apply (mem_iidCentersCoveredFrom_iff r n₀ ω.2 z).2
  refine ⟨j, hjlower, ?_⟩
  rw [← hxi] at hball
  change z ∈ Metric.ball
      (ω.2 (retainedAtomPrefix ω.1 k + i))
      (r (retainedIndex k)) at hball
  exact Metric.ball_subset_ball (hmono hjmark) hball

theorem lowMoment_dePoissonizedSufficiency
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ -> ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (hsum : Summable
      (fun n => radiusVolume d r n ^ (4 / 3 : ℝ)))
    (htop :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞) :
    iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 1 := by
  have hretTop := lintegral_retainedRadius_overlapSumExp_eq_top
    d hd hr hrsmall hrlim hsum hmono htop
  have hrRet : ∀ k, 0 < retainedRadius r k := retainedRadius_pos hr
  have hrRetSmall : ∀ k, retainedRadius r k < 1 / 4 :=
    retainedRadius_lt_quarter hrsmall
  have hmonoRet : Antitone (retainedRadius r) :=
    retainedRadius_antitone hmono
  have hlimRet : Tendsto (retainedRadius r) atTop (nhds 0) :=
    retainedRadius_tendsto_zero hrlim
  obtain ⟨Q⟩ :=
    (poissonizedSufficiency d hd hrRet hrRetSmall hmonoRet hlimRet hretTop).1
  let A : Set (FullPoissonSupportSample d) :=
    fullPoissonSupportAllTailsCoverEvent (d := d) (retainedRadius r)
  have hAmeas : MeasurableSet A := by
    exact measurableSet_fullPoissonSupportAllTailsCoverEvent
      hd hrRet hrRetSmall hmonoRet hlimRet hretTop
  have hAcanonical : fullPoissonSupportMeasure Q A = 1 := by
    exact fullPoissonSupportMeasure_allTailsCoverEvent_measure_one
      hd hrRet hrRetSmall hmonoRet hlimRet hretTop Q
  have hAcoupled : rankCouplingMeasure d
      {ω | rankCoupledSupports ω ∈ A} = 1 := by
    have hLaw := (rankCoupledSupports_hasLaw Q).measure_eq
      (p := fun S => S ∈ A) hAmeas
    exact hLaw.trans hAcanonical
  have hcoverAE :
      ∀ᵐ ω : RankCouplingSample d ∂rankCouplingMeasure d,
        rankCoupledSupports ω ∈ A := by
    have hBmeas : MeasurableSet
        {ω : RankCouplingSample d | rankCoupledSupports ω ∈ A} :=
      hAmeas.preimage (measurable_rankCoupledSupports Q)
    apply ae_iff.2
    change rankCouplingMeasure d
      ({ω | rankCoupledSupports ω ∈ A})ᶜ = 0
    rw [measure_compl hBmeas, hAcoupled]
    all_goals simp [hAcoupled]
  have hfitAE :
      ∀ᵐ ω : RankCouplingSample d ∂rankCouplingMeasure d,
        ∀ᶠ k : ℕ in atTop,
          retainedAtomPrefix ω.1 (k + 1) ≤ retainedIndex k + 1 := by
    unfold rankCouplingMeasure
    exact measurePreserving_fst.quasiMeasurePreserving.ae
      ae_eventually_retainedAtomPrefix_succ_le
  have hiidJoint :
      ∀ᵐ ω : RankCouplingSample d ∂rankCouplingMeasure d,
        ω.2 ∈ iidLimsupCoverEvent (d := d) r := by
    filter_upwards [hfitAE, hcoverAE] with ω hfit hcover
    exact iidLimsupCover_of_rankCoupled_allTailsCover
      hmono ω hfit hcover
  have hiidDouble :
      ∀ᵐ P : RetainedPoissonCountSample ∂retainedPoissonCountMeasure,
        ∀ᵐ X : IIDCenterSample d ∂iidCenterMeasure d,
          X ∈ iidLimsupCoverEvent (d := d) r := by
    unfold rankCouplingMeasure at hiidJoint
    exact Measure.ae_ae_of_ae_prod hiidJoint
  obtain ⟨_P, hiidAE⟩ := hiidDouble.exists
  have hcompl : iidCenterMeasure d
      (iidLimsupCoverEvent (d := d) r)ᶜ = 0 := by
    apply ae_iff.1
    simpa only [Set.mem_compl_iff, not_not] using hiidAE
  have hfull := measure_of_measure_compl_eq_zero hcompl
  simpa using hfull

end Shepp.Section6
end SheppFlattenedModule074

section SheppFlattenedModule075
open scoped ENNReal ProbabilityTheory Topology BigOperators
open Filter Set MeasureTheory

namespace Shepp.Section6

open ProbabilityTheory Shepp.Section2 Shepp.Section3 Shepp.Section4
  Shepp.Section5 TopologicalSpace

theorem dePoissonizedSufficiency
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0))
    (htop :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) = ∞) :
    iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 1 := by
  by_cases hsum : Summable
      (fun n => radiusVolume d r n ^ (4 / 3 : ℝ))
  · exact lowMoment_dePoissonizedSufficiency
      d hd hr hrsmall hmono hrlim hsum htop
  · exact highMoment_dePoissonizedSufficiency
      d hd hr hrsmall hmono hrlim hsum htop

end Shepp.Section6
end SheppFlattenedModule075

section SheppFlattenedModule076
open scoped Topology
open Set Module

namespace Shepp.Section7

open Shepp.Section2

theorem flatTorus_isCompact_univ (d : ℕ) :
    IsCompact (Set.univ : Set (FlatTorus d)) := by
  let R : ℝ := ∑ i : Fin d, ‖flatTorusBasis d i‖
  let C : Set (EuclideanSpace ℝ (Fin d)) := Metric.closedBall 0 R
  have hC : IsCompact C := isCompact_closedBall 0 R
  have hcont : Continuous (flatTorusMk d) := by
    apply LipschitzWith.continuous
    apply LipschitzWith.of_dist_le_mul (K := 1)
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  have himage : flatTorusMk d '' C = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    intro q _hq
    rcases QuotientAddGroup.mk'_surjective (integerLattice d) q with
      ⟨x, hx⟩
    let y := ZSpan.fract (flatTorusBasis d) x
    refine ⟨y, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact ZSpan.norm_fract_le (flatTorusBasis d) x
    · rw [← hx]
      change (y : FlatTorus d) = (x : FlatTorus d)
      rw [QuotientAddGroup.eq_iff_sub_mem]
      have hfloor :
          ((ZSpan.floor (flatTorusBasis d) x :
              Submodule.span ℤ (Set.range (flatTorusBasis d))) :
            EuclideanSpace ℝ (Fin d)) ∈ integerLattice d := by
        rw [integerLattice_eq_zspan]
        exact (ZSpan.floor (flatTorusBasis d) x).property
      dsimp [y]
      rw [ZSpan.fract_apply]
      have hid :
          x - (ZSpan.floor (flatTorusBasis d) x :
              EuclideanSpace ℝ (Fin d)) - x =
            -(ZSpan.floor (flatTorusBasis d) x :
              EuclideanSpace ℝ (Fin d)) := by
        abel
      rw [hid]
      exact (integerLattice d).neg_mem hfloor
  rw [← himage]
  exact hC.image hcont

noncomputable instance flatTorusCompactSpace (d : ℕ) :
    CompactSpace (FlatTorus d) :=
  isCompact_univ_iff.mp (flatTorus_isCompact_univ d)

end Shepp.Section7
end SheppFlattenedModule076

section SheppFlattenedModule077
open scoped ENNReal Topology
open MeasureTheory Set

namespace Shepp.Section7

open Shepp.Section2

theorem flatTorusVolumeReal_ball_zero_eq_radiusVolume
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrsmall : ∀ n, r n < 1 / 4)
    (n : ℕ) :
    (flatTorusVolume d).real
        (Metric.ball (0 : FlatTorus d) (r n)) =
      radiusVolume d r n := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [show (0 : FlatTorus d) =
      flatTorusMk d (0 : EuclideanSpace ℝ (Fin d)) by rfl]
  rw [Measure.real, flatTorusVolume_ball_eq_volume d (hrsmall n),
    EuclideanSpace.volume_ball, Fintype.card_fin]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (hr n)]
  rw [ENNReal.toReal_ofReal (by
    simpa only [euclideanUnitBallVolume] using
      (euclideanUnitBallVolume_pos d).le)]
  unfold radiusVolume euclideanUnitBallVolume
  ring

theorem lintegral_flatTorus_ballLens
    (d : ℕ) (ρ : ℝ) :
    (∫⁻ z : FlatTorus d,
      flatTorusVolume d (flatTorusBallLens d ρ 0 z)
        ∂(flatTorusVolume d)) =
      flatTorusVolume d (Metric.ball (0 : FlatTorus d) ρ) ^ 2 := by
  let μ : Measure (FlatTorus d) := flatTorusVolume d
  let A : Set (FlatTorus d) := Metric.ball 0 ρ
  let f : FlatTorus d × FlatTorus d → FlatTorus d × FlatTorus d :=
    fun p => (p.1 - p.2, p.2)
  let S : Set (FlatTorus d × FlatTorus d) := f ⁻¹' (A ×ˢ A)
  have hA : MeasurableSet A := Metric.isOpen_ball.measurableSet
  have hf : Measurable f :=
    (measurable_fst.sub measurable_snd).prodMk measurable_snd
  have hS : MeasurableSet S := (hA.prod hA).preimage hf
  have hslice (z : FlatTorus d) :
      Prod.mk z ⁻¹' S = flatTorusBallLens d ρ 0 z := by
    ext x
    simp only [S, f, A, Set.mem_preimage, Set.mem_prod,
      flatTorusBallLens, Set.mem_inter_iff, Metric.mem_ball]
    rw [dist_zero_right]
    constructor
    · rintro ⟨hzx, hx⟩
      exact ⟨hx, by simpa [dist_eq_norm, norm_sub_rev] using hzx⟩
    · rintro ⟨hx, hxz⟩
      exact ⟨by simpa [dist_eq_norm, norm_sub_rev] using hxz, hx⟩
  calc
    (∫⁻ z : FlatTorus d,
        flatTorusVolume d (flatTorusBallLens d ρ 0 z)
          ∂(flatTorusVolume d)) =
        ∫⁻ z : FlatTorus d, μ (Prod.mk z ⁻¹' S) ∂μ := by
      apply lintegral_congr
      intro z
      rw [hslice]
    _ = (μ.prod μ) S := by
      exact (Measure.prod_apply hS).symm
    _ = (μ.prod μ) (A ×ˢ A) := by
      exact (measurePreserving_sub_prod μ μ).measure_preimage
        (hA.prod hA).nullMeasurableSet
    _ = μ A * μ A := Measure.prod_prod A A
    _ = flatTorusVolume d (Metric.ball (0 : FlatTorus d) ρ) ^ 2 := by
      simp [μ, A, pow_two]

theorem lintegral_flatTorusOverlapTerm
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrsmall : ∀ n, r n < 1 / 4)
    (n : ℕ) :
    (∫⁻ z : FlatTorus d,
      ENNReal.ofReal (flatTorusOverlapTerm d r n z)
        ∂(flatTorusVolume d)) =
      ENNReal.ofReal (radiusVolume d r n ^ 2) := by
  have hball := flatTorusVolumeReal_ball_zero_eq_radiusVolume
    d hd hr hrsmall n
  simp only [flatTorusOverlapTerm]
  have hof (z : FlatTorus d) :
      ENNReal.ofReal
          ((flatTorusVolume d).real (flatTorusBallLens d (r n) 0 z)) =
        flatTorusVolume d (flatTorusBallLens d (r n) 0 z) :=
    MeasureTheory.ofReal_measureReal
  simp_rw [hof]
  rw [lintegral_flatTorus_ballLens]
  rw [← MeasureTheory.ofReal_measureReal, hball]
  have hv0 : 0 ≤ radiusVolume d r n := by
    unfold radiusVolume
    exact mul_nonneg (euclideanUnitBallVolume_pos d).le
      (pow_nonneg (hr n) d)
  rw [ENNReal.ofReal_pow hv0]

end Shepp.Section7
end SheppFlattenedModule077

section SheppFlattenedModule078
open scoped ENNReal Topology
open Filter MeasureTheory Set

namespace Shepp.Section7

open Shepp.Section2

theorem measurable_ofReal_flatTorusOverlapTerm
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (n : ℕ) :
    Measurable fun z : FlatTorus d =>
      ENNReal.ofReal (flatTorusOverlapTerm d r n z) := by
  have heq : flatTorusOverlapTerm d r n =
      fun z => radialOverlapTerm d r n (dist 0 z) := by
    funext z
    exact flatTorusOverlapTerm_eq_radialOverlapTerm
      d hd hr hrsmall n z
  rw [heq]
  exact ENNReal.measurable_ofReal.comp
    ((measurable_radialOverlapTerm d r n).comp
      (measurable_dist_zero_flatTorus d))

theorem lintegral_flatTorusOverlapEnergy
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4) :
    (∫⁻ z : FlatTorus d, flatTorusOverlapEnergy d r z
      ∂(flatTorusVolume d)) =
      ∑' n, ENNReal.ofReal (radiusVolume d r n ^ 2) := by
  unfold flatTorusOverlapEnergy
  rw [lintegral_tsum fun n =>
      (measurable_ofReal_flatTorusOverlapTerm
        d hd hr hrsmall n).aemeasurable]
  apply tsum_congr
  intro n
  exact lintegral_flatTorusOverlapTerm
    d (by omega) (fun n => (hr n).le) hrsmall n

theorem flatTorusOverlapEnergy_le_exp
    (d : ℕ) (r : ℕ → ℝ) (z : FlatTorus d) :
    flatTorusOverlapEnergy d r z ≤
      flatTorusOverlapEnergyExp d r z := by
  let x : ℝ≥0∞ := flatTorusOverlapEnergy d r z
  change x ≤ EReal.exp (x : EReal)
  by_cases hx : x = ∞
  · simp [hx]
  · have hcoe : (x.toReal : EReal) = (x : EReal) :=
      EReal.coe_ennreal_toReal hx
    have hle : x.toReal ≤ x.toReal + 1 := by linarith
    calc
      x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx).symm
      _ ≤ ENNReal.ofReal (Real.exp x.toReal) :=
        ENNReal.ofReal_le_ofReal <|
          hle.trans (Real.add_one_le_exp x.toReal)
      _ = EReal.exp (x : EReal) := by rw [← hcoe, EReal.exp_coe]

theorem squareSummable_of_finite_overlap_energy
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (nhds 0))
    (hfinite :
      (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d)) < ∞) :
    Summable fun n => radiusVolume d r n ^ 2 := by
  have hexpfinite :
      (∫⁻ z : FlatTorus d, flatTorusOverlapEnergyExp d r z
        ∂(flatTorusVolume d)) < ∞ := by
    rw [lintegral_flatTorusOverlapEnergyExp_eq_real
      d hd hr hrsmall hrlim]
    exact hfinite
  have henergyfinite :
      (∫⁻ z : FlatTorus d, flatTorusOverlapEnergy d r z
        ∂(flatTorusVolume d)) < ∞ :=
    (lintegral_mono fun z => flatTorusOverlapEnergy_le_exp d r z).trans_lt
      hexpfinite
  rw [lintegral_flatTorusOverlapEnergy d hd hr hrsmall] at henergyfinite
  have hs := ENNReal.summable_toReal henergyfinite.ne
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hs

end Shepp.Section7
end SheppFlattenedModule078

section SheppFlattenedModule079
open scoped ENNReal Topology BigOperators
open Filter MeasureTheory Set

namespace Shepp.Section7

open Shepp.Section2 Shepp.Section6

theorem avoidanceFactor_nonneg
    {u v : ℝ} (hu0 : 0 ≤ u) (_hv0 : 0 ≤ v) (hv : v ≤ 1 / 4) :
    0 ≤ (1 - 2 * v + u) / (1 - v) ^ 2 := by
  apply div_nonneg
  · nlinarith
  · positivity

theorem avoidanceFactor_le_one_add
    {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v)
    (_hv0 : 0 ≤ v) (hv : v ≤ 1 / 4) :
    (1 - 2 * v + u) / (1 - v) ^ 2 ≤ 1 + u + 4 * v ^ 2 := by
  have hden : 0 < (1 - v) ^ 2 := sq_pos_of_pos (by linarith)
  rw [div_le_iff₀ hden]
  have huvprod : u * v ≤ v ^ 2 := by nlinarith
  have hv3 : v ^ 3 ≤ v ^ 2 / 4 := by
    nlinarith [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hv)]
  nlinarith [mul_nonneg hu0 (sq_nonneg v), sq_nonneg v,
    mul_nonneg (sq_nonneg v) (sq_nonneg v)]

theorem avoidanceFactor_le_exp
    {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v)
    (hv0 : 0 ≤ v) (hv : v ≤ 1 / 4) :
    (1 - 2 * v + u) / (1 - v) ^ 2 ≤
      Real.exp (u + 4 * v ^ 2) := by
  calc
    (1 - 2 * v + u) / (1 - v) ^ 2 ≤ 1 + u + 4 * v ^ 2 :=
      avoidanceFactor_le_one_add hu0 huv hv0 hv
    _ = 1 + (u + 4 * v ^ 2) := by ring
    _ ≤ Real.exp (u + 4 * v ^ 2) := by
      simpa only [add_comm] using Real.add_one_le_exp (u + 4 * v ^ 2)

noncomputable def finiteAvoidanceKernel
    (d : ℕ) (r : ℕ → ℝ) (I : Finset ℕ) (z : FlatTorus d) : ℝ :=
  ∏ n ∈ I,
    (1 - 2 * radiusVolume d r n + flatTorusOverlapTerm d r n z) /
      (1 - radiusVolume d r n) ^ 2

theorem measurable_flatTorusOverlapTerm
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (n : ℕ) :
    Measurable (flatTorusOverlapTerm d r n) := by
  have heq : flatTorusOverlapTerm d r n =
      fun z => radialOverlapTerm d r n (dist 0 z) := by
    funext z
    exact flatTorusOverlapTerm_eq_radialOverlapTerm
      d hd hr hrsmall n z
  rw [heq]
  exact (measurable_radialOverlapTerm d r n).comp
    (measurable_dist_zero_flatTorus d)

theorem measurable_finiteAvoidanceKernel
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (I : Finset ℕ) :
    Measurable (finiteAvoidanceKernel d r I) := by
  unfold finiteAvoidanceKernel
  classical
  induction I using Finset.induction_on with
  | empty =>
      exact measurable_const
  | @insert n I hn hI =>
      have hterm := measurable_flatTorusOverlapTerm d hd hr hrsmall n
      have hfactor : Measurable fun z : FlatTorus d =>
          (1 - 2 * radiusVolume d r n + flatTorusOverlapTerm d r n z) /
            (1 - radiusVolume d r n) ^ 2 := by
        exact (measurable_const.add hterm).div_const _
      have hm := hfactor.mul hI
      change Measurable fun z : FlatTorus d =>
        (1 - 2 * radiusVolume d r n + flatTorusOverlapTerm d r n z) /
            (1 - radiusVolume d r n) ^ 2 *
          ∏ i ∈ I,
            (1 - 2 * radiusVolume d r i + flatTorusOverlapTerm d r i z) /
              (1 - radiusVolume d r i) ^ 2 at hm
      simpa only [Finset.prod_insert hn] using hm

theorem finiteAvoidanceKernel_nonneg
    (d : ℕ) (_hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (_hrsmall : ∀ n, r n < 1 / 4)
    (I : Finset ℕ)
    (hvsmall : ∀ n ∈ I, radiusVolume d r n ≤ 1 / 4)
    (z : FlatTorus d) :
    0 ≤ finiteAvoidanceKernel d r I z := by
  unfold finiteAvoidanceKernel
  apply Finset.prod_nonneg
  intro n hn
  exact avoidanceFactor_nonneg
    (flatTorusOverlapTerm_nonneg d r n z)
    (radiusVolume_nonneg d hr n) (hvsmall n hn)

theorem finiteAvoidanceKernel_le_exp_sum
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrsmall : ∀ n, r n < 1 / 4)
    (I : Finset ℕ)
    (hvsmall : ∀ n ∈ I, radiusVolume d r n ≤ 1 / 4)
    (z : FlatTorus d) :
    finiteAvoidanceKernel d r I z ≤
      Real.exp (∑ n ∈ I,
        (flatTorusOverlapTerm d r n z +
          4 * radiusVolume d r n ^ 2)) := by
  unfold finiteAvoidanceKernel
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro n hn
    exact avoidanceFactor_nonneg
      (flatTorusOverlapTerm_nonneg d r n z)
      (radiusVolume_nonneg d hr n) (hvsmall n hn)
  · intro n hn
    exact avoidanceFactor_le_exp
      (flatTorusOverlapTerm_nonneg d r n z)
      (flatTorusOverlapTerm_le_radiusVolume
        d hd hr hrsmall n z)
      (radiusVolume_nonneg d hr n) (hvsmall n hn)

theorem finiteAvoidanceKernel_le_global
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (nhds 0))
    (hsq : Summable fun n => radiusVolume d r n ^ 2)
    (I : Finset ℕ)
    (hvsmall : ∀ n ∈ I, radiusVolume d r n ≤ 1 / 4)
    {z : FlatTorus d} (hz : z ≠ 0) :
    finiteAvoidanceKernel d r I z ≤
      Real.exp (4 * ∑' n, radiusVolume d r n ^ 2) *
        Real.exp (flatTorusOverlapSum d r z) := by
  have hdist : 0 < dist (0 : FlatTorus d) z :=
    dist_pos.mpr (Ne.symm hz)
  have hsu : Summable fun n => flatTorusOverlapTerm d r n z := by
    have heq : (fun n => flatTorusOverlapTerm d r n z) =
        fun n => euclideanOverlapTerm d r n (dist 0 z) := by
      funext n
      exact flatTorusOverlapTerm_eq_euclideanOverlapTerm_dist
        d hd hr hrsmall n z
    rw [heq]
    exact summable_euclideanOverlapTerm d hr hrlim hdist
  have huI :
      (∑ n ∈ I, flatTorusOverlapTerm d r n z) ≤
        flatTorusOverlapSum d r z := by
    unfold flatTorusOverlapSum
    exact hsu.sum_le_tsum I fun n _ =>
      flatTorusOverlapTerm_nonneg d r n z
  have hvI :
      (∑ n ∈ I, radiusVolume d r n ^ 2) ≤
        ∑' n, radiusVolume d r n ^ 2 :=
    hsq.sum_le_tsum I fun n _ => sq_nonneg _
  have hsum :
      (∑ n ∈ I,
          (flatTorusOverlapTerm d r n z +
            4 * radiusVolume d r n ^ 2)) ≤
        flatTorusOverlapSum d r z +
          4 * ∑' n, radiusVolume d r n ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact add_le_add huI (mul_le_mul_of_nonneg_left hvI (by norm_num))
  calc
    finiteAvoidanceKernel d r I z ≤
        Real.exp (∑ n ∈ I,
          (flatTorusOverlapTerm d r n z +
            4 * radiusVolume d r n ^ 2)) :=
      finiteAvoidanceKernel_le_exp_sum d (by omega)
        (fun n => (hr n).le) hrsmall I hvsmall z
    _ ≤ Real.exp (flatTorusOverlapSum d r z +
          4 * ∑' n, radiusVolume d r n ^ 2) :=
      Real.exp_le_exp.mpr hsum
    _ = Real.exp (4 * ∑' n, radiusVolume d r n ^ 2) *
          Real.exp (flatTorusOverlapSum d r z) := by
      rw [add_comm, Real.exp_add]

theorem lintegral_finiteAvoidanceKernel_le_global
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (nhds 0))
    (hsq : Summable fun n => radiusVolume d r n ^ 2)
    (I : Finset ℕ)
    (hvsmall : ∀ n ∈ I, radiusVolume d r n ≤ 1 / 4) :
    (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (finiteAvoidanceKernel d r I z)
          ∂(flatTorusVolume d)) ≤
      ENNReal.ofReal (Real.exp
          (4 * ∑' n, radiusVolume d r n ^ 2)) *
        (∫⁻ z : FlatTorus d,
          ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
            ∂(flatTorusVolume d)) := by
  have hH : Measurable (flatTorusOverlapSum d r) := by
    unfold flatTorusOverlapSum
    exact Measurable.tsum fun n =>
      measurable_flatTorusOverlapTerm d hd hr hrsmall n
  have hexpH : Measurable fun z : FlatTorus d =>
      ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hH)
  calc
    (∫⁻ z : FlatTorus d,
        ENNReal.ofReal (finiteAvoidanceKernel d r I z)
          ∂(flatTorusVolume d)) ≤
        ∫⁻ z : FlatTorus d,
          ENNReal.ofReal (Real.exp
            (4 * ∑' n, radiusVolume d r n ^ 2)) *
            ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
              ∂(flatTorusVolume d) := by
      apply lintegral_mono_ae
      have hzero := flatTorusVolume_singleton_zero d (by omega)
      filter_upwards [compl_mem_ae_iff.2 hzero] with z hz
      have hz0 : z ≠ 0 := by simpa using hz
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      exact ENNReal.ofReal_le_ofReal
        (finiteAvoidanceKernel_le_global
          d hd hr hrsmall hrlim hsq I hvsmall hz0)
    _ = ENNReal.ofReal (Real.exp
          (4 * ∑' n, radiusVolume d r n ^ 2)) *
        (∫⁻ z : FlatTorus d,
          ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
            ∂(flatTorusVolume d)) := by
      exact lintegral_const_mul _ hexpH

end Shepp.Section7
end SheppFlattenedModule079

section SheppFlattenedModule080
open scoped ENNReal BigOperators
open MeasureTheory Set

namespace Shepp.Section7

theorem secondMoment_event_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZmeas : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hZ1 : ∀ ω, Z ω ≤ 1) {p B : ℝ}
    (hp : 0 < p) (hB : 0 < B)
    (hmean : MeasureTheory.integral μ Z = p)
    (hsecond : MeasureTheory.integral μ (fun ω => (Z ω) ^ 2) ≤ B * p ^ 2) :
    1 / B ≤ μ.real {ω | 0 < Z ω} := by
  let A : Set Ω := {ω | 0 < Z ω}
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const hZmeas
  let J : Ω → ℝ := A.indicator (fun _ => 1)
  have hJmeas : Measurable J := measurable_const.indicator hA
  have hJ0 : ∀ ω, 0 ≤ J ω := by
    intro ω
    simp only [J, Set.indicator]
    split_ifs <;> norm_num
  have hJ1 : ∀ ω, J ω ≤ 1 := by
    intro ω
    simp only [J, Set.indicator]
    split_ifs <;> norm_num
  have hJZ : ∀ ω, J ω * Z ω = Z ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp [J, hω]
    · have hz : Z ω = 0 := by
        have hnpos : ¬0 < Z ω := by simpa [A] using hω
        exact le_antisymm (not_lt.mp hnpos) (hZ0 ω)
      simp [J, hω, hz]
  have hJmem : MemLp J (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hJmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hJ0 ω)]
        exact hJ1 ω)
  have hZmem : MemLp Z (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hZmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 ω)]
        exact hZ1 ω)
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall hJ0)
    (Filter.Eventually.of_forall hZ0) hJmem hZmem
  have hleft : (∫ ω, J ω * Z ω ∂μ) = p := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hJZ), hmean]
  have hJsq : (∫ ω, J ω ^ (2 : ℝ) ∂μ) = μ.real A := by
    have hpow : (fun ω => J ω ^ (2 : ℝ)) = J := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [J, hω]
    rw [hpow]
    change (∫ ω, A.indicator (1 : Ω → ℝ) ω ∂μ) = μ.real A
    exact integral_indicator_one hA
  rw [hleft, hJsq] at hcs
  norm_num at hcs
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
  have hq0 : 0 ≤ μ.real A := measureReal_nonneg
  have hb0 : 0 ≤ ∫ ω, Z ω ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg (Z ω)
  have hsqrt0 : 0 ≤ √(μ.real A) * √(∫ ω, Z ω ^ 2 ∂μ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsquare : p ^ 2 ≤ μ.real A * (∫ ω, Z ω ^ 2 ∂μ) := by
    calc
      p ^ 2 ≤ (√(μ.real A) * √(∫ ω, Z ω ^ 2 ∂μ)) ^ 2 := by
        exact (sq_le_sq₀ hp.le hsqrt0).2 hcs
      _ = μ.real A * (∫ ω, Z ω ^ 2 ∂μ) := by
        rw [mul_pow, Real.sq_sqrt hq0, Real.sq_sqrt hb0]
  have hbound : p ^ 2 ≤ μ.real A * (B * p ^ 2) :=
    hsquare.trans (mul_le_mul_of_nonneg_left hsecond hq0)
  have hp2 : 0 < p ^ 2 := sq_pos_of_pos hp
  have hone : 1 ≤ μ.real A * B := by
    nlinarith [hbound]
  dsimp [A] at hone ⊢
  rw [div_le_iff₀ hB]
  simpa [mul_comm] using hone

end Shepp.Section7
end SheppFlattenedModule080

section SheppFlattenedModule081
open scoped ENNReal ProbabilityTheory Topology BigOperators
open Filter MeasureTheory Set

namespace Shepp.Section7

open ProbabilityTheory Shepp.Section2 Shepp.Section4 Shepp.Section5 Shepp.Section6

def centerMissesPointSet
    {d : ℕ} (r : ℕ → ℝ) (n : ℕ) (x : FlatTorus d) :
    Set (FlatTorus d) :=
  (Metric.ball x (r n))ᶜ

theorem measurableSet_centerMissesPointSet
    {d : ℕ} (r : ℕ → ℝ) (n : ℕ) (x : FlatTorus d) :
    MeasurableSet (centerMissesPointSet r n x) :=
  Metric.isOpen_ball.measurableSet.compl

theorem flatTorusVolumeReal_centerMissesPointSet
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrsmall : ∀ n, r n < 1 / 4)
    (n : ℕ) (x : FlatTorus d) :
    (flatTorusVolume d).real (centerMissesPointSet r n x) =
      1 - radiusVolume d r n := by
  rw [centerMissesPointSet,
    measureReal_compl Metric.isOpen_ball.measurableSet,
    probReal_univ,
    (flatTorusVolume d).addHaar_real_ball_center,
    flatTorusVolumeReal_ball_zero_eq_radiusVolume d hd hr hrsmall n]

theorem flatTorusVolumeReal_ballLens_eq_overlap_sub
    (d : ℕ) (r : ℕ → ℝ) (n : ℕ)
    (x y : FlatTorus d) :
    (flatTorusVolume d).real (flatTorusBallLens d (r n) x y) =
      flatTorusOverlapTerm d r n (y - x) := by
  let μ : Measure (FlatTorus d) := flatTorusVolume d
  let g : FlatTorus d → FlatTorus d := fun z => x + z
  have hpre : g ⁻¹' flatTorusBallLens d (r n) x y =
      flatTorusBallLens d (r n) 0 (y - x) := by
    ext z
    simp only [g, flatTorusBallLens, Set.mem_preimage,
      Set.mem_inter_iff, Metric.mem_ball]
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, dist_eq_norm]
    constructor
    · rintro ⟨hxz, hyz⟩
      constructor
      · simpa using hxz
      · convert hyz using 1 <;> abel
    · rintro ⟨hz0, hzy⟩
      constructor
      · simpa using hz0
      · convert hzy using 1 <;> abel
  have hmp : MeasurePreserving g μ μ :=
    MeasureTheory.measurePreserving_add_left μ x
  have hmeas : MeasurableSet (flatTorusBallLens d (r n) x y) :=
    Metric.isOpen_ball.measurableSet.inter
      Metric.isOpen_ball.measurableSet
  have hmeasure := hmp.measure_preimage hmeas.nullMeasurableSet
  rw [hpre] at hmeasure
  unfold flatTorusOverlapTerm
  have hreal := congrArg ENNReal.toReal hmeasure.symm
  simpa only [μ, Measure.real] using hreal

def centerMissesPairSet
    {d : ℕ} (r : ℕ → ℝ) (n : ℕ) (x y : FlatTorus d) :
    Set (FlatTorus d) :=
  (Metric.ball x (r n) ∪ Metric.ball y (r n))ᶜ

theorem measurableSet_centerMissesPairSet
    {d : ℕ} (r : ℕ → ℝ) (n : ℕ) (x y : FlatTorus d) :
    MeasurableSet (centerMissesPairSet r n x y) :=
  (Metric.isOpen_ball.measurableSet.union
    Metric.isOpen_ball.measurableSet).compl

theorem flatTorusVolumeReal_centerMissesPairSet
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrsmall : ∀ n, r n < 1 / 4)
    (n : ℕ) (x y : FlatTorus d) :
    (flatTorusVolume d).real (centerMissesPairSet r n x y) =
      1 - 2 * radiusVolume d r n +
        flatTorusOverlapTerm d r n (y - x) := by
  let A : Set (FlatTorus d) := Metric.ball x (r n)
  let B : Set (FlatTorus d) := Metric.ball y (r n)
  have hA : (flatTorusVolume d).real A = radiusVolume d r n := by
    rw [(flatTorusVolume d).addHaar_real_ball_center]
    exact flatTorusVolumeReal_ball_zero_eq_radiusVolume
      d hd hr hrsmall n
  have hB : (flatTorusVolume d).real B = radiusVolume d r n := by
    rw [(flatTorusVolume d).addHaar_real_ball_center]
    exact flatTorusVolumeReal_ball_zero_eq_radiusVolume
      d hd hr hrsmall n
  have hAB : (flatTorusVolume d).real (A ∩ B) =
      flatTorusOverlapTerm d r n (y - x) :=
    flatTorusVolumeReal_ballLens_eq_overlap_sub d r n x y
  have hunion := measureReal_union_add_inter
    (μ := flatTorusVolume d) (s := A) (t := B)
    Metric.isOpen_ball.measurableSet
  rw [hA, hB, hAB] at hunion
  rw [centerMissesPairSet,
    measureReal_compl
      (Metric.isOpen_ball.measurableSet.union
        Metric.isOpen_ball.measurableSet),
    probReal_univ]
  change 1 - (flatTorusVolume d).real (A ∪ B) = _
  linarith

noncomputable def finiteUncoveredSet
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ)
    (X : IIDCenterSample d) : Set (FlatTorus d) :=
  ⋂ n ∈ I, (Metric.ball (X n) (r n))ᶜ

theorem isClosed_finiteUncoveredSet
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ)
    (X : IIDCenterSample d) :
    IsClosed (finiteUncoveredSet r I X) := by
  classical
  unfold finiteUncoveredSet
  exact isClosed_biInter fun n _ => Metric.isOpen_ball.isClosed_compl

theorem measurableSet_finiteUncoveredSet
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ)
    (X : IIDCenterSample d) :
    MeasurableSet (finiteUncoveredSet r I X) :=
  (isClosed_finiteUncoveredSet r I X).measurableSet

def pointUncoveredEvent
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ) (x : FlatTorus d) :
    Set (IIDCenterSample d) :=
  {X | x ∈ finiteUncoveredSet r I X}

theorem pointUncoveredEvent_eq_iInter
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ) (x : FlatTorus d) :
    pointUncoveredEvent r I x =
      ⋂ n ∈ I,
        (fun X : IIDCenterSample d => X n) ⁻¹'
          centerMissesPointSet r n x := by
  ext X
  simp [pointUncoveredEvent, finiteUncoveredSet, centerMissesPointSet,
    dist_comm]

noncomputable def finiteAvoidanceProbability
    (d : ℕ) (r : ℕ → ℝ) (I : Finset ℕ) : ℝ :=
  ∏ n ∈ I, (1 - radiusVolume d r n)

theorem iidCenterMeasureReal_pointUncoveredEvent
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrsmall : ∀ n, r n < 1 / 4)
    (I : Finset ℕ) (x : FlatTorus d) :
    (iidCenterMeasure d).real (pointUncoveredEvent r I x) =
      finiteAvoidanceProbability d r I := by
  have hind := (iidCenterCoordinates_iIndepFun d).measure_inter_preimage_eq_mul
    I (sets := fun n => centerMissesPointSet r n x)
      (fun n _ => measurableSet_centerMissesPointSet r n x)
  rw [← pointUncoveredEvent_eq_iInter] at hind
  have hreal := congrArg ENNReal.toReal hind
  rw [ENNReal.toReal_prod] at hreal
  change (iidCenterMeasure d).real (pointUncoveredEvent r I x) =
      ∏ n ∈ I,
        (iidCenterMeasure d).real
          ((fun X : IIDCenterSample d => X n) ⁻¹'
            centerMissesPointSet r n x) at hreal
  have hcoord (n : ℕ) :
      (iidCenterMeasure d).real
          ((fun X : IIDCenterSample d => X n) ⁻¹'
            centerMissesPointSet r n x) =
        1 - radiusVolume d r n := by
    exact (iidCenterCoordinate_hasLaw d n).measureReal_eq
      (measurableSet_centerMissesPointSet r n x) |>.trans
        (flatTorusVolumeReal_centerMissesPointSet
          d hd hr hrsmall n x)
  have hprod :
      (∏ n ∈ I,
        (iidCenterMeasure d).real
          ((fun X : IIDCenterSample d => X n) ⁻¹'
            centerMissesPointSet r n x)) =
        finiteAvoidanceProbability d r I := by
    unfold finiteAvoidanceProbability
    apply Finset.prod_congr rfl
    intro n _hn
    exact hcoord n
  exact hreal.trans hprod

def pairUncoveredEvent
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ)
    (x y : FlatTorus d) : Set (IIDCenterSample d) :=
  {X | x ∈ finiteUncoveredSet r I X ∧
    y ∈ finiteUncoveredSet r I X}

theorem pairUncoveredEvent_eq_iInter
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ)
    (x y : FlatTorus d) :
    pairUncoveredEvent r I x y =
      ⋂ n ∈ I,
        (fun X : IIDCenterSample d => X n) ⁻¹'
          centerMissesPairSet r n x y := by
  ext X
  simp only [pairUncoveredEvent, finiteUncoveredSet,
    centerMissesPairSet, Set.mem_setOf_eq, Set.mem_iInter,
    Set.mem_preimage, Set.mem_compl_iff, Set.mem_union,
    Metric.mem_ball, not_or]
  constructor
  · rintro ⟨hx, hy⟩ n hn
    exact ⟨by simpa [dist_comm] using hx n hn,
      by simpa [dist_comm] using hy n hn⟩
  · intro h
    exact ⟨fun n hn => by simpa [dist_comm] using (h n hn).1,
      fun n hn => by simpa [dist_comm] using (h n hn).2⟩

noncomputable def finitePairAvoidanceProbability
    (d : ℕ) (r : ℕ → ℝ) (I : Finset ℕ)
    (x y : FlatTorus d) : ℝ :=
  ∏ n ∈ I,
    (1 - 2 * radiusVolume d r n +
      flatTorusOverlapTerm d r n (y - x))

theorem iidCenterMeasureReal_pairUncoveredEvent
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrsmall : ∀ n, r n < 1 / 4)
    (I : Finset ℕ) (x y : FlatTorus d) :
    (iidCenterMeasure d).real (pairUncoveredEvent r I x y) =
      finitePairAvoidanceProbability d r I x y := by
  have hind := (iidCenterCoordinates_iIndepFun d).measure_inter_preimage_eq_mul
    I (sets := fun n => centerMissesPairSet r n x y)
      (fun n _ => measurableSet_centerMissesPairSet r n x y)
  rw [← pairUncoveredEvent_eq_iInter] at hind
  have hreal := congrArg ENNReal.toReal hind
  rw [ENNReal.toReal_prod] at hreal
  change (iidCenterMeasure d).real (pairUncoveredEvent r I x y) =
      ∏ n ∈ I,
        (iidCenterMeasure d).real
          ((fun X : IIDCenterSample d => X n) ⁻¹'
            centerMissesPairSet r n x y) at hreal
  have hcoord (n : ℕ) :
      (iidCenterMeasure d).real
          ((fun X : IIDCenterSample d => X n) ⁻¹'
            centerMissesPairSet r n x y) =
        1 - 2 * radiusVolume d r n +
          flatTorusOverlapTerm d r n (y - x) := by
    exact (iidCenterCoordinate_hasLaw d n).measureReal_eq
      (measurableSet_centerMissesPairSet r n x y) |>.trans
        (flatTorusVolumeReal_centerMissesPairSet
          d hd hr hrsmall n x y)
  have hprod :
      (∏ n ∈ I,
        (iidCenterMeasure d).real
          ((fun X : IIDCenterSample d => X n) ⁻¹'
            centerMissesPairSet r n x y)) =
        finitePairAvoidanceProbability d r I x y := by
    unfold finitePairAvoidanceProbability
    apply Finset.prod_congr rfl
    intro n _hn
    exact hcoord n
  exact hreal.trans hprod

def finiteUncoveredPairs
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ) :
    Set (IIDCenterSample d × FlatTorus d) :=
  {p | p.2 ∈ finiteUncoveredSet r I p.1}

theorem measurableSet_finiteUncoveredPairs
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ) :
    MeasurableSet (finiteUncoveredPairs (d := d) r I) := by
  have heq : finiteUncoveredPairs (d := d) r I =
      ⋂ n ∈ I, {p : IIDCenterSample d × FlatTorus d |
        r n ≤ dist p.2 (p.1 n)} := by
    ext p
    simp [finiteUncoveredPairs, finiteUncoveredSet, Metric.mem_ball]
  rw [heq]
  exact I.finite_toSet.measurableSet_biInter fun n _hn =>
    measurableSet_le measurable_const
      (measurable_snd.dist ((measurable_pi_apply n).comp measurable_fst))

theorem finiteUncoveredPairs_slice
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ)
    (X : IIDCenterSample d) :
    Prod.mk X ⁻¹' finiteUncoveredPairs (d := d) r I =
      finiteUncoveredSet r I X :=
  rfl

noncomputable def finiteUncoveredMass
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ)
    (X : IIDCenterSample d) : ℝ :=
  (flatTorusVolume d).real (finiteUncoveredSet r I X)

theorem measurable_finiteUncoveredMass
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ) :
    Measurable (finiteUncoveredMass (d := d) r I) := by
  have hmeas : Measurable fun X : IIDCenterSample d =>
      flatTorusVolume d
        (Prod.mk X ⁻¹' finiteUncoveredPairs (d := d) r I) :=
    measurable_measure_prodMk_left
      (measurableSet_finiteUncoveredPairs (d := d) r I)
  have hreal := hmeas.ennreal_toReal
  change Measurable fun X : IIDCenterSample d =>
    (flatTorusVolume d
      (Prod.mk X ⁻¹' finiteUncoveredPairs (d := d) r I)).toReal at hreal
  change Measurable fun X : IIDCenterSample d =>
    (flatTorusVolume d (finiteUncoveredSet r I X)).toReal
  convert hreal using 1
  funext X
  rw [finiteUncoveredPairs_slice]

theorem finiteUncoveredMass_nonneg
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ)
    (X : IIDCenterSample d) :
    0 ≤ finiteUncoveredMass r I X :=
  measureReal_nonneg

theorem finiteUncoveredMass_le_one
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ)
    (X : IIDCenterSample d) :
    finiteUncoveredMass r I X ≤ 1 := by
  unfold finiteUncoveredMass
  rw [← probReal_univ (μ := flatTorusVolume d)]
  exact measureReal_mono (Set.subset_univ _)

theorem lintegral_finiteUncoveredMass
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrsmall : ∀ n, r n < 1 / 4)
    (I : Finset ℕ) :
    (∫⁻ X : IIDCenterSample d,
        ENNReal.ofReal (finiteUncoveredMass r I X)
          ∂(iidCenterMeasure d)) =
      ENNReal.ofReal (finiteAvoidanceProbability d r I) := by
  let S := finiteUncoveredPairs (d := d) r I
  have hS : MeasurableSet S :=
    measurableSet_finiteUncoveredPairs (d := d) r I
  have hswap : MeasurableSet (Prod.swap ⁻¹' S) :=
    hS.preimage measurable_swap
  have hof (X : IIDCenterSample d) :
      ENNReal.ofReal (finiteUncoveredMass r I X) =
        flatTorusVolume d (Prod.mk X ⁻¹' S) := by
    rw [finiteUncoveredMass, ← finiteUncoveredPairs_slice]
    exact ofReal_measureReal
  calc
    (∫⁻ X : IIDCenterSample d,
        ENNReal.ofReal (finiteUncoveredMass r I X)
          ∂(iidCenterMeasure d)) =
        ∫⁻ X : IIDCenterSample d,
          flatTorusVolume d (Prod.mk X ⁻¹' S)
            ∂(iidCenterMeasure d) := by
      apply lintegral_congr
      exact hof
    _ = ((iidCenterMeasure d).prod (flatTorusVolume d)) S := by
      exact (Measure.prod_apply hS).symm
    _ = ((flatTorusVolume d).prod (iidCenterMeasure d))
          (Prod.swap ⁻¹' S) := by
      exact (Measure.measurePreserving_swap
        (μ := flatTorusVolume d) (ν := iidCenterMeasure d)).measure_preimage
          hS.nullMeasurableSet |>.symm
    _ = ∫⁻ x : FlatTorus d,
          iidCenterMeasure d (Prod.mk x ⁻¹' (Prod.swap ⁻¹' S))
            ∂(flatTorusVolume d) := Measure.prod_apply hswap
    _ = ∫⁻ _x : FlatTorus d,
          ENNReal.ofReal (finiteAvoidanceProbability d r I)
            ∂(flatTorusVolume d) := by
      apply lintegral_congr
      intro x
      have hslice : Prod.mk x ⁻¹' (Prod.swap ⁻¹' S) =
          pointUncoveredEvent r I x := by
        rfl
      rw [hslice, ← ofReal_measureReal]
      rw [iidCenterMeasureReal_pointUncoveredEvent
        d hd hr hrsmall I x]
    _ = ENNReal.ofReal (finiteAvoidanceProbability d r I) := by
      simp

theorem finitePairAvoidanceProbability_eq_kernel
    (d : ℕ) {r : ℕ → ℝ} (I : Finset ℕ)
    (hvsmall : ∀ n ∈ I, radiusVolume d r n ≤ 1 / 4)
    (x y : FlatTorus d) :
    finitePairAvoidanceProbability d r I x y =
      finiteAvoidanceProbability d r I ^ 2 *
        finiteAvoidanceKernel d r I (y - x) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [finitePairAvoidanceProbability,
      finiteAvoidanceProbability, finiteAvoidanceKernel]
  | @insert n I hn hI =>
      have hvn := hvsmall n (Finset.mem_insert_self n I)
      have hden : 1 - radiusVolume d r n ≠ 0 := by nlinarith
      have htail : ∀ i ∈ I, radiusVolume d r i ≤ 1 / 4 := by
        intro i hi
        exact hvsmall i (Finset.mem_insert_of_mem hi)
      specialize hI htail
      simp only [finitePairAvoidanceProbability,
        finiteAvoidanceProbability, finiteAvoidanceKernel] at hI
      simp only [finitePairAvoidanceProbability,
        finiteAvoidanceProbability, finiteAvoidanceKernel,
        Finset.prod_insert hn]
      rw [hI]
      field_simp [hden]

def finiteDoubleUncoveredSet
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ) :
    Set (IIDCenterSample d × (FlatTorus d × FlatTorus d)) :=
  {p | p.2.1 ∈ finiteUncoveredSet r I p.1 ∧
    p.2.2 ∈ finiteUncoveredSet r I p.1}

theorem measurableSet_finiteDoubleUncoveredSet
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ) :
    MeasurableSet (finiteDoubleUncoveredSet (d := d) r I) := by
  let S := finiteUncoveredPairs (d := d) r I
  let L : IIDCenterSample d × (FlatTorus d × FlatTorus d) →
      IIDCenterSample d × FlatTorus d := fun p => (p.1, p.2.1)
  let R : IIDCenterSample d × (FlatTorus d × FlatTorus d) →
      IIDCenterSample d × FlatTorus d := fun p => (p.1, p.2.2)
  have hS : MeasurableSet S :=
    measurableSet_finiteUncoveredPairs (d := d) r I
  have hL : Measurable L :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hR : Measurable R :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  change MeasurableSet (L ⁻¹' S ∩ R ⁻¹' S)
  exact (hS.preimage hL).inter (hS.preimage hR)

theorem finiteDoubleUncoveredSet_slice
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ)
    (X : IIDCenterSample d) :
    Prod.mk X ⁻¹' finiteDoubleUncoveredSet (d := d) r I =
      finiteUncoveredSet r I X ×ˢ finiteUncoveredSet r I X := by
  ext p
  rfl

theorem finiteDoubleUncoveredSet_swap_slice
    {d : ℕ} (r : ℕ → ℝ) (I : Finset ℕ)
    (p : FlatTorus d × FlatTorus d) :
    Prod.mk p ⁻¹'
        (Prod.swap ⁻¹' finiteDoubleUncoveredSet (d := d) r I) =
      pairUncoveredEvent r I p.1 p.2 := by
  ext X
  rfl

theorem lintegral_finiteUncoveredMass_sq_eq_pair
    (d : ℕ) (hd : 0 < d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrsmall : ∀ n, r n < 1 / 4)
    (I : Finset ℕ) :
    (∫⁻ X : IIDCenterSample d,
        ENNReal.ofReal (finiteUncoveredMass r I X ^ 2)
          ∂(iidCenterMeasure d)) =
      ∫⁻ p : FlatTorus d × FlatTorus d,
        ENNReal.ofReal
          (finitePairAvoidanceProbability d r I p.1 p.2)
          ∂((flatTorusVolume d).prod (flatTorusVolume d)) := by
  let m : Measure (FlatTorus d) := flatTorusVolume d
  let P : Measure (IIDCenterSample d) := iidCenterMeasure d
  let D := finiteDoubleUncoveredSet (d := d) r I
  have hD : MeasurableSet D :=
    measurableSet_finiteDoubleUncoveredSet (d := d) r I
  have hswap : MeasurableSet (Prod.swap ⁻¹' D) :=
    hD.preimage measurable_swap
  have hof (X : IIDCenterSample d) :
      ENNReal.ofReal (finiteUncoveredMass r I X ^ 2) =
        (m.prod m) (Prod.mk X ⁻¹' D) := by
    rw [finiteDoubleUncoveredSet_slice]
    rw [Measure.prod_prod]
    rw [finiteUncoveredMass, ENNReal.ofReal_pow measureReal_nonneg]
    rw [ofReal_measureReal]
    ring
  calc
    (∫⁻ X : IIDCenterSample d,
        ENNReal.ofReal (finiteUncoveredMass r I X ^ 2) ∂P) =
        ∫⁻ X : IIDCenterSample d, (m.prod m) (Prod.mk X ⁻¹' D) ∂P := by
      apply lintegral_congr
      exact hof
    _ = (P.prod (m.prod m)) D := (Measure.prod_apply hD).symm
    _ = ((m.prod m).prod P) (Prod.swap ⁻¹' D) := by
      exact (Measure.measurePreserving_swap
        (μ := m.prod m) (ν := P)).measure_preimage
          hD.nullMeasurableSet |>.symm
    _ = ∫⁻ p : FlatTorus d × FlatTorus d,
          P (Prod.mk p ⁻¹' (Prod.swap ⁻¹' D)) ∂(m.prod m) :=
      Measure.prod_apply hswap
    _ = ∫⁻ p : FlatTorus d × FlatTorus d,
        ENNReal.ofReal
          (finitePairAvoidanceProbability d r I p.1 p.2) ∂(m.prod m) := by
      apply lintegral_congr
      intro p
      rw [finiteDoubleUncoveredSet_swap_slice]
      rw [← ofReal_measureReal]
      rw [iidCenterMeasureReal_pairUncoveredEvent
        d hd hr hrsmall I p.1 p.2]
    _ = ∫⁻ p : FlatTorus d × FlatTorus d,
        ENNReal.ofReal
          (finitePairAvoidanceProbability d r I p.1 p.2)
          ∂((flatTorusVolume d).prod (flatTorusVolume d)) := by
      rfl

theorem lintegral_finitePairAvoidanceProbability_eq_kernel
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (I : Finset ℕ)
    (hvsmall : ∀ n ∈ I, radiusVolume d r n ≤ 1 / 4) :
    (∫⁻ p : FlatTorus d × FlatTorus d,
        ENNReal.ofReal
          (finitePairAvoidanceProbability d r I p.1 p.2)
          ∂((flatTorusVolume d).prod (flatTorusVolume d))) =
      ENNReal.ofReal (finiteAvoidanceProbability d r I ^ 2) *
        (∫⁻ z : FlatTorus d,
          ENNReal.ofReal (finiteAvoidanceKernel d r I z)
            ∂(flatTorusVolume d)) := by
  let m : Measure (FlatTorus d) := flatTorusVolume d
  let c : ℝ≥0∞ :=
    ENNReal.ofReal (finiteAvoidanceProbability d r I ^ 2)
  let F : FlatTorus d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (finiteAvoidanceKernel d r I z)
  have hF : Measurable F := by
    exact ENNReal.measurable_ofReal.comp
      (measurable_finiteAvoidanceKernel d hd hr hrsmall I)
  have hsub : Measurable fun p : FlatTorus d × FlatTorus d =>
      F (p.2 - p.1) :=
    hF.comp (measurable_snd.sub measurable_fst)
  calc
    (∫⁻ p : FlatTorus d × FlatTorus d,
        ENNReal.ofReal
          (finitePairAvoidanceProbability d r I p.1 p.2) ∂(m.prod m)) =
        ∫⁻ p : FlatTorus d × FlatTorus d,
          c * F (p.2 - p.1) ∂(m.prod m) := by
      apply lintegral_congr
      intro p
      rw [finitePairAvoidanceProbability_eq_kernel
        d I hvsmall p.1 p.2]
      rw [ENNReal.ofReal_mul (sq_nonneg _)]
    _ = c * (∫⁻ p : FlatTorus d × FlatTorus d,
          F (p.2 - p.1) ∂(m.prod m)) :=
      lintegral_const_mul c hsub
    _ = c * (∫⁻ p : FlatTorus d × FlatTorus d,
          F p.2 ∂(m.prod m)) := by
      have hpres := (measurePreserving_prod_sub m m).lintegral_comp
        (hF.comp measurable_snd)
      simpa only [Function.comp_apply] using
        congrArg (fun q : ℝ≥0∞ => c * q) hpres
    _ = c * (∫⁻ z : FlatTorus d, F z ∂m) := by
      have hprod :
          (∫⁻ p : FlatTorus d × FlatTorus d,
              F p.2 ∂(m.prod m)) =
            ∫⁻ z : FlatTorus d, F z ∂m := by
        rw [lintegral_prod (fun p : FlatTorus d × FlatTorus d => F p.2)
          (hF.comp measurable_snd).aemeasurable]
        simp
      exact congrArg (fun q : ℝ≥0∞ => c * q) hprod
    _ = ENNReal.ofReal (finiteAvoidanceProbability d r I ^ 2) *
        (∫⁻ z : FlatTorus d,
          ENNReal.ofReal (finiteAvoidanceKernel d r I z)
            ∂(flatTorusVolume d)) := by
      rfl

noncomputable def finiteEnergyIntegral
    (d : ℕ) (r : ℕ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z : FlatTorus d,
    ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
      ∂(flatTorusVolume d)

noncomputable def finiteEnergyMomentBound
    (d : ℕ) (r : ℕ → ℝ) : ℝ :=
  Real.exp (4 * ∑' n, radiusVolume d r n ^ 2) *
    (finiteEnergyIntegral d r).toReal

theorem finiteEnergyIntegral_one_le
    (d : ℕ) (r : ℕ → ℝ) :
    1 ≤ finiteEnergyIntegral d r := by
  have hH0 (z : FlatTorus d) :
      0 ≤ flatTorusOverlapSum d r z := by
    unfold flatTorusOverlapSum
    exact tsum_nonneg fun n => flatTorusOverlapTerm_nonneg d r n z
  calc
    (1 : ℝ≥0∞) = ∫⁻ _z : FlatTorus d, (1 : ℝ≥0∞)
        ∂(flatTorusVolume d) := by simp
    _ ≤ ∫⁻ z : FlatTorus d,
        ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
          ∂(flatTorusVolume d) := by
      apply lintegral_mono
      intro z
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (hH0 z))
    _ = finiteEnergyIntegral d r := rfl

theorem finiteEnergyMomentBound_pos
    (d : ℕ) (r : ℕ → ℝ)
    (hfinite : finiteEnergyIntegral d r < ∞) :
    0 < finiteEnergyMomentBound d r := by
  have hE0 : finiteEnergyIntegral d r ≠ 0 := by
    exact ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le
      (finiteEnergyIntegral_one_le d r))
  unfold finiteEnergyMomentBound
  exact mul_pos (Real.exp_pos _)
    (ENNReal.toReal_pos hE0 hfinite.ne)

theorem lintegral_finiteUncoveredMass_sq_le_energy_bound
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (nhds 0))
    (hfinite : finiteEnergyIntegral d r < ∞)
    (I : Finset ℕ)
    (hvsmall : ∀ n ∈ I, radiusVolume d r n ≤ 1 / 4) :
    (∫⁻ X : IIDCenterSample d,
        ENNReal.ofReal (finiteUncoveredMass r I X ^ 2)
          ∂(iidCenterMeasure d)) ≤
      ENNReal.ofReal
        (finiteEnergyMomentBound d r *
          finiteAvoidanceProbability d r I ^ 2) := by
  have hsq : Summable fun n => radiusVolume d r n ^ 2 :=
    squareSummable_of_finite_overlap_energy
      d hd hr hrsmall hrlim hfinite
  have hkernel := lintegral_finiteAvoidanceKernel_le_global
    d hd hr hrsmall hrlim hsq I hvsmall
  have hpair := lintegral_finiteUncoveredMass_sq_eq_pair
    d (by omega) (fun n => (hr n).le) hrsmall I
  have hreduce := lintegral_finitePairAvoidanceProbability_eq_kernel
    d hd hr hrsmall I hvsmall
  rw [hpair, hreduce]
  calc
    ENNReal.ofReal (finiteAvoidanceProbability d r I ^ 2) *
        (∫⁻ z : FlatTorus d,
          ENNReal.ofReal (finiteAvoidanceKernel d r I z)
            ∂(flatTorusVolume d)) ≤
      ENNReal.ofReal (finiteAvoidanceProbability d r I ^ 2) *
        (ENNReal.ofReal (Real.exp
            (4 * ∑' n, radiusVolume d r n ^ 2)) *
          finiteEnergyIntegral d r) := by
      gcongr
      simpa [finiteEnergyIntegral] using hkernel
    _ = ENNReal.ofReal
        (finiteEnergyMomentBound d r *
          finiteAvoidanceProbability d r I ^ 2) := by
      rw [← ENNReal.ofReal_toReal hfinite.ne]
      unfold finiteEnergyMomentBound
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      rw [mul_comm (ENNReal.ofReal (finiteAvoidanceProbability d r I ^ 2))]
      rw [← ENNReal.ofReal_mul
        (mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg)]

theorem finiteAvoidanceProbability_pos
    (d : ℕ) {r : ℕ → ℝ} (I : Finset ℕ)
    (hvsmall : ∀ n ∈ I, radiusVolume d r n ≤ 1 / 4) :
    0 < finiteAvoidanceProbability d r I := by
  unfold finiteAvoidanceProbability
  exact Finset.prod_pos fun n hn => by
    nlinarith [hvsmall n hn]

theorem integral_finiteUncoveredMass
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (I : Finset ℕ)
    (hvsmall : ∀ n ∈ I, radiusVolume d r n ≤ 1 / 4) :
    (∫ X : IIDCenterSample d,
        finiteUncoveredMass r I X ∂(iidCenterMeasure d)) =
      finiteAvoidanceProbability d r I := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun X =>
      finiteUncoveredMass_nonneg r I X)
    (measurable_finiteUncoveredMass (d := d) r I).aestronglyMeasurable]
  rw [lintegral_finiteUncoveredMass d (by omega)
    (fun n => (hr n).le) hrsmall I]
  exact ENNReal.toReal_ofReal
    (finiteAvoidanceProbability_pos d I hvsmall).le

theorem integral_finiteUncoveredMass_sq_le_energy_bound
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (nhds 0))
    (hfinite : finiteEnergyIntegral d r < ∞)
    (I : Finset ℕ)
    (hvsmall : ∀ n ∈ I, radiusVolume d r n ≤ 1 / 4) :
    (∫ X : IIDCenterSample d,
        finiteUncoveredMass r I X ^ 2 ∂(iidCenterMeasure d)) ≤
      finiteEnergyMomentBound d r *
        finiteAvoidanceProbability d r I ^ 2 := by
  have hlin := lintegral_finiteUncoveredMass_sq_le_energy_bound
    d hd hr hrsmall hrlim hfinite I hvsmall
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun X =>
      sq_nonneg (finiteUncoveredMass r I X))
    ((measurable_finiteUncoveredMass (d := d) r I).pow_const 2).aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofReal
    (mul_nonneg (finiteEnergyMomentBound_pos d r hfinite).le
      (sq_nonneg (finiteAvoidanceProbability d r I)))] using hreal

theorem iidCenterMeasureReal_finiteUncoveredMass_pos_lower_bound
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (nhds 0))
    (hfinite : finiteEnergyIntegral d r < ∞)
    (I : Finset ℕ)
    (hvsmall : ∀ n ∈ I, radiusVolume d r n ≤ 1 / 4) :
    1 / finiteEnergyMomentBound d r ≤
      (iidCenterMeasure d).real
        {X | 0 < finiteUncoveredMass r I X} := by
  apply secondMoment_event_lower_bound (iidCenterMeasure d)
    (measurable_finiteUncoveredMass (d := d) r I)
    (fun X => finiteUncoveredMass_nonneg r I X)
    (fun X => finiteUncoveredMass_le_one r I X)
    (finiteAvoidanceProbability_pos d I hvsmall)
    (finiteEnergyMomentBound_pos d r hfinite)
  · exact integral_finiteUncoveredMass
      d hd hr hrsmall I hvsmall
  · exact integral_finiteUncoveredMass_sq_le_energy_bound
      d hd hr hrsmall hrlim hfinite I hvsmall

theorem tendsto_radiusVolume_zero
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hrlim : Tendsto r atTop (nhds 0)) :
    Tendsto (radiusVolume d r) atTop (nhds 0) := by
  unfold radiusVolume
  convert tendsto_const_nhds.mul (hrlim.pow d) using 1
  simp [show d ≠ 0 by omega]

theorem exists_radiusVolume_tail_le_quarter
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hrlim : Tendsto r atTop (nhds 0)) :
    ∃ s : ℕ, ∀ n, s ≤ n → radiusVolume d r n ≤ 1 / 4 := by
  have hev : ∀ᶠ n : ℕ in atTop,
      radiusVolume d r n < 1 / 4 :=
    (tendsto_radiusVolume_zero d hd hrlim).eventually_lt_const (by norm_num)
  rw [eventually_atTop] at hev
  obtain ⟨s, hs⟩ := hev
  exact ⟨s, fun n hn => (hs n hn).le⟩

def tailFiniteIndexSet (s N : ℕ) : Finset ℕ :=
  Finset.Icc s (s + N)

def tailFinitePositiveMassEvent
    {d : ℕ} (r : ℕ → ℝ) (s N : ℕ) :
    Set (IIDCenterSample d) :=
  {X | 0 < finiteUncoveredMass r (tailFiniteIndexSet s N) X}

theorem measurableSet_tailFinitePositiveMassEvent
    {d : ℕ} (r : ℕ → ℝ) (s N : ℕ) :
    MeasurableSet (tailFinitePositiveMassEvent (d := d) r s N) :=
  measurableSet_lt measurable_const
    (measurable_finiteUncoveredMass (d := d) r (tailFiniteIndexSet s N))

theorem finiteUncoveredSet_anti
    {d : ℕ} (r : ℕ → ℝ) {I J : Finset ℕ}
    (hIJ : I ⊆ J) (X : IIDCenterSample d) :
    finiteUncoveredSet r J X ⊆ finiteUncoveredSet r I X := by
  intro z hz
  simp only [finiteUncoveredSet, Set.mem_iInter] at hz ⊢
  intro n hn
  exact hz n (hIJ hn)

theorem finiteUncoveredMass_anti
    {d : ℕ} (r : ℕ → ℝ) {I J : Finset ℕ}
    (hIJ : I ⊆ J) (X : IIDCenterSample d) :
    finiteUncoveredMass r J X ≤ finiteUncoveredMass r I X := by
  unfold finiteUncoveredMass
  exact measureReal_mono (finiteUncoveredSet_anti r hIJ X)

theorem antitone_tailFinitePositiveMassEvent
    {d : ℕ} (r : ℕ → ℝ) (s : ℕ) :
    Antitone (tailFinitePositiveMassEvent (d := d) r s) := by
  intro N M hNM X hX
  have hsub : tailFiniteIndexSet s N ⊆ tailFiniteIndexSet s M := by
    intro n hn
    simp only [tailFiniteIndexSet, Finset.mem_Icc] at hn ⊢
    omega
  exact lt_of_lt_of_le hX (finiteUncoveredMass_anti r hsub X)

def tailPositiveMassLimitEvent
    {d : ℕ} (r : ℕ → ℝ) (s : ℕ) :
    Set (IIDCenterSample d) :=
  ⋂ N : ℕ, tailFinitePositiveMassEvent (d := d) r s N

theorem measurableSet_tailPositiveMassLimitEvent
    {d : ℕ} (r : ℕ → ℝ) (s : ℕ) :
    MeasurableSet (tailPositiveMassLimitEvent (d := d) r s) :=
  MeasurableSet.iInter fun N =>
    measurableSet_tailFinitePositiveMassEvent r s N

theorem iidCenterMeasure_tailPositiveMassLimitEvent_pos
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (nhds 0))
    (hfinite : finiteEnergyIntegral d r < ∞)
    (s : ℕ)
    (hvsmall : ∀ n, s ≤ n → radiusVolume d r n ≤ 1 / 4) :
    0 < iidCenterMeasure d (tailPositiveMassLimitEvent (d := d) r s) := by
  let A : ℕ → Set (IIDCenterSample d) :=
    tailFinitePositiveMassEvent (d := d) r s
  let b : ℝ := 1 / finiteEnergyMomentBound d r
  have hb : 0 < b := one_div_pos.mpr
    (finiteEnergyMomentBound_pos d r hfinite)
  have hlower (N : ℕ) :
      ENNReal.ofReal b ≤ iidCenterMeasure d (A N) := by
    have hvI : ∀ n ∈ tailFiniteIndexSet s N,
        radiusVolume d r n ≤ 1 / 4 := by
      intro n hn
      exact hvsmall n (Finset.mem_Icc.1 hn).1
    have hreal :=
      iidCenterMeasureReal_finiteUncoveredMass_pos_lower_bound
        d hd hr hrsmall hrlim hfinite (tailFiniteIndexSet s N) hvI
    have hof := ENNReal.ofReal_le_ofReal hreal
    rw [ofReal_measureReal] at hof
    exact hof
  have hmeasure :
      iidCenterMeasure d (⋂ N, A N) =
        ⨅ N, iidCenterMeasure d (A N) := by
    exact (antitone_tailFinitePositiveMassEvent (d := d) r s).measure_iInter
      (fun N => (measurableSet_tailFinitePositiveMassEvent r s N).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  have hlowerLimit :
      ENNReal.ofReal b ≤ iidCenterMeasure d (⋂ N, A N) := by
    rw [hmeasure]
    exact le_iInf hlower
  have hofpos : 0 < ENNReal.ofReal b := ENNReal.ofReal_pos.mpr hb
  change 0 < iidCenterMeasure d (⋂ N, A N)
  exact hofpos.trans_le hlowerLimit

theorem tailPositiveMassLimitEvent_disjoint_iidLimsupCoverEvent
    {d : ℕ} (r : ℕ → ℝ) (s : ℕ) :
    Disjoint (tailPositiveMassLimitEvent (d := d) r s)
      (iidLimsupCoverEvent (d := d) r) := by
  rw [Set.disjoint_left]
  intro X hmass hcover
  let F : ℕ → Set (FlatTorus d) := fun N =>
    finiteUncoveredSet r (tailFiniteIndexSet s N) X
  have hdec : ∀ N, F (N + 1) ⊆ F N := by
    intro N
    apply finiteUncoveredSet_anti r
    intro n hn
    simp only [tailFiniteIndexSet, Finset.mem_Icc] at hn ⊢
    omega
  have hne : ∀ N, (F N).Nonempty := by
    intro N
    have hpos : 0 < finiteUncoveredMass
        r (tailFiniteIndexSet s N) X := by
      exact Set.mem_iInter.1 hmass N
    exact nonempty_of_measureReal_ne_zero hpos.ne'
  have hcompact : ∀ N, IsCompact (F N) := fun N =>
    (isClosed_finiteUncoveredSet r (tailFiniteIndexSet s N) X).isCompact
  obtain ⟨z, hz⟩ := Shepp.Section4.decreasing_compact_iInter_nonempty
    F hdec hne hcompact
  have hzNotCovered : z ∉ iidCentersCoveredFrom r s X := by
    intro hzCovered
    obtain ⟨n, hsn, hzball⟩ :=
      (mem_iidCentersCoveredFrom_iff r s X z).1 hzCovered
    let N : ℕ := n - s
    have hnmem : n ∈ tailFiniteIndexSet s N := by
      simp only [tailFiniteIndexSet, Finset.mem_Icc, N]
      exact ⟨hsn, by omega⟩
    have hzF : z ∈ F N := Set.mem_iInter.1 hz N
    have hzmiss : z ∈ (Metric.ball (X n) (r n))ᶜ := by
      exact Set.mem_iInter.1 (Set.mem_iInter.1 hzF n) hnmem
    exact hzmiss hzball
  have hzlimsup : z ∈ iidLimsupSet r X := by
    rw [(mem_iidLimsupCoverEvent_iff r X).1 hcover]
    exact Set.mem_univ z
  rw [iidLimsupSet_eq_iInter_coveredFrom] at hzlimsup
  exact hzNotCovered (Set.mem_iInter.1 hzlimsup s)

abbrev TailFiniteIndex (s N : ℕ) :=
  {n : ℕ // n ∈ tailFiniteIndexSet s N}

noncomputable def iidTailFiniteSupports
    {d : ℕ} (s N : ℕ) (X : IIDCenterSample d) :
    TailFiniteIndex s N → CompactResidual (FlatTorus d) :=
  fun n => ({X n} : CompactResidual (FlatTorus d))

def iidTailFiniteCoverEvent
    {d : ℕ} (r : ℕ → ℝ) (s N : ℕ) :
    Set (IIDCenterSample d) :=
  iidTailFiniteSupports (d := d) s N ⁻¹'
    compactSupportCoverEvent
      (K := FlatTorus d) (fun n : TailFiniteIndex s N => r n)

theorem measurable_iidTailFiniteSupports
    {d : ℕ} (s N : ℕ) :
    Measurable (iidTailFiniteSupports (d := d) s N) := by
  apply measurable_pi_lambda
  intro n
  exact (measurable_pi_apply (n : ℕ)).comp
    (measurable_iidSingletonSupports (d := d))

theorem measurableSet_iidTailFiniteCoverEvent
    {d : ℕ} (r : ℕ → ℝ) (s N : ℕ) :
    MeasurableSet (iidTailFiniteCoverEvent (d := d) r s N) := by
  exact (measurableSet_compactSupportCoverEvent
    (K := FlatTorus d) (fun n : TailFiniteIndex s N => r n)).preimage
      (measurable_iidTailFiniteSupports (d := d) s N)

theorem mem_iidTailFiniteCoverEvent_iff
    {d : ℕ} (r : ℕ → ℝ) (s N : ℕ)
    (X : IIDCenterSample d) :
    X ∈ iidTailFiniteCoverEvent (d := d) r s N ↔
      finiteUncoveredSet r (tailFiniteIndexSet s N) X = ∅ := by
  change compactSupportsCovered
      (fun n : TailFiniteIndex s N => r n)
      (iidTailFiniteSupports (d := d) s N X) = Set.univ ↔ _
  rw [Set.eq_univ_iff_forall, Set.eq_empty_iff_forall_notMem]
  simp only [compactSupportsCovered, iidTailFiniteSupports,
    finiteUncoveredSet, Set.mem_iUnion, Set.mem_iInter,
    Set.mem_compl_iff]
  constructor
  · intro h z hz
    obtain ⟨n, x, hx, hzball⟩ := h z
    subst x
    exact (hz n n.property) hzball
  · intro h z
    by_contra hz
    push Not at hz
    exact h z (fun n hn => hz ⟨n, hn⟩ (X n) (by simp))

def iidTailCoverEvent
    {d : ℕ} (r : ℕ → ℝ) (s : ℕ) :
    Set (IIDCenterSample d) :=
  ⋃ N : ℕ, iidTailFiniteCoverEvent (d := d) r s N

theorem measurableSet_iidTailCoverEvent
    {d : ℕ} (r : ℕ → ℝ) (s : ℕ) :
    MeasurableSet (iidTailCoverEvent (d := d) r s) :=
  MeasurableSet.iUnion fun N =>
    measurableSet_iidTailFiniteCoverEvent r s N

theorem mem_iidTailCoverEvent_iff
    {d : ℕ} (r : ℕ → ℝ) (s : ℕ)
    (X : IIDCenterSample d) :
    X ∈ iidTailCoverEvent (d := d) r s ↔
      iidCentersCoveredFrom r s X = Set.univ := by
  constructor
  · intro hX
    obtain ⟨N, hN⟩ := Set.mem_iUnion.1 hX
    have hF := (mem_iidTailFiniteCoverEvent_iff r s N X).1 hN
    apply Set.eq_univ_of_univ_subset
    intro z _hz
    by_contra hzCovered
    have hzF : z ∈ finiteUncoveredSet
        r (tailFiniteIndexSet s N) X := by
      simp only [finiteUncoveredSet, Set.mem_iInter,
        Set.mem_compl_iff]
      intro n hn hzball
      apply hzCovered
      exact (mem_iidCentersCoveredFrom_iff r s X z).2
        ⟨n, (Finset.mem_Icc.1 hn).1, hzball⟩
    rw [hF] at hzF
    exact hzF
  · intro hcover
    let U : {n : ℕ // s ≤ n} → Set (FlatTorus d) :=
      fun n => Metric.ball (X n) (r n)
    have hU : ∀ n, IsOpen (U n) := fun _ => Metric.isOpen_ball
    have huniv : Set.univ ⊆ ⋃ n, U n := by
      intro z _hz
      have hzCovered : z ∈ iidCentersCoveredFrom r s X := by
        rw [hcover]
        exact Set.mem_univ z
      obtain ⟨n, hn, hzball⟩ :=
        (mem_iidCentersCoveredFrom_iff r s X z).1 hzCovered
      exact Set.mem_iUnion.2 ⟨⟨n, hn⟩, hzball⟩
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU huniv
    let N : ℕ := t.sup fun n => (n : ℕ)
    apply Set.mem_iUnion.2
    refine ⟨N, (mem_iidTailFiniteCoverEvent_iff r s N X).2 ?_⟩
    apply Set.eq_empty_iff_forall_notMem.2
    intro z hzF
    have hzUnion := ht (Set.mem_univ z)
    simp only [Set.mem_iUnion] at hzUnion
    obtain ⟨n, hn, hzball⟩ := hzUnion
    have hnle : (n : ℕ) ≤ N := Finset.le_sup hn
    have hnI : (n : ℕ) ∈ tailFiniteIndexSet s N := by
      simp only [tailFiniteIndexSet, Finset.mem_Icc]
      exact ⟨n.property, hnle.trans (Nat.le_add_left N s)⟩
    have hzmiss : z ∈ (Metric.ball (X n) (r n))ᶜ := by
      exact Set.mem_iInter.1 (Set.mem_iInter.1 hzF (n : ℕ)) hnI
    exact hzmiss hzball

def iidAllTailCoverEvent
    {d : ℕ} (r : ℕ → ℝ) : Set (IIDCenterSample d) :=
  ⋂ s : ℕ, iidTailCoverEvent (d := d) r s

theorem iidAllTailCoverEvent_eq_iidLimsupCoverEvent
    {d : ℕ} (r : ℕ → ℝ) :
    iidAllTailCoverEvent (d := d) r =
      iidLimsupCoverEvent (d := d) r := by
  ext X
  simp only [iidAllTailCoverEvent, Set.mem_iInter]
  constructor
  · intro htails
    rw [mem_iidLimsupCoverEvent_iff,
      iidLimsupSet_eq_iInter_coveredFrom]
    apply Set.eq_univ_of_univ_subset
    intro z _hz
    apply Set.mem_iInter.2
    intro s
    rw [(mem_iidTailCoverEvent_iff r s X).1 (htails s)]
    exact Set.mem_univ z
  · intro hlimsup s
    apply (mem_iidTailCoverEvent_iff r s X).2
    apply Set.eq_univ_of_univ_subset
    intro z _hz
    have hzlimsup : z ∈ iidLimsupSet r X := by
      rw [(mem_iidLimsupCoverEvent_iff r X).1 hlimsup]
      exact Set.mem_univ z
    rw [iidLimsupSet_eq_iInter_coveredFrom] at hzlimsup
    exact Set.mem_iInter.1 hzlimsup s

theorem iidTailCoverEvent_anti
    {d : ℕ} (r : ℕ → ℝ) {s q : ℕ} (hsq : s ≤ q) :
    iidTailCoverEvent (d := d) r q ⊆
      iidTailCoverEvent (d := d) r s := by
  intro X hq
  apply (mem_iidTailCoverEvent_iff r s X).2
  have hqcover := (mem_iidTailCoverEvent_iff r q X).1 hq
  apply Set.eq_univ_of_univ_subset
  intro z _hz
  have hzq : z ∈ iidCentersCoveredFrom r q X := by
    rw [hqcover]
    exact Set.mem_univ z
  obtain ⟨n, hqn, hzball⟩ :=
    (mem_iidCentersCoveredFrom_iff r q X z).1 hzq
  exact (mem_iidCentersCoveredFrom_iff r s X z).2
    ⟨n, hsq.trans hqn, hzball⟩

theorem iidAllTailCoverEvent_eq_iInter_add
    {d : ℕ} (r : ℕ → ℝ) (m : ℕ) :
    iidAllTailCoverEvent (d := d) r =
      ⋂ k : ℕ, iidTailCoverEvent (d := d) r (m + k) := by
  ext X
  simp only [iidAllTailCoverEvent, Set.mem_iInter]
  constructor
  · intro h k
    exact h (m + k)
  · intro h s
    let k : ℕ := max m s - m
    have hmk : m + k = max m s := by
      dsimp [k]
      omega
    apply iidTailCoverEvent_anti r (show s ≤ m + k by omega)
    exact h k

theorem measurable_compactResidual_singleton (d : ℕ) :
    Measurable fun x : FlatTorus d =>
      ({x} : CompactResidual (FlatTorus d)) := by
  let diagonal : FlatTorus d → IIDCenterSample d := fun x _n => x
  have hdiagonal : Measurable diagonal := by
    apply measurable_pi_lambda
    intro n
    exact measurable_id
  have h := (measurable_pi_apply 0).comp
    ((measurable_iidSingletonSupports (d := d)).comp hdiagonal)
  change Measurable (fun x : FlatTorus d =>
    ({x} : CompactResidual (FlatTorus d))) at h
  exact h

theorem measurable_iidTailFiniteSupports_of_coordinates
    {d : ℕ} (m : MeasurableSpace (IIDCenterSample d))
    (s N : ℕ)
    (hcoord : ∀ n ∈ tailFiniteIndexSet s N,
      Measurable[m] fun X : IIDCenterSample d => X n) :
    Measurable[m] (iidTailFiniteSupports (d := d) s N) := by
  apply measurable_pi_lambda
  intro n
  exact (measurable_compactResidual_singleton d).comp
    (hcoord n n.property)

theorem measurableSet_iidTailFiniteCoverEvent_of_coordinates
    {d : ℕ} (m : MeasurableSpace (IIDCenterSample d))
    (r : ℕ → ℝ) (s N : ℕ)
    (hcoord : ∀ n ∈ tailFiniteIndexSet s N,
      Measurable[m] fun X : IIDCenterSample d => X n) :
    MeasurableSet[m] (iidTailFiniteCoverEvent (d := d) r s N) := by
  exact (measurableSet_compactSupportCoverEvent
    (K := FlatTorus d) (fun n : TailFiniteIndex s N => r n)).preimage
      (measurable_iidTailFiniteSupports_of_coordinates m s N hcoord)

@[instance_reducible]
def iidCenterCoordinateSigma (d n : ℕ) :
    MeasurableSpace (IIDCenterSample d) :=
  MeasurableSpace.comap (fun X : IIDCenterSample d => X n) inferInstance

@[instance_reducible]
def iidCenterTailSigma (d m : ℕ) :
    MeasurableSpace (IIDCenterSample d) :=
  ⨆ n : ℕ, ⨆ (_h : m ≤ n), iidCenterCoordinateSigma d n

theorem iidCenterCoordinateSigma_le
    (d n : ℕ) :
    iidCenterCoordinateSigma d n ≤
      (inferInstance : MeasurableSpace (IIDCenterSample d)) := by
  exact (measurable_pi_apply n).comap_le

theorem iidCenterCoordinateSigma_iIndep (d : ℕ) :
    iIndep (iidCenterCoordinateSigma d) (iidCenterMeasure d) := by
  unfold iidCenterCoordinateSigma
  exact (iIndepFun_iff_iIndep
    (fun _n : ℕ => inferInstance)
    (fun n (X : IIDCenterSample d) => X n)
    (iidCenterMeasure d)).1 (iidCenterCoordinates_iIndepFun d)

theorem measurable_eval_iidCenterTailSigma
    (d m n : ℕ) (hmn : m ≤ n) :
    Measurable[iidCenterTailSigma d m]
      (fun X : IIDCenterSample d => X n) := by
  apply Measurable.of_comap_le
  change iidCenterCoordinateSigma d n ≤ iidCenterTailSigma d m
  unfold iidCenterTailSigma
  exact le_iSup_of_le n (le_iSup_of_le hmn le_rfl)

theorem measurableSet_iidTailFiniteCoverEvent_tailSigma
    {d : ℕ} (r : ℕ → ℝ) {m s : ℕ} (hms : m ≤ s) (N : ℕ) :
    MeasurableSet[iidCenterTailSigma d m]
      (iidTailFiniteCoverEvent (d := d) r s N) := by
  apply measurableSet_iidTailFiniteCoverEvent_of_coordinates
  intro n hn
  exact measurable_eval_iidCenterTailSigma d m n
    (hms.trans (Finset.mem_Icc.1 hn).1)

theorem measurableSet_iidTailCoverEvent_tailSigma
    {d : ℕ} (r : ℕ → ℝ) {m s : ℕ} (hms : m ≤ s) :
    MeasurableSet[iidCenterTailSigma d m]
      (iidTailCoverEvent (d := d) r s) := by
  unfold iidTailCoverEvent
  exact MeasurableSet.iUnion fun N =>
    measurableSet_iidTailFiniteCoverEvent_tailSigma r hms N

theorem measurableSet_iidAllTailCoverEvent_tailSigma
    {d : ℕ} (r : ℕ → ℝ) (m : ℕ) :
    MeasurableSet[iidCenterTailSigma d m]
      (iidAllTailCoverEvent (d := d) r) := by
  rw [iidAllTailCoverEvent_eq_iInter_add r m]
  exact MeasurableSet.iInter fun k =>
    measurableSet_iidTailCoverEvent_tailSigma r
      (show m ≤ m + k by omega)

theorem measurableSet_iidLimsupCoverEvent
    {d : ℕ} (r : ℕ → ℝ) :
    MeasurableSet (iidLimsupCoverEvent (d := d) r) := by
  rw [← iidAllTailCoverEvent_eq_iidLimsupCoverEvent r]
  unfold iidAllTailCoverEvent
  exact MeasurableSet.iInter fun s =>
    measurableSet_iidTailCoverEvent r s

theorem measurableSet_iidLimsupCoverEvent_tail
    {d : ℕ} (r : ℕ → ℝ) :
    MeasurableSet[limsup (iidCenterCoordinateSigma d) atTop]
      (iidLimsupCoverEvent (d := d) r) := by
  rw [← iidAllTailCoverEvent_eq_iidLimsupCoverEvent r]
  rw [limsup_eq_iInf_iSup_of_nat]
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  change MeasurableSet[iidCenterTailSigma d m]
    (iidAllTailCoverEvent (d := d) r)
  exact measurableSet_iidAllTailCoverEvent_tailSigma (d := d) r m

theorem iidCenterMeasure_iidLimsupCoverEvent_zero_or_one
    {d : ℕ} (r : ℕ → ℝ) :
    iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 0 ∨
      iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 1 := by
  exact measure_zero_or_one_of_measurableSet_limsup_atTop
    (iidCenterCoordinateSigma_le d)
    (iidCenterCoordinateSigma_iIndep d)
    (measurableSet_iidLimsupCoverEvent_tail r)

theorem finiteEnergyNoncovering
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hrlim : Tendsto r atTop (nhds 0))
    (hfinite : finiteEnergyIntegral d r < ∞) :
    iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 0 := by
  obtain ⟨s, hvsmall⟩ :=
    exists_radiusVolume_tail_le_quarter d hd hrlim
  let A := tailPositiveMassLimitEvent (d := d) r s
  let E := iidLimsupCoverEvent (d := d) r
  have hApos : 0 < iidCenterMeasure d A :=
    iidCenterMeasure_tailPositiveMassLimitEvent_pos
      d hd hr hrsmall hrlim hfinite s hvsmall
  have hdisjoint : Disjoint A E :=
    tailPositiveMassLimitEvent_disjoint_iidLimsupCoverEvent r s
  rcases iidCenterMeasure_iidLimsupCoverEvent_zero_or_one
      (d := d) r with hzero | hone
  · exact hzero
  · exfalso
    have hEmeas : MeasurableSet E :=
      measurableSet_iidLimsupCoverEvent r
    have hcompl : iidCenterMeasure d Eᶜ = 0 := by
      rw [measure_compl hEmeas (measure_ne_top _ _), measure_univ, hone]
      simp
    have hsubset : A ⊆ Eᶜ := by
      intro X hXA hXE
      exact Set.disjoint_left.1 hdisjoint hXA hXE
    have hmeasure := measure_mono (μ := iidCenterMeasure d) hsubset
    rw [hcompl] at hmeasure
    exact (not_lt_of_ge hmeasure) hApos

end Shepp.Section7
end SheppFlattenedModule081

section SheppFlattenedModule082
open scoped BigOperators ENNReal
open MeasureTheory Filter Set

namespace Shepp.Section2

theorem pairwiseDisjoint_radiusIntervals
    {r : ℕ → ℝ} (hmono : Antitone r) :
    Pairwise (fun n m : ℕ =>
      Disjoint (Set.Ioc (r (n + 1)) (r n))
        (Set.Ioc (r (m + 1)) (r m))) := by
  intro n m hne
  rw [Set.disjoint_left]
  intro t htn htm
  rcases lt_or_gt_of_ne hne with hnm | hmn
  · have hindex : n + 1 ≤ m := by omega
    have hrle : r m ≤ r (n + 1) := hmono hindex
    exact (not_lt_of_ge (htm.2.trans hrle)) htn.1
  · have hindex : m + 1 ≤ n := by omega
    have hrle : r n ≤ r (m + 1) := hmono hindex
    exact (not_lt_of_ge (htn.2.trans hrle)) htm.1

theorem iUnion_radiusIntervals
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hmono : Antitone r)
    (hrlim : Tendsto r atTop (nhds 0)) :
    (⋃ n : ℕ, Set.Ioc (r (n + 1)) (r n)) = Set.Ioc 0 (r 0) := by
  ext t
  constructor
  · intro ht
    rcases Set.mem_iUnion.mp ht with ⟨n, hn⟩
    exact ⟨(hr (n + 1)).trans hn.1, hn.2.trans (hmono (Nat.zero_le n))⟩
  · intro ht
    have hevent : ∀ᶠ n in atTop, r n < t :=
      hrlim.eventually_lt_const ht.1
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hevent
    have hex : ∃ n : ℕ, r (n + 1) < t :=
      ⟨K, hK (K + 1) (by omega)⟩
    let N := Nat.find hex
    have hlower : r (N + 1) < t := Nat.find_spec hex
    have hupper : t ≤ r N := by
      by_contra hnot
      have hlt : r N < t := lt_of_not_ge hnot
      by_cases hN : N = 0
      · exact (not_lt_of_ge ht.2) (by simpa [hN] using hlt)
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hN
        have hfindle : N ≤ k := by
          apply Nat.find_min' hex
          simpa [hk] using hlt
        omega
    exact Set.mem_iUnion.mpr ⟨N, hlower, hupper⟩

theorem coneRadialIntegral_eq_tsum_intervals
    (d : ℕ) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hmono : Antitone r)
    (hrlim : Tendsto r atTop (nhds 0)) :
    coneRadialIntegral d r (r 0) =
      ∑' N : ℕ,
        ∫⁻ t in Set.Ioc (r (N + 1)) (r N),
          ENNReal.ofReal (t ^ (d - 1)) *
            coneEnergyExp r (radiusVolume d r) t ∂volume := by
  unfold coneRadialIntegral
  rw [← iUnion_radiusIntervals hr hmono hrlim]
  exact MeasureTheory.lintegral_iUnion
    (fun _ => measurableSet_Ioc)
    (pairwiseDisjoint_radiusIntervals hmono) _

noncomputable def explicitEnergyTerm
    (d : ℕ) (r : ℕ → ℝ) (N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (prefixMass (radiusVolume d r) N)) *
    ∫⁻ t in Set.Ioc (r (N + 1)) (r N),
      ENNReal.ofReal (t ^ (d - 1)) *
        ENNReal.ofReal
          (Real.exp (-prefixSlope r (radiusVolume d r) N * t)) ∂volume

theorem coneRadialIntegral_interval_eq_explicitEnergyTerm
    (d : ℕ) {r : ℕ → ℝ} (N : ℕ)
    (hr : ∀ n, 0 < r n) (hmono : Antitone r)
    (hrlim : Tendsto r atTop (nhds 0)) :
    (∫⁻ t in Set.Ioc (r (N + 1)) (r N),
      ENNReal.ofReal (t ^ (d - 1)) *
        coneEnergyExp r (radiusVolume d r) t ∂volume) =
      explicitEnergyTerm d r N := by
  have hv : ∀ n, 0 ≤ radiusVolume d r n := by
    intro n
    unfold radiusVolume
    exact mul_nonneg (euclideanUnitBallVolume_pos d).le
      (pow_nonneg (hr n).le d)
  unfold explicitEnergyTerm
  rw [← MeasureTheory.lintegral_const_mul]
  · apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [coneEnergyExp_eq_ofReal_exp_coneSum hr hv hrlim
      ((hr (N + 1)).trans ht.1)]
    rw [coneSum_eq_mass_sub_slope_closed hr hmono
      (le_of_lt ht.1) ht.2]
    rw [sub_eq_add_neg, Real.exp_add]
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    have hexponent : -(t * prefixSlope r (radiusVolume d r) N) =
        -prefixSlope r (radiusVolume d r) N * t := by ring
    rw [hexponent]
    ac_rfl
  · fun_prop

theorem coneRadialIntegral_eq_tsum_explicitEnergyTerm
    (d : ℕ) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hmono : Antitone r)
    (hrlim : Tendsto r atTop (nhds 0)) :
    coneRadialIntegral d r (r 0) =
      ∑' N : ℕ, explicitEnergyTerm d r N := by
  rw [coneRadialIntegral_eq_tsum_intervals d hr hmono hrlim]
  apply tsum_congr
  intro N
  exact coneRadialIntegral_interval_eq_explicitEnergyTerm
    d N hr hmono hrlim

noncomputable def explicitEnergyRealTerm
    (d : ℕ) (r : ℕ → ℝ) (N : ℕ) : ℝ :=
  Real.exp (prefixMass (radiusVolume d r) N) *
    ∫ t in r (N + 1)..r N,
      Real.exp (-prefixSlope r (radiusVolume d r) N * t) *
        t ^ (d - 1)

theorem explicitEnergyTerm_eq_ofReal_realTerm
    (d : ℕ) {r : ℕ → ℝ} (N : ℕ)
    (hr : ∀ n, 0 < r n) (hmono : Antitone r) :
    explicitEnergyTerm d r N =
      ENNReal.ofReal (explicitEnergyRealTerm d r N) := by
  let f : ℝ → ℝ := fun t =>
    Real.exp (-prefixSlope r (radiusVolume d r) N * t) * t ^ (d - 1)
  have hfcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hle : r (N + 1) ≤ r N := hmono (Nat.le_succ N)
  have hfint : IntegrableOn f (Set.Ioc (r (N + 1)) (r N)) volume :=
    hfcont.integrableOn_Ioc
  have hfnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (r (N + 1)) (r N))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (Real.exp_pos _).le
      (pow_nonneg ((hr (N + 1)).trans ht.1).le _)
  have hbridge :
      ENNReal.ofReal (∫ t in r (N + 1)..r N, f t) =
        ∫⁻ t in Set.Ioc (r (N + 1)) (r N),
          ENNReal.ofReal (f t) ∂volume := by
    rw [intervalIntegral.integral_of_le hle]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfint hfnonneg
  unfold explicitEnergyTerm explicitEnergyRealTerm
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [hbridge]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro t _
  dsimp only [f]
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  ac_rfl

theorem explicit_energy_series_equivalence_aux
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0)) :
    (∫⁻ z : FlatTorus d,
      ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
        ∂(flatTorusVolume d)) = ∞ ↔
      (∑' N : ℕ,
        ENNReal.ofReal (explicitEnergyRealTerm d r N)) = ∞ := by
  rw [cone_criterion d hd hr hrsmall hrlim (hr 0)]
  rw [← coneRadialIntegral_eq_real d hr hrlim (r 0)]
  rw [coneRadialIntegral_eq_tsum_explicitEnergyTerm d hr hmono hrlim]
  have hseries :
      (∑' N : ℕ, explicitEnergyTerm d r N) =
        ∑' N : ℕ, ENNReal.ofReal (explicitEnergyRealTerm d r N) := by
    apply tsum_congr
    intro N
    exact explicitEnergyTerm_eq_ofReal_realTerm d N hr hmono
  rw [hseries]

theorem explicit_energy_series_equivalence
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0)) :
    (∫⁻ z : FlatTorus d,
      ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z))
        ∂(flatTorusVolume d)) = ∞ ↔
      (∑' N : ℕ,
        ENNReal.ofReal
          (Real.exp (prefixMass (radiusVolume d r) N) *
            ∫ t in r (N + 1)..r N,
              Real.exp (-prefixSlope r (radiusVolume d r) N * t) *
                t ^ (d - 1))) = ∞ := by
  simpa only [explicitEnergyRealTerm] using
    explicit_energy_series_equivalence_aux
      d hd hr hrsmall hmono hrlim

end Shepp.Section2
end SheppFlattenedModule082

section SheppFlattenedModule083
open scoped ENNReal ProbabilityTheory Topology BigOperators
open Filter MeasureTheory Set

namespace Shepp.Section8

open ProbabilityTheory Shepp.Section2 Shepp.Section3 Shepp.Section4
  Shepp.Section5 Shepp.Section6 Shepp.Section7

theorem exists_tailRadius_lt_quarter
    {r : ℕ → ℝ} (hrlim : Tendsto r atTop (nhds 0)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, tailRadius r n₀ n < 1 / 4 := by
  have hsmall : ∀ᶠ n : ℕ in atTop, r n < 1 / 4 :=
    hrlim.eventually_lt_const (by norm_num)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hsmall
  refine ⟨n₀, fun n => hn₀ (n₀ + n) ?_⟩
  omega

theorem summable_flatTorusOverlapTerm_of_tendsto_zero
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (nhds 0))
    {z : FlatTorus d} (hz : z ≠ 0) :
    Summable (fun n => flatTorusOverlapTerm d r n z) := by
  obtain ⟨n₀, hsmall⟩ := exists_tailRadius_lt_quarter hrlim
  have hdist : 0 < dist (0 : FlatTorus d) z :=
    dist_pos.mpr (Ne.symm hz)
  have htail : Summable (fun n =>
      flatTorusOverlapTerm d (tailRadius r n₀) n z) := by
    have heq : (fun n =>
        flatTorusOverlapTerm d (tailRadius r n₀) n z) =
        fun n => euclideanOverlapTerm d (tailRadius r n₀) n (dist 0 z) := by
      funext n
      exact flatTorusOverlapTerm_eq_euclideanOverlapTerm_dist
        d hd (tailRadius_pos hr n₀) hsmall n z
    rw [heq]
    exact summable_euclideanOverlapTerm d (tailRadius_pos hr n₀)
      (tailRadius_tendsto_zero hrlim n₀) hdist
  have hshift : Summable (fun n =>
      flatTorusOverlapTerm d r (n + n₀) z) := by
    rw [show (fun n => flatTorusOverlapTerm d r (n + n₀) z) =
        (fun n => flatTorusOverlapTerm d (tailRadius r n₀) n z) by
      funext n
      rw [Nat.add_comm]
      exact (flatTorusOverlapTerm_tailRadius d r n₀ n z).symm]
    exact htail
  exact (summable_nat_add_iff n₀).mp hshift

theorem flatTorusOverlapEnergyExp_eq_ofReal_exp_of_tendsto_zero
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (nhds 0))
    {z : FlatTorus d} (hz : z ≠ 0) :
    flatTorusOverlapEnergyExp d r z =
      ENNReal.ofReal (Real.exp (flatTorusOverlapSum d r z)) := by
  have hsummable :=
    summable_flatTorusOverlapTerm_of_tendsto_zero d hd hr hrlim hz
  have henergy : flatTorusOverlapEnergy d r z =
      ENNReal.ofReal (flatTorusOverlapSum d r z) := by
    rw [flatTorusOverlapEnergy, flatTorusOverlapSum]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun n => by unfold flatTorusOverlapTerm; positivity)
      hsummable).symm
  rw [flatTorusOverlapEnergyExp, henergy,
    EReal.coe_ennreal_ofReal,
    max_eq_left (flatTorusOverlapSum_nonneg d r z), EReal.exp_coe]

noncomputable def extendedOverlapEnergyIntegral
    (d : ℕ) (r : ℕ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z : FlatTorus d,
    flatTorusOverlapEnergyExp d r z ∂(flatTorusVolume d)

theorem extendedOverlapEnergyIntegral_eq_finiteEnergyIntegral
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (nhds 0)) :
    extendedOverlapEnergyIntegral d r = finiteEnergyIntegral d r := by
  unfold extendedOverlapEnergyIntegral finiteEnergyIntegral
  apply lintegral_congr_ae
  have hzero := flatTorusVolume_singleton_zero d (by omega)
  filter_upwards [compl_mem_ae_iff.2 hzero] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  exact flatTorusOverlapEnergyExp_eq_ofReal_exp_of_tendsto_zero
    d hd hr hrlim hz0

theorem flatTorusOverlapEnergyExp_tail_le
    (d : ℕ) (r : ℕ → ℝ) (n₀ : ℕ) (z : FlatTorus d) :
    flatTorusOverlapEnergyExp d (tailRadius r n₀) z ≤
      flatTorusOverlapEnergyExp d r z := by
  have henergy : flatTorusOverlapEnergy d (tailRadius r n₀) z ≤
      flatTorusOverlapEnergy d r z := by
    rw [← flatTorusOverlapEnergy_tail_decomposition d r n₀ z]
    exact le_add_of_nonneg_left (by positivity)
  exact EReal.exp_monotone
    (EReal.coe_ennreal_le_coe_ennreal_iff.2 henergy)

theorem extendedOverlapEnergyIntegral_tail_le
    (d : ℕ) (r : ℕ → ℝ) (n₀ : ℕ) :
    extendedOverlapEnergyIntegral d (tailRadius r n₀) ≤
      extendedOverlapEnergyIntegral d r := by
  apply lintegral_mono
  intro z
  exact flatTorusOverlapEnergyExp_tail_le d r n₀ z

theorem extendedOverlapEnergyIntegral_tail_eq_top_of_eq_top
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (n₀ : ℕ)
    (hsmall : ∀ n, tailRadius r n₀ n < 1 / 4)
    (htop : extendedOverlapEnergyIntegral d r = ∞) :
    extendedOverlapEnergyIntegral d (tailRadius r n₀) = ∞ := by
  let c : ℝ≥0∞ := EReal.exp (n₀ : EReal)
  have hmono : extendedOverlapEnergyIntegral d r ≤
      ∫⁻ z : FlatTorus d,
        c * flatTorusOverlapEnergyExp d (tailRadius r n₀) z
          ∂(flatTorusVolume d) := by
    apply lintegral_mono
    intro z
    exact flatTorusOverlapEnergyExp_le_exp_nat_mul_tail d r n₀ z
  rw [htop] at hmono
  have hprod : (∫⁻ z : FlatTorus d,
      c * flatTorusOverlapEnergyExp d (tailRadius r n₀) z
        ∂(flatTorusVolume d)) = ∞ :=
    top_unique hmono
  have hmeas : Measurable
      (flatTorusOverlapEnergyExp d (tailRadius r n₀)) :=
    measurable_flatTorusOverlapEnergyExp d hd
      (tailRadius_pos hr n₀) hsmall
  rw [lintegral_const_mul c hmeas] at hprod
  have hc : c ≠ ∞ := by
    intro hcTop
    exact EReal.natCast_ne_top n₀ (EReal.exp_eq_top_iff.mp hcTop)
  rcases ENNReal.mul_eq_top.mp hprod with htail | hconst
  · exact htail.2
  · exact (hc hconst.1).elim

theorem extendedOverlapEnergyIntegral_tail_eq_top_iff
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (n₀ : ℕ)
    (hsmall : ∀ n, tailRadius r n₀ n < 1 / 4) :
    extendedOverlapEnergyIntegral d (tailRadius r n₀) = ∞ ↔
      extendedOverlapEnergyIntegral d r = ∞ := by
  constructor
  · intro htail
    exact top_unique (htail ▸ extendedOverlapEnergyIntegral_tail_le d r n₀)
  · exact extendedOverlapEnergyIntegral_tail_eq_top_of_eq_top
      d hd hr n₀ hsmall

theorem finiteEnergyIntegral_tail_eq_top_iff
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (nhds 0))
    (n₀ : ℕ) (hsmall : ∀ n, tailRadius r n₀ n < 1 / 4) :
    finiteEnergyIntegral d (tailRadius r n₀) = ∞ ↔
      finiteEnergyIntegral d r = ∞ := by
  rw [← extendedOverlapEnergyIntegral_eq_finiteEnergyIntegral
      d hd (tailRadius_pos hr n₀) (tailRadius_tendsto_zero hrlim n₀),
    ← extendedOverlapEnergyIntegral_eq_finiteEnergyIntegral d hd hr hrlim]
  exact extendedOverlapEnergyIntegral_tail_eq_top_iff
    d hd hr n₀ hsmall

def iidCenterShift
    {d : ℕ} (n₀ : ℕ) (X : IIDCenterSample d) : IIDCenterSample d :=
  fun n => X (n₀ + n)

theorem measurable_iidCenterShift
    {d : ℕ} (n₀ : ℕ) :
    Measurable (iidCenterShift (d := d) n₀) := by
  apply measurable_pi_lambda
  intro n
  exact measurable_pi_apply (n₀ + n)

theorem iidCenterShift_hasLaw
    (d : ℕ) (n₀ : ℕ) :
    HasLaw (iidCenterShift (d := d) n₀)
      (iidCenterMeasure d) (iidCenterMeasure d) := by
  refine ⟨(measurable_iidCenterShift (d := d) n₀).aemeasurable, ?_⟩
  unfold iidCenterMeasure
  have hinj : Function.Injective (fun n : ℕ => n₀ + n) := by
    intro a b hab
    exact Nat.add_left_cancel hab
  exact Measure.map_infinitePi_infinitePi_of_inj hinj

theorem iidLimsupSet_tailRadius_shift
    {d : ℕ} (r : ℕ → ℝ) (n₀ : ℕ) (X : IIDCenterSample d) :
    iidLimsupSet (tailRadius r n₀) (iidCenterShift n₀ X) =
      iidLimsupSet r X := by
  rw [iidLimsupSet_eq_iInter_coveredFrom,
    iidLimsupSet_eq_iInter_coveredFrom]
  ext z
  simp only [Set.mem_iInter]
  constructor
  · intro htail q
    obtain ⟨n, hqn, hzball⟩ :=
      (mem_iidCentersCoveredFrom_iff
        (tailRadius r n₀) q (iidCenterShift n₀ X) z).1 (htail q)
    apply (mem_iidCentersCoveredFrom_iff r q X z).2
    refine ⟨n₀ + n, ?_, ?_⟩
    · omega
    · simpa only [iidCenterShift, tailRadius] using hzball
  · intro hfull q
    obtain ⟨m, hmq, hzball⟩ :=
      (mem_iidCentersCoveredFrom_iff r (n₀ + q) X z).1
        (hfull (n₀ + q))
    let n : ℕ := m - n₀
    have hmn : n₀ + n = m := by
      dsimp [n]
      omega
    apply (mem_iidCentersCoveredFrom_iff
      (tailRadius r n₀) q (iidCenterShift n₀ X) z).2
    refine ⟨n, ?_, ?_⟩
    · dsimp [n]
      omega
    · simpa only [iidCenterShift, tailRadius, hmn] using hzball

theorem iidCenterShift_preimage_limsupCoverEvent
    {d : ℕ} (r : ℕ → ℝ) (n₀ : ℕ) :
    iidCenterShift (d := d) n₀ ⁻¹'
        iidLimsupCoverEvent (d := d) (tailRadius r n₀) =
      iidLimsupCoverEvent (d := d) r := by
  ext X
  simp only [Set.mem_preimage, mem_iidLimsupCoverEvent_iff]
  rw [iidLimsupSet_tailRadius_shift]

theorem iidCenterMeasure_limsupCoverEvent_tailRadius
    (d : ℕ) (r : ℕ → ℝ) (n₀ : ℕ) :
    iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) =
      iidCenterMeasure d
        (iidLimsupCoverEvent (d := d) (tailRadius r n₀)) := by
  let E := iidLimsupCoverEvent (d := d) (tailRadius r n₀)
  have hE : MeasurableSet E := measurableSet_iidLimsupCoverEvent _
  have hlaw := (iidCenterShift_hasLaw d n₀).measure_eq
    (p := fun X => X ∈ E) hE
  have hpre : {X : IIDCenterSample d | iidCenterShift n₀ X ∈ E} =
      iidCenterShift n₀ ⁻¹' E := rfl
  have hset : {X : IIDCenterSample d | X ∈ E} = E := Set.setOf_mem_eq
  rw [hpre, hset, iidCenterShift_preimage_limsupCoverEvent] at hlaw
  exact hlaw

theorem smallRadiusMainCriterion
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0)) :
    iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 1 ↔
      finiteEnergyIntegral d r = ∞ := by
  constructor
  · intro hone
    by_contra hnotTop
    have hfinite : finiteEnergyIntegral d r < ∞ :=
      lt_top_iff_ne_top.mpr hnotTop
    have hzero := finiteEnergyNoncovering
      d hd hr hrsmall hrlim hfinite
    rw [hone] at hzero
    norm_num at hzero
  · intro htop
    exact dePoissonizedSufficiency
      d hd hr hrsmall hmono hrlim (by simpa [finiteEnergyIntegral] using htop)

theorem mainCriterion
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hmono : Antitone r)
    (hrlim : Tendsto r atTop (nhds 0)) :
    iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 1 ↔
      finiteEnergyIntegral d r = ∞ := by
  obtain ⟨n₀, hsmall⟩ := exists_tailRadius_lt_quarter hrlim
  rw [iidCenterMeasure_limsupCoverEvent_tailRadius d r n₀]
  exact (smallRadiusMainCriterion d hd
    (tailRadius_pos hr n₀) hsmall (tailRadius_antitone hmono n₀)
    (tailRadius_tendsto_zero hrlim n₀)).trans
      (finiteEnergyIntegral_tail_eq_top_iff
        d hd hr hrlim n₀ hsmall)

theorem finiteEnergyNoncovering_without_smallRadius
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (nhds 0))
    (hfinite : finiteEnergyIntegral d r < ∞) :
    iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 0 := by
  obtain ⟨n₀, hsmall⟩ := exists_tailRadius_lt_quarter hrlim
  have htailNotTop : finiteEnergyIntegral d (tailRadius r n₀) ≠ ∞ := by
    intro htail
    have htop : finiteEnergyIntegral d r = ∞ :=
      (finiteEnergyIntegral_tail_eq_top_iff
        d hd hr hrlim n₀ hsmall).mp htail
    exact hfinite.ne htop
  have htailFinite : finiteEnergyIntegral d (tailRadius r n₀) < ∞ :=
    lt_top_iff_ne_top.mpr htailNotTop
  rw [iidCenterMeasure_limsupCoverEvent_tailRadius d r n₀]
  exact finiteEnergyNoncovering d hd
    (tailRadius_pos hr n₀) hsmall
    (tailRadius_tendsto_zero hrlim n₀) htailFinite

theorem divergentEnergyCovering
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hmono : Antitone r)
    (hrlim : Tendsto r atTop (nhds 0))
    (htop : finiteEnergyIntegral d r = ∞) :
    iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 1 :=
  (mainCriterion d hd hr hmono hrlim).2 htop

theorem coveringEnergyDichotomy
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hmono : Antitone r)
    (hrlim : Tendsto r atTop (nhds 0)) :
    (finiteEnergyIntegral d r = ∞ ∧
        iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 1) ∨
      (finiteEnergyIntegral d r < ∞ ∧
        iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 0) := by
  by_cases htop : finiteEnergyIntegral d r = ∞
  · exact Or.inl ⟨htop,
      divergentEnergyCovering d hd hr hmono hrlim htop⟩
  · have hfinite : finiteEnergyIntegral d r < ∞ :=
      lt_top_iff_ne_top.mpr htop
    exact Or.inr ⟨hfinite,
      finiteEnergyNoncovering_without_smallRadius
        d hd hr hrlim hfinite⟩

end Shepp.Section8
end SheppFlattenedModule083

section SheppFlattenedModule084
open scoped ENNReal ProbabilityTheory Topology BigOperators
open Filter MeasureTheory Set

namespace Shepp.Section8

open Shepp.Section2 Shepp.Section5 Shepp.Section6 Shepp.Section7

noncomputable def explicitEnergySeries
    (d : ℕ) (r : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' N : ℕ,
    ENNReal.ofReal
      (Real.exp (prefixMass (radiusVolume d r) N) *
        ∫ t : ℝ in r (N + 1)..r N,
          Real.exp (-prefixSlope r (radiusVolume d r) N * t) *
            t ^ (d - 1))

theorem smallRadiusExplicitCriterion
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrsmall : ∀ n, r n < 1 / 4)
    (hmono : Antitone r) (hrlim : Tendsto r atTop (nhds 0)) :
    iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 1 ↔
      explicitEnergySeries d r = ∞ := by
  exact (smallRadiusMainCriterion d hd hr hrsmall hmono hrlim).trans
    (by
      simpa only [finiteEnergyIntegral, explicitEnergySeries] using
        (explicit_energy_series_equivalence
          d hd hr hrsmall hmono hrlim))

theorem explicitRadiusSequenceCriterion
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hmono : Antitone r)
    (hrlim : Tendsto r atTop (nhds 0))
    (n₀ : ℕ) (hsmall : ∀ n, tailRadius r n₀ n < 1 / 4) :
    iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 1 ↔
      explicitEnergySeries d (tailRadius r n₀) = ∞ := by
  rw [iidCenterMeasure_limsupCoverEvent_tailRadius d r n₀]
  exact smallRadiusExplicitCriterion d hd
    (tailRadius_pos hr n₀) hsmall (tailRadius_antitone hmono n₀)
    (tailRadius_tendsto_zero hrlim n₀)

theorem exists_relabelledExplicitRadiusSequenceCriterion
    (d : ℕ) (hd : 2 ≤ d) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hmono : Antitone r)
    (hrlim : Tendsto r atTop (nhds 0)) :
    ∃ n₀ : ℕ,
      (∀ n, tailRadius r n₀ n < 1 / 4) ∧
      (iidCenterMeasure d (iidLimsupCoverEvent (d := d) r) = 1 ↔
        explicitEnergySeries d (tailRadius r n₀) = ∞) := by
  obtain ⟨n₀, hsmall⟩ := exists_tailRadius_lt_quarter hrlim
  exact ⟨n₀, hsmall,
    explicitRadiusSequenceCriterion
      d hd hr hmono hrlim n₀ hsmall⟩

end Shepp.Section8
end SheppFlattenedModule084
