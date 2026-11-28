module

import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform -- shake: keep (needed public by an exposed definition)
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral -- shake: keep (needed public by an exposed definition)
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Presheaf
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.DiscreteSeries.Bessel.Basic
public import Lib.DiscreteSeries.Bruhat.FloorMeasures
import Lib.Adelic.Adeles.AdditiveCharacter
import Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure
import Lib.DiscreteSeries.Haar.GramPolar
import Lib.DiscreteSeries.Haar.TotalMass
import Lib.General.Analysis.GaussianIntegral

/-!
# The place ℂ: polar coordinates, Cartan decomposition and the measure of the hyperboloid

The archimedean instance of the local theory: the place `ℂ` and the top floor `ϱ` of the group
`New.Shape.G₁`, the unitary group of `ϱ` hyperbolic planes plus `V_ϱ = X₀ ⊕ ℂ z`, where `X₀ = ℂ^κ`
is standard and `h(z, z) = -1`. `New.RealPlace.embedH` embeds `U(X₀)` (written `U 1`) in it.
`floorGroup l` is the subgroup that fixes the basis vectors of the floors below `l`.

* `New.Floors.complexPlace`, `New.Floors.complexBasis`: `ℂ` is a place (`New.Floors.Place`); a
  hyperbolic basis of `V_ϱ`.
* `New.Floors.lintegral_eq_polar`: polar coordinates on `ℂ^κ` by the unitary group.
* `New.Floors.cellChart`, `New.Floors.cellDensity`, `New.Floors.cellLaw`: for each floor a chart
  `ℂ → G₁` (a boost at the top for `c ≠ 0`, a Weyl element otherwise), its density, and the law of
  its inverse.
* `New.Floors.cartan_decomposition`: the Cartan decomposition `U(X₀) · boost · U(X₀)` of an element
  of the top floor group whose corner entry `h(z, σ z)` has absolute value above 1.
* `New.Floors.map_orbitPoint_cellLaw_top`: polar coordinates for the measure of the hyperboloid
  `h(v, v) = -1`.

Notions from other files:
* `New.Shape.middleGram`: for a scalar N, the diagonal matrix on κ plus one point, with entries 1 on
  κ and −N at the extra point.
* `New.Floors.FloorGroups.orbitPoint`: for b ≤ ϱ and an isometry g, the vector g⁻¹f_b, where
  f = (e_0, …, e_{ϱ-1}, z) is the frame; `𝔰.top` is the position ϱ of z.
* `New.Floors.HyperbolicBasis.floorQuadricMeasure`: the measure on a quadric in V_b, a level set of
  v ↦ h(v, v) (by default h(f_b, f_b)): the image of `New.Floors.Place.quadricMeasure` under the
  basis `F.floorBasis b`.
* `New.realFrameGram`: for y in G₁, the (ϱ+1)×(ϱ+1) complex matrix Z(y) of products h(f_j, y f_l) of
  the frame with its translate.

## Relation to the literature

Known results: polar coordinates on ℂ^κ, the Cartan decomposition of a unitary group of rank one,
and the invariant measure of the hyperboloid h(v, v) = −1, here written in the coordinates of the
top floor. Source: Knapp, Lie Groups Beyond an Introduction; Helgason, Groups and Geometric
Analysis, Ch. I §5.
-/

@[expose] public section

noncomputable section

namespace New.Floors

open MeasureTheory Measure Matrix Real Fintype Set Complex ComplexConjugate RealPlace Sum
  FloorGroups GaussianFourier ComplexOrder Function

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The place `ℂ`: `τ = 1/2`, `δ = i/2`, `ν` the image of Lebesgue measure under `r ↦ r i`,
modulus `‖x‖ ^ 2`, character `x ↦ exp (x - x̄)` and constant `c = π ^ 2`. -/
@[simps]
instance complexPlace : Place ℂ := by
  -- The kernel is the Gaussian `exp (-‖x‖²)`, and `gauss` says that its integral is `π`.
  have gauss := HasGaussianIntegral.integral_exp_eq (V := ℂ) one_pos
  have integrable := Integrable.of_integral_ne_zero (gauss.trans_ne (by positivity))
  -- its Fourier transform, and the mass of `π exp (-‖x‖²)` as a Lebesgue integral
  have fourier (z : ℂ) := integral_cexp_neg_mul_sq_norm_add (b := 1) one_pos (2 * I) (z / I)
  have mass := ofReal_integral_norm_eq_lintegral_eNorm (integrable.const_mul π)
  refine .mk (toTraceOne := ⟨2⁻¹, by norm_num⟩) (skewUnit := .mk0 (I / 2) (by norm_num))
    (skewMeasure := volume.map fun r : ℝ ↦ ⟨r * I, by simp [skewAdjoint.mem_iff]⟩)
    (modulus := ⟨⟨(‖·‖ₑ ^ 2), by norm_num⟩, by norm_num [mul_pow]⟩)
    (ψ := ⟨wave, by norm_num [wave], by simp [← Complex.exp_add, sub_add_sub_comm, wave]⟩)
    (kernelBound := .ofReal (π ^ 2))
    (haar := ?haar)
    (continuous_psi := Complex.continuous_exp.comp (continuous_id.sub Complex.continuous_conj))
    (measurable_modulus := continuous_eNorm.measurable.pow_const 2)
    (star_skewUnit := by norm_num [neg_div]) (measurePreserving_split := ⟨by fun_prop, ?split⟩)
    (modulus_star_and_neg := by norm_num)
    (map_mulVec_volume := by norm_num +contextual
                               [Fock.map_mulVec_addHaar_eq_smul, ENNReal.inv_pow])
    (ae_isUnit := by simpa only [isUnit_iff_ne_zero, ne_eq] using ae_ne volume 0)
    (exists_locallyIntegrable_bound := ⟨(‖·‖⁻¹), ?int, by norm_num [ENNReal.inv_pow]⟩)
    (norm_psi := by norm_num)
    (exists_plancherel_kernel :=
      ⟨_, (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2))), integrable,
        fun _ ↦ (exp_pos _).le, by norm_num, ?ker⟩)
  case haar =>
    -- `r ↦ r * I` is a bicontinuous additive isomorphism onto the skew elements
    refine AddEquiv.isAddHaarMeasure_map _ ⟨⟨_, (·.val.im),
      fun r ↦ by simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
        add_zero],
      fun x ↦ Subtype.ext <| Complex.ext
        (by
          simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self]
          have hx : (x : ℂ).re = -(x : ℂ).re := congrArg Complex.re (skewAdjoint.mem_iff.1 x.2)
          linarith)
        (by simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
          add_zero])⟩,
      fun a b ↦ Subtype.ext <| by
        change ((a + b : ℝ) : ℂ) * I = (a : ℂ) * I + (b : ℂ) * I
        simp only [ofReal_add, add_mul]⟩ ?_ ?_
    · exact Continuous.subtype_mk (continuous_ofReal.mul continuous_const) _
    · exact Complex.continuous_im.comp continuous_subtypeVal
  case split =>
    -- with `τ = 1 / 2` and `δ = I / 2` the splitting sends `(r I, s I)` to `r + s I`
    rw [map_prod_map, Measure.map_map, ← volume_preserving_equiv_real_prod.symm.2] <;> try fun_prop
    congr 1
    simp [Complex.ext_iff, funext_iff]
  -- the bound `‖x‖⁻¹` is locally integrable, ℂ having real dimension 2
  case int =>
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) ?_ ?_ ?_ (by fun_prop) <;>
      norm_num [rpow_neg_one]
  case ker =>
    -- by `fourier` the inner integral is `π exp (-‖z‖²)`, whose integral is `π ^ 2`
    simp_all [← Complex.exp_add, ↓sub_conj, mul_right_comm _ _ I, ← sub_eq_add_neg, sq,
      ← ofReal_norm, abs_of_pos pi_pos, neg_add_eq_sub, integral_const_mul, wave, norm_exp]
    grind

/-- For the fixed index k₀ of κ (`𝔰.k₀`), the basis of V_ϱ = X₀ ⊕ ℂz made of the hyperbolic pair
(1+i)/2·(x_{k₀} ± z) and the orthonormal vectors x_i, i ≠ k₀. -/
def complexBasis (𝔰 : Shape) : HyperbolicBasis {i // i ≠ 𝔰.k₀} (𝔰.middleGram (1 : ℂ)) 0 :=
  { basisMatrix :=
      of fun i ↦
        (fun a ↦
          (1 + I) / 2 *
            (Pi.single 𝔰.k₀ 1 ⊕ᵥ ![1, -1] a) i) ⊕ᵥ (0 ⊕ᵥ (inclMatrix ℂ (inl ·.val) i ⊕ᵥ 0))
    gram_eq := by
      -- entry by entry, the products of the columns are those of a plane and an orthonormal family
      simp only [ne_eq, Nat.succ_eq_add_one, Nat.reduceAdd, zero_empty, inclMatrix, middleGram,
        ← ext_iff, Matrix.mul_apply, conjTranspose_apply, of_apply, star_def, sum_sum_type,
        elim_inl, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.univ_unique,
        PUnit.default_eq_unit, elim_inr, cons_val', Pi.one_apply, Pi.neg_apply, cons_val_fin_one,
        Finset.sum_singleton, fromBlocks_apply₁₁, Matrix.one_apply, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, fromBlocks_apply₂₁, Matrix.zero_apply, add_zero,
        fromBlocks_apply₁₂, Finset.sum_const_zero, fromBlocks_apply₂₂, mul_neg, zero_add, neg_mul,
        Finset.sum_neg_distrib, Sum.forall, Fin.forall_fin_two, Fin.isValue, cons_val_zero,
        cons_val_one, neg_neg, IsEmpty.forall_iff, submatrix_apply, id_eq, inl.injEq,
        reduceCtorEq, neg_zero, Subtype.forall, and_true, true_and, map_div₀, map_add, map_one,
        conj_I, map_ofNat, map_mul, map_eq_zero, ite_eq_right_iff, div_eq_zero_iff,
        OfNat.ofNat_ne_zero, or_false, add_neg_cancel, map_neg, and_self, add_self_eq_zero,
        mul_eq_zero, fromCols_apply_inl, MonoidWithZeroHom.map_ite_one_zero, ite_mul, one_mul,
        zero_mul, map_zero, Subtype.mk.injEq]
      grind [I_sq]
    card_eq := by
      simp only [Shape.k, card_subtype_compl, Fintype.card_unique, add_assoc]
      have : 0 < Fintype.card 𝔰.κ := card_pos_iff.2 ⟨𝔰.k₀⟩
      omega
    modulus_det := by simp [middleGram] }

/-- Polar coordinates on `ℂ^κ`, with `m = |κ|`: for an index `k` in `κ` and measurable
`g : ℂ^κ → [0, ∞]`, `∫ g(ω) dω = ∫₀^∞ π^m r^(m-1) / (m-1)! ∫_{U(m)} g(h (√r x)) dh dr`, where `x` is
the basis vector of index `k`, `r` is the squared norm and `dh` is the Haar probability measure. -/
lemma lintegral_eq_polar (k : κ) {g : (κ → ℂ) → ENNReal} (hg : Measurable g) :
    ∫⁻ ω : κ → ℂ, g ω =
      ∫⁻ r : ℝ in Ioi 0,
        ENNReal.ofReal (sphereDensity (card κ) r / 2) *
          ∫⁻ h : U 1, g (h.val.val *ᵥ √r • Pi.single k 1) := by
  -- Average `g` over the unitary group, which preserves the volume; the average depends only on
  -- `r = |ω|²`, whose law is given by `measurePreserving_normSq_sphereDensity`.
  have : Nonempty κ := ⟨k⟩
  have rot (h : U 1) : ∫⁻ ω : κ → ℂ, g (h.val.val *ᵥ ω) = ∫⁻ ω : κ → ℂ, g ω :=
    (complexPlace.measurePreserving_mulVec _ (U.det (by simp) h).property.1).lintegral_comp hg
  let F (r : ℝ) : ENNReal := ∫⁻ h : U 1, g (h.val.val *ᵥ √r • Pi.single k 1)
  have hF : Measurable F := by fun_prop
  have h_dens : Measurable fun r : ℝ ↦ ENNReal.ofReal (sphereDensity (card κ) r / 2) :=
    (ENNReal.continuous_ofReal.comp ((continuous_const.mul
      (continuous_pow (card κ - 1))).div_const 2)).measurable
  calc ∫⁻ ω, g ω = ∫⁻ h : U 1, ∫⁻ ω, g (h.val.val *ᵥ ω) := by
        simp only [rot, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ ω, ∫⁻ h : U 1, g (h.val.val *ᵥ ω) := lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ ω : κ → ℂ, ∫⁻ h : U 1, g (h.val.val *ᵥ √‖star ω ⬝ᵥ ω‖ • Pi.single k 1) := by
      -- a unitary `u` takes `ω` to the multiple of the basis vector with the same norm
      refine lintegral_congr fun ω ↦ ?_
      obtain ⟨u, hu⟩ := exists_unitary_mulVec_eq ω (v := √‖star ω ⬝ᵥ ω‖ • Pi.single k 1)
        (by simp (disch := positivity) only [dotProduct, Pi.star_apply, star_def, conj_mul',
          Pi.smul_apply, Pi.single_apply, smul_ite, real_smul, mul_one, smul_zero, mul_ite,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, conj_ofReal, ← ofReal_mul,
          mul_self_sqrt, norm_of_nonneg'])
      rw [← lintegral_mul_right_eq_self _ u]
      refine lintegral_congr fun h ↦ ?_
      simp only [Units.val_mul, Subgroup.coe_mul, ← mulVec_mulVec, hu]
    _ = ∫⁻ r : ℝ, F r ∂((volume.restrict (Ioi 0)).withDensity fun r : ℝ ↦
        ENNReal.ofReal (sphereDensity (card κ) r / 2)) :=
      (measurePreserving_normSq_sphereDensity (κ := κ)).lintegral_comp hF
    _ = _ := lintegral_withDensity_eq_lintegral_mul _ h_dens hF

/-- The boost in the plane of k₀ and z with parameter a, for 1 ≤ |a|. With s = √(|a|² - 1) it acts
on that plane by the matrix with rows (conj a, s) and (-s, -a), and it fixes the other basis
vectors. -/
def cellBoost (𝔰 : Shape) (a : ℂ) (ha : 1 ≤ ‖a‖) : 𝔰.G₁ :=
  let s : 𝔰.κ → ℂ := √(‖a‖ ^ 2 - 1) • Pi.single 𝔰.k₀ 1
  let boost : Matrix (𝔰.κ ⊕ Unit) (𝔰.κ ⊕ Unit) ℂ :=
    fromBlocks (diagonal (update 1 𝔰.k₀ (conj a))) (replicateCol Unit s) (-replicateRow Unit s)
      (of fun _ _ ↦ -a)
  U.of IsHermitianUnit.isUnit (fromBlocks 1 0 0 (fromBlocks boost 0 0 1)) <| by
    simp only [replicateCol_smul, replicateRow_smul, fromBlocks_conjTranspose, conjTranspose_one,
      conjTranspose_zero, diagonal_conjTranspose, conjTranspose_neg, conjTranspose_smul,
      RCLike.star_def, ringHom_apply, conjTranspose_replicateRow, Pi.star_single, star_one,
      conjTranspose_replicateCol, splitGram, middleGram, fromBlocks_multiply, mul_zero,
      Matrix.zero_mul, add_zero, Matrix.one_mul, Matrix.mul_zero, zero_add, mul_one,
      Matrix.neg_mul, smul_mul, Matrix.mul_one, diagonal_mul_diagonal, Pi.star_apply,
      update_apply, Pi.one_apply, apply_ite conj, RingHomCompTriple.comp_apply, RingHom.id_apply,
      map_one, mul_ite, ite_mul, one_mul, Matrix.mul_neg, Matrix.mul_smul, smul_neg, neg_neg,
      ← ext_iff, Sum.forall, fromBlocks_apply₁₁, Matrix.zero_apply, implies_true,
      fromBlocks_apply₁₂, Matrix.mul_apply, sum_sum_type, fromCols_apply_inl, zero_mul,
      Finset.sum_const_zero, fromCols_apply_inr, Matrix.one_apply, fromBlocks_apply₂₁, and_self,
      fromBlocks_apply₂₂, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, fromRows_apply_inl,
      fromRows_apply_inr, and_true, true_and, Matrix.add_apply, diagonal_apply, Matrix.smul_apply,
      Finset.univ_unique, PUnit.default_eq_unit, replicateCol_apply, Pi.single_apply, of_apply,
      mul_neg, Finset.sum_neg_distrib, Finset.sum_ite_irrel, Finset.sum_const,
      Finset.card_singleton, one_smul, replicateRow_apply, smul_ite, real_smul, smul_zero,
      ← ofReal_mul, sub_nonneg, one_le_sq_iff_one_le_abs, abs_norm, ha, mul_self_sqrt, ofReal_sub,
      ofReal_pow, ofReal_one, Matrix.neg_apply, neg_mul, forall_const, conjTranspose_apply,
      star_neg, conj_mul', boost, s]
    grind [conj_mul']

/-- The boost depends continuously on its parameter. -/
@[fun_prop]
lemma continuous_cellBoost (𝔰 : Shape) {X : Type*} [TopologicalSpace X] {a : X → ℂ}
    (ha : Continuous a) (ha_norm : ∀ x : X, 1 ≤ ‖a x‖) :
    Continuous fun x : X ↦ cellBoost 𝔰 (a x) (ha_norm x) := by
  refine continuous_U_iff_matrix.2 ?_
  simp only [cellBoost, U.of, IsUnit.unit_spec]
  fun_prop

/-- For a ≠ 0 the point a / min(1, |a|) lies outside the open unit disc. -/
lemma one_le_norm_div_min {a : ℂ} (ha : a ≠ 0) : 1 ≤ ‖a / (min 1 ‖a‖ : ℝ)‖ := by
  have h_pos : 0 < min 1 ‖a‖ := lt_min one_pos (norm_pos_iff.2 ha)
  simp [abs_of_pos h_pos, one_le_div h_pos]

/-- The chart of the big cell of floor l. On the top floor and for c ≠ 0 it is the boost at
c / min(1, |c|), which is c if 1 ≤ |c| and c / |c| otherwise. In all other cases it is
`floorWeyl l c`. -/
def cellChart (𝔰 : Shape) (l : ℕ) (c : ℂ) : 𝔰.G₁ :=
  if h : l = 𝔰.ϱ ∧ c ≠ 0 then cellBoost 𝔰 (c / (min 1 ‖c‖ : ℝ)) (one_le_norm_div_min h.2)
  else floorWeyl l c

/-- The density of floor l at c: |c|^{2(k−1)+4(ϱ−l)} for l < ϱ; otherwise
2π^k((|c|²−1)⁺)^{k−1}/(k−1)!; k = |κ|. For l ≥ ϱ and |c| ≤ 1 this is 0 if and only if k > 1. -/
def cellDensity (𝔰 : Shape) (l : ℕ) (c : ℂ) : ENNReal :=
  if l < 𝔰.ϱ then
    ‖c‖ₑ ^ (2 * (𝔰.k - 1) + 4 * (𝔰.ϱ - l))
  else
    ENNReal.ofReal (sphereDensity 𝔰.k (‖c‖ ^ 2 - 1)⁺)

variable {𝔰 : Shape}

/-- The measure on G₁ that is the image of the density `New.Floors.cellDensity` of floor l times dc
on ℂ under c ↦ w_l(c)⁻¹ (`New.Floors.cellChart`). -/
abbrev cellLaw (l : ℕ) : Measure 𝔰.G₁ :=
  (volume.withDensity (cellDensity 𝔰 l)).map fun c ↦ (cellChart 𝔰 l c)⁻¹

/-- On the top floor and for 1 ≤ |c|, the chart is the boost at c. -/
lemma cellChart_top_of_one_le {c : ℂ} (hc : 1 ≤ ‖c‖) :
    cellChart 𝔰 𝔰.ϱ c = cellBoost 𝔰 c hc := by
  simp [cellChart, norm_pos_iff.1 (one_pos.trans_le hc), min_eq_left hc]

/-- For 1 ≤ |c| the boost at c fixes the basis vectors of the floors below the top, that is, it
lies in `floorGroup ϱ`. -/
lemma cellBoost_mem_floorGroup {c : ℂ} (hc : 1 ≤ ‖c‖) : cellBoost 𝔰 c hc ∈ floorGroup 𝔰.ϱ := by
  simp +contextual only [cellBoost, replicateCol_smul, replicateRow_smul, mem_floorGroup,
    U.val_of_coe, Matrix.one_apply, Sum.forall, floorOf.eq_1, Fin.is_lt, forall_const,
    floorOf.eq_3, add_lt_iff_neg_left, not_lt_zero, IsEmpty.forall_iff, implies_true,
    floorOf.eq_4, lt_self_iff_false, and_self, floorOf.eq_2, true_and, fromBlocks_apply₁₁,
    inl.injEq, fromBlocks_apply₁₂, Matrix.zero_apply, reduceCtorEq, ↓reduceIte, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, inr.injEq]

/-- The chart of floor l takes its values in the group of floor l, which fixes the basis vectors
of the floors below l. -/
lemma cellChart_mem_floorGroup {l : ℕ} {c : ℂ} : cellChart 𝔰 l c ∈ floorGroup l := by
  unfold cellChart
  split_ifs with h
  · obtain ⟨rfl, hc⟩ := h
    exact cellBoost_mem_floorGroup (one_le_norm_div_min hc)
  · exact floorWeyl_mem_floorGroup

/-- The embedding of U(X₀) in G₁ takes its values in the group of the top floor, which fixes the
basis vectors of all floors below ϱ. -/
lemma embedH_mem_floorGroup (k : U 1) : embedH (𝔰 := 𝔰) k ∈ floorGroup 𝔰.ϱ := by
  simp [mem_floorGroup, val_toBesselH_apply_coe, Matrix.one_apply]

/-- The chart of floor l is a measurable function of its parameter. -/
@[fun_prop]
lemma measurable_cellChart {l : ℕ} : Measurable (cellChart 𝔰 l) := by
  by_cases hl : l = 𝔰.ϱ
  · subst hl
    let s : Set ℂ := {0}ᶜ
    have hs : MeasurableSet s := (measurableSet_singleton 0).compl
    have h_eq : cellChart 𝔰 𝔰.ϱ = fun c ↦ if hc : c ∈ s then
        cellBoost 𝔰 (c / (min 1 ‖c‖ : ℝ)) (one_le_norm_div_min hc) else floorWeyl 𝔰.ϱ c := by
      funext c
      by_cases hc : c = 0
      · simp only [cellChart, hc, ne_eq, not_true_eq_false, and_false, s, mem_compl_iff,
          mem_singleton_iff, ↓reduceDIte]
      · simp only [cellChart, hc, ne_eq, not_false_eq_true, and_self, s, mem_compl_iff,
          mem_singleton_iff, ↓reduceDIte]
    rw [h_eq]
    refine Measurable.dite
      (f := fun c : s ↦ cellBoost 𝔰 (c.1 / (min 1 ‖c.1‖ : ℝ)) (one_le_norm_div_min c.2))
      (g := fun c : ↥sᶜ ↦ floorWeyl 𝔰.ϱ c.1) ?_
      (measurable_floorWeyl.comp measurable_subtypeVal) hs
    exact (continuous_cellBoost 𝔰 (continuous_subtypeVal.div (Complex.continuous_ofReal.comp
      (continuous_const.min (continuous_norm.comp continuous_subtypeVal))) fun c ↦
        Complex.ofReal_ne_zero.2 (lt_min one_pos (norm_pos_iff.2 c.2)).ne')
      fun c ↦ one_le_norm_div_min c.2).measurable
  · have h_eq : cellChart 𝔰 l = floorWeyl l :=
      funext fun c ↦ by simp only [cellChart, hl, false_and, ↓reduceDIte]
    rw [h_eq]
    exact measurable_floorWeyl

/-- The density of floor l is a measurable function on ℂ. -/
@[fun_prop]
lemma measurable_cellDensity {l : ℕ} : Measurable (cellDensity 𝔰 l) := by
  by_cases hl : l < 𝔰.ϱ
  · have h_eq : cellDensity 𝔰 l = fun c ↦ ‖c‖ₑ ^ (2 * (𝔰.k - 1) + 4 * (𝔰.ϱ - l)) :=
      funext fun c ↦ by simp only [cellDensity, hl, ↓reduceIte]
    rw [h_eq]
    exact continuous_eNorm.measurable.pow_const _
  · have h_eq : cellDensity 𝔰 l = fun c ↦ ENNReal.ofReal (sphereDensity 𝔰.k (‖c‖ ^ 2 - 1)⁺) :=
      funext fun c ↦ by simp only [cellDensity, hl, ↓reduceIte]
    rw [h_eq]
    exact (ENNReal.continuous_ofReal.comp (continuous_const.mul
      ((continuous_posPart.comp ((continuous_norm.pow 2).sub continuous_const)).pow
        (𝔰.k - 1)))).measurable

/-- For `1 < ‖c‖` the boost `w = cellChart 𝔰 ϱ c` has `h(z, w z) = c`: this is the entry at
(`top`, `top`) of the matrix `realFrameGram` of products of the frame with its translate by `w`,
`top` being the position of `z`. -/
lemma realFrameGram_cellChart {c : ℂ} (hc : 1 < ‖c‖) :
    realFrameGram (cellChart 𝔰 𝔰.ϱ c) 𝔰.top 𝔰.top = c := by
  simp [cellChart_top_of_one_le hc.le, cellBoost, U.of, middleGram, splitGram, frameGram,
    Matrix.mul_apply]

/-! ### The top floor: Cartan decomposition and the hyperboloid -/

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Cartan decomposition of `U(V_ϱ)`, the isometry group of the form `middleGram 1` (diagonal: 1 on
X₀, indexed by κ, and −1 at z). Let `σ` fix the basis vectors of the floors below the top
(`σ ∈ floorGroup ϱ`) and let `c = h(z, σ z)`, the last diagonal entry of `realFrameGram σ`, have
`|c| > 1`. Then `σ = k w_ϱ(c) k'` for some `k`, `k'` in `U(X₀)`, embedded by `embedH` (identity off
X₀), where `w_ϱ(c)` is the boost `cellChart 𝔰 ϱ c`. -/
lemma cartan_decomposition {c : ℂ} {σ : (𝔰.middleGram (1 : ℂ)).G} (hσ : σ ∈ floorGroup 𝔰.ϱ)
    (hZ : realFrameGram σ 𝔰.top 𝔰.top = c) (hc : 1 < ‖c‖) :
    ∃ k k' : U 1, σ = embedH k * cellChart 𝔰 𝔰.ϱ c * embedH k' := by
  -- The column of `σ` at `z` has `h(·,·) = -1` and entry `-c` at `z`, so its part `v` in `X₀` has
  -- `‖v‖² = ‖c‖² - 1`.
  let v (i : 𝔰.κ) : ℂ := σ.val.val (inr (inl (inl i))) 𝔰.z
  have h_entry : σ.val.val 𝔰.z 𝔰.z = -c := by
    simp only [middleGram, ← hZ, frameGram, splitGram, submatrix_apply, besselFrame_top,
      Matrix.mul_apply, sum_sum_type, fromBlocks_apply₂₁, fromRows_apply_inl, Matrix.zero_apply,
      floorOf.eq_1, Fin.is_lt, and_self, floorOf.eq_4, lt_self_iff_false, or_false,
      apply_eq_one_apply_of_mem_floorGroup hσ, ne_eq, reduceCtorEq, not_false_eq_true,
      one_apply_ne, mul_zero, Finset.sum_const_zero, fromBlocks_apply₂₂, fromBlocks_apply₁₁,
      zero_mul, Finset.univ_unique, PUnit.default_eq_unit, of_apply, neg_mul, one_mul,
      Finset.sum_neg_distrib, Finset.sum_singleton, zero_add, fromBlocks_apply₁₂, floorOf.eq_2,
      inr.injEq, add_zero, neg_neg]
  have h_gram : (σ.val.valᴴ * (𝔰.middleGram (1 : ℂ)).splitGram * σ.val.val) 𝔰.z 𝔰.z =
      (𝔰.middleGram (1 : ℂ)).splitGram 𝔰.z 𝔰.z := congr_fun₂ (mem_unitaryGroupOf_iff.1 σ.2) 𝔰.z 𝔰.z
  have h_col : ∑ i : 𝔰.κ, (‖v i‖ : ℂ) ^ 2 = ‖c‖ ^ 2 - 1 := by
    simpa only [middleGram, splitGram, Matrix.mul_apply, conjTranspose_apply, star_def,
      sum_sum_type, floorOf.eq_1, Fin.is_lt, and_self, floorOf.eq_4, lt_self_iff_false, or_false,
      apply_eq_one_apply_of_mem_floorGroup hσ, ne_eq, reduceCtorEq, not_false_eq_true,
      one_apply_ne, map_zero, zero_mul, Finset.sum_const_zero, Finset.univ_unique,
      PUnit.default_eq_unit, h_entry, map_neg, neg_mul, Finset.sum_neg_distrib,
      Finset.sum_singleton, floorOf.eq_2, inr.injEq, add_zero, zero_add, fromBlocks_apply₂₁,
      fromRows_apply_inl, Matrix.zero_apply, mul_zero, neg_zero, fromBlocks_apply₂₂,
      fromBlocks_apply₁₁, Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, conj_mul', fromBlocks_apply₁₂, of_apply, mul_neg, neg_neg, Finset.sum_const,
      Finset.card_singleton, one_smul, add_neg_eq_iff_eq_add, neg_add_eq_sub] using h_gram
  obtain ⟨u, hu⟩ : ∃ u : U 1, u.val.val *ᵥ (√(‖c‖ ^ 2 - 1) • Pi.single 𝔰.k₀ 1) = v :=
    exists_unitary_mulVec_eq _
      (by simp only [dotProduct, Pi.star_apply, Pi.smul_apply, Pi.single_apply, smul_ite,
        real_smul, mul_one, smul_zero, star_def, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, conj_ofReal, ← ofReal_mul, sub_pos,
        one_lt_sq_iff_one_lt_abs, abs_norm, hc, le_of_lt, mul_self_sqrt, ofReal_sub, ofReal_pow,
        ofReal_one, conj_mul', h_col])
  -- `embedH u * cellChart 𝔰 ϱ c` and `σ` take `z` to the same vector
  have h_eq : orbitPoint 𝔰.top (embedH u * cellChart 𝔰 𝔰.ϱ c)⁻¹ = orbitPoint 𝔰.top σ⁻¹ := by
    simpa only [orbitPoint, cellChart_top_of_one_le hc.le, cellBoost, replicateCol_smul,
      replicateRow_smul, _root_.mul_inv_rev, inv_inv, Subgroup.coe_mul, Units.val_mul,
      val_toBesselH_apply_coe, U.val_of_coe, fromBlocks_multiply, mul_one, Matrix.mul_zero,
      add_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.mul_smul, smul_zero,
      neg_zero, Matrix.one_mul, zero_add, one_mul, besselFrame_top, mulVec_single,
      MulOpposite.op_one, one_smul, funext_iff, col_apply, Sum.forall, fromBlocks_apply₁₂,
      Matrix.zero_apply, floorOf.eq_1, Fin.is_lt, and_self, floorOf.eq_4, lt_self_iff_false,
      or_false, apply_eq_one_apply_of_mem_floorGroup hσ, ne_eq, reduceCtorEq, not_false_eq_true,
      one_apply_ne, implies_true, fromBlocks_apply₂₂, fromBlocks_apply₁₁, Matrix.smul_apply,
      Matrix.mul_apply, replicateCol_apply, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, real_smul, of_apply, h_entry, and_true, fromBlocks_apply₂₁,
      floorOf.eq_2, inr.injEq, true_and, mulVec_smul, Pi.smul_apply] using hu
  -- both lie in `floorGroup ϱ` and their quotient fixes `z`, so it comes from `U(X₀)`
  have h_prod : embedH u * cellChart 𝔰 𝔰.ϱ c ∈ floorGroup 𝔰.ϱ :=
    mul_mem (embedH_mem_floorGroup u) cellChart_mem_floorGroup
  have h_mem := inv_mul_mem_of_orbitPoint_eq (b := 𝔰.top) h_prod hσ h_eq
  obtain ⟨k', hk' : (embedH u * cellChart 𝔰 𝔰.ϱ c)⁻¹ * σ = embedH k'⟩ :=
    exists_eq_toBesselH (partialUnitriangularGroup_inf_floorGroup_last.le h_mem) isUnit_one
  exact ⟨u, k', eq_mul_of_inv_mul_eq hk'⟩

/-- The point √(Γ + |c|²) h x + c z of X₀ ⊕ ℂz, in the coordinates `BesselIndex` of the whole space
(`definiteCols` puts X₀ into them), for a real level Γ and a pair (c, h), x being the basis vector
at k₀. For Γ + |c|² ≥ 0 it lies on the hyperboloid h(v, v) = Γ. -/
abbrev hyperboloidPoint (Γ : ℝ) (p : ℂ × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) : 𝔰.BesselIndex → ℂ :=
  update (𝔰.definiteCols *ᵥ (√(Γ + ‖p.1‖ ^ 2) * p.2.val.val · 𝔰.k₀)) 𝔰.z p.1

/-- The image of S((Γ + |c|²)⁺) dc dh under `hyperboloidPoint Γ`, where S is `sphereDensity k`,
S(r) = 2π^k r^(k−1)/(k−1)! with k = |κ|, and dh is the Haar probability measure of U(X₀). For k > 1
it is a measure on the hyperboloid h(v, v) = Γ of V_ϱ, written in polar coordinates. -/
abbrev hyperboloidMeasure (Γ : ℝ) : Measure (𝔰.BesselIndex → ℂ) :=
  map (hyperboloidPoint Γ)
    (volume.withDensity fun p : ℂ × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) ↦
      .ofReal (sphereDensity 𝔰.k (Γ + ‖p.1‖ ^ 2)⁺))

/-- An integral against `hyperboloidMeasure Γ` is the iterated integral over c and h of the
integrand at `hyperboloidPoint Γ (c, h)`, with the density S((Γ + |c|²)⁺). -/
lemma lintegral_hyperboloidMeasure (Γ : ℝ) {g : (𝔰.BesselIndex → ℂ) → ENNReal} (hg : Measurable g) :
    ∫⁻ v : 𝔰.BesselIndex → ℂ, g v ∂hyperboloidMeasure Γ =
      ∫⁻ c : ℂ, .ofReal (sphereDensity 𝔰.k (Γ + ‖c‖ ^ 2)⁺) *
        ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), g (hyperboloidPoint Γ (c, h)) := by
  have h_hp : Continuous (hyperboloidPoint (𝔰 := 𝔰) Γ) := by fun_prop [hyperboloidPoint]
  have h_dens : Measurable fun p : ℂ × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) ↦
      ENNReal.ofReal (sphereDensity 𝔰.k (Γ + ‖p.1‖ ^ 2)⁺) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.mul ((continuous_posPart.comp
      (continuous_const.add ((continuous_norm.comp continuous_fst).pow 2))).pow
        (𝔰.k - 1)))).measurable
  have h_comp : Measurable fun a : ℂ × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) ↦ g (hyperboloidPoint Γ a) :=
    hg.comp h_hp.measurable
  rw [lintegral_map hg h_hp.measurable,
    lintegral_withDensity_eq_lintegral_mul volume h_dens h_comp,
    volume_eq_prod, lintegral_prod _ (h_dens.mul h_comp).aemeasurable]
  refine lintegral_congr fun c ↦ ?_
  simp only [Pi.mul_apply]
  exact lintegral_const_mul _
    (hg.comp (h_hp.comp (continuous_const.prodMk continuous_id)).measurable)

/-- For Γ + |c|² ≥ 0 the point `hyperboloidPoint Γ (c, u)` has h(v, v) = Γ. -/
lemma star_dotProduct_hyperboloidPoint {Γ : ℝ} {c : ℂ} (hΓ : 0 ≤ Γ + ‖c‖ ^ 2)
    (u : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) :
    star (hyperboloidPoint Γ (c, u)) ⬝ᵥ
      (𝔰.middleGram (1 : ℂ)).splitGram *ᵥ hyperboloidPoint Γ (c, u) = Γ := by
  -- the column of `u` at `k₀` has norm one
  have h_col : ∑ i, (‖u.val.val i 𝔰.k₀‖ : ℂ) ^ 2 = 1 := by
    simpa only [mul_one, Matrix.mul_apply, star_apply, star_def, conj_mul', one_apply_eq] using
      congr_fun₂ (mem_unitaryGroupOf_iff.1 u.property) 𝔰.k₀ 𝔰.k₀
  -- the part in X₀ has squared norm `Γ + ‖c‖²` and the entry at z contributes `-‖c‖²`
  suffices ((√(Γ + ‖c‖ ^ 2) ^ 2 : ℝ) : ℂ) + -(‖c‖ : ℂ) ^ 2 = Γ by
    simpa only [dotProduct, Pi.star_apply, star_def, mulVec, splitGram, middleGram, sum_sum_type,
      ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, inclMatrix, submatrix_apply, id_eq,
      one_apply_ne, zero_mul, Finset.sum_const_zero, mul_zero, update_inr_apply_inr,
      update_inl_apply_inl, Function.comp_apply, Matrix.one_apply, inr.injEq, inl.injEq, ite_mul,
      one_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.univ_unique,
      PUnit.default_eq_unit, update_self, ← Finset.sum_mul, Finset.sum_singleton, add_zero,
      zero_add, map_zero, fromBlocks_apply₁₂, fromCols_apply_inl, Matrix.zero_apply,
      fromBlocks_apply₂₂, fromBlocks_apply₁₁, conj_mul', Complex.norm_mul, norm_real, norm_eq_abs,
      abs_of_nonneg (sqrt_nonneg _), ofReal_mul, mul_pow, ← Finset.mul_sum, h_col, mul_one,
      fromBlocks_apply₂₁, of_apply, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_singleton, one_smul, ofReal_pow] using this
  simp only [sq_sqrt hΓ, ofReal_add, ofReal_pow, add_neg_cancel_right]

/-- Polar coordinates on the slice of X₀ ⊕ ℂz with coordinate c at z, for |κ| > 1: with r the
squared norm of the part in X₀ and r = 2t + |c|², the integral over x ∈ X₀ of f(h(v, v), v) is,
where v is (x, c) in the indices `MiddleIndex` of X₀ ⊕ ℂz, put by `inclMatrix` into the coordinates
`BesselIndex` of the whole space, ∫ S((2t + |c|²)⁺) ∫ f(2t, `hyperboloidPoint (2t) (c, u)`) du dt, S
being `sphereDensity k`. -/
lemma lintegral_slice_eq_hyperboloid (hk : 1 < 𝔰.k) (c : ℂ)
    {f : ℂ × (𝔰.BesselIndex → ℂ) → ENNReal} (hf : Measurable f) :
    (∫⁻ x : 𝔰.κ → ℂ,
        let v : 𝔰.BesselIndex → ℂ :=
          inclMatrix ℂ (inr ∘ inl : 𝔰.MiddleIndex → 𝔰.BesselIndex) *ᵥ (x ⊕ᵥ fun _ : Unit ↦ c)
        f (star v ⬝ᵥ (𝔰.middleGram (1 : ℂ)).splitGram *ᵥ v, v)) =
      ∫⁻ t : ℝ, .ofReal (sphereDensity 𝔰.k (2 * t + ‖c‖ ^ 2)⁺) *
        ∫⁻ u : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
          f ((2 * t : ℝ), hyperboloidPoint (2 * t) (c, u)) := by
  let F (r : ℝ) : ENNReal :=
    ∫⁻ u : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
      f ((r - ‖c‖ ^ 2 : ℝ), hyperboloidPoint (r - ‖c‖ ^ 2) (c, u))
  have h_point {r : ℝ} (u : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) :
      inclMatrix ℂ (inr ∘ inl : 𝔰.MiddleIndex → 𝔰.BesselIndex) *ᵥ
          ((u.val.val *ᵥ √r • Pi.single 𝔰.k₀ 1) ⊕ᵥ fun _ ↦ c) =
        hyperboloidPoint (r - ‖c‖ ^ 2) (c, u) := by
    simp only [inclMatrix, funext_iff, mulVec, dotProduct, submatrix_apply, Matrix.one_apply, id_eq,
      Function.comp_apply, ite_mul, one_mul, zero_mul, sum_sum_type, elim_inl, Pi.smul_apply,
      Pi.single_apply, smul_ite, real_smul, mul_comm, smul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, Finset.univ_unique, PUnit.default_eq_unit, elim_inr,
      Finset.sum_singleton, Sum.forall, reduceCtorEq, Finset.sum_const_zero, add_zero, ne_eq,
      not_false_eq_true, update_of_ne, sub_add_cancel, implies_true, inr.injEq,
      update_inr_apply_inr, inl.injEq, update_inl_apply_inl, Finset.sum_ite_eq, zero_add,
      update_self, and_self]
  have h_hp_t : Continuous fun p : ℝ × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) ↦
      hyperboloidPoint (p.1 - ‖c‖ ^ 2) (c, p.2) := by fun_prop [hyperboloidPoint]
  have hF_meas : Measurable F := Measurable.lintegral_prod_right
    (hf.comp ((Complex.continuous_ofReal.comp
      (continuous_fst.sub continuous_const)).measurable.prodMk h_hp_t.measurable))
  have h_step3 : Measurable fun a : ℝ ↦
      ENNReal.ofReal (sphereDensity 𝔰.k (a + ‖c‖ ^ 2)⁺ / 2) * F (a + ‖c‖ ^ 2) :=
    ((ENNReal.continuous_ofReal.comp ((continuous_const.mul
      ((continuous_posPart.comp (continuous_id.add continuous_const)).pow
        (𝔰.k - 1))).div_const 2)).measurable).mul (hF_meas.comp (measurable_add_const _))
  calc _ = ∫⁻ r in Ioi 0, .ofReal (sphereDensity 𝔰.k r / 2) * F r := by
        rw [lintegral_eq_polar 𝔰.k₀ (by fun_prop)]
        refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
        simp only [sphereDensity, h_point, sub_add_cancel, hr.le, star_dotProduct_hyperboloidPoint,
          ofReal_sub, ofReal_pow, F]
    _ = ∫⁻ r, .ofReal (sphereDensity 𝔰.k r⁺ / 2) * F r := by
        -- for `k > 1` the density vanishes at `r⁺ = 0`
        rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_congr fun r ↦ ?_
        by_cases hr : 0 < r
        · simp only [sphereDensity, mem_Ioi, hr, indicator_of_mem, le_of_lt, posPart_of_nonneg]
        · simp only [sphereDensity, mem_Ioi, hr, not_false_eq_true, indicator_of_notMem,
            le_of_not_gt, posPart_of_nonpos, ne_eq, show 𝔰.k - 1 ≠ 0 by omega, zero_pow, mul_zero,
            zero_div, ENNReal.ofReal_zero, zero_mul]
    _ = ∫⁻ t, 2 * (.ofReal (sphereDensity 𝔰.k (2 * t + ‖c‖ ^ 2)⁺ / 2) *
          F (2 * t + ‖c‖ ^ 2)) := by
        conv_lhs =>
          rw [← lintegral_add_right_eq_self _ (‖c‖ ^ 2), ← smul_map_volume_mul_left two_ne_zero]
        rw [lintegral_smul_measure, lintegral_map h_step3 (measurable_const_mul 2), smul_eq_mul,
          ← lintegral_const_mul' _ _ (by simp only [ne_eq, ENNReal.ofReal_ne_top,
            not_false_eq_true])]
        simp only [abs_of_pos (two_pos : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
    _ = _ := lintegral_congr fun t ↦ by
        simp only [← ENNReal.ofReal_ofNat, sphereDensity, ofReal_sub, ofReal_pow, ofReal_add,
          ofReal_mul, ofReal_ofNat, add_sub_cancel_right, ← mul_assoc, Nat.ofNat_nonneg,
          ← ENNReal.ofReal_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel₀, F]

/-- For k = |κ| > 1, let h be standard on X₀ = ℂ^κ with h(z, z) = −1. The measures
`hyperboloidMeasure (2 Im β)` on the level sets h(v, v) = 2 Im β, β skew, disintegrate the volume of
V_ϱ = X₀ ⊕ ℂz along h(v, v). The volume is extended by zero to the whole space, and integrating
f(δ⁻¹β, v) against them and then over β = ri (Lebesgue in r) gives the integral of f(h(v, v), v);
here δ = i/2, so δ⁻¹β = 2 Im β. -/
lemma isDisintegration_hyperboloidMeasure (hk : 1 < 𝔰.k) :
    complexPlace.IsDisintegration
      (volume.map (inclMatrix ℂ (inr ∘ inl : 𝔰.MiddleIndex → 𝔰.BesselIndex) *ᵥ ·))
      (𝔰.middleGram (1 : ℂ)).splitGram
      fun β : skewAdjoint ℂ ↦ hyperboloidMeasure (2 * im (β : ℂ)) := by
  have h_hp : Continuous fun q : skewAdjoint ℂ × (ℂ × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) ↦
      hyperboloidPoint (2 * im (q.1 : ℂ)) q.2 := by fun_prop [hyperboloidPoint]
  refine ⟨fun {g} (hg_cont : Continuous g) (hg_supp : HasCompactSupport g) ↦ ?_, fun f hf ↦ ?_⟩
  · -- the integrands vanish off one compact set of `(c, h)`, as `c` is the coordinate at `z`
    have h_hp_b (β : skewAdjoint ℂ) : Continuous (hyperboloidPoint (2 * im (β : ℂ))) :=
      h_hp.comp (continuous_const.prodMk continuous_id)
    have h_dens_b (β : skewAdjoint ℂ) : Measurable fun p : ℂ × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) ↦
        ENNReal.ofReal (sphereDensity 𝔰.k (2 * im (β : ℂ) + ‖p.1‖ ^ 2)⁺) :=
      (ENNReal.continuous_ofReal.comp (continuous_const.mul ((continuous_posPart.comp
        (continuous_const.add ((continuous_norm.comp continuous_fst).pow 2))).pow
          (𝔰.k - 1)))).measurable
    have h_comp_b (β : skewAdjoint ℂ) :
        Measurable fun a : ℂ × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) ↦
          (g (hyperboloidPoint (2 * im (β : ℂ)) a) : ENNReal) :=
      (ENNReal.continuous_coe.comp hg_cont).measurable.comp (h_hp_b β).measurable
    have h_lhs (β : skewAdjoint ℂ) :
        ∫⁻ v, (g v : ENNReal) ∂hyperboloidMeasure (2 * im (β : ℂ)) =
          ∫⁻ a : ℂ × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
            ((sphereDensity 𝔰.k (2 * im (β : ℂ) + ‖a.1‖ ^ 2)⁺).toNNReal *
              g (hyperboloidPoint (2 * im (β : ℂ)) a) : ENNReal) := by
      rw [lintegral_map (f := fun v ↦ (g v : ENNReal))
          (ENNReal.continuous_coe.comp hg_cont).measurable (h_hp_b β).measurable,
        lintegral_withDensity_eq_lintegral_mul volume (h_dens_b β) (h_comp_b β)]
      exact lintegral_congr fun a ↦ by simp only [Pi.mul_apply, ENNReal.ofReal]
    simp_rw [h_lhs]
    have h_compact : IsCompact
        (((· 𝔰.z) '' tsupport g) ×ˢ (univ : Set (U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)))) :=
      (hg_supp.image_of_continuous (· 𝔰.z)).prod isCompact_univ
    have h_joint : Continuous ↿fun (β : skewAdjoint ℂ) (a : ℂ × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) ↦
        (sphereDensity 𝔰.k (2 * im (β : ℂ) + ‖a.1‖ ^ 2)⁺).toNNReal *
          g (hyperboloidPoint (2 * im (β : ℂ)) a) :=
      (continuous_real_toNNReal.comp (continuous_const.mul ((continuous_posPart.comp
        ((continuous_const.mul (Complex.continuous_im.comp
          (continuous_subtypeVal.comp continuous_fst))).add
          ((continuous_norm.comp (continuous_fst.comp continuous_snd)).pow 2))).pow
            (𝔰.k - 1)))).mul (hg_cont.comp h_hp)
    -- the first coordinate of a point where the integrand is nonzero is the value at `z`
    exact continuous_lintegral_and_lt_top h_compact h_joint fun _ _ h_ne ↦
      ⟨⟨_, subset_closure (right_ne_zero_of_mul h_ne),
        by simp only [hyperboloidPoint, update_self]⟩, trivial⟩
  -- split off the coordinate `c` at `z`
  have h_split (g : (𝔰.MiddleIndex → ℂ) → ENNReal) (hg : Measurable g) :
      ∫⁻ a, g a = ∫⁻ c : ℂ, ∫⁻ x : 𝔰.κ → ℂ, g (x ⊕ᵥ fun _ ↦ c) := by
    rw [← (measurePreserving_sumElim (A := ℂ) (ι := 𝔰.κ) (κ := Unit)).lintegral_comp hg,
      volume_eq_prod, lintegral_prod_symm _ (by fun_prop),
      ← (volume_preserving_funUnique Unit ℂ).symm.lintegral_comp (by fun_prop)]
    rfl
  simp (disch := fun_prop) only [lintegral_hyperboloidMeasure]
  rw [lintegral_map (by fun_prop) (by fun_prop), lintegral_lintegral_swap (by fun_prop),
    h_split _ (by fun_prop)]
  refine lintegral_congr fun c ↦ ?_
  -- the skew elements are `t * I`, and `δ⁻¹ (t * I) = 2 t`
  rw [lintegral_slice_eq_hyperboloid hk c hf, complexPlace_skewMeasure,
    lintegral_map (by fun_prop) (by fun_prop)]
  refine lintegral_congr fun t ↦ ?_
  have h_sk : ((complexPlace.skewUnit : ℂ)⁻¹) * (t * I) = ((2 * t : ℝ) : ℂ) := by
    simp only [complexPlace_skewUnit, Units.val_mk0, inv_div]
    calc (2 / I) * (↑t * I) = 2 * ↑t * (I / I) := by ring
      _ = (2 * t : ℝ) := by simp only [div_self I_ne_zero, mul_one, ofReal_mul, ofReal_ofNat]
  rw [Units.val_inv_eq_inv_val, h_sk]
  simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]

/-- Polar coordinates on the hyperboloid h(v, v) = −1 of V_ϱ = X₀ ⊕ ℂz, where X₀ has an orthonormal
basis indexed by κ and h(z, z) = −1, assuming `1 < 𝔰.k` (i.e. |κ| > 1). Let c have the law
`cellDensity`(c) dc, let w_ϱ(c) be the boost `cellChart 𝔰 ϱ c`, and let h ∈ U(X₀), embedded in G₁ by
`embedH`, have the Haar probability law. Then the map σ ↦ σ⁻¹z (`orbitPoint` at the top position)
carries the law of w_ϱ(c)⁻¹h to `floorQuadricMeasure`, the image of `quadricMeasure` of that
hyperboloid under the basis `complexBasis 𝔰`. -/
lemma map_orbitPoint_cellLaw_top (hk : 1 < 𝔰.k) :
    (cellLaw 𝔰.ϱ ∗ₘ volume.map embedH).map (orbitPoint 𝔰.top) =
    (complexBasis 𝔰).floorQuadricMeasure 𝔰.top := by
  -- By uniqueness of disintegrations the right side is `hyperboloidMeasure (-1)`; the left side
  -- becomes this measure on substituting `-c` for `c` and `h⁻¹` for `h`.
  have h_quadric : (complexBasis 𝔰).floorQuadricMeasure 𝔰.top = hyperboloidMeasure (-1) := by
    rw [((complexBasis 𝔰).isDisintegration_floorVolume 𝔰.top
      map_inclMatrix_middle_eq_floorVolume).unique (isDisintegration_hyperboloidMeasure hk)]
    simp only [splitGram, middleGram, besselFrame_top, fromBlocks_apply₂₂, fromBlocks_apply₁₁,
      of_apply, Place.skewUnitMul_coe, complexPlace_skewUnit, Units.val_mk0, mul_neg, mul_one,
      neg_im, div_ofNat_im, I_im, one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_inv_cancel₀]
  refine ext_of_lintegral _ fun f hf ↦ ?_
  have h_orb : Measurable (orbitPoint 𝔰.top : 𝔰.G₁ → 𝔰.BesselIndex → ℂ) :=
    (continuous_orbitPoint (b := 𝔰.top)).measurable
  have h_f_orb : Measurable fun g : 𝔰.G₁ ↦ f (orbitPoint 𝔰.top g) := hf.comp h_orb
  have h_f_mul : Measurable fun p : 𝔰.G₁ × 𝔰.G₁ ↦ f (orbitPoint 𝔰.top (p.1 * p.2)) :=
    h_f_orb.comp continuous_mul.measurable
  have h_chart_inv : Measurable fun c : ℂ ↦ (cellChart 𝔰 𝔰.ϱ c)⁻¹ := measurable_cellChart.inv
  have h_inn : Measurable fun g : 𝔰.G₁ ↦
      ∫⁻ y : 𝔰.G₁, f (orbitPoint 𝔰.top (g * y)) ∂volume.map embedH :=
    Measurable.lintegral_prod_right h_f_mul
  have h_inn_c : Measurable fun c : ℂ ↦
      ∫⁻ y : 𝔰.G₁, f (orbitPoint 𝔰.top ((cellChart 𝔰 𝔰.ϱ c)⁻¹ * y)) ∂volume.map embedH :=
    h_inn.comp h_chart_inv
  rw [h_quadric, lintegral_hyperboloidMeasure _ hf]
  rw [lintegral_map hf h_orb, lintegral_mconv h_f_orb, cellLaw,
    lintegral_map h_inn h_chart_inv,
    lintegral_withDensity_eq_lintegral_mul volume measurable_cellDensity h_inn_c]
  refine Eq.trans (lintegral_congr fun c ↦ congrArg (cellDensity 𝔰 𝔰.ϱ c * ·)
    (lintegral_map (f := fun y : 𝔰.G₁ ↦ f (orbitPoint 𝔰.top ((cellChart 𝔰 𝔰.ϱ c)⁻¹ * y)))
      (h_f_orb.comp (measurable_const_mul _)) continuous_embedH.measurable)) ?_
  change ∫⁻ c : ℂ, cellDensity 𝔰 𝔰.ϱ c *
      ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), f (orbitPoint 𝔰.top ((cellChart 𝔰 𝔰.ϱ c)⁻¹ * embedH h)) =
    ∫⁻ c : ℂ, .ofReal (sphereDensity 𝔰.k (-1 + ‖c‖ ^ 2)⁺) *
      ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), f (hyperboloidPoint (-1) (c, h))
  rw [← lintegral_neg_eq_self]
  refine lintegral_congr fun c ↦ ?_
  rw [← lintegral_inv_eq_self]
  by_cases hc : 1 < ‖c‖
  · have hc_neg : 1 ≤ ‖-c‖ := by simpa only [norm_neg] using hc.le
    -- `h` times the boost at `-c` takes `z` to `√(‖c‖² - 1) h x + c z`
    have h_point (h : U 1) : orbitPoint 𝔰.top ((cellBoost 𝔰 (-c) hc_neg)⁻¹ * embedH h⁻¹) =
        hyperboloidPoint (-1) (c, h) := by
      have h_inv : (embedH (𝔰 := 𝔰) h⁻¹)⁻¹ = embedH h := by simp only [embedH, map_inv, inv_inv]
      rw [orbitPoint, _root_.mul_inv_rev, inv_inv, h_inv]
      simp only [cellBoost, map_neg, norm_neg, replicateCol_smul, replicateRow_smul, neg_neg,
        Subgroup.coe_mul, Units.val_mul, val_toBesselH_apply_coe, U.val_of_coe, besselFrame_top,
        mulVec_single, MulOpposite.op_one, one_smul, hyperboloidPoint, inclMatrix, neg_add_eq_sub,
        mul_comm (√(‖c‖ ^ 2 - 1) : ℂ), funext_iff, col_apply, Matrix.mul_apply, sum_sum_type,
        fromBlocks_apply₁₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, fromBlocks_apply₂₂,
        fromBlocks_apply₁₁, Matrix.smul_apply, replicateCol_apply, Pi.single_apply, smul_ite,
        real_smul, one_mul, smul_zero, mul_ite, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        Finset.univ_unique, PUnit.default_eq_unit, of_apply, Finset.sum_singleton,
        fromBlocks_apply₂₁, add_zero, zero_add, Sum.forall, zero_mul, ne_eq, reduceCtorEq,
        not_false_eq_true, update_of_ne, mulVec, dotProduct, submatrix_apply, id_eq, one_apply_ne,
        implies_true, update_inr_apply_inr, update_inl_apply_inl, Function.comp_apply,
        Matrix.one_apply, inr.injEq, inl.injEq, ite_mul, Finset.sum_ite_eq,
        update_self, and_self]
    simp only [cellChart_top_of_one_le hc_neg, h_point]
    simp only [cellDensity, lt_self_iff_false, ↓reduceIte, sphereDensity, norm_neg, neg_add_eq_sub]
  · -- for `‖c‖ ≤ 1` both densities vanish, as `k > 1`
    have h_pos : (‖c‖ ^ 2 - 1)⁺ = 0 :=
      posPart_eq_zero.2 (sub_nonpos.2 (pow_le_one₀ (norm_nonneg c) (not_lt.1 hc)))
    simp only [cellDensity, lt_self_iff_false, ↓reduceIte, sphereDensity, norm_neg, h_pos, ne_eq,
      show 𝔰.k - 1 ≠ 0 by omega, not_false_eq_true, zero_pow, mul_zero, ENNReal.ofReal_zero,
      map_inv, zero_mul, neg_add_eq_sub]

instance : IsProbabilityMeasure (volume.map (embedH (𝔰 := 𝔰))) :=
  (isProbabilityMeasure_map_iff continuous_embedH.aemeasurable).2 inferInstance

end New.Floors

end
