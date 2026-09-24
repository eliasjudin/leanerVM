/-
  LeanerVMTests.Protocol.SumcheckSecurity

  Controls for the rejecting single-round sumcheck knowledge reduction.
-/

module

public import LeanerVM.Protocol.Generic.SumcheckSecurity
import Mathlib.Algebra.Field.ZMod
import ArkLib.OracleReduction.Composition.Sequential.Append.Basic

/-!
# Sumcheck knowledge leaf controls

These check the fixed-size coefficient codec, rejection in the actual verifier, an exact
false-claim success probability and exclusion of a higher-degree wire polynomial.
-/

namespace LeanerVMTests.Protocol.SumcheckSecurity

open LeanerVM.Protocol LeanerVM.Protocol.SumcheckSecurity OracleComp
open scoped ENNReal

@[expose] public section

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- A bounded zero polynomial. -/
noncomputable def zeroPoly : SumcheckMessage (ZMod 7) 1 := ⟨0, by simp⟩
/-- A bounded linear polynomial. -/
noncomputable def linearPoly : SumcheckMessage (ZMod 7) 1 := ⟨Polynomial.X, by simp⟩
/-- A false endpoint claim about the zero polynomial. -/
noncomputable def wrong : Input (ZMod 7) 1 := ⟨zeroPoly, 1⟩

example (p : SumcheckMessage (ZMod 7) 0) : decode (encode p) = p := decode_encode p
example (q : Wire (ZMod 7) 4) : encode (decode q) = q := encode_decode q

example (r : ZMod 7) : result wrong (transcript (encode zeroPoly) r) = none := by
  simp [result, transcript, wrong, zeroPoly]

example : Pr[fun out ↦ ∃ y, out = some y ∧ (y, ()) ∈
    (relOut : Set (Output (ZMod 7) 1 × Unit)) | sample wrong (encode linearPoly)] =
      (1 : ℝ≥0∞) / 7 := by
  simp [sample, result, transcript, probEvent_map, Function.comp_def, wrong, zeroPoly,
    linearPoly, relOut, probEvent_eq_eq_probOutput', probOutput_uniformSample]

example (q : Wire (ZMod 7) 1) : (decode q).val ≠ Polynomial.X ^ 2 := by
  intro h
  have hd := (decode q).property
  rw [h, Polynomial.natDegree_pow, Polynomial.natDegree_X] at hd
  norm_num at hd

example (p : SumcheckMessage (ZMod 7) 0) :
    Pr[fun out ↦ ∃ y, out = some y ∧ (y, ()) ∈
      (relOut : Set (Output (ZMod 7) 0 × Unit)) |
      sample ⟨p, p.val.eval 0 + p.val.eval 1⟩ (encode p)] = 1 :=
  sample_honest _ rfl

/-- If the challenge is revealed first, a degree-two message can repair every false claim. -/
noncomputable def adaptiveMessage (r : ZMod 7) : SumcheckMessage (ZMod 7) 2 :=
  if r = 1 then ⟨1 - Polynomial.X, by
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)⟩
  else ⟨Polynomial.C (1 - r)⁻¹ * (Polynomial.X * (Polynomial.X - Polynomial.C r)), by
    apply (Polynomial.natDegree_mul_le).trans
    simp only [Polynomial.natDegree_C, zero_add]
    apply (Polynomial.natDegree_mul_le).trans
    simp⟩

/-- The challenge-dependent message passes the endpoint check for the false target one. -/
theorem adaptive_endpoints (r : ZMod 7) :
    (adaptiveMessage r).val.eval 0 + (adaptiveMessage r).val.eval 1 = 1 := by
  by_cases h : r = 1
  · simp [adaptiveMessage, h]
  · simp [adaptiveMessage, h, sub_ne_zero.mpr (Ne.symm h)]

/-- The same message agrees with the true zero polynomial at the already known challenge. -/
theorem adaptive_hits (r : ZMod 7) : (adaptiveMessage r).val.eval r = 0 := by
  by_cases h : r = 1 <;> simp [adaptiveMessage, h]

/-- This deliberately reversed game violates the fresh-prefix bound `2 / 7`. -/
example : Pr[fun out ↦ ∃ y, out = some y ∧ (y, ()) ∈
    (relOut : Set (Output (ZMod 7) 2 × Unit)) |
    (fun r ↦ result (⟨⟨0, by simp⟩, 1⟩ : Input (ZMod 7) 2)
      (transcript (encode (adaptiveMessage r)) r)) <$> uniformSample (ZMod 7)] = 1 := by
  simp [probEvent_map, Function.comp_def, result, transcript, adaptive_endpoints,
    adaptive_hits, relOut]

example : (2 : ℝ≥0∞) / 7 < 1 := by
  rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  norm_num

/-- ArkLib's total `PureForm` cannot represent this verifier's genuine rejection branch. -/
example : ¬ Nonempty ((verifier (F := ZMod 7) (d := 1) unifSpec).PureForm) := by
  rintro ⟨p⟩
  have h := congrArg OptionT.run (p.verify_eq wrong (transcript (encode zeroPoly) 0))
  simp [verifier, result, transcript, wrong, zeroPoly] at h


-- Rejection is a result of the actual ArkLib verifier, not an invented default output.
example (r : ZMod 7) :
    (verifier unifSpec).verify wrong (transcript (encode zeroPoly) r) = failure := by
  simp [verifier, result, transcript, wrong, zeroPoly]
  rfl

-- A rejected prefix rejects the actual sequential verifier for every suffix verifier.
example {n : ℕ} {p : ProtocolSpec n} {S : Type}
    (V : Verifier unifSpec (Output (ZMod 7) 1) S p)
    (tr : p.FullTranscript) (r : ZMod 7) :
    ((verifier (F := ZMod 7) (d := 1) unifSpec).append V).run wrong
      ((transcript (encode zeroPoly) r).append tr) = failure := by
  simp [Verifier.run, Verifier.append, verifier, result, wrong, zeroPoly, transcript]
  change (failure >>= fun out ↦ V.verify out tr) = failure
  simp

-- Keeping the polynomial while dropping the challenge does not give the next sum relation.
example : ∃ out : Output (ZMod 7) 1,
    (out, ()) ∈ (relOut : Set (Output (ZMod 7) 1 × Unit)) ∧
    ((⟨out.poly, out.target⟩ : Input (ZMod 7) 1), ()) ∉ relIn := by
  refine ⟨⟨linearPoly, 0, 0⟩, ?_, ?_⟩ <;> simp [relOut, relIn, linearPoly]

-- The re-export retains the complete multivariate honest-input constructor.
example (p : MvPolynomial (Fin 2) (ZMod 7)) (h : MvPolynomial.degreeOf 0 p ≤ 3) :
    (initialInput p h, ()) ∈ (relIn : Set (Input (ZMod 7) 3 × Unit)) :=
  initialInput_related p h

end
end LeanerVMTests.Protocol.SumcheckSecurity
