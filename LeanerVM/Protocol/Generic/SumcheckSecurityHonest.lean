/-
  LeanerVM.Protocol.Generic.SumcheckSecurityHonest

  Constructed honest inputs for the pinned sumcheck knowledge verifier.
-/

module

public import LeanerVM.Protocol.Generic.SumcheckSecurityCore
public import LeanerVM.Protocol.Generic.HonestSumcheck

/-!
# Honest multivariate inputs

The original suffix-sum constructor scope is retained separately from the fixed-polynomial
knowledge core. Input ordering is explicit: use `sumcheckHighFirst` for high-first VM rounds.
-/

namespace LeanerVM.Protocol.SumcheckSecurity

@[expose] public section

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] {d : ℕ}

/-- Honest messages are the actual suffix sums from the reusable sumcheck algebra. -/
noncomputable def honestRoundMessage {m : ℕ} (P : MvPolynomial (Fin m) F)
    (k : Fin m) (c : Fin k.val → F) (hd : MvPolynomial.degreeOf k P ≤ d) :
    SumcheckMessage F d :=
  ⟨sumcheckRoundPoly P k.val c, (sumcheck_natDegree_roundPoly_le P k c).trans hd⟩

/-- The first claim is the Boolean-cube sum; the message is constructed, not assumed to exist. -/
noncomputable def initialInput {m : ℕ} (P : MvPolynomial (Fin (m + 1)) F)
    (hd : MvPolynomial.degreeOf 0 P ≤ d) : Input F d :=
  ⟨honestRoundMessage P 0 Fin.elim0 hd,
    ∑ b : Fin (m + 1) → Fin 2, MvPolynomial.eval (fun i ↦ ((b i).val : F)) P⟩

omit [DecidableEq F] [SampleableType F] in
/-- The constructed first input satisfies the endpoint relation by the cube-splitting identity. -/
theorem initialInput_related {m : ℕ} (P : MvPolynomial (Fin (m + 1)) F)
    (hd : MvPolynomial.degreeOf 0 P ≤ d) :
    (initialInput P hd, ()) ∈ (relIn : Set (Input F d × Unit)) := by
  exact sumcheck_roundPoly_initial P Fin.elim0 (Nat.succ_pos m)

end
end LeanerVM.Protocol.SumcheckSecurity
