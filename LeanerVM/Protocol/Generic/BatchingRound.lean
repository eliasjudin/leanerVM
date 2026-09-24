/-
  LeanerVM.Protocol.Generic.BatchingRound

  Power batching after an arbitrary probabilistic prover prefix.
-/

module

public import LeanerVM.Protocol.Generic.PowerBatching
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Operational power batching

Category A: random identity testing in `cor:idtest`,
`doc/leanvm/body/03-proving-primitives.tex`, and the zero-based batching powers in §5's
`doc/leanvm/body/05-arithmetization.tex` (`sec:gkr`, `sec:air`), at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. This generic scalar game does not assign the
VM's Category B constraint/side powers or implement its transcript.

The claimed values are produced first and the batching challenge is sampled afterwards.
The transcript retains the claimed values so that the false-input event is explicit. The
bound applies to every probabilistic message computation and includes the empty family.

This supplies the direct scalar batching game toward the protocol blueprint's
Layer 4 batching consumer.
Its future sumcheck consumer is tracked by
[ArkLib #1](https://github.com/Verified-zkEVM/ArkLib/issues/1); an ArkLib batching
knowledge-security adapter remains a separate obligation. The source-derived scalar algebra
is imported from `PowerBatching`; this module adds the probabilistic prefix and fresh sample.

This compatibility game uses the pinned VCVio `ProbComp` interface. ArkLib
`BatchingStrategy.gammaPowers` in open [#615](https://github.com/Verified-zkEVM/ArkLib/pull/615)
at `ca7a2577` is absent from the ArkLib pin `dca90385`; its current native probability
interface differs from this one. Adopting that strategy and its knowledge-security adapter
requires a separate dependency and API migration.
-/

namespace LeanerVM.Protocol

open OracleComp
open scoped ENNReal

@[expose] public section

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] {J : ℕ}

/-- The message, fresh challenge, and scalar claim of one batching round. -/
structure PowerBatchTranscript (F : Type) (J : ℕ) where
  /-- The prover's claims, fixed before the challenge. -/
  claims : Fin J → F
  /-- The verifier's fresh challenge. -/
  challenge : F
  /-- The scalar computed with powers starting at zero. -/
  value : F

/-- Sample the challenge after the claims have been produced. -/
def runBatchingRound (message : ProbComp (Fin J → F)) : ProbComp (PowerBatchTranscript F J) :=
  message >>= fun claims ↦
    (fun ρ ↦ ⟨claims, ρ, powerBatch claims ρ⟩) <$> uniformSample F

/-- A false family has become a true scalar claim. -/
def FalseBatchAccepted (values : Fin J → F) (tr : PowerBatchTranscript F J) : Prop :=
  (∃ j, tr.claims j ≠ values j) ∧ tr.value = powerBatch values tr.challenge

/-- The actual fresh-sampling game inherits the degree `J - 1` root bound. -/
theorem runBatchingRound_false_accept_le (values : Fin J → F)
    (message : ProbComp (Fin J → F)) :
    Pr[FalseBatchAccepted values | runBatchingRound message] ≤
      (J - 1 : ℕ) / (Fintype.card F : ℝ≥0∞) := by
  classical
  unfold runBatchingRound
  apply probEvent_bind_le_of_forall_le
  intro claims _
  rw [probEvent_map]
  by_cases hfalse : ∃ j, claims j ≠ values j
  · simp only [Function.comp_def, FalseBatchAccepted, hfalse, true_and]
    rw [probEvent_uniformSample]
    have h := card_false_batch_le claims values hfalse
    gcongr
  · simp [Function.comp_def, FalseBatchAccepted, hfalse]

omit [Fintype F] [DecidableEq F] in
/-- Honest claims always yield the expected scalar claim. -/
theorem runBatchingRound_honest (values : Fin J → F) :
    Pr[fun tr ↦ tr.value = powerBatch values tr.challenge |
      runBatchingRound (pure values)] = 1 := by
  simp [runBatchingRound, probEvent_map, Function.comp_def]

end
end LeanerVM.Protocol
