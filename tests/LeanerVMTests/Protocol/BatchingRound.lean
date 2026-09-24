/-
  LeanerVMTests.Protocol.BatchingRound

  Regression controls for the fresh-challenge batching game.
-/

module

public import LeanerVM.Protocol.Generic.BatchingRound
import Mathlib.Algebra.Field.ZMod

/-!
# Operational batching controls

Empty and singleton families have zero false-acceptance probability under arbitrary
probabilistic claim generation before the fresh challenge. A reversed-order game shows why
the claims must be fixed before the challenge.
-/

namespace LeanerVMTests.Protocol.BatchingRoundControls

open LeanerVM.Protocol OracleComp
open scoped ENNReal

public section

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example (message : ProbComp (Fin 1 → ZMod 5)) :
    Pr[FalseBatchAccepted (fun _ ↦ 0) | runBatchingRound message] = 0 := by
  have h := runBatchingRound_false_accept_le (fun _ : Fin 1 ↦ (0 : ZMod 5)) message
  exact le_antisymm (by simpa using h) (by positivity)

example (message : ProbComp (Fin 0 → ZMod 5)) :
    Pr[FalseBatchAccepted Fin.elim0 | runBatchingRound message] = 0 := by
  have h := runBatchingRound_false_accept_le (Fin.elim0 : Fin 0 → ZMod 5) message
  exact le_antisymm (by simpa using h) (by positivity)

/-- Revealing the challenge first lets the false family `[-ρ, 1]` cancel with certainty. -/
example : Pr[FalseBatchAccepted (fun _ : Fin 2 ↦ (0 : ZMod 5)) |
    (fun ρ : ZMod 5 ↦ (⟨![-ρ, 1], ρ, powerBatch ![-ρ, 1] ρ⟩ :
      PowerBatchTranscript (ZMod 5) 2)) <$> uniformSample (ZMod 5)] = 1 := by
  have hfalse (ρ : ZMod 5) : ∃ j : Fin 2, (![-ρ, 1] : Fin 2 → ZMod 5) j ≠ 0 :=
    ⟨1, by simp⟩
  simp [probEvent_map, Function.comp_def, FalseBatchAccepted, hfalse, powerBatch,
    Fin.sum_univ_two]

example : (1 : ℝ≥0∞) / 5 < 1 := by
  rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  norm_num

end
end LeanerVMTests.Protocol.BatchingRoundControls
