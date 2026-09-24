/-
  LeanerVM.Protocol.Generic.SumcheckSecurityCore

  A concrete degree-enforced sumcheck leaf in ArkLib's knowledge framework.
-/

module

public import Mathlib.Algebra.Polynomial.Roots
public import ArkLib.OracleReduction.Security.RoundByRound
public import Mathlib.Algebra.Polynomial.OfFn

/-!
# Single-round sumcheck knowledge soundness

Category A: the endpoint test, honest strategy and fresh-challenge root bound in
`fact:sumcheck`, `doc/leanvm/body/03-proving-primitives.tex`, at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`.

The generic wire carries exactly `d + 1` coefficients. It does not transcribe the Category B
encoding in `crates/fiat_shamir/src/transcript.rs:289-309` at that pin, which derives one
coefficient from the incoming claim; that correspondence belongs to Layer 12's decoder.
The verifier checks the two endpoints,
then forwards the true polynomial and the new evaluation claim without evaluating that
polynomial. The same fixed unit extractor and explicit knowledge states are used in both
worst-case and adversarial-prefix ArkLib games. Honest execution is an actual ArkLib
reduction and has perfect completeness for every ambient oracle implementation.

The separately imported honest-input adapter constructs suffix-sum messages and the initial
Boolean-cube claim. The codec is bijective with degree-bounded polynomials. The per-round
error is `d / |F|`; the message is fixed before the challenge. Rejection remains `none`.
The caller supplies the polynomial's variable ordering; the high-first VM adapter is not
implicit in `initialInput`.

This leaf uses an explicit polynomial in its statement representation. Transport to the
virtual oracle summand, final table claims and composition across multiple rounds remain
separate integration obligations. It is not the full VM sumcheck protocol.

This leaf supports the protocol blueprint's sumcheck layer, tracked by
[ArkLib #1](https://github.com/Verified-zkEVM/ArkLib/issues/1). This pinned compatibility
implementation has a fixed-extractor knowledge contract; it does not replace the newer typed
Interaction API or prove full sumcheck. Retire this compatibility layer after explicit upstream
adoption and relation/representation transport, without incidental dependency changes.
Pinned staging is tracked by [leanerVM #37](https://github.com/Verified-zkEVM/leanerVM/issues/37).
-/

namespace LeanerVM.Protocol

/-- Polynomial message carrier retained for the pinned sumcheck verifier interface. -/
public abbrev SumcheckMessage (F : Type) [Semiring F] (d : ℕ) :=
  {p : Polynomial F // p.natDegree ≤ d}

namespace SumcheckSecurity

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

@[expose] public section

section Codec

variable {F : Type} [Semiring F] [DecidableEq F] {d : ℕ}

/-- Exactly `d + 1` coefficients, including trailing zero coefficients. -/
abbrev Wire (F : Type) (d : ℕ) := Fin (d + 1) → F

/-- The wire format enforces the degree cap by construction. -/
noncomputable def decode (q : Wire F d) : SumcheckMessage F d :=
  ⟨Polynomial.ofFn (d + 1) q,
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) q)⟩

/-- Canonical fixed-length coefficient encoding. -/
noncomputable def encode (p : SumcheckMessage F d) : Wire F d := Polynomial.toFn (d + 1) p.val

/-- Decoding the canonical coefficients recovers the bounded polynomial. -/
@[simp] theorem decode_encode (p : SumcheckMessage F d) : decode (encode p) = p := by
  apply Subtype.ext
  exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le p.property)

/-- Encoding a decoded wire retains every coefficient, including trailing zeros. -/
@[simp] theorem encode_decode (q : Wire F d) : encode (decode q) = q :=
  Polynomial.toFn_comp_ofFn_eq_id (d + 1) q

end Codec

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] {d : ℕ}

/-- The true round polynomial and claimed endpoint sum. -/
structure Input (F : Type) [Semiring F] (d : ℕ) where
  /-- The fixed polynomial against which the endpoint claim is interpreted. -/
  poly : SumcheckMessage F d
  /-- The claimed sum of its evaluations at zero and one. -/
  target : F

/-- The unchanged true polynomial and the next evaluation claim. -/
structure Output (F : Type) [Semiring F] (d : ℕ) where
  /-- The same polynomial retained from the input. -/
  poly : SumcheckMessage F d
  /-- The challenge sampled after the prover message. -/
  point : F
  /-- The sent polynomial's evaluation at the challenge. -/
  target : F

/-- One degree-bounded prover message followed by one field challenge. -/
def spec (F : Type) [Semiring F] (d : ℕ) : ProtocolSpec 2 :=
  ⟨!v[.P_to_V, .V_to_P], !v[Wire F d, F]⟩

omit [DecidableEq F] [SampleableType F] in
/-- The coefficient message is sent by the prover. -/
@[simp] theorem dir_zero : (spec F d).dir 0 = .P_to_V := rfl
omit [DecidableEq F] [SampleableType F] in
/-- The following field challenge is sent by the verifier. -/
@[simp] theorem dir_one : (spec F d).dir 1 = .V_to_P := rfl

/-- The unique challenge is sampled using the field's supplied uniform sampler. -/
instance challengeSampleable : ∀ i, SampleableType ((spec F d).Challenge i) := by
  intro ⟨i, hi⟩
  have hv : i = (1 : Fin 2) := by
    fin_cases i
    · simp [spec] at hi
    · rfl
  subst i
  exact inferInstanceAs (SampleableType F)

/-- Input truth is the endpoint identity; there is no auxiliary witness. -/
def relIn : Set (Input F d × Unit) :=
  {p | p.1.poly.val.eval 0 + p.1.poly.val.eval 1 = p.1.target}

/-- Output truth is evaluation at the sampled point. -/
def relOut : Set (Output F d × Unit) :=
  {p | p.1.poly.val.eval p.1.point = p.1.target}

variable {ι : Type} (oSpec : OracleSpec ι)

/-- Pure verifier result, including endpoint-check rejection. -/
noncomputable def result (stmt : Input F d) (tr : (spec F d).FullTranscript) :
    Option (Output F d) :=
  let q : SumcheckMessage F d := decode (tr 0)
  let r : F := tr 1
  if q.val.eval 0 + q.val.eval 1 = stmt.target then some ⟨stmt.poly, r, q.val.eval r⟩ else none

/-- The full transcript has the wire message first and the field challenge second. -/
def transcript (q : Wire F d) (r : F) : (spec F d).FullTranscript
  | ⟨0, _⟩ => q
  | ⟨1, _⟩ => r

/-- Execute the same guarded verifier with a fresh challenge after a fixed message. -/
noncomputable def sample (stmt : Input F d) (q : Wire F d) : ProbComp (Option (Output F d)) :=
  (fun r ↦ result stmt (transcript q r)) <$> uniformSample F

/-- The actual verifier sampler retains its endpoint guard and its sampled point. -/
theorem sample_eq (stmt : Input F d) (q : Wire F d) :
    sample stmt q = (fun r ↦
      if (decode q).val.eval 0 + (decode q).val.eval 1 = stmt.target then
        some (⟨stmt.poly, r, (decode q).val.eval r⟩ : Output F d) else none) <$>
      uniformSample F := rfl

omit [SampleableType F] in
/-- An honest message is accepted and the terminal evaluation claim is retained. -/
theorem result_honest (stmt : Input F d) (h : (stmt, ()) ∈ (relIn : Set (Input F d × Unit)))
    (r : F) : result stmt (transcript (encode stmt.poly) r) =
      some ⟨stmt.poly, r, stmt.poly.val.eval r⟩ := by
  change stmt.poly.val.eval 0 + stmt.poly.val.eval 1 = stmt.target at h
  simp [result, transcript, decode_encode, h]

/-- Every honest fresh-challenge output satisfies the output relation. -/
theorem sample_honest (stmt : Input F d)
    (h : (stmt, ()) ∈ (relIn : Set (Input F d × Unit))) :
    Pr[fun out ↦ ∃ y, out = some y ∧ (y, ()) ∈ (relOut : Set (Output F d × Unit)) |
      sample stmt (encode stmt.poly)] = 1 := by
  simp [sample, probEvent_map, Function.comp_def, result_honest stmt h, relOut]

/-- The verifier reads the message endpoints and forwards the true polynomial unchanged. -/
noncomputable def verifier : Verifier oSpec (Input F d) (Output F d) (spec F d) where
  verify := fun stmt tr ↦ OptionT.mk (pure (result stmt tr))

/-- Honest sender: send the fixed-length coefficients, remember the received challenge,
and output the resulting evaluation claim. -/
noncomputable def prover : Prover oSpec (Input F d) Unit (Output F d) Unit (spec F d) where
  PrvState := fun _ ↦ Input F d × F
  input := fun sw ↦ (sw.1, 0)
  sendMessage := by
    intro ⟨i, hi⟩
    have hz : i = (0 : Fin 2) := by
      fin_cases i
      · rfl
      · simp [spec] at hi
    subst i
    exact fun s ↦ pure (encode s.1.poly, s)
  receiveChallenge := by
    intro ⟨i, hi⟩
    have ho : i = (1 : Fin 2) := by
      fin_cases i
      · simp [spec] at hi
      · rfl
    subst i
    exact fun s ↦ pure (fun r ↦ (s.1, r))
  output := fun s ↦ pure (⟨s.1.poly, s.2, s.1.poly.val.eval s.2⟩, ())

/-- The actual two-message interactive reduction. -/
noncomputable def reduction : Reduction oSpec (Input F d) Unit (Output F d) Unit (spec F d) :=
  ⟨prover oSpec, verifier oSpec⟩

/-- A single fixed unit extractor, independent of every prover. -/
def extractor : Extractor.RoundByRound oSpec (Input F d) Unit Unit (spec F d) (fun _ ↦ Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ _ ↦ ()
  extractOut := fun _ _ _ ↦ ()

/-- Before the challenge the sent polynomial must equal the true one; after the challenge only
its evaluation is required. The endpoint check is retained in both post-message states. -/
def state : (k : Fin 3) → Input F d → (spec F d).Transcript k → Unit → Prop
  | ⟨0, _⟩, stmt, _, _ => stmt.poly.val.eval 0 + stmt.poly.val.eval 1 = stmt.target
  | ⟨1, _⟩, stmt, tr, _ =>
    let q : SumcheckMessage F d := decode (tr 0)
    (q.val.eval 0 + q.val.eval 1 = stmt.target) ∧ q.val = stmt.poly.val
  | ⟨2, _⟩, stmt, tr, _ =>
    let q : SumcheckMessage F d := decode (tr 0)
    let r : F := tr 1
    (q.val.eval 0 + q.val.eval 1 = stmt.target) ∧ stmt.poly.val.eval r = q.val.eval r

omit [SampleableType F] in
/-- Successful related output establishes the final state. -/
theorem state_of_result_some {stmt : Input F d} {tr : (spec F d).FullTranscript}
    {out : Output F d} {w : Unit} (h : result stmt tr = some out)
    (hr : (out, w) ∈ (relOut : Set (Output F d × Unit))) : state 2 stmt tr () := by
  unfold result at h
  dsimp only at h
  split at h
  · rename_i hc
    cases Option.some.inj h
    exact ⟨hc, hr⟩
  · contradiction

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

omit [DecidableEq F] [SampleableType F] in
set_option backward.isDefEq.respectTransparency false in
/-- The honest prover's execution consists of its fixed message and one challenge query. -/
theorem prover_run_to_round (stmt : Input F d) :
    (prover oSpec).runToRound (Fin.last 2) stmt () =
      (fun r ↦ (transcript (encode stmt.poly) r, (stmt, r))) <$>
        (liftM ((spec F d).getChallenge ⟨1, dir_one⟩) :
          OracleComp (oSpec + [(spec F d).Challenge]ₒ) F) := by
  change (prover oSpec).runToRound (Fin.succ (1 : Fin 2)) stmt () = _
  erw [Prover.runToRound_succ (1 : Fin 2),
    Prover.processRound_of_dir_eq_V_to_P (1 : Fin 2) dir_one,
    Prover.runToRound_succ (0 : Fin 2),
    Prover.processRound_of_dir_eq_P_to_V (0 : Fin 2) dir_zero,
    Prover.runToRound_zero_of_prover_first]
  simp [prover]
  congr 1
  funext r
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Perfect completeness of the actual ArkLib reduction, for every ambient oracle. -/
theorem perfect_completeness :
    (reduction (F := F) (d := d) oSpec).perfectCompleteness init impl relIn relOut := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt w h x hx
  cases w
  simp only [Reduction.run, reduction, Prover.run, Verifier.run, verifier] at hx
  rw [prover_run_to_round] at hx
  simp [prover] at hx
  obtain ⟨tr, out, w, hp, z, hz, heq⟩ := hx
  erw [support_bind, support_map] at hp
  obtain ⟨s, hp⟩ := Set.mem_iUnion.mp hp
  obtain ⟨hs, hp⟩ := Set.mem_iUnion.mp hp
  obtain ⟨r, _, rfl⟩ := hs
  change (tr, out, w) ∈ support (pure (transcript (encode stmt.poly) r,
    (⟨stmt.poly, r, stmt.poly.val.eval r⟩ : Output F d), ()) :
      OracleComp (oSpec + [(spec F d).Challenge]ₒ) _) at hp
  rw [support_pure, Set.mem_singleton_iff] at hp
  cases Prod.mk.inj hp with
  | intro ht ho =>
    subst tr
    cases Prod.mk.inj ho with
    | intro hout hw =>
      subst out
      subst w
      rw [result_honest stmt h] at hz
      simp at hz
      subst z
      refine ⟨_, heq.symm, ?_, rfl⟩
      rfl

/-- Knowledge states for this verifier and the fixed unit extractor. -/
noncomputable def knowledgeState :
    (verifier (F := F) (d := d) oSpec).KnowledgeStateFunction init impl relIn relOut
      (extractor oSpec) where
  toFun := state
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := by
    intro i hi stmt tr msg _ h
    fin_cases i
    · change ((decode msg).val.eval 0 + (decode msg).val.eval 1 = stmt.target) ∧
        (decode msg).val = stmt.poly.val at h
      change stmt.poly.val.eval 0 + stmt.poly.val.eval 1 = stmt.target
      simpa only [h.2] using h.1
    · simp [spec] at hi
  toFun_full := by
    intro stmt tr w h
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨out, hout, hr⟩ := h
    rw [OptionT.mem_support_iff] at hout
    simp only [Verifier.run, verifier, OptionT.run_mk, support_bind, Set.mem_iUnion] at hout
    obtain ⟨s, _, hout⟩ := hout
    change some out ∈ _root_.support
      ((simulateQ impl (pure (result stmt tr) : OracleComp oSpec _)).run' s) at hout
    rw [simulateQ_pure] at hout
    change some out ∈ _root_.support
      (Prod.fst <$> (pure (result stmt tr) : StateT σ ProbComp _).run s) at hout
    rw [StateT.run_pure] at hout
    simp only [map_pure, support_pure, Set.mem_singleton_iff] at hout
    exact state_of_result_some hout.symm hr

variable [Fintype F]

omit [SampleableType F] in
/-- Two distinct bounded-degree polynomials agree on at most `d` points. -/
private theorem card_sumcheck_agreement_le (p q : SumcheckMessage F d) (hne : q.val ≠ p.val) :
    (Finset.univ.filter fun r ↦ p.val.eval r = q.val.eval r).card ≤ d := by
  have hpoly : p.val - q.val ≠ 0 := sub_ne_zero.mpr hne.symm
  calc
    _ ≤ (p.val - q.val).roots.toFinset.card := by
      apply Finset.card_le_card
      intro r hr
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hpoly]
      change (p.val - q.val).eval r = 0
      rw [Polynomial.eval_sub, sub_eq_zero]
      exact (Finset.mem_filter.mp hr).2
    _ ≤ (p.val - q.val).roots.card := Multiset.toFinset_card_le _
    _ ≤ (p.val - q.val).natDegree := Polynomial.card_roots' _
    _ ≤ d := (Polynomial.natDegree_sub_le _ _).trans (max_le p.property q.property)


/-- Every fixed pre-challenge prefix has repair probability at most `d / |F|`, for the
same concrete extractor and knowledge states. -/
theorem worst_case_with :
    (verifier (F := F) (d := d) oSpec).rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut
      (fun _ ↦ Unit) (extractor oSpec) (knowledgeState oSpec init impl)
      (fun _ ↦ (d : ℝ≥0) / Fintype.card F) := by
  classical
  intro stmt ⟨i, hi⟩ tr
  fin_cases i
  · simp [spec] at hi
  · change (spec F d).Transcript (1 : Fin 3) at tr
    let q : SumcheckMessage F d := decode (tr ⟨0, by decide⟩)
    change Pr[fun r : F ↦ ∃ _ : Unit,
      ¬ (q.val.eval 0 + q.val.eval 1 = stmt.target ∧ q.val = stmt.poly.val) ∧
      (q.val.eval 0 + q.val.eval 1 = stmt.target ∧
        stmt.poly.val.eval r = q.val.eval r) | uniformSample F] ≤
        ↑((d : ℝ≥0) / Fintype.card F)
    simp only [exists_const]
    rw [ENNReal.coe_div (by exact_mod_cast Fintype.card_ne_zero (α := F)),
      ENNReal.coe_natCast, ENNReal.coe_natCast]
    by_cases hc : q.val.eval 0 + q.val.eval 1 = stmt.target
    · by_cases heq : q.val = stmt.poly.val
      · simp [heq]
      · simp only [hc, heq, and_false, not_false_eq_true, true_and]
        rw [probEvent_uniformSample]
        have h := card_sumcheck_agreement_le stmt.poly q heq
        gcongr
    · simp [hc]

/-- The concrete single-round verifier satisfies ArkLib's worst-case knowledge contract. -/
theorem worst_case :
    (verifier (F := F) (d := d) oSpec).rbrKnowledgeSoundnessWorstCase init impl relIn relOut
      (fun _ ↦ (d : ℝ≥0) / Fintype.card F) := by
  exact ⟨fun _ ↦ Unit, extractor oSpec, knowledgeState oSpec init impl,
    worst_case_with oSpec init impl⟩

/-- The operational adversarial-prefix game has the same bound and the same fixed extractor. -/
theorem knowledge_soundness_with :
    (verifier (F := F) (d := d) oSpec).rbrKnowledgeSoundnessWith init impl relIn relOut
      (fun _ ↦ Unit) (extractor oSpec) (knowledgeState oSpec init impl)
      (fun _ ↦ (d : ℝ≥0) / Fintype.card F) := by
  exact Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith
    init impl (worst_case_with oSpec init impl)

end
end SumcheckSecurity
end LeanerVM.Protocol
