# Lean agent instructions for Psi Zoo proofs

- This is the independent Lean 4 + Mathlib companion repo. Do not copy npm files into it.
- Target documented mathematical claims connected to Psi Zoo, not proofs of the UI.
- Begin with short, independently compilable lemmas, not the full matrix-unity theorem.
- For every claimed theorem, run `lake build` and show actual checking output.
- No `sorry`, `admit`, `unsafe`, custom axioms or `native_decide` shortcuts presented as full proofs.
- Explain each Lean tactic and the corresponding mathematics to the user.
- Avoid changing Lean toolchain or Mathlib version without approval.
- Measurement: an exact coordinate projection and a Gaussian mask are different objects.
- Recommended order: Lean basics -> finite coordinate projection -> Cayley unitarity -> Bloch.
- A completed result may be cross-linked in the app's lab notebook after it compiles.
- Before edits: state the theorem in ordinary mathematical language.
- After edits: show the theorem statement, code path, build result, remaining gaps.
- Do not commit or push without explicit approval.
