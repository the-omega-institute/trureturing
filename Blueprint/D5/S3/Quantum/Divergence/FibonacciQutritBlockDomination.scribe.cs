using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class FibonacciQutritBlockDominationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal relocation of the Fibonacci null state strictly improves a full-rank block comparison.",
        H("Fibonacci qutrit block domination"),
        Blocks(Describe.Lean(
            DescribeId.Create("strict-block-domination"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/FibonacciQutritBlockDomination.strict_block_domination"),
            H("Strict domination after positive reference replacement"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/mathlib2026schurcomplement")),
            Blocks(Paragraph(Text(
                "Let C = Cₚ ⊕ λ with Cₚ positive definite on the qubit and Cₚ ≥ λI. "
                + "Let A have diagonal blocks F and a, and coupling column h with lower adjoint h*. "
                + "Assume Re Tr F + a = 1, 4C/3 ≤ A ≤ 7C/3, and that ρ is positive semidefinite "
                + "with trace one on the qutrit. Set b = Re Tr Cₚ, c = b + λ and assume "
                + "0 < λ < 1/500, c ≥ 11/19 and e ≥ c/3.")),
                Paragraph(Text(
                    "Write τ = Cₚ/b, F′ = F + aτ and C′ = cτ. The gain of the new actual pair "
                    + "A′ = F′ ⊕ 0 and B′ = C′ ⊕ e over A and C + eρ is at least "
                    + "(4/3)λ log(1 + e/λ) − (12/55)λ(c/b)log(c/λ) "
                    + "− a[log(a/(λ·4/3)) − 1] − log(c/b) + Re Tr[(aτ)* (aτ)]/2. "
                    + "This lower bound is strictly positive.")),
                Paragraph(Text(
                    "The reference logarithm is block diagonal, so pinching A leaves its reference "
                    + "pairing unchanged. Apply the null-reference increment bound to the original "
                    + "pair, the integral estimate to the change in trace entropy, and the quadratic "
                    + "replacement bound to the pinched pair. Block logarithms give the actual "
                    + "divergence of the relocated pair as D(F′∥C′). The scalar margin uses "
                    + "c/b ≤ 3/2, c/λ > 64, log 3 < 2 log 2 and log 2 > 2/3."))),
            DescribeRole.Theorem))));
}
