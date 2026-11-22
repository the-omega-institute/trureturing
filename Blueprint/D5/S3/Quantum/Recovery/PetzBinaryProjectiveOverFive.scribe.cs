using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzBinaryProjectiveOverFiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary Petz recovery after computational-basis measurement exceeds coefficient five on faithful qubit states.",
        H("Ordinary Petz recovery after binary projective measurement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-projective-petz-five-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The coefficient-five estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix the computational-basis measurement on a qubit. Its completely positive "
                    + "trace-preserving action retains exactly the diagonal of the input. For two "
                    + "positive-definite input states, write Δ for the finite trace-log Umegaki "
                    + "relative entropy before measurement minus the same relative entropy after "
                    + "measurement. The claim bounds the squared full trace norm of the ordinary "
                    + "Petz recovery error by 5Δ whenever Δ is positive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-projective-petz-five-family"),
                DeclarationHandle.Create(Prefix + "family_bounds"),
                H("Uniform estimates for the faithful family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take 0 < x ≤ 1/100. The input has diagonal (1/10, 9/10) and both "
                        + "off-diagonal entries −x/3. The reference has eigenvalues 1−x⁴ and x⁴ "
                        + "and eigenvectors proportional to (1, x³) and (−x³, 1), respectively. "
                        + "Both inputs and both measured outputs are positive definite.")),
                    Paragraph(Text(
                        "Let q₀ and q₁ be the measured probabilities of the reference and "
                        + "let S be its positive square root. The reference output has full "
                        + "support, so the completed Petz channel acts on every matrix X by "
                        + "S diag(X₀₀/q₀, X₁₁/q₁) S. The diagonal projection is its own "
                        + "trace adjoint, and the recovery maps the measured reference back "
                        + "to the reference.")),
                    Paragraph(Text(
                        "The loss satisfies x²/5 < Δ < (12141/10000)x². Expanding the input "
                        + "and output trace-log expressions in their spectral bases cancels "
                        + "the dominant reference logarithm. The remaining terms are bounded "
                        + "using the binary entropy derivative and elementary logarithm "
                        + "inequalities. The squared full trace norm of the recovery error "
                        + "is greater than (152/25)x². The error is traceless and real "
                        + "symmetric, so its squared norm is four times the sum of the "
                        + "squares of its first diagonal and off-diagonal entries."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-projective-petz-five-counterexamples"),
                DeclarationHandle.Create(Prefix + "counterexamples"),
                H("Rational sequence with vanishing loss and commutator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Set x = 1/(n + 100) for natural n. Both matrices have rational entries. "
                    + "Every pair has positive loss and squared recovery error strictly "
                    + "above five times that loss. The loss tends to zero by its quadratic "
                    + "upper bound. The maximum operator norm of the two measurement "
                    + "projector commutators tends to zero by its cubic upper bound."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-projective-petz-five-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A rational counterexample"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Set x = 1/100, so the reference eigenvalue x⁴ is 1/100000000 and the "
                    + "rotation parameter x³ is 1/1000000. Both state matrices have rational "
                    + "entries. The loss is positive, and five times its upper bound is "
                    + "strictly below the lower bound on the squared recovery error."))),
                DescribeRole.Theorem))));
}
