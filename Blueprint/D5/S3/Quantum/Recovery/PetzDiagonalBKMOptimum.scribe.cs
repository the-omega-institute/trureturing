using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzDiagonalBKMOptimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp full-fibre quotient with the diagonal Umegaki Hessian.",
        H("Exact diagonal BKM optimum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petz-diagonal-bkm-maximum"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PetzDiagonalBKMOptimum.diagonal_bkm_maximum"),
                H("The actual logarithmic derivative in the quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a diagonal base ρ with positive entries β in the given retained " +
                        "and flag coordinates. The Hessian is Re Tr[Z D log(ρ)[Z]]. In the " +
                        "resolvent integral each entry contributes its squared modulus times " +
                        "the reciprocal logarithmic mean of the two diagonal entries. The " +
                        "coincident-value branch has coefficient 1/β.")),
                    Paragraph(Text(
                        "The logarithmic means are positive and bounded by the arithmetic " +
                        "means. Form m as the product over the sum of the two within-flag " +
                        "logarithmic means. For C,f,g > 0 and the same two nonnegative margins " +
                        "with positive sum, the quotient with this Hessian attains " +
                        "16m+(f+g)²/C on the full Hermitian zero-marginal fibre.")),
                    Paragraph(Text(
                        "The unique tangent has real within-flag coherences −4Cm/(f+g) and " +
                        "4Cm/(f+g), with all other entries zero."))),
                DescribeRole.Theorem))));
}
