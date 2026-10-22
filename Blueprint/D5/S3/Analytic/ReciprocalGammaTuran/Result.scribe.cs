using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReciprocalGammaTuran;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refutation of reciprocal Gamma coefficient positivity.",
        H("The coefficient positivity clause is false"), Blocks(
            Describe.Lean(DescribeId.Create("reciprocal-gamma-coefficient-refutation"),
                DeclarationHandle.Create("D5/S3/Analytic/ReciprocalGammaTuran/Result.result"),
                H("An admissible sequence with a negative coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constant unit sequence is nontrivial, nonnegative, log concave and has no internal zeros. The interior existence theorem supplies admissible parameters with a strictly negative second coefficient. Universal positivity at degree two would give the opposite strict inequality. This refutes the coefficient assertion while leaving the assertion concerning log concavity in the positive parameter range untouched."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kalmykov-karp-2012-reciprocal-gamma-coefficient-positivity"),
                    ResolutionKind.Refuted)))));
}
