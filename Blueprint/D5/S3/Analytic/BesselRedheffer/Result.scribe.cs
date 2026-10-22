using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BesselRedheffer;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counterexamples to the normalized Bessel Redheffer lower bound.",
        H("A family of strict counterexamples"), Blocks(
            Describe.Lean(DescribeId.Create("bessel-redheffer-failure-family"),
                DeclarationHandle.Create("D5/S3/Analytic/BesselRedheffer/Result.failure_family"),
                H("Every order at least thirty"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each real order nu at least 30, there is a positive x below the first positive zero of the normalized Bessel function such that the proposed lower bound is strictly greater than the ratio. The first-zero theorem supplies positivity and the energy upper bound. The local comparison supplies a positive interval of strict violations, from which half the interval radius is chosen."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bessel-redheffer-refutation"),
                DeclarationHandle.Create("D5/S3/Analytic/BesselRedheffer/Result.result"),
                H("The universal lower bound is false"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pinned claim quantifies over every real order greater than -1 and every real x of absolute value below the first positive zero. Specializing the counterexample family to order 30 gives an admissible positive x and contradicts the claimed inequality. The series definition, the first zero defined as an infimum, and the real-power exponent are those of the pinned claim."))),
                DescribeRole.Theorem))));
}
