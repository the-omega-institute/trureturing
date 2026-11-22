using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ReflectingHeatSaddleBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The boundary value of the reflecting heat saddle potential controls the real-axis multiplier.",
        H("Reflecting heat saddle on the real boundary"),
        Blocks(Describe.Lean(
            DescribeId.Create("reflecting-heat-saddle-real-cancellation"),
            DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatSaddleBoundary.saddle_real_cancellation"),
            H("Real-axis cancellation at the saddle"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The imaginary potential determines a holomorphic expression in the saddle square-root variable. Dominated convergence takes its real part to the boundary, including logarithmic singularities inside the integration domain. The angular Green function is the logarithm of the exterior Joukowski radius by the quadratic Mahler measure formula. Comparing it with the boundary value gives the cancellation inequality."))),
            DescribeRole.Theorem))));
}
