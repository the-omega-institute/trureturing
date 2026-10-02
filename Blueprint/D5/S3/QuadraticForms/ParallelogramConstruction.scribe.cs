using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class ParallelogramConstructionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/tauceti2026canonicalheight");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integer quadratic map from the parallelogram law.",
        H("An integer quadratic map from the parallelogram law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parallelogram-quadratic-map"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/ParallelogramConstruction.ofParallelogram"),
                H("An integer quadratic map from the parallelogram law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For additive commutative groups M and N with injective doubling on N, a function f satisfying f(x + y) + f(x - y) = 2f(x) + 2f(y) determines an integer quadratic map with underlying function f and companion polarization f(x + y) - f(x) - f(y).")),
                    Paragraph(Text("The construction derives the value at zero, evenness, integer quadratic scaling and the three-variable polarization identity. The latter gives biadditivity. Injective doubling permits cancellation; without it a constant nonzero function on a group of exponent two can satisfy the parallelogram law and fail the required zero identity."))),
                DescribeRole.Definition))));
}
