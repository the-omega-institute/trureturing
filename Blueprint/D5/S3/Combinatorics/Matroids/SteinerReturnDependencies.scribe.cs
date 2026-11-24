using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerReturnDependenciesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerReturnDependencies";
    private static readonly LibraryNoteRef Extensions =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/falconefigulagalici2025veblenpoints");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A linear condition for simultaneous returns in a central extension of a Steiner loop.",
        H("Compatibility of Steiner Circuit Returns"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("steiner-simultaneous-circuit-returns"),
                DeclarationHandle.Create(Module + ".realizesExactlyCompatibleReturns"),
                H("Realizing compatible circuit returns"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Extensions),
                Blocks(
                    Paragraph(Text("Fix a Steiner loop with trivial centre, an additive group of exponent at most two, and a family of requests. Each request names a pair of matching pivots, an alternating component via one representative, and a desired shift in the fibre. At a periodic representative the first quotient return occurs after the minimal period of the two-step map. All representatives are periodic in a finite loop. At an aperiodic representative the minimal period convention gives zero rounds and a zero row, so the only compatible shift is zero.")),
                    Paragraph(Text("The row of a request counts each triple in those rounds modulo two. Steps involving the identity or a repeated point have zero label and contribute nothing. One assignment of labels realizes all requests exactly when every finitely supported binary combination of zero total row also has zero total desired shift.")),
                    Paragraph(Text("Evaluating the row at the triple labels gives the shift by iterating the extension multiplication. This proves necessity. For sufficiency, the relation condition defines a linear map on the span of the rows. Extend the map to the entire free vector space and read the labels on its basis. The resulting loop has centre equal to the identity fibre. Reversing the circuit along a matching step negates the shift, which preserves its value in a group of exponent at most two, so all starts in the requested component have the prescribed return."))),
                DescribeRole.Theorem))));
}
