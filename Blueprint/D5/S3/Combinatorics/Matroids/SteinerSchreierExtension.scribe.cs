using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerSchreierExtensionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerSchreierExtension";
    private static readonly LibraryNoteRef Extensions =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/falconefigulagalici2025veblenpoints");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triple labels realize prescribed component returns in a central extension.",
        H("Prescribed Returns in a Steiner Central Extension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("steiner-schreier-prescribed-returns"),
                DeclarationHandle.Create(Module + ".realizeSchreierReturns"),
                H("Prescribing the returns throughout each component"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Extensions),
                Blocks(
                    Paragraph(Text("Fix a finite centreless Steiner loop, two distinct nonidentity pivots, and a commutative additive group in which doubling is zero. The graph consists of the two pivot matchings. Assign an element of the group to each component other than the one through the identity.")),
                    Paragraph(Text("The extension adds one group label for the triple traversed at each step. Within a component, the disjoint product orbits keep the two directions of a matching edge from occurring twice in one circuit. Outside the identity component, different matching edges use different triples. One chosen label per component therefore realizes all prescribed returns.")),
                    Paragraph(Text("The first return to the fibre of any vertex shifts the fibre coordinate by the prescribed element. Conjugation by either matching step reverses the circuit and negates its return. Every group element equals its negative, so this gives the same return at all corners. The component through the identity has zero return. The extension is a Steiner loop, and its centre is exactly the fibre over the identity."))),
                DescribeRole.Theorem))));
}
