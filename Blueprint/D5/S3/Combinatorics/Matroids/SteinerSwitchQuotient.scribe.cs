using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerSwitchQuotientDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerSwitchQuotient";
    private static readonly LibraryNoteRef Extensions =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/falconefigulagalici2025veblenpoints");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A central return translation determines the lifted components over a quotient component.",
        H("Alternating Components over the Central Quotient of a Steiner Loop"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("central-quotient-component-lifts"),
                DeclarationHandle.Create(Module + ".point_deleted_component_lifts"),
                H("The component size and multiplicity over the central quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Extensions),
                Blocks(
                    Paragraph(Text("Suppose the deleted point and the retained pivot of a finite complete Steiner triple system have distinct nonidentity classes in the quotient by the centre. The theorem constructs the quotient map by central orbits and descends the two matching translations. Their union on the quotient is a graph with the two projected partners at each vertex.")),
                    Paragraph(Text("Over a quotient component C, the least period of the product of the two steps is half its size. After one such period upstairs, the lifted point returns to its fibre. This return is multiplication by a central element. Put d equal to one for the identity element and two otherwise. The lifted components have size d times the size of C, and their number times d equals the size of the centre.")),
                    Paragraph(Text("The two parity classes of an alternating walk are disjoint forward orbits of the two-step map. Equivariance reduces repeated returns to powers of a single central element. Each base fibre has the size of the centre. Lifting paths and translating by the centre show that all components over C have the same size, so their total vertex count gives the multiplicity."))),
                DescribeRole.Theorem))));
}
