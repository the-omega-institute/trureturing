using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class BinaryCodeCoordinateClassDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCodeCoordinateClass";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An additive binary code containing the all-one word has uniform evaluation classes when every nonconstant word has half the code length.",
        H("All coordinate evaluation classes have the same size"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coordinate-class-cardinality"),
                DeclarationHandle.Create(Module + ".card_mul_coordinateClass_card"),
                H("All coordinate evaluation classes have the same size"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let K be an additive binary code of length 2n, containing the all-one word and with weight n for every word other than zero and one. The size of each evaluation class times the size of K is 4n. Translation by the all-one word pairs both slices of the code. In the slice vanishing at a fixed coordinate, each coordinate outside its evaluation class takes the value one on half the slice. Counting these incidences by codewords and by coordinates determines the size of the class."))),
                DescribeRole.Theorem)),
        []));
}
