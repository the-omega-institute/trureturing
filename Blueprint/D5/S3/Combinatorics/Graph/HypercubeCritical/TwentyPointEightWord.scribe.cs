using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class TwentyPointEightWordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive eight-cycle words", H("Positive eight-cycle words"),
        Blocks(
            Paragraph(Text(
                "A simple eight-cycle in a balanced induced cube support has even multiplicity in every direction, since it returns to its starting vertex. "
                    + "Two occurrences of the same direction at cyclic distance one would repeat a vertex. Distance two would give a selected coordinate square. "
                    + "With both distances forbidden and multiplicities even, every used direction occurs twice.")),
            Paragraph(Text(
                "Label the first three directions a, b and c. The two remaining positions use a common fourth direction d, since each actual direction has multiplicity two. "
                    + "A finite kernel check of these abstract labels yields seven patterns. The original Huang direction operators square to the identity and anticommute for unequal directions. "
                    + "Four patterns reduce to the negative identity, while the switching signs telescope to positive one on the actual cycle.")),
            Paragraph(Text(
                "The three remaining words are abcdabcd, abcadcbd and abcdbadc. Reading the final five directions in reverse gives dcbad, dbcda and cdabd."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagonSigns")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth"))
        ]));
}
