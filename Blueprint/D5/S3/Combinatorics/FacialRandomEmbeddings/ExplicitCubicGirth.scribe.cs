using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FacialRandomEmbeddings;

internal sealed class ExplicitCubicGirthDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/FacialRandomEmbeddings/ExplicitCubicGirth";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three explicit residue-ring involutions give finite matching-colored cubic graphs of prescribed girth.",
        H("Explicit Cubic Graphs of Prescribed Girth"),
        Blocks(Describe.Lean(DescribeId.Create("explicit-cubic-girth"),
            DeclarationHandle.Create(Owner + ".result"),
            H("An explicit cubic graph for every girth threshold"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For each integer g at least two, act on pairs over the residue ring modulo 5^g+1 by three involutions, and use their tagged permutation orbit as the vertex set. The three moves give the matching neighbors of the actual simple graph.")),
                Paragraph(Text("An integral separated-cone estimate keeps the second coordinate of every nonempty reduced word of length at most g strictly nonzero modulo 5^g+1. A short graph cycle would give a forbidden reduced word. The tag gives a bipartition; alternating two colors shows that no edge is a bridge. Two columns determine the permutation, and their determinant determines the tag, giving at most (5^g+1)^4 vertices.")),
                Paragraph(Text("The result formalizes this particular explicit family and its marked matching coordinates, not a new existence theorem or an optimal bound. Biggs, Constructions for Cubic Graphs with Large Girth (1998, DOI 10.37236/1386), surveys the established Cayley method and sharper constructions. No signed-density claim is made here."))),
            DescribeRole.Theorem))));
}
