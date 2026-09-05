using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class EdgeTranspositionGenerationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Zeros/EdgeTranspositionGeneration.connected_edge_transpositions_generate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The swaps across the edges of a finite connected graph generate every permutation "
            + "of its vertices.",
        H("Edge Transposition Generation"),
        Blocks(Describe.Lean(
            DescribeId.Create("connected-edge-transpositions-generate"),
            DeclarationHandle.Create(Declaration),
            H("Connected edge transpositions generate the full symmetric group"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a simple graph G, edgeTranspositions(G) is exactly the set of swaps "
                        + "whose two endpoints are adjacent. Graph adjacency supplies the "
                        + "distinct-endpoint condition required of every transposition.")),
                Paragraph(Text(
                    "Reachability is unfolded as the reflexive transitive closure of adjacency. "
                        + "Induction along that closure constructs a swap of the two path "
                        + "endpoints inside the generated subgroup, so connectedness makes the "
                        + "subgroup action pretransitive.")),
                Paragraph(Text(
                    "The final equality is the direct specialization of Mathlib's "
                        + "closure_of_isSwap_of_isPretransitive. Applying the theorem to the "
                        + "induced graph on any connected component gives the componentwise "
                        + "form. No concrete monodromy graph is asserted to be connected."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula vertices = F.Id("V");
        Formula graph = F.Id("G");
        Formula graphType = Call("SimpleGraph", vertices);
        Formula permutations = Call("Perm", vertices);
        Formula generators = Call("edgeTranspositions", graph);

        return Disp(Seq(
            Forall, Sp, vertices, Comma, Sp,
            graph, Colon, Sp, graphType, Comma, Sp,
            Call("Finite", vertices), Sp, Land, Sp,
            Call("Connected", graph), Sp, Rightarrow, Sp,
            Call("closure", generators), Sp, Eq, Sp,
            Call("topSubgroup", permutations), Dot));
    }
}
