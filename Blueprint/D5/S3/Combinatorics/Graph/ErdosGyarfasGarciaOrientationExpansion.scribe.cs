using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ErdosGyarfasGarciaOrientationExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationExpansion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cyclic sequence of internally simple, mutually disjoint path blocks gives a "
            + "simple cycle. Its length counts every block vertex once, including the "
            + "attachment edge following each block.",
        H("Simple cycles from disjoint path blocks"),
        Blocks(Describe.Lean(
            DescribeId.Create("garcia-cycle-expansion"),
            DeclarationHandle.Create(Prefix + "cycle_of_disjoint_blocks"),
            H("Cyclic gluing of simple paths"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let G be a simple graph and let b_i, indexed by Fin(n+1), be nonempty "
                    + "lists of vertices. CyclicDisjointPaths(G,b) means: every b_i has no "
                    + "repeated vertex and is a chain for G.Adj; lists at distinct indices "
                    + "are disjoint; the last vertex of b_i is adjacent to the first vertex "
                    + "of b_(finRotate(n+1)(i)). Assume the total number of vertices in "
                    + "the lists is at least three. There exist a vertex v and a closed "
                    + "Mathlib walk p at v satisfying Walk.IsCycle, with length equal to "
                    + "that total. The paths contribute one fewer edge than their vertex "
                    + "counts, and the cyclic attachment edges contribute one per block.")),
                Paragraph(Text(
                    "Flatten the lists. Mathlib's list-chain and disjointness lemmas "
                        + "give an adjacent vertex sequence without repetitions. Build "
                        + "its walk with Walk.ofSupport and append the closing edge. "
                        + "The support with its last vertex removed is precisely the "
                        + "flattened list. Mathlib's permutation between this list and "
                        + "the tail support gives a simple tail path, and the length "
                        + "bound makes the closed walk a simple cycle."))),
            DescribeRole.Theorem)),
        []));

}
