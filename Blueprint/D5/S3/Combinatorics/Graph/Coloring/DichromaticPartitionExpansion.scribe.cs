using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Coloring;

internal sealed class DichromaticPartitionExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/GraphInvariants/crew2026dichromatic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Acyclic colourings of a finite digraph give a falling-factorial expansion.",
        H("Dichromatic polynomial and vertex partitions"),
        Blocks(
            Paragraph(Text("Crew, Keller, Kuehr, Lin, Monroy Rodríguez and Williams define the "
                + "dichromatic polynomial by acyclic colourings in Properties of the Dichromatic "
                + "Polynomial, Section 2. Section 8.1, Conjecture 2 concerns its ratio to the "
                + "power of the palette size. https://arxiv.org/html/2611.13273v1")),
            Node("acyclic-on", "Acyclic induced digraphs", "AcyclicOn",
                "An induced digraph has no injectively indexed cyclic sequence following its arcs. "
                + "Sequences of lengths one and two detect loops and digons.", DescribeRole.Definition),
            Node("colouring", "Acyclic colour maps", "AcyclicColoring",
                "Each inverse image of a palette name induces an acyclic digraph. Unused names have empty inverse image.",
                DescribeRole.Definition),
            Node("partition", "Unlabelled acyclic blocks", "IsAcyclic",
                "Every block of a finite partition of all the vertices induces an acyclic digraph.", DescribeRole.Definition),
            Node("weight", "Real partition weights", "partitionWeight",
                "The weight of a partition with k blocks on n vertices is the falling factorial "
                + "of x of length k divided by the nth power of x.", DescribeRole.Definition),
            Node("polynomial", "Falling-factorial expansion", "dichromaticPolynomial",
                "Sum the real falling-factorial polynomial of degree k over acyclic partitions with k blocks.",
                DescribeRole.Definition),
            Node("palette-count", "Integer evaluations count colour maps", "eval_dichromaticPolynomial_nat",
                "For every natural palette size q, the evaluation is the number of acyclic maps into Fin q. "
                + "A colour map yields its nonempty fibres and an injection from these fibres to the palette. "
                + "An acyclic partition and such an injection recover the map. Counting the injections gives "
                + "one falling factorial for each partition.", DescribeRole.Theorem),
            Node("unique-polynomial", "Uniqueness from natural palette sizes", "eq_dichromaticPolynomial_of_eval_nat",
                "Agreement at every natural palette size gives infinitely many real evaluation points. "
                + "A polynomial satisfying the colouring count is therefore the dichromatic polynomial.",
                DescribeRole.Theorem),
            Node("ratio", "The normalized polynomial as a sum over partitions", "dichromaticPolynomial_div_eq_sum_weight",
                "The ratio of the dichromatic polynomial to the nth power of x is the sum of the weights "
                + "of the acyclic partitions.", DescribeRole.Theorem),
            Node("refinement", "Refining acyclic blocks", "isAcyclic_of_le",
                "Each block of a finer partition is contained in a block of the coarser partition. "
                + "Any cycle in a finer block would be a cycle in its containing block.", DescribeRole.Theorem),
            Node("acyclic-polynomial", "The entire digraph is acyclic", "dichromaticPolynomial_eq_pow_of_acyclic",
                "All maps into a palette of size q are acyclic. Their number is q to the power n, "
                + "which determines the polynomial.", DescribeRole.Theorem),
            Node("loop-polynomial", "A loop forces the zero polynomial", "dichromaticPolynomial_eq_zero_of_loop",
                "The fibre containing a loop vertex contains that loop at every palette size.", DescribeRole.Theorem),
            Node("small-order", "Orders zero and one", "dichromaticPolynomial_small",
                "At orders zero and one the polynomial is the nth power of the variable for an acyclic "
                + "digraph, and zero if there is a loop. Injectivity bounds the length of a cycle by n.",
                DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
