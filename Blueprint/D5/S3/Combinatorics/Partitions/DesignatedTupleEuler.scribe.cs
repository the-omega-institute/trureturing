using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class DesignatedTupleEulerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/DesignatedTupleEuler.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual ordered designated partitions have the integral Euler quotient coefficients.",
        H("Designated partition tuples"), Blocks(
            Paragraph(Text("The source is Section 2 and Definition 2.1 of arXiv:2611.05623v1. A partition with designated summands chooses exactly one occurrence in each nonempty block of equal positive parts. A block of multiplicity m therefore has exactly m choices. Components are ordered, and every component may be empty.")),
            Node("marks", "Marks", "For a partition p, Marks p is the dependent product of Fin(count(s,p)) over the distinct occurring sizes s. Each element records one occurrence in each block.", DescribeRole.Definition),
            Node("designated", "Designated", "Designated N is the dependent sum of the underlying partitions of N and their independent marks. It is finite before any cardinality is taken.", DescribeRole.Definition),
            Node("tuple", "Tuple", "Tuple k N is the dependent sum over all functions e from Fin k to the natural numbers with sum N of the ordered dependent product of Designated(e(i)). Zero sizes are included. The existing energy-allocation antidiagonal equivalence proves finiteness of the size allocations.", DescribeRole.Definition),
            Node("count", "count", "count k N is Nat.card(Tuple k N), the independently defined count of actual objects; it is not defined as a coefficient.", DescribeRole.Definition),
            Node("series", "markedSeries", "The integer series is Mathlib Nat.Partition.genFun with local weight m for multiplicity m. Finite dependent-sum and dependent-product cardinalities identify its coefficients with the designated-partition count.", DescribeRole.Definition),
            Node("euler", "euler", "For every positive m, euler m is the actual integral Euler product over positive t of (1-X^(mt)), represented by the m-dilation of Mathlib's pentagonalSeries. Its constant coefficient is one.", DescribeRole.Definition),
            Node("quotient", "quotient", "quotient is euler 6 times PowerSeries.invOfUnit(euler 1 * euler 2 * euler 3, 1), the constant-term-one inverse in the integer power-series ring. No rational-to-residue-ring map is used.", DescribeRole.Definition),
            Node("bridge", "count_six_eq_coeff", "For every natural N, including zero, the integer cast of count 6 N equals coefficient N of quotient^6. The local marked factor times (1-X^t)(1-X^(2t))(1-X^(3t)) equals 1-X^(6t). Actual convergent formal products and finite coefficient convolution give the all-degree statement.", DescribeRole.Theorem),
            Paragraph(Text("This bridge supplies the source-faithful meaning of A6. The universal congruence modulo 243 on degrees 12n+10 and the existence of a degree in that progression failing divisibility by 729 are separate obligations and are not asserted here. Mathlib's weighted partition product and pentagonal product are used directly; this application carries no claim of a new external problem resolution."))
        ), []));

    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("designated-tuple-euler-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(declaration),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
