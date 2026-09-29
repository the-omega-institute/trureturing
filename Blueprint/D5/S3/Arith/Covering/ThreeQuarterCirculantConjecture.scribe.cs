using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class ThreeQuarterCirculantConjectureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/dalfofiolreyes2026threequarters");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The specified lattice and three-sector distance work for every positive k; "
            + "the two steps give degree two from k equal to two onward.",
        H("The Three-Quarter Circulant Construction"),
        Blocks(
            Entry("SectorReach", "The source's three sectors", DescribeRole.Definition,
                "A residue is reached within radius r exactly when nonnegative m,n with "
                    + "m+n at most r represent it by m*a+n*b, -m*a+n*b, or m*a-n*b. "
                    + "The three alternatives may overlap.", true),
            Entry("order", "The proposed order", DescribeRole.Definition,
                "For positive k, (k-1)(k+4)+(k+2) is the source order k squared "
                    + "plus four k minus two."),
            Entry("stepB", "The second step", DescribeRole.Definition,
                "The second residue is the negative of k+4, written -(k+4), "
                    + "in ZMod of the proposed order."),
            Entry("sector", "The proposed sector relation", DescribeRole.Definition,
                "This specializes the source's three-sector reachability to a=1 and b=-(k+4)."),
            Entry("latticeFirst", "First source lattice column", DescribeRole.Definition,
                "The integer vector is (k+2,1-k).", true),
            Entry("latticeSecond", "Second source lattice column", DescribeRole.Definition,
                "The integer vector is (2,k).", true),
            Entry("integerKernel", "The step congruence kernel", DescribeRole.Definition,
                "This is the kernel of (x,y) mapped to x-(k+4)y modulo the proposed order."),
            Entry("generatedLattice", "The displayed integer lattice", DescribeRole.Definition,
                "The set contains every integral linear combination of the two source columns."),
            Entry("kernel_eq_generated", "Exact lattice and determinant", DescribeRole.Theorem,
                "For every k at least one, the order equals k squared plus four k minus two, "
                    + "the determinant of the displayed columns equals that order, and their "
                    + "integer span is exactly the congruence kernel. The proof gives explicit "
                    + "integer coefficients for every kernel point."),
            Entry("sector_cover", "Radius-k coverage", DescribeRole.Theorem,
                "For every k at least one and every residue, a quotient and remainder by k+4 "
                    + "select a witness in one of the source's three sectors with m+n at most k."),
            Entry("sector_radius_lower", "The exact-radius witness", DescribeRole.Theorem,
                "For every k at least one, the residue k has no representation in the three "
                    + "source sectors with m+n at most k-1."),
            Entry("generator_regular_for_k_ge_two", "Nondegenerate generator pair",
                DescribeRole.Theorem,
                "For every k at least two, both step residues are nonzero and distinct; "
                    + "the set of outgoing neighbors from each vertex has cardinality two."))));

    private static DocumentBlock Entry(string name, string title, DescribeRole role,
        string prose, bool fromLiterature = false) => Describe.Lean(
        DescribeId.Create("three-quarter-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        fromLiterature ? AssessedProvenance.FromLiterature(Source)
                       : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role);
}
