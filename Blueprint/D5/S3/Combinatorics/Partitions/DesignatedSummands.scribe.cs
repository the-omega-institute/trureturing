using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class DesignatedSummandsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/DesignatedSummands.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/yaqubi2026designatedsummands");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficient of the Euler quotient counts ordered tuples with an actual designated occurrence.",
        H("Ordered tuples with designated summands"),
        Blocks(
            Paragraph(Text("For each distinct part size of multiplicity m, a marked partition carries a choice in Fin m. An ordered tuple uses a degree assignment on the component positions with total degree n. A component of degree zero is the empty partition. The local multiplicity series is 1 plus the sum of m times q to the power im for positive m, where i is the part size. Multiplying its Euler denominators gives the factor in degree 6i. Taking the product over all part sizes yields the quotient F, and coefficient convolution gives the ordered tuple count.")),
            Node("euler", "Dilate the pentagonal series by a positive natural degree.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("etaUnit", "The corresponding unit, with inverse at constant coefficient one.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("tendsto_expand_discrete", "Dilation is continuous for coefficientwise convergence over a discrete ring.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("euler_tendsto", "The finite Euler products with exponents d(i+1) converge to the dilated series.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("euler_const", "The constant coefficient of a dilated Euler product is one.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("map_eta", "A ring homomorphism on the coefficients preserves the dilated Euler unit.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("expand_eta", "Dilating an Euler unit again multiplies its dilation index.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("MarkedPartition", "A partition of n together with one choice of actual occurrence for each part size present.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("MarkedTuple", "An ordered tuple of k marked partitions with total size n. Each position may have degree zero.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("markedCount", "The cardinality of the type of ordered marked tuples.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("markedPartitionFintype", "The type of markings of partitions of a fixed size is finite.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("markedTupleFintype", "There are finitely many ordered marked tuples at fixed component count and total size.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("F", "The Euler quotient f6 divided by f1 f2 f3 as a formal power series.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("F_const", "The Euler quotient has constant coefficient one.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("marked_count_coeff", "For all natural k and n, the integer cast of the tuple count equals the coefficient of degree n in F raised to k.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source))),
        []));

    private static DocumentBlock Node(
        string declaration, string narrative, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("designatedsummands-" + declaration.ToLowerInvariant().Replace('_', '-').Replace('₀', '0')),
            DeclarationHandle.Create(Prefix + declaration), H(declaration),
            StatementSource.WithoutFormula(), provenance, Blocks(Paragraph(Text(narrative))), role);
}
