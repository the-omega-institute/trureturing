using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class LeeSquareCompressionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/bajnokbeatty2024cayleydiameteroriginal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual index dichotomy used by the abstract finite-group maximum.",
        H("A uniform upper bound for relation lattices"),
        Blocks(Describe.Lean(
            DescribeId.Create("lee-lattice-upper-bound"),
            DeclarationHandle.Create("D5/S3/FiniteGroups/LeeSquareCompression.lattice_upper_bound"),
            H("The common divisor controls the high-index branch"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("Let K be any integer submodule of the integral plane, and let c,s be integers with c ≥ 2 and s ≥ 3. Suppose both coordinates of every vector in K are divisible by c, and every integral vector z has a representative r with |r₀|+|r₁| ≤ s and z−r in K. Then the actual additive-subgroup index I of K satisfies I ≤ 2s², or c is odd, c divides 2s+1, and 2I ≤ (2s+1)²−c². The statement assumes neither a product normal form nor a prescribed generating pair.")),
                Paragraph(Text("Above the baseline, square compression forces the remainder of 2s+1 modulo c to vanish. Thus the cofactor m=(2s+1)/c and c are odd. The scaled-index identity gives I=k c² for a natural k, and compression gives 2k ≤ m². Since m is odd, integrality sharpens this to 2k ≤ m²−1; multiplying by c² yields the square correction. BajnokBeattyFiniteUpper.finite_noncyclic_upper_dichotomy consumes this theorem for the actual coefficient kernel, using Smith normal form to obtain its common coordinate divisor and a quotient equivalence to identify I with the group cardinality. The source comparison is Bajnok–Beatty arXiv:2406.04045v1; no current literature novelty or priority is claimed."))),
            DescribeRole.Theorem))));
}
