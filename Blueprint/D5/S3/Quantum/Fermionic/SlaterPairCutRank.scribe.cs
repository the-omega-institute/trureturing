using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class SlaterPairCutRankDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/SlaterPairCutRank.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered Slater marginal spectra from paired orbitals",
        H("Ordered Slater marginal spectra from paired orbitals"),
        Blocks(
            Entry("alternationMatrix", "The binary alternation matrix",
                "Given two indexed families of ordered endpoint pairs on a linearly ordered site type, the matrix has one in the binary field exactly at a retained and discarded pair whose endpoints alternate. All other entries are zero.",
                DescribeRole.Definition),
            Entry("cutPairOrbitals", "Orbitals supported on disjoint pairs",
                "The retained and discarded endpoint embeddings each send the product of an orbital index and a Boolean endpoint to its side of the cut. Each column has the supplied weights at the two sites of its pair and vanishes elsewhere. Retained columns precede discarded columns.",
                DescribeRole.Definition),
            Entry("orderedCut_pair_charpoly", "Full occupation spectrum from the binary rank",
                "On a finite linearly ordered site type, use disjoint pairs on the two sides with endpoints in increasing order. Give each endpoint the same complex amplitude w of squared modulus one half. Let D be the number of retained occupations and r the rank of the alternation matrix over the binary field. The characteristic polynomial of the ordinary retained marginal is X to the power D minus two to the power r, times X minus the reciprocal of two to the power r, raised to two to the power r. Each nonzero determinant picks one site from each pair. The mixed difference of the four endpoint inversion indicators gives the alternation entry. Row and column signs cancel from the spectrum, and character orthogonality leaves a constant Gram block on each fiber of the transposed alternation matrix. Rank-nullity counts the fibers and their common size. The occupation embedding supplies the remaining zero multiplicity.",
                DescribeRole.Theorem),
            Entry("coordinateReplacementWeights", "Coordinate replacement weights",
                "Retained endpoint weights both equal w. For each discarded pair the endpoint labeled false has weight one and the endpoint labeled true has weight zero.",
                DescribeRole.Definition),
            Entry("coordinate_replacement", "Equal compression and a pure marginal",
                "For any disjoint retained and discarded pairs on a finite linearly ordered site type, start with common endpoint amplitude w of squared modulus one half. Replace every discarded orbital by the coordinate vector at the endpoint labeled false. With increasing labels, it is the earlier endpoint. Both orbital matrices have orthonormal columns and equal retained compressions. The replacement marginal has characteristic polynomial X to the power D minus one times X minus one, with D the full retained occupation dimension. The discarded occupation is fixed and the squared norm of the one active amplitude column is one.",
                DescribeRole.Theorem),
            Paragraph(Text("For the graph-state rank formula, see Hein, Eisert and Briegel, Multi-party entanglement in graph states, Proposition 3. The Slater proof obtains the binary phase from actual sorted minors. For equal positive amplitudes, the eigenvalue multiplicities give the entropy gap r log 2. In consecutive alternating four-site blocks, pairs from different blocks do not alternate, so the alternation matrix is the identity and the gap equals the number of blocks times log 2.")))));

    private static DocumentBlock Entry(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("slater-pair-cut-rank-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
