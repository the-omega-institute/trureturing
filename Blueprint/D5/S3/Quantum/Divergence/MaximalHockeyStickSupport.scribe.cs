using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalization and reconstruction on the actual support of the pair",
        H("Normalization and reconstruction on the actual support of the pair"), Blocks(
            Paragraph(Text("The generalized inverse square root is used only through its support identities. No inverse of A, B or A+B is assumed. These repository proofs implement common-support localization and trace transport.")),
            Node("normalize", "normalize S X is invSqrt(S) X invSqrt(S), using the repository generalized inverse square root. OriginalPair takes S=A+B and C=normalize S A.", false, false),
            Node("reconstruct", "reconstruct S Y is sqrt(S) Y sqrt(S). It sends normalized feasible overlaps and positive spectral components back to the original matrix pair.", false, false),
            Node("pair_supported", "For PSD A,B and P=spectralSupport(A+B), PA=AP=A and PB=BP=B. normalized_pair and reconstruction use all four support identities.", true, false),
            Node("normalized_pair", "For PSD A,B, both normalized matrices are PSD and sum to spectralSupport(A+B). The original-pair proof derives its normalized contraction and complementary upper bound from this identity.", true, false),
            Node("reconstruct_normalize", "For PSD S and any X supported by spectralSupport(S) on both sides, reconstruct S (normalize S X)=X. The overlap bijection consumes this recovery statement.", true, false),
            Node("overlap_bijection", "For PSD A,B and every real t, normalization sends each positive overlap of A,tB to an overlap of the two normalized upper bounds and reconstructs it exactly. Conversely reconstruction sends each normalized overlap to an original feasible overlap and normalization recovers it. OriginalPair uses this actual two-way feasible transport.", true, false),
            Node("reconstruction_trace", "For PSD S and arbitrary Y, Tr(reconstruct S Y)=Tr(SY), by cyclic trace. Weighted normalized optimization and the canonical spectral test consume this exact objective transport.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-support-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
