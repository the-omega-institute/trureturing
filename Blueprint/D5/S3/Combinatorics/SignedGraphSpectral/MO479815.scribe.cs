using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SignedGraphSpectral;

internal sealed class MO479815Document : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/SignedGraphSpectral/MO479815.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/hameed2025signedspectraldeletion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pendant-edge counterexample to signed-graph spectral-deviation monotonicity.",
        H("MO479815 signed-graph spectral deletion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The source monotonicity claim"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every finite simple graph, every Boolean signing of unordered vertex "
                    + "pairs, and every edge, delete the edge on the same vertex carrier and "
                    + "compare the full decreasing real spectra, with multiplicity, of the signed "
                    + "and underlying adjacency matrices. The source quantity is the sum of the "
                    + "squared coordinate differences, beta_A(Sigma). The claim asserts that this "
                    + "quantity cannot increase after deletion; no connectedness, non-bridge, "
                    + "non-isolation, sign, or dimension restriction is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The monotonicity claim is refuted"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The literal universal claim is false. On Fin 4 take the paw graph with "
                        + "edges 01, 02, 12 and 03, give every edge the negative sign, and delete "
                        + "the pendant edge 03. The underlying matrices are the paw matrix and "
                        + "K3 disjoint union K1. If a, b, c are the three ordered roots of "
                        + "x^3 - x^2 - 3x + 1 in (2,3), (0,1), and (-2,-1), respectively, "
                        + "the full ordered spectra are (a,b,-1,c), (-c,1,-b,-a) before deletion "
                        + "and (2,0,-1,-1), (1,1,0,-2) after deletion. Thus beta before is "
                        + "4(1-b)^2 and beta after is 4, with a strict increase.")),
                    Paragraph(Text(
                        "The Lean proof establishes the graph and signing correspondence, both "
                        + "Hermitian matrices, characteristic polynomials, existence and ordering "
                        + "of all roots with multiplicity, and the strict beta inequality on the "
                        + "same Fin 4 carrier."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathoverflow-479815-signed-spectral-deletion"),
                    ResolutionKind.Refuted)))));
}
