using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class StronglyCospectralTwinAmplitudeBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/meaghermonterdenguyen2026sedentary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every odd integer relation among the supported adjacency gaps of strongly cospectral "
        + "twins gives an explicit positive floor for their return amplitudes.",
        H("Return amplitudes of strongly cospectral twins"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strongly-cospectral-twins-eigenvalue"),
                DeclarationHandle.Create(Prefix + "twinEigenvalue"),
                H("The twin eigenvalue"),
                StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The difference of the two vertex basis vectors has "
                    + "eigenvalue minus one for adjacent twins and zero for nonadjacent twins."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("strongly-cospectral-twins-remaining-support"),
                DeclarationHandle.Create(Prefix + "remainingSupport"),
                H("The remaining adjacency support"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The finite support contains the distinct eigenvalues "
                    + "whose projector diagonals at the first twin are positive, excluding the twin eigenvalue. "
                    + "Each projector combines all basis vectors of its eigenspace."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("strongly-cospectral-twins-amplitude-bound"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The odd-relation return-amplitude bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For distinct strongly cospectral twins in a finite simple graph, "
                    + "the projector at the twin eigenvalue sends the first vertex vector to half the "
                    + "difference of the two vectors, including when the eigenvalue is repeated. "
                    + "The remaining weights are positive and sum to one half. Their weighted phase "
                    + "sum together with the twin contribution gives the diagonal of exp(itA). "
                    + "The projector diagonals agree at both twins, so their complex return amplitudes agree. "
                    + "The positive-time orbit closure yields the parity criterion of Theorem 2.2(2) "
                    + "of Meagher, Monterde and Nguyen. On the actual orbit an odd zero-gap relation has "
                    + "character one, while its character at the constant phase minus one is minus one. "
                    + "The weighted character chord bound gives a squared displacement of four. "
                    + "The total weighted squared coordinate chord is twice the real part of the "
                    + "dephased amplitude. This gives the bound 2/D for every real time, where D is "
                    + "the sum of the squared integer coefficients divided by their projector weights."))),
                DescribeRole.Theorem)),
        []));
}
