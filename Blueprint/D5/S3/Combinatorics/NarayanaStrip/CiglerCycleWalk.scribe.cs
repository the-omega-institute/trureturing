using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerCycleWalkDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalk.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Dyck paths in the strip of height 4k minus two count walks on the cycle with 4k vertices.",
        H("Cigler's Signed Strip and Cycle Walk Identities"),
        Blocks(
            Node("cigler-cycle-walk-result", "The three cycle walk equalities", "result", "For every integer k at least one and every nonnegative integer n, let c_r be the sum of the weights of Dyck paths of semilength r confined to heights zero through 4k minus two. Up-steps have weight one, and down-steps arriving at height j have weight (-1)^floor(j/2), repeating 1, 1, minus one, minus one. If U_k is the adjacency matrix of the cycle on 4k vertices, then c_{2n+1} = U_k^{2n+1}(0, 1) and c_{2n+2} = U_k^{2n+2}(0, 0) = 2c_{2n+1}. These are Conjecture 1, equation (74), of Cigler's paper. Pairing steps and factoring their transfer matrix identifies c_r for positive r with closed walks at an endpoint of the 2k-vertex path with a loop at each end. Folding the 4k-cycle expresses this count as the sum of walks from zero to zero and from zero to minus one. Parity eliminates one endpoint at each length, and reflection together with the one-step recurrence gives the factor two.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
