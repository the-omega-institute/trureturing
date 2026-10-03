using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerCycleWalkDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Dyck path sums in bounded strips are compared with counts of walks on finite cycles.",
        H("Signed Strip Sums and Cycle Walks"),
        Blocks(
            Node("cigler-cycle-walk-defs-walk-count", "Walks with a prescribed endpoint", "walkCount",
                "For natural numbers N and r and a residue a modulo N, walkCount counts the Boolean sequences of length r whose increments sum to a modulo N. A true entry contributes one and a false entry contributes minus one. For N at least three, this is the number of walks of length r from zero to a on the N-cycle. The two step choices are counted separately even when they give the same residue. For N equal to zero the endpoint is an integer rather than a residue in a finite cycle.", DescribeRole.Definition),
            Node("cigler-cycle-walk-defs-signed-strip", "Signed Dyck paths in a strip", "signedStrip",
                "For natural numbers H and r, signedStrip is the integer sum of the weights of Dyck paths of semilength r confined to heights zero through H, inclusive. Every up-step has weight one, and a down-step arriving at height j has weight (-1)^floor(j/2). Thus the down-step weights repeat 1, 1, minus one, minus one. This sum is the signed Narayana strip polynomial evaluated at t = 1.", DescribeRole.Definition),
            Node("cigler-cycle-walk-defs-claim", "The strip and cycle identities", "claim",
                "For every integer k at least one and every nonnegative integer n, write c_r for the signed Dyck path sum of semilength r in the strip of height 4k minus two, and U_k for the adjacency matrix of the cycle on 4k vertices. The assertion is c_{2n+1} = U_k^{2n+1}(0, 1), c_{2n+2} = U_k^{2n+2}(0, 0), and U_k^{2n+2}(0, 0) = 2c_{2n+1}. Each matrix entry counts walks of the indicated length and endpoints. These are the three equalities in Conjecture 1, equation (74), of Cigler's paper.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
