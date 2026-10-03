using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerCycleWalkFoldingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection folds an even cycle onto a path with endpoint loops and relates their walk counts.",
        H("Folding an Even Cycle"),
        Blocks(
            Node("cigler-cycle-walk-folding-cycle-adj", "The cycle transition matrix", "cycleAdj",
                "For a positive integer N, cycleAdj is the integer matrix on residues modulo N. Its entry from s to t is the sum of the indicator that s plus one equals t and the indicator that s minus one equals t, with all equalities taken modulo N. For N at least three this is the adjacency matrix of the N-cycle. For N equal to one or two, coincident step destinations are counted with multiplicity two.", DescribeRole.Definition),
            Node("cigler-cycle-walk-folding-fold", "Reflection onto a half-cycle", "fold",
                "For a positive integer v and a residue on the cycle of length 2v, let j be its representative between zero and 2v minus one. Its folded vertex is min(j, 2v - 1 - j), which lies between zero and v minus one. Thus the reflection exchanging j and 2v minus one minus j identifies each reflected pair of vertices.", DescribeRole.Definition),
            Node("cigler-cycle-walk-folding-folded-moment-eq-walk-count", "Closed folded walks and two cycle endpoints", "folded_moment_eq_walkCount",
                "For every integer v at least two and every nonnegative integer r, foldedAdj(v)^r(0, 0) equals the number of r-step walks on the 2v-cycle from zero to zero plus the number from zero to minus one. Folding intertwines the cycle adjacency matrix with the adjacency matrix of the v-vertex path with a loop at each end. The two cycle vertices lying over the first path vertex are zero and minus one.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
