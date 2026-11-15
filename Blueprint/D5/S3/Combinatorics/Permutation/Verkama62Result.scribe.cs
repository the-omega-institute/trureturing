using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class Verkama62ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/Verkama62Result.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/verkama2026connectivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Verkama Conjecture 6.2.", H("Verkama Conjecture 6.2"), Blocks(
            Node("verkama62-result-complete-run", "Existence of a complete run", "complete_run",
                "For every n at least three and permutation pi of Fin n, assume the value-labelled inversion graph is connected and its induced complement of every singleton is connected. Then there is a northeast ear run ending at every point. An anchored triangle or 3412 square starts the construction. Induction on the number of missing points uses the anchored extension and the deletion connectivity of every run. This proof uses no pattern avoidance.", DescribeRole.Theorem),
            Node("verkama62-result-result", "The exact inversion bound", "result",
                "For every integer n at least zero and every permutation pi of {1,...,n}, suppose pi classically avoids 351624 and its inversion graph has at least three vertices, is connected, and remains connected after deletion of each vertex. Then inv(pi) is at least (7/4)n - 3, with comparison in the rationals. In Lean the graph vertices are values in Fin n, the source label of i is i.val+1, and the graph is defined by the strictly negative integer product of the difference of value labels and the difference of their inverse-position labels. The at-least-three-vertices condition is 3 <= n. An occurrence uses six increasing positions and the relative value order [3,5,1,6,2,4], corresponding to [2,4,0,5,1,3] in Fin 6. The inversion statistic is the existing list counter on the one-based permutation word, proved equal to the number of increasing-position inversions, each counted once. A complete ear run and avoidance imply 7n <= 4 inv(pi)+12, which is equivalent to the displayed rational bound. No further avoidance, bipartiteness, asymptotic qualification, or assumed ear decomposition is used.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
