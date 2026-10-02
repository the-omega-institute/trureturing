using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215GroupedRenewalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Grouping histories by expenditure and remaining budget gives bivariate renewal identities.",
        H("Grouped Renewal Series"),
        Blocks(
            Node("weak-ascent-weakascent215groupedrenewal-recordseries", "The record-ending series", "recordSeries",
                "The coefficient of z to the power s and x to the power l in the record-ending series counts pure histories of expenditure s and length l whose last step is a record.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215groupedrenewal-survivorseries", "The marked-survivor series", "survivorSeries",
                "The coefficient of z to the power s and x to the power l in the survivor series counts pairs consisting of a pure history of expenditure s and length l and a choice of one of its terminal old entries.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215groupedrenewal-fullseries", "Full histories with fixed initial budget", "fullSeries",
                "For a Boolean e and a nonnegative budget b, the coefficient of x to the power l in F_e(b;x) counts full histories of length l with initial mode e and budget b. The initial stack consists of a single true mark when e is true and is empty otherwise.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215groupedrenewal-budgetseries", "The positive-budget series", "budgetSeries",
                "The positive-budget series B_e(z,x) is the sum, over nonnegative b, of z to the power b times F_e(b + 1;x). Thus the exponent of z records the initial budget minus one.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215groupedrenewal-grouped-renewal", "Grouped renewal equations", "grouped_renewal",
                "Write P, R and S for the pure, record-ending and marked-survivor series, with z recording expenditure and x recording length. Then R = xP + zR. For each Boolean e, put U = S + P when e is true and U = S otherwise, and put M = R + 1 when e is true and M = R otherwise. Let T be the sum of z to the power b times F_true(b + 2;x), let O = x(U B_false + M T), and let A = B_e + x M B_false. The renewal equation is A + zO = P + O + zA.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
