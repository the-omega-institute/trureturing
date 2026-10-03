using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215PureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Record and descent steps act on Boolean stacks, with record gaps recording expenditure.",
        H("Pure Stack Histories"),
        Blocks(
            Node("weak-ascent-weakascent215pure-purestep", "Record and descent steps", "PureStep",
                "A pure step is either a record with a nonnegative gap or a descent to a nonnegative site.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215pure-purestep-shift", "Shifting descent sites", "shift",
                "Shifting a pure step by a nonnegative offset leaves a record gap unchanged and adds the offset to a descent site.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215pure-spend", "Expenditure of a pure step list", "spend",
                "The expenditure of a list of pure steps is the sum of its record gaps; descents contribute zero.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215pure-purerun", "Pure runs on Boolean stacks", "PureRun",
                "The empty step list leaves the stack unchanged. A record of gap g appends g false marks and then a true mark. A descent to site s is permitted precisely when s is below the stack length and its mark is false, and replaces the stack by its prefix of length s. A pure run applies these transitions successively and records the terminal stack.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215pure-budgetrun", "Pure runs with a positive remaining budget", "BudgetRun",
                "A budgeted pure run uses the same stack transitions as a pure run. A record of gap g requires g to be strictly less than the current budget and subtracts g from it. Descents leave the budget unchanged, and an empty terminal list requires a positive budget.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
