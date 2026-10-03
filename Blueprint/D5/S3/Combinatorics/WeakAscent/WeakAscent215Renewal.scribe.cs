using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215RenewalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full histories extend pure histories by visits to old sites and split at the first such visit.",
        H("Renewal at the First Old Site"),
        Blocks(
            Node("weak-ascent-weakascent215renewal-fullstep", "Full steps", "FullStep",
                "A full step is either a pure record or descent step, or an old-site step with a nonnegative site.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215renewal-finishmode", "The mode after a pure prefix", "finishMode",
                "The mode of an empty pure step list is its initial Boolean mode. A record changes the mode to true and a descent changes it to false; subsequent steps determine the final mode in the same way.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215renewal-fullrun", "Full stack runs", "FullRun",
                "A full run starts from a Boolean stack, a nonnegative budget and a Boolean mode. A record appends false marks and one true mark, subtracts its gap from the budget and sets the mode to true; its gap must be less than the budget. A descent at a false-marked site truncates the stack before that site, preserves the budget and sets the mode to false. An old-site step requires a positive budget and a true-marked site. When the mode is true and the site is last, it leaves the singleton true stack, increases the budget by one and retains true mode; otherwise it leaves the empty stack, preserves the budget and sets false mode. The empty list is permitted exactly when the budget is positive.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215renewal-first-old-decomposition", "Decomposition at the first old-site step", "first_old_decomposition",
                "For every initial stack, budget and mode, full histories are in bijection with either a budgeted pure prefix or a budgeted pure prefix followed by an old-site choice in its terminal stack and a full suffix. Reconstruction concatenates the pure prefix, the chosen old-site step and the suffix. The suffix starts with a singleton true stack, one extra unit of remaining budget and true mode exactly when the pure prefix finishes in true mode and the chosen site is last; otherwise it starts with an empty stack and false mode. Moreover, for a positive budget and a stack of length c, histories of length n + 1 are in bijection with a choice among the record gaps below the budget or the c stack sites, followed by a history of length n from the state prescribed by that first transition.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
