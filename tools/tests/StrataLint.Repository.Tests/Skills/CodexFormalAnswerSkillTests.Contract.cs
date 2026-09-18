using static StrataLint.TestSupport.FormalAnswerSkillContract;
using Markdig.Syntax;

namespace StrataLint.Repository.Tests;

/// <summary>
/// The conversation contract and the anchor registries of the codex-formal-answer skill.
/// The contract pins the three interaction modes (plain answer, show-work disclosure, and
/// in-repository modeling); the anchor tests make every declaration the skill cites resolve
/// to a tracked theorem, so a renamed or deleted theorem turns the skill red instead of
/// leaving a dangling reference.
/// </summary>
public sealed partial class CodexFormalAnswerSkillTests
{
    private const string ConversationContractHeading = "Conversation contract";

    [Fact]
    public void ConversationContractWithoutDisclosureModeIsRejected()
    {
        var document = Parse(
            """
            ## Conversation contract

            Apply the first matching mode:

            1. `plain`: answer in ordinary prose.
            2. `in-repository`: model in `D5/` and judge with `make lean`.
            """);

        Assert.False(DefinesConversationContract(document));
    }

    [Fact]
    public void ConversationContractWhoseDisclosureModeDoesNotAttachTheRecordIsRejected()
    {
        var document = Parse(
            """
            ## Conversation contract

            Apply the first matching mode:

            1. `plain`: answer in ordinary prose.
            2. `show-work`: explain the reasoning again in fresh prose.
            3. `in-repository`: model in `D5/` and judge with `make lean`.
            """);

        Assert.False(DefinesConversationContract(document));
    }

    [Fact]
    public void ConversationContractWithPlainDisclosureAndRepositoryModesIsAccepted()
    {
        var document = Parse(
            """
            ## Conversation contract

            Apply the first matching mode:

            1. `plain`: answer in ordinary prose.
            2. `show-work`: append the run `record` on request.
            3. `in-repository`: model in `D5/`, judge with `make lean`, and retain successful exact specializations as `tracked-S`.
            """);

        Assert.True(DefinesConversationContract(document));
    }

    [Fact]
    public void CodexFormalAnswerDefinesConversationContract()
    {
        var skill = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "skills",
            "codex-formal-answer",
            "SKILL.md"));

        Assert.True(DefinesConversationContract(Parse(skill)));
    }

    [Fact]
    public void AnchorRegistryWithDanglingDeclarationIsRejected()
    {
        var document = Parse(
            """
            ## Self anchors

            - `settle_first_match` - `D5/Answering/AssertionSettlementCeiling.lean`
            - `missing_theorem` - `D5/Answering/AssertionSettlementCeiling.lean`
            - `absent_module_theorem` - `D5/Answering/Absent.lean`
            """);
        var sources = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["D5/Answering/AssertionSettlementCeiling.lean"] =
                "theorem settle_first_match (e : Evidence) : True := trivial\n",
        };

        var unresolved = UnresolvedAnchors(AnchorEntries(document, SelfAnchorsHeading), sources);

        Assert.Equal(["missing_theorem", "absent_module_theorem"], unresolved);
    }

    [Fact]
    public void AnchorRegistryResolvingEveryDeclarationIsAccepted()
    {
        var document = Parse(
            """
            ## Self anchors

            - `settle_first_match` - `D5/Answering/AssertionSettlementCeiling.lean`
            - `settle_first_match_prefix_does_not_count` - `D5/Answering/Other.lean`
            """);
        var sources = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["D5/Answering/AssertionSettlementCeiling.lean"] =
                "theorem settle_first_match (e : Evidence) : True := trivial\n",
            ["D5/Answering/Other.lean"] =
                "theorem settle_first_match_prefix_does_not_count : True := trivial\n",
        };

        Assert.Empty(UnresolvedAnchors(AnchorEntries(document, SelfAnchorsHeading), sources));
    }

    private static bool DefinesConversationContract(MarkdownDocument document)
    {
        var section = FindSection(document, ConversationContractHeading);
        var orderedLists = section
            .SelectMany(SelfAndDescendants)
            .OfType<ListBlock>()
            .Where(list => list.IsOrdered)
            .ToArray();
        if (orderedLists.Length != 1)
        {
            return false;
        }

        var items = orderedLists[0].OfType<ListItemBlock>().ToArray();
        if (items.Length != 3)
        {
            return false;
        }

        var plainCodes = InlineCodeValuesFromBlock(items[0]).ToHashSet(StringComparer.Ordinal);
        var disclosureCodes = InlineCodeValuesFromBlock(items[1]).ToHashSet(StringComparer.Ordinal);
        var repositoryCodes = InlineCodeValuesFromBlock(items[2]).ToHashSet(StringComparer.Ordinal);

        return plainCodes.Contains("plain")
            && disclosureCodes.Contains("show-work")
            && disclosureCodes.Contains("record")
            && repositoryCodes.Contains("in-repository")
            && repositoryCodes.Contains("D5/")
            && repositoryCodes.Contains("make lean")
            && repositoryCodes.Contains("tracked-S");
    }

}
