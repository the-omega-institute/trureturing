using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MissionFileLoaderTests
{
    [Fact]
    public void PrimedIdentifierAfterTheFirstTaskPoisonsTheWholeScan()
    {
        var target = GovernanceDeferrals + "\n" + """
            def separator' : Unit := ()
            /-- TASK D5-T0040
                This duplicate follows a primed identifier. -/
            def duplicateMissionNoveltyTicket : Unit := ()
            """;

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            LoadRepository(Encoding.UTF8.GetBytes(ValidMission), target));

        Assert.Equal(MissionLoadErrorCode.DanglingCaseReference, invalid.Error.Code);
        Assert.Contains("ambiguous", invalid.Error.Message, StringComparison.Ordinal);
        Assert.Contains("primed identifier", invalid.Error.Message, StringComparison.Ordinal);
        Assert.IsType<TaskBlockScanResult.Ambiguous>(
            TaskBlockReferenceSyntax.ScanDocumentationCommentTaskStarts(target, "D5-T0040"));
    }

    [Fact]
    public void AmbiguousRawIntroducerCannotRecoverAtAGuessedTerminator()
    {
        var target = ReplaceNoveltyTaskBlock(string.Empty) + "\n" + """
            def x := identifierr##"
            inside "
            "##
            /-- TASK D5-T0040
                This block is inert under the correct lexical state. -/
            "
            """;

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            LoadRepository(Encoding.UTF8.GetBytes(ValidMission), target));

        Assert.Equal(MissionLoadErrorCode.DanglingCaseReference, invalid.Error.Code);
        Assert.Contains("ambiguous", invalid.Error.Message, StringComparison.Ordinal);
        Assert.Contains("raw string", invalid.Error.Message, StringComparison.Ordinal);
        Assert.IsType<TaskBlockScanResult.Ambiguous>(
            TaskBlockReferenceSyntax.ScanDocumentationCommentTaskStarts(target, "D5-T0040"));
    }
}
