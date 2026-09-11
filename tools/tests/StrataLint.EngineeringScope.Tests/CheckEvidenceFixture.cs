using StrataLint.TestSupport;

namespace StrataLint.EngineeringScope.Tests;

internal static class CheckEvidenceFixture
{
    internal static void Seal(string root, string stage, CommonStageRecord build)
    {
        var checks = CommonExecutionEvidence.BeginChecks(root, stage, build, TextWriter.Null);
        foreach (var id in checks.Ids)
            checks.Run(id, () => new CheckWork(id.StartsWith("SL-", StringComparison.Ordinal)
                ? [new(id, 0, CommonCheckRegistrationFixture.Predicate(id))] : CommonCheckExecutionTests.Fixture.Work(id),
                id == "scribe-describe" ? CommonCheckRegistrationFixture.ScribeMaterial : null));
        checks.Seal();
    }
}
