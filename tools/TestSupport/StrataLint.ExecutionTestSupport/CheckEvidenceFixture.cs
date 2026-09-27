using StrataLint.EngineeringScope;
using StrataLint.TestSupport;

namespace StrataLint.TestSupport;

internal static class CheckEvidenceFixture
{
    internal static void Seal(string root, string stage, CommonStageRecord build, string[]? selectedIds = null)
    {
        var checks = CommonExecutionEvidence.BeginChecks(root, stage, build, TextWriter.Null, selectedIds);
        foreach (var id in checks.Ids)
            checks.Run(id, () => new CheckWork(id.StartsWith("SL-", StringComparison.Ordinal)
                ? [new(id, 0, CommonCheckRegistrationFixture.Predicate(id))] : Work(id),
                id == "scribe-describe" ? CommonCheckRegistrationFixture.ScribeMaterial : null));
        checks.Seal();
    }
    internal static CheckOperation[] Work(string id) => id switch
    {
        "selftest-pair" => [new("selftest-first", 0, "SELFTEST PASS\n"), new("selftest-second", 0, "SELFTEST PASS\n")],
        "capability-proof" => [new("restore-CompileFailProof", 0, "restored"), new(id, 1, "MissingCapability.cs(13,9): error CS7036: missing metaClear\n")],
        "banned-api-proof" => [new("restore-BannedApiCompileFailProof", 0, "restored"), new(id, 1, "BannedApiViolations.cs(1,1): error RS0030: banned symbol\n")],
        _ => [new(id, 0, "passed")],
    };
}
