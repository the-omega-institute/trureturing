using StrataLint.Engine;
using static StrataLint.Tests.InformationTemplateDebtStoreTests;

namespace StrataLint.Tests;

public sealed class InformationTemplateRoutingTests
{
    private const string DebtPath = "Golden/InformationTemplateDebt/rows/" +
        "1a49292654bc35592997b07d5fab4dbc7527947ec8c534fefdf5a4ff34d07daa.json";
    private const string ContentPath = "D5/Fixture/Binding.lean";
    private const string JudgePath = "tools/lean-inspector/LeanInformationAudit/Registry.lean";

    private static RepositorySnapshot Tree(string debtPlane = "content", string sourcePlane = "content") =>
        Snapshot((AdmissionPlanePolicy.FileMapPath, "schema_version = 2\n" + string.Concat(
            new[] { ("Golden/InformationTemplateDebt/rows/*.json", debtPlane),
                ("D5/**", sourcePlane), ("tools/**", "judge"), ("Meta/**", "judge") }
                .Select(pair => $"""

                    [[files]]
                    pattern = "{pair.Item1}"
                    kind = "data"
                    admission_plane = "{pair.Item2}"
                    produced_by = "none"
                    consumed_by = ["StrataLint"]
                    verified_by = ["StrataLint"]
                    artifact_id = "none"
                    runtime_disposition = "committed-source"

                    """))));

    private static void Check(RepositorySnapshot before, RepositorySnapshot after, params string[] paths) =>
        DeclaredTemplateBindingRule.CheckRouting(before, after, paths.ToHashSet(StringComparer.Ordinal));

    [Fact]
    public void debt_content_plane_discharge_allowed() => Check(Tree(), Tree(), DebtPath, ContentPath);

    [Fact]
    public void judge_content_mixed_blocked()
    {
        var failure = Assert.Throws<FormatException>(() => Check(Tree(), Tree(), DebtPath, JudgePath));
        Assert.Contains("DTR-Routing: mixed delta", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void base_candidate_routing_agrees()
    {
        // Both snapshots parse; a candidate reclassification cannot hide that
        // these bytes were judge-owned in the independent protected input.
        var failure = Assert.Throws<FormatException>(() => Check(Tree(sourcePlane: "judge"), Tree(), ContentPath));
        Assert.Contains("DTR-Routing", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void separate_judge_and_content_batches_accepted()
    {
        Check(Tree(), Tree(), JudgePath, AdmissionPlanePolicy.FileMapPath);
        Check(Tree(), Tree(), ContentPath);
    }
}
