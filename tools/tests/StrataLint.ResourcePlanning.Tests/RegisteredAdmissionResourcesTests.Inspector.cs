using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    private static void AssertInspectorSourceObligations(JsonNode plan, string mode)
    {
        var resources = Strings(plan["resources"]!);
        foreach (var required in new[] { "current", "filemap", "lean-inspector-build", "lean-report", "scribe" })
        {
            Assert.Contains(required, Strings(plan["declared_require"]!));
            Assert.Contains(required, resources);
        }
        Assert.Contains("delta", Strings(plan["declared_require"]!));
        Assert.Equal(mode == "pr", resources.Contains("delta"));
        Assert.DoesNotContain("engineering", resources);
        Assert.DoesNotContain("engineering-guards", resources);
        Assert.Equal(CommonCheckRegistrationFixture.Ids
            .Where(id => id is not ("banned-api-proof" or "capability-proof" or "selftest-pair")).Order(StringComparer.Ordinal),
            Strings(plan["execution"]!["checks"]!));
        Assert.Equal(new[] { "leanInspector/LeanInformationAudit", "leanInspector/reportInspector", "leanInspectorInterface/LeanInformationAuditInterface", "reg/Reg", "regInspector/LeanInformationAuditRegTests" },
            Strings(plan["execution"]!["lean_targets"]!));
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" },
            Strings(plan["execution"]!["steps"]!));
        foreach (var stage in new[] { "build", "engineering", "current" })
            Assert.Equal("required", plan["stages"]![stage]!["status"]!.GetValue<string>());
        Assert.Equal(mode == "pr" ? "required" : "not-applicable",
            plan["stages"]!["delta"]!["status"]!.GetValue<string>());
    }

    [Theory]
    [InlineData("tools/lean-inspector/Inspector.lean", "push")]
    [InlineData("tools/lean-inspector/Inspector.lean", "pr")]
    [InlineData("tools/lean-inspector/native_image.c", "push")]
    [InlineData("tools/lean-inspector/native_image.c", "pr")]
    [InlineData("tools/lean-inspector/lakefile.lean", "push")]
    [InlineData("tools/lean-inspector/lakefile.lean", "pr")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Tests/Projection/AnalysisContract.lean", "push")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Tests/Projection/AnalysisContract.lean", "pr")]
    [InlineData("tools/lean-inspector-interface/LeanInformationAuditInterface/Records.lean", "push")]
    [InlineData("tools/lean-inspector-interface/LeanInformationAuditInterface/Records.lean", "pr")]
    [InlineData("tools/lean-inspector/LeanInformationAuditRegTests/LandedFinite.lean", "push")]
    [InlineData("tools/lean-inspector/LeanInformationAuditRegTests/LandedFinite.lean", "pr")]
    public void RegisteredInspectorProgramsAndTestsRequireCompilationWithoutAnotherReportStep(string input, string mode)
    {
        var plan = Plan(input, "", mode);
        Assert.Contains("lean-inspector-build", Strings(plan["resources"]!));
        Assert.Equal(new[] { "leanInspector/LeanInformationAudit", "leanInspector/reportInspector", "leanInspectorInterface/LeanInformationAuditInterface", "reg/Reg", "regInspector/LeanInformationAuditRegTests" },
            Strings(plan["execution"]!["lean_targets"]!));
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" },
            Strings(plan["execution"]!["steps"]!));
    }

}
