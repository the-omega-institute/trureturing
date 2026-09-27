using StrataLint.EngineeringScope;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.StageIntegration.Tests;

public sealed partial class CurrentExecutionContractTests
{
    [Theory]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/lean-inspector/LeanInformationAudit/Enrollment.lean", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/lean-inspector/native.py", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/lean-inspector/native_image.c", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/lean-inspector/Inspector.lean", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/lean-inspector/materials.py", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/lean-inspector/publication.py", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/lean-inspector-interface/LeanInformationAuditInterface/Records.lean", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/scripts/worktree/lean-cache-run.sh", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/scripts/worktree/lean_cache_release.py", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/scripts/worktree/cache_material.py", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/scripts/report/lean-report-selection.py", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/scripts/report/lean-report-input.sh", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/StrataLint.Lean/Lean/LeanUtilityInputCommand.cs", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/StrataLint.Lean/packages.lock.json", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "D5/S3/Fourier/IntegerCharacterCoercivity.lean", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "D5/S3/TotalVariation/PrimitiveBridgeCancellation.lean", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "Reg/D5/S3/Fourier/IntegerCharacterCoercivity.lean", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "Reg/D5/S3/TotalVariation/PrimitiveBridgeCancellation.lean", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "Reg/Support/DependentFamily.lean", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "lean-toolchain", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "lake-manifest.json", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "lakefile.toml", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "Reg/lake-manifest.json", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "Reg/lakefile.toml", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/lean-inspector/lakefile.lean", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/lean-inspector-interface/lake-manifest.json", true)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "README.md", false)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "docs/develop/theory/native-input-control.md", false)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "D5/README.md", false)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/lean-inspector/tests/test_native.py", false)]
    [InlineData("StrataLint.DeclaredTemplate.Tests", "tools/scripts/workflow/truth_release.py", false)]
    [InlineData("StrataLint.Lean.Tests", "tools/lean-inspector/native_image.c", true)]
    [InlineData("StrataLint.Lean.Tests", "Makefile", true)]
    [InlineData("StrataLint.Lean.Tests", "README.md", false)]
    [InlineData("StrataLint.NativeTransportIntegration.Tests", "tools/lean-inspector/tests/test_native.py", false)]
    [InlineData("StrataLint.NativeTransportIntegration.Tests", "tools/lean-inspector/tests/test_reuse.py", false)]
    [InlineData("StrataLint.NativeTransportIntegration.Tests", "tools/lean-inspector/tests/test_native_invalidation.py", false)]
    [InlineData("StrataLint.NativeTransportIntegration.Tests", "tools/lean-inspector/tests/test_native_support.py", true)]
    [InlineData("StrataLint.NativeTransportIntegration.Tests", "tools/lean-inspector-interface/LeanInformationAuditInterface/Records.lean", true)]
    [InlineData("StrataLint.NativeTransportIntegration.Tests", "tools/lean-inspector-interface/lakefile.toml", true)]
    [InlineData("StrataLint.NativeTransportIntegration.Tests", "tools/lean-inspector-interface/lake-manifest.json", true)]
    [InlineData("StrataLint.NativeTransportIntegration.Tests", "tools/lean-inspector/native.py", true)]
    [InlineData("StrataLint.NativeTransportIntegration.Tests", "tools/scripts/workflow/truth_release.py", false)]
    [InlineData("StrataLint.ReleaseIntegration.Tests", "tools/scripts/workflow/truth_release.py", true)]
    [InlineData("StrataLint.ReleaseIntegration.Tests", "tools/lean-inspector/tests/test_native.py", false)]
    [InlineData("StrataLint.ResourcePlanning.Tests", "tools/scripts/workflow/ci_plan.py", true)]
    [InlineData("StrataLint.ResourcePlanning.Tests", "tools/scripts/workflow/truth_release.py", false)]
    [InlineData("StrataLint.InspectionIntegration.Tests", "Meta/ci-checks.json", true)]
    [InlineData("StrataLint.InspectionIntegration.Tests", "tools/scripts/workflow/ci_plan.py", false)]
    [InlineData("StrataLint.StageIntegration.Tests", "tools/scripts/preflight.sh", true)]
    [InlineData("StrataLint.StageIntegration.Tests", "tools/lean-inspector/tests/test_native.py", false)]
    [InlineData("StrataLint.ReleaseSelection.Tests", "tools/scripts/workflow/truth_release.py", false)]
    [InlineData("StrataLint.EngineeringScope.Tests", "tools/scripts/preflight.sh", false)]
    public void RegisteredNativeFixtureInputsRerunConsumedFilesAndReuseUnrelatedChanges(string project, string path, bool invalidates)
    {
        using var fixture = new ExecutionFixture();
        var registration = JsonNode.Parse(File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), EngineeringRegistrationFixture.Path)))!;
        var declaration = registration["projects"]!.AsArray().Single(row => row!["path"]!.ToString()
            == $"tools/tests/{project}/{project}.csproj")!;
        EditRegistration(fixture, rows =>
        {
            foreach (var field in new[] { "execution_inputs", "execution_excludes", "execution_environment" })
                rows[0]![field] = declaration[field]!.DeepClone();
        });
        // Use the real execution declaration with synthetic compile inputs and
        // runner results, so only the consumed file changes between executions.
        if (project == "StrataLint.DeclaredTemplate.Tests")
            RegisterRuntimeSourceOwners(fixture, declaration["execution_inputs"]!.AsArray().Select(value => value!.ToString()));
        foreach (var input in declaration["execution_inputs"]!.AsArray().Select(value => value!.ToString()).Where(value => !value.Contains('*')))
            if (!File.Exists(Path.Combine(fixture.Root, input))) fixture.Write(input, input == "Meta/FILEMAP.toml"
                ? "schema_version = 5\nresources = []\nevidence = { artifact_kinds = { json = { profile = \"structured-json\", selectors = [\"result\"], path_selectors = [\"formal\"] } } }\n[[files]]\npattern = \"tools/tests/First/**\"\nrequire = []\nkind = \"program\"\n"
                : "registered fixture material\n");
        if (project == "StrataLint.NativeTransportIntegration.Tests")
        {
            const string owner = "tools/fixture/NativeSource.csproj";
            fixture.Write(owner, "<Project />\n");
            var manifest = Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path);
            File.WriteAllText(manifest, EngineeringRegistrationFixture.Append(File.ReadAllText(manifest),
                new EngineeringProjectFixture(owner, "NativeSource", "test-support", false,
                    ["tools/StrataLint.Lean/Lean/LeanUtilityInputCommand.cs"])));
        }
        fixture.Write(path, "original fixture input\n");
        fixture.Track();
        Assert.Equal(new[] { ExecutionFixture.First, ExecutionFixture.Second }, Execute(fixture));
        var original = CommonExecutionEvidence.ValidateTests(fixture.Root);
        Seed(fixture);

        fixture.Write(path, "changed fixture input\n");
        fixture.Track();

        var calls = Execute(fixture);
        var current = CommonExecutionEvidence.ValidateTests(fixture.Root);
        var prior = original.Projects[0];
        var accepted = current.Projects[0];
        Assert.True(calls.SequenceEqual(invalidates ? new[] { ExecutionFixture.First } : []),
            $"[FAIL] native_fixture_execution_input: {project}: {path}: invalidates={invalidates}; executed={string.Join(',', calls)}; old={prior.InputFingerprint}; new={accepted.InputFingerprint}");
        if (invalidates)
        {
            Assert.NotEqual(prior.InputFingerprint, accepted.InputFingerprint);
            Assert.Equal("executed", accepted.Status);
            Assert.Equal(current.Candidate, accepted.ExecutionCandidate);
            Assert.Equal(current.Round, accepted.ExecutionRound);
        }
        else Assert.Equal(prior with { Status = "reused" }, accepted);
        Assert.Equal(original.Projects[1] with { Status = "reused" }, current.Projects[1]);
    }
}
