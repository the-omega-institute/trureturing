using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanReportProducerInputScriptTests
{
    [Theory]
    [InlineData("root_namespace")]
    [InlineData("namespace_exclude")]
    [InlineData("global_namespace_exceptions")]
    [InlineData("conflicting-namespace")]
    [InlineData("unowned-exception")]
    [InlineData("missing-rule-inputs")]
    public void MissingOrConflictingComposedRegistrationFailsBeforeAddressing(string defect)
    {
        using var fixture = new ProducerInputFixture();
        fixture.EditRegistry(registry =>
        {
            if (defect == "conflicting-namespace")
                registry["projects"]![2]!["include"]!.AsArray().Add("tools/StrataLint.Cli/Fixture.cs");
            else if (defect == "unowned-exception")
                registry["projects"]![0]!["global_namespace_exceptions"] = new JsonArray("unowned/Source.cs");
            else if (defect == "missing-rule-inputs") registry.Remove("rule_build_inputs");
            else registry["projects"]![0]!.AsObject().Remove(defect);
        });
        AssertRegistrationFailure(fixture.Run("address"), ProducerInputFixture.ProjectRegistrationPath);
    }

    [Fact]
    public void ComposedNamespaceRegistrationIsAcceptedByProducer()
    {
        using var fixture = new ProducerInputFixture();
        Assert.Equal(fixture.ExpectedAddressBytes(), fixture.Run("address").StandardOutput);
    }

    [Fact]
    public void NamespaceAndExecutionPolicyDoNotChangeProducerIdentity()
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.EditRegistry(registry =>
        {
            var row = registry["projects"]![0]!;
            row["root_namespace"] = "Changed.Namespace";
            row["namespace_exclude"] = new JsonArray("tools/StrataLint.Cli/Fixture.cs");
            row["role"] = "cross-cutting-test";
            row["ci"] = true;
            row["test_partition"] = "explicit-checks";
        });
        Assert.Equal(before, fixture.Address());
    }

    [Fact]
    public void NativeIncrementalReportEqualsFullReportWithRefutationMaterials()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("/usr/bin/env",
            [$"NATIVE_REPORT_PRODUCER={Path.Combine(AppContext.BaseDirectory, "StrataLint.Lean.dll")}",
                "python3", Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/native_report_contract.py")],
            root, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("metadata", 0)]
    [InlineData("unrelated-row", 0)]
    [InlineData("blueprint", 0)]
    [InlineData("producer", 2)]
    [InlineData("dependency", 2)]
    [InlineData("configuration", 2)]
    [InlineData("source", 2)]
    public void RegisteredInputsDriveRealPlannerInvalidation(string change, int expectedRechecks)
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        Assert.Empty(fixture.Plan(before, before)["recheck"]!.AsArray());
        switch (change)
        {
            case "metadata": fixture.Write("lakefile.toml", "name = \"renamed\"\nkeywords = [\"metadata\"]\n"); break;
            case "unrelated-row": fixture.EditRegistry(registry => registry["projects"]![2]!["assembly"] = "UnrelatedRenamed"); break;
            case "blueprint": fixture.Write("Blueprint/Unrelated.scribe.cs", "// unrelated narrative"); break;
            case "producer": fixture.Append("tools/StrataLint.Cli/Fixture.cs", "// producer changed"); break;
            case "dependency": fixture.Append("tools/Trureturing.Truth/Fixture.cs", "// dependency changed"); break;
            case "configuration": fixture.Append("producer.props", "<!-- changed configuration -->"); break;
            case "source": fixture.Append("D5/Probe.lean", "-- changed source"); break;
        }
        var plan = fixture.Plan(before, fixture.Address());

        Assert.Equal(expectedRechecks, plan["recheck"]!.AsArray().Count);
        Assert.Equal(expectedRechecks == 0 ? "reuse" : "delta", plan["status"]!.GetValue<string>());
        Assert.Equal(change is "producer" or "dependency" or "configuration", plan["semantic_changed"]!.GetValue<bool>());
        var evidence = Environment.GetEnvironmentVariable("JUDGE_SEED_EVIDENCE");
        if (!string.IsNullOrEmpty(evidence))
        {
            Directory.CreateDirectory(evidence);
            File.WriteAllText(Path.Combine(evidence, "report-" + change + ".json"), plan.ToJsonString());
        }
    }

    [Theory]
    [InlineData("producer-paths")]
    [InlineData("scribe-producer-paths")]
    public void RegisteredDependencyWithoutCodeMentionIsRequired(string command)
    {
        using var fixture = new ProducerInputFixture();
        const string dependency = "tools/scripts/worktree/fetch-input.sh";
        fixture.Write(dependency, "#!/usr/bin/env bash\n");
        fixture.RegisterScripts(dependency);

        var complete = fixture.Run(command);

        Assert.True(complete.ExitCode == 0, Encoding.UTF8.GetString(complete.StandardError));
        Assert.Contains(ProducerInputFixture.FetcherPath, Lines(complete));
        Assert.Contains(dependency, Lines(complete));
        fixture.Remove(dependency);
        var missingDependency = fixture.Run(command);
        Assert.Equal(2, missingDependency.ExitCode);
        Assert.Empty(missingDependency.StandardOutput);
        Assert.Contains(dependency, Encoding.UTF8.GetString(missingDependency.StandardError));
        fixture.Remove(ProducerInputFixture.FetcherPath);
        var missingFetcher = fixture.Run(command);
        Assert.Equal(2, missingFetcher.ExitCode);
        Assert.Empty(missingFetcher.StandardOutput);
        Assert.Contains(ProducerInputFixture.FetcherPath, Encoding.UTF8.GetString(missingFetcher.StandardError));
    }

    [Theory]
    [InlineData("producer-paths")]
    [InlineData("scribe-producer-paths")]
    public void UnregisteredShellPythonAndDllMentionsDoNotAddInputs(string command)
    {
        using var fixture = new ProducerInputFixture();
        const string shell = "tools/scripts/worktree/unregistered.sh";
        const string python = "tools/lean-inspector/unregistered.py";
        fixture.Write(shell, "#!/bin/bash\n");
        fixture.Write(python, "VALUE = 1\n");
        fixture.Append(ProducerInputFixture.FetcherPath,
            "source \"$SCRIPT_DIR/unregistered.sh\"\n"
            + "python3 \"$ROOT/tools/lean-inspector/delta.py\"\n"
            + "dotnet \"$ROOT/tools/unregistered/bin/Release/net10.0/unregistered.dll\"\n"
            + "dotnet run --project \"$ROOT/tools/unregistered/unregistered.csproj\"\n");
        fixture.Append("tools/lean-inspector/delta.py", "import unregistered\n");

        var result = fixture.Run(command);

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.DoesNotContain(shell, Lines(result));
        Assert.DoesNotContain(python, Lines(result));
        var before = fixture.Address();
        fixture.Remove(shell);
        fixture.Remove(python);
        Assert.Equal(before, fixture.Address());
    }

    [Fact]
    public void RegisteredProjectContributesWithoutEntrypointMention()
    {
        using var fixture = new ProducerInputFixture();
        fixture.Write("tools/lean-inspector/inspect.sh", "#!/bin/bash\n");
        var before = fixture.Address();

        fixture.Append("tools/StrataLint.Cli/Fixture.cs", "// changed producer\n");

        Assert.NotEqual(before[1], fixture.Address()[1]);
    }

    [Fact]
    public void DeclaredBytesAndRegistrationBytesChangeProducerDigest()
    {
        using var fixture = new ProducerInputFixture();
        const string dependency = "tools/scripts/worktree/declared.py";
        fixture.Write(dependency, "VALUE = 1\n");
        var original = fixture.Address();
        fixture.RegisterScripts(dependency);
        var registered = fixture.Address();
        Assert.NotEqual(original[1], registered[1]);
        fixture.Append(dependency, "VALUE = 2\n");
        var changed = fixture.Address();
        Assert.NotEqual(registered[1], changed[1]);
        fixture.Append(ProducerInputFixture.LeanRegistrationPath, "\n");
        Assert.NotEqual(changed[1], fixture.Address()[1]);
        Assert.Equal(original[2..], changed[2..]);
    }

    [Theory]
    [InlineData("producer-paths", ProducerInputFixture.LeanRegistrationPath)]
    [InlineData("scribe-producer-paths", ProducerInputFixture.ScribeRegistrationPath)]
    public void MissingScopeRegistrationFailsWithDiagnostic(string command, string registration)
    {
        using var fixture = new ProducerInputFixture();
        fixture.Remove(registration);

        AssertRegistrationFailure(fixture.Run(command), registration);
    }

    [Theory]
    [InlineData("{")]
    [InlineData("[]")]
    [InlineData("{\"schema\":\"unknown\",\"scripts\":[],\"projects\":[]}")]
    [InlineData("{\"schema\":\"report-producer-scope-v1\",\"scripts\":[]}")]
    [InlineData("{\"schema\":\"report-producer-scope-v1\",\"scripts\":[],\"projects\":[],\"extra\":true}")]
    [InlineData("{\"schema\":\"report-producer-scope-v1\",\"scripts\":\"script.sh\",\"projects\":[]}")]
    [InlineData("{\"schema\":\"report-producer-scope-v1\",\"scripts\":[],\"projects\":[],\"scripts\":[]}")]
    public void MalformedScopeRegistrationFailsWithDiagnostic(string contents)
    {
        using var fixture = new ProducerInputFixture();
        fixture.Write(ProducerInputFixture.LeanRegistrationPath, contents);

        AssertRegistrationFailure(fixture.Run("address"), ProducerInputFixture.LeanRegistrationPath);
    }

    [Theory]
    [InlineData("scripts")]
    [InlineData("projects")]
    public void DuplicateScopeRegistrationFailsWithDiagnostic(string field)
    {
        using var fixture = new ProducerInputFixture();
        fixture.WriteRegistration(ProducerInputFixture.LeanRegistrationPath,
            field == "scripts" ? [ProducerInputFixture.FetcherPath, ProducerInputFixture.FetcherPath] : [ProducerInputFixture.FetcherPath],
            field == "projects" ? [ProducerInputFixture.CliProjectPath, ProducerInputFixture.CliProjectPath] : [ProducerInputFixture.CliProjectPath]);

        var result = fixture.Run("address");

        AssertRegistrationFailure(result, ProducerInputFixture.LeanRegistrationPath);
        Assert.Contains("duplicate", Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("/absolute.sh")]
    [InlineData("../outside.sh")]
    [InlineData("tools/../script.sh")]
    [InlineData("./script.sh")]
    [InlineData("tools//script.sh")]
    [InlineData("tools\\script.sh")]
    [InlineData("tools/*.sh")]
    [InlineData("")]
    public void NonCanonicalRegisteredPathFails(string path)
    {
        using var fixture = new ProducerInputFixture();
        fixture.WriteRegistration(ProducerInputFixture.LeanRegistrationPath, [path], [ProducerInputFixture.CliProjectPath]);

        AssertRegistrationFailure(fixture.Run("address"), ProducerInputFixture.LeanRegistrationPath);
    }

    [Theory]
    [InlineData("tools/lean-inspector/inspect.sh")]
    [InlineData("tools/lean-inspector/Inspector.lean")]
    [InlineData("tools/StrataLint.Cli/Fixture.cs")]
    [InlineData(ProducerInputFixture.CliProjectPath)]
    public void MissingRegisteredSourceFails(string source)
    {
        using var fixture = new ProducerInputFixture();
        fixture.Remove(source);
        var result = fixture.Run("address");

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Contains(source, Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void MissingInspectorRootIsNotOptional()
    {
        using var fixture = new ProducerInputFixture();
        fixture.RemoveInspectorRoot();
        var result = fixture.Run("address");

        AssertRegistrationFailure(result, ProducerInputFixture.LeanRegistrationPath);
        Assert.Contains("tools/lean-inspector/", Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void UnrelatedScopeDoesNotInvalidateLeanProducer()
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.Append("tools/scripts/workflow/scribe-content-checks.sh", "# Scribe only\n");
        fixture.Write(ProducerInputFixture.ScribeRegistrationPath, "malformed unrelated scope");

        Assert.Equal(before, fixture.Address());
        AssertRegistrationFailure(fixture.Run("scribe-producer-paths"), ProducerInputFixture.ScribeRegistrationPath);
    }

    [Fact]
    public void MetadataOnlyLeanConfigurationDoesNotChangeProducerDigest()
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.Write("lakefile.toml", "name = \"renamed\"\nkeywords = [\"metadata\"]\n");

        Assert.Equal(before, fixture.Address());
    }

    [Theory]
    [InlineData("producer-paths")]
    [InlineData("scribe-producer-paths")]
    public void ScopePathsAreUniqueAndDeterministicallyOrdered(string command)
    {
        using var fixture = new ProducerInputFixture();
        var result = fixture.Run(command);

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        var paths = Lines(result);
        Assert.Equal(paths.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal), paths);
        Assert.Equal(result.StandardOutput, fixture.Run(command).StandardOutput);
    }

    private static void AssertRegistrationFailure(ProcessOutput result, string registration)
    {
        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        var diagnostic = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains("registration", diagnostic);
        Assert.Contains(registration, diagnostic);
    }

    [Fact]
    public void CacheFetcherBytesChangeProducerWithoutChangingLeanInputs()
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();

        fixture.Append(ProducerInputFixture.FetcherPath, "# fetch acceptance changed\n");
        var after = fixture.Address();

        Assert.NotEqual(before[0], after[0]);
        Assert.NotEqual(before[1], after[1]);
        Assert.Equal(before[2..], after[2..]);
    }

    [Fact]
    public void AddressIsIndependentOfCallerWorkingDirectorySdk()
    {
        using var fixture = new ProducerInputFixture();
        var fromRepository = fixture.Run("address");

        var fromForeignSdk = fixture.AddressFromForeignSdkDirectory();

        Assert.Equal(0, fromRepository.ExitCode);
        Assert.Equal(fromRepository.ExitCode, fromForeignSdk.ExitCode);
        Assert.Equal(fromRepository.StandardOutput, fromForeignSdk.StandardOutput);
    }

    [Fact]
    public void AddressConsumesRegisteredBytesWithoutInvokingSdkEvaluation()
    {
        using var fixture = new ProducerInputFixture();
        fixture.Append(ProducerInputFixture.CliProjectPath, "<");
        fixture.Write("global.json", ProducerInputFixture.UnavailableSdk);

        var result = fixture.Run("address");

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("duplicate")]
    [InlineData("reference")]
    [InlineData("material")]
    [InlineData("conflicting-assembly")]
    [InlineData("version")]
    [InlineData("cycle")]
    [InlineData("missing-reference-file")]
    public void InvalidProjectRegistrationBlocksAddress(string defect)
    {
        using var fixture = new ProducerInputFixture();
        if (defect == "missing") fixture.Remove(ProducerInputFixture.ProjectRegistrationPath);
        else if (defect == "missing-reference-file") fixture.Remove(ProducerInputFixture.EngineProjectPath);
        else fixture.EditRegistry(registry =>
        {
            var rows = registry["projects"]!.AsArray();
            if (defect == "duplicate") rows.Add(rows[0]!.DeepClone());
            if (defect == "reference") rows[0]!["references"]!.AsArray().Add("tools/Missing/Missing.csproj");
            if (defect == "material") rows[0]!["include"]!.AsArray().Add("tools/StrataLint.Cli/Missing.cs");
            if (defect == "conflicting-assembly") rows[1]!["assembly"] = rows[0]!["assembly"]!.DeepClone();
            if (defect == "version") registry["version"] = true;
            if (defect == "cycle") rows[4]!["references"]!.AsArray().Add(ProducerInputFixture.CliProjectPath);
        });

        AssertRegistrationFailure(fixture.Run("address"), ProducerInputFixture.ProjectRegistrationPath);
    }

    [Fact]
    public void UnregisteredTrackedProjectBlocksInsteadOfEnlargingSelection()
    {
        using var fixture = new ProducerInputFixture();
        fixture.Write("tools/Neighbor/Neighbor.csproj", "<Project />");
        fixture.Track("tools/Neighbor/Neighbor.csproj");

        var result = fixture.Run("producer-paths");

        AssertRegistrationFailure(result, ProducerInputFixture.ProjectRegistrationPath);
        Assert.Contains("tools/Neighbor/Neighbor.csproj", Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void DeclaredClosureAndExcludeControlInputsWithoutNeighborDiscovery()
    {
        using var fixture = new ProducerInputFixture();
        fixture.Write("tools/StrataLint.Cli/Neighbor.cs", "// untracked neighbor");
        var before = fixture.Address();
        Assert.DoesNotContain("tools/StrataLint.Cli/Neighbor.cs", Lines(fixture.Run("producer-paths")));
        fixture.Track("tools/StrataLint.Cli/Neighbor.cs");
        fixture.EditRegistry(registry => registry["projects"]![0]!["exclude"]!.AsArray().Add("tools/StrataLint.Cli/Neighbor.cs"));
        Assert.DoesNotContain("tools/StrataLint.Cli/Neighbor.cs", Lines(fixture.Run("producer-paths")));
        fixture.EditRegistry(registry =>
        {
            registry["projects"]![0]!["include"] = new JsonArray("tools/StrataLint.Cli/**/*.cs");
            registry["projects"]![0]!["exclude"] = new JsonArray();
        });
        Assert.Contains("tools/StrataLint.Cli/Neighbor.cs", Lines(fixture.Run("producer-paths")));
        Assert.NotEqual(before[1], fixture.Address()[1]);
        before = fixture.Address();
        fixture.Append("tools/Trureturing.Truth/Fixture.cs", "// transitive dependency mutation");
        Assert.NotEqual(before[1], fixture.Address()[1]);
    }

    [Fact]
    public void UnrelatedProjectRowsAndTheirSourcesDoNotChangeSelectedIdentity()
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.EditRegistry(registry => registry["projects"]![2]!["assembly"] = "UnrelatedRenamed");
        fixture.Append("tools/StrataLint.Scribe/Fixture.cs", "// unrelated source");
        fixture.Append(ProducerInputFixture.ProjectRegistrationPath, "\n");

        Assert.Equal(before, fixture.Address());
    }

    [Fact]
    public void HistoricalRegistrationDoesNotSelectCurrentMaterials()
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.EditRegistry(registry =>
        {
            var row = registry["projects"]![2]!.DeepClone();
            row["path"] = "tools/Retired/Retired.csproj";
            row["assembly"] = "Retired";
            row["include"] = new JsonArray("tools/Retired/Absent.cs");
            registry["historical_projects"]!.AsArray().Add(row);
        });
        Assert.Equal(before, fixture.Address());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AddressMatchesIndependentFixturePreimage(bool prebuilt)
    {
        using var fixture = new ProducerInputFixture();
        if (prebuilt) fixture.UsePrebuiltEntrypoint();
        var sources = fixture.ProducerSourceImage();

        var result = fixture.Run("address");

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal(fixture.ExpectedAddressBytes(), result.StandardOutput);
        Assert.Empty(result.StandardError);
        Assert.Equal(sources, fixture.ProducerSourceImage());
    }

    private static string[] Lines(ProcessOutput output) =>
        Encoding.UTF8.GetString(output.StandardOutput).Split('\n', StringSplitOptions.RemoveEmptyEntries);
}
