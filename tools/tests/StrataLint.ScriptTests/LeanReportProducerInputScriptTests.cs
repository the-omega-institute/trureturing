using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanReportProducerInputScriptTests
{
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
    [InlineData("ProducerIsolationTests.test_blueprint_only_change_selects_no_report_modules")]
    [InlineData("ProducerIsolationTests.test_metadata_only_change_selects_no_report_modules")]
    [InlineData("ProducerIsolationTests.test_shared_utility_parser_change_invalidates_report_modules")]
    [InlineData("ReportImportTests.test_import_edit_rechecks_dependents_and_updates_reverse_closure")]
    public void ExecutableProducerGraphDrivesRealPlannerInvalidation(string scenario)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            [Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/lean_seed_contract.py"), scenario],
            root, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
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

    [Theory]
    [InlineData("msbuild")]
    [InlineData("sdk")]
    public void AddressFailurePreservesProjectAndRawDiagnostic(string failure)
    {
        using var fixture = new ProducerInputFixture();
        if (failure == "msbuild") fixture.Append(ProducerInputFixture.CliProjectPath, "<");
        else fixture.Write("global.json", ProducerInputFixture.UnavailableSdk);
        var raw = fixture.EvaluateCliProject();
        Assert.NotEqual(0, raw.ExitCode);
        Assert.NotEmpty(raw.StandardOutput.Concat(raw.StandardError));

        var result = fixture.Run("address");

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        var diagnostic = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains(fixture.CliProject, diagnostic, StringComparison.Ordinal);
        foreach (var stream in new[] { raw.StandardOutput, raw.StandardError })
        {
            if (stream.Length > 0)
                Assert.Contains(Encoding.UTF8.GetString(stream), diagnostic, StringComparison.Ordinal);
        }
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
