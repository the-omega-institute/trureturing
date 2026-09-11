using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;

namespace StrataLint.Tests;

public sealed partial class LeanReportInputScriptTests
{
    internal static void WritePairInputRegistration(string repository, params string[] producerPaths)
    {
        var meta = Path.Combine(repository, "Meta");
        Directory.CreateDirectory(meta);
        File.WriteAllText(Path.Combine(meta, "FILEMAP.toml"), """
            schema_version = 2
            [residence_policy]
            case_id = "RESIDENCE-EPOCH"
            desired = "data-must-live-outside-tools"
            known_violation_count = 0
            status = "closed"

            """ + "\n" + LeanReportInputFixture.Registration + "\n");
        object Input(string pattern) => new
            { patterns = new[] { pattern }, exclude = Array.Empty<string>(), optional_root = (string?)null, min_matches = 1 };
        object Scope(string name, string[] includes, params object[] inputs) => new { name, includes, inputs };
        File.WriteAllText(Path.Combine(meta, "LeanInputs.json"), JsonSerializer.Serialize(new
        {
            schema_version = 1,
            scopes = new[]
            {
                Scope("managed-modules", [], Input("Trureturing.lean"), Input("D5/**/*.lean")),
                Scope("inspector-lean", [], Input("tools/lean-inspector/Inspector.lean")),
                Scope("lean-sources", ["managed-modules", "inspector-lean"]),
                Scope("lean-dependencies", [], Input("lean-toolchain"), Input("lake-manifest.json")),
                Scope("lean-config", ["lean-dependencies"], Input("lakefile.toml")),
                Scope("producer", ["inspector-lean"],
                    new[] { "Meta/FILEMAP.toml", "Meta/LeanInputs.json" }.Concat(producerPaths).Select(Input).ToArray()),
            },
        }) + "\n");
    }

    [Theory]
    [InlineData("producer-paths")]
    [InlineData("scribe-producer-paths")]
    public void NativeProducerIncludesCacheWriter(string command)
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("bash",
            [Path.Combine(root, InputHelperPath), command, "--repository", root],
            root, StrataLint.Engine.BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Contains("tools/scripts/worktree/lean-cache-run.sh", Lines(result));
    }

    [Fact]
    public void CacheWriterEditInvalidatesAddressAndReportReuseAndAbsenceNamesInput()
    {
        using var fixture = new LeanReportInputFixture();
        const string launcher = "tools/scripts/worktree/lean-cache-run.sh";
        fixture.WriteSource(launcher, "#!/usr/bin/env bash\nexec \"$@\"\n");
        fixture.RegisterProducerInput(launcher);
        var before = Fields(fixture.RunCommand("address"));
        Assert.Equal(0, fixture.CaptureProductionInput().ExitCode);
        Assert.Equal(0, fixture.Verify().ExitCode);
        fixture.CreateDeltaBaseline();
        Assert.Equal("reuse", fixture.DeltaPlanStatus());

        fixture.Append(launcher, "# changed launcher\n");
        var after = Fields(fixture.RunCommand("address"));
        Assert.NotEqual(before[0], after[0]);
        Assert.NotEqual(before[1], after[1]);
        Assert.Equal(before[2..], after[2..]);
        Assert.Equal(2, fixture.Verify().ExitCode);
        Assert.Equal("fallback", fixture.DeltaPlanStatus());

        fixture.RemoveSource(launcher);
        var absent = fixture.RunCommand("address");
        Assert.Equal(2, absent.ExitCode);
        Assert.Empty(absent.StandardOutput);
        Assert.Contains(launcher, Encoding.UTF8.GetString(absent.StandardError));
    }

    [Theory]
    [InlineData("address")]
    [InlineData("producer-paths")]
    [InlineData("scribe-producer-paths")]
    [InlineData("modules")]
    public void MissingInputRegistrationNamesTheObject(string command)
    {
        using var fixture = new LeanReportInputFixture();
        fixture.RemoveSource("Meta/FILEMAP.toml");
        var result = fixture.RunCommand(command);
        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Contains("Meta/FILEMAP.toml", Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("missing-scope", "producer")]
    [InlineData("duplicate-scope", "producer")]
    [InlineData("duplicate-registration", "LeanInputManifest")]
    public void ConflictingOrMissingInputScopeFailsBeforeAddress(string defect, string expected)
    {
        using var fixture = new LeanReportInputFixture();
        fixture.BreakRegistration(defect);
        var result = fixture.RunCommand("address");
        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Contains(expected, Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void RegistrationChangeRejectsProducerBaselineReuse()
    {
        using var fixture = new LeanReportInputFixture();
        fixture.CreateDeltaBaseline();
        Assert.Equal("reuse", fixture.DeltaPlanStatus());
        fixture.RegisterProducerInput("tools/StrataLint.Scribe/Emission/FixtureEmitter.cs");
        Assert.Equal("fallback", fixture.DeltaPlanStatus());
    }

    private sealed partial class LeanReportInputFixture
    {
        internal const string Registration = """
            [[files]]
            pattern = "Meta/LeanInputs.json"
            kind = "program"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["LeanInputManifest"]
            verified_by = ["LeanInputManifest"]
            artifact_id = "LeanInputManifest"
            runtime_disposition = "committed-source"
            """;

        private static object Input(string[] patterns, string? optionalRoot = null,
            int minimum = 1, string[]? exclude = null) => new
            { patterns, exclude = exclude ?? [], optional_root = optionalRoot, min_matches = minimum };

        private void WriteRegistration()
        {
            Write("Meta/FILEMAP.toml", """
                schema_version = 2
                [residence_policy]
                case_id = "RESIDENCE-EPOCH"
                desired = "data-must-live-outside-tools"
                known_violation_count = 0
                status = "closed"

                """ + "\n" + Registration + "\n");
            object Scope(string name, string[] includes, params object[] inputs) => new { name, includes, inputs };
            string[] producer =
            [
                "tools/StrataLint.Cli/**/*.cs", "tools/StrataLint.Engine/**/*.cs", "tools/Trureturing.Truth/**/*.cs",
                CliProjectPath, EngineProjectPath, TruthProjectPath,
                "Directory.Build.props", "Directory.Packages.props", "global.json",
                "Meta/FILEMAP.toml", "Meta/LeanInputs.json", InputHelperPath, PairScriptPath, SupervisorScriptPath, CiBaselineScriptPath,
                CacheEnsureScriptPath, CachePublishScriptPath, "tools/scripts/worktree/lean-cache-input.sh",
                ResourceObservationLibraryPath, ToolchainInstallerPath, JudgeContentAddressPath,
                ScribeContentChecksPath, WorkflowPath, EngineLockPath, CliLockPath, TruthLockPath,
            ];
            Write("Meta/LeanInputs.json", JsonSerializer.Serialize(new
            {
                schema_version = 1,
                scopes = new[]
                {
                    Scope("managed-modules", [], Input(["Trureturing.lean"]), Input(["D5/**/*.lean"])),
                    Scope("inspector-lean", [], Input(["tools/lean-inspector/**/*.lean"], "tools/lean-inspector")),
                    Scope("lean-sources", ["managed-modules", "inspector-lean"]),
                    Scope("lean-dependencies", [], Input(["lean-toolchain"]), Input(["lake-manifest.json"])),
                    Scope("lean-config", ["lean-dependencies"], Input(["lakefile.toml", "lakefile.lean"])),
                    Scope("producer", ["inspector-lean"], producer.Select(path => Input([path])).Concat(new[]
                    {
                        Input(["tools/lean-inspector/inspect.sh"], "tools/lean-inspector"),
                        Input(["tools/lean-inspector/source-context.sh"], "tools/lean-inspector"),
                    }).ToArray()),
                    Scope("scribe-producer", ["producer"], Input(["tools/StrataLint.Scribe/**/*.cs"]),
                        Input(["Blueprint/**/*.scribe.cs"]), Input([ScribeProjectPath, DocumentsProjectPath,
                            ScribeLockPath, DocumentsLockPath])),
                },
            }) + "\n");
        }

        internal void RegisterProducerInput(string path)
        {
            var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(repository, "Meta/LeanInputs.json")))!;
            var scope = manifest["scopes"]!.AsArray().Single(item => item!["name"]!.GetValue<string>() == "producer")!;
            scope["inputs"]!.AsArray().Add(JsonSerializer.SerializeToNode(Input([path])));
            Write("Meta/LeanInputs.json", manifest.ToJsonString() + "\n");
        }

        internal void BreakRegistration(string defect)
        {
            if (defect == "duplicate-registration")
            {
                Append("Meta/FILEMAP.toml", "\n" + Registration.Replace("Meta/LeanInputs.json", "Meta/OtherInputs.json") + "\n");
                return;
            }
            var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(repository, "Meta/LeanInputs.json")))!;
            var scopes = manifest["scopes"]!.AsArray();
            var producer = scopes.Single(item => item!["name"]!.GetValue<string>() == "producer")!;
            if (defect == "missing-scope") scopes.Remove(producer);
            else scopes.Add(producer.DeepClone());
            Write("Meta/LeanInputs.json", manifest.ToJsonString() + "\n");
        }
    }
}
