using System.Formats.Tar;
using System.IO.Compression;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class ColdPreflightContractTests
{
    [Theory]
    [InlineData("push", "filemap")]
    [InlineData("pr", "filemap")]
    [InlineData("push", "none")]
    [InlineData("pr", "none")]
    [InlineData("push", "engineering")]
    public void ColdPreflightSchedulesOnlyRequiredBuild(string mode, string resource)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"], "Evidence/D5/Fixture.result.json");
        Configure(fixture);
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        var start = map.IndexOf("[[files]]", StringComparison.Ordinal);
        var row = map[start..];
        fixture.Write("Meta/FILEMAP.toml", map[..start] + string.Concat(new[] { "*", "Evidence/D5/**/*.result.json", "Meta/**", "docs/**", "tools/**" }.Select(pattern =>
            row.Replace("pattern = \"**\"", "pattern = \"" + pattern + "\"", StringComparison.Ordinal)
                .Replace("require = [\"filemap\"]", pattern == "Evidence/D5/**/*.result.json" ? "require = [\"filemap\"]"
                    : pattern == "docs/**" ? "require = []" : resource == "engineering" && pattern == "tools/**" ? "require = [\"engineering\"]" : "require = []", StringComparison.Ordinal))));
        if (resource == "engineering")
        {
            map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
            fixture.Write("Meta/FILEMAP.toml", map.Replace("  { id = \"filemap\"", "  { id = \"engineering\", stage = \"engineering\", owner = \"tools/scripts/workflow/ci.py\", prerequisites = [\"build\"], tools = [], cache_layers = [], materials = [] },\n  { id = \"filemap\"", StringComparison.Ordinal));
            var mapping = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "Meta/ci-resources.json")))!;
            mapping["resources"]!.AsArray().Add(new JsonObject {
                ["id"] = "engineering", ["projects"] = new JsonArray(ResourceRouteTests.ResourceFixture.Foo),
                ["checks"] = new JsonArray(CommonExecutionEvidence.EngineeringCheckIds.Order(StringComparer.Ordinal).Select(s => (JsonNode?)JsonValue.Create(s)).ToArray()),
                ["steps"] = new JsonArray("tests") });
            fixture.Write("Meta/ci-resources.json", mapping.ToJsonString());
        }
        fixture.CommitPlan();
        var baseline = fixture.Commit;
        fixture.Write(resource == "none" ? "docs/note.md" : resource == "engineering" ? "tools/Foo/Program.cs" : "Evidence/D5/Fixture.result.json",
            resource == "engineering" ? File.ReadAllText(Path.Combine(fixture.Root, "tools/Foo/Program.cs")) + "\n// changed compiler input\n" : "changed registered input\n");
        fixture.CommitPlan();
        File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.BuildPath));
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.RunnerPath)));
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CliPath)));
        var environment = EnvironmentFor(fixture);
        environment["MODE"] = mode; environment["BASE"] = baseline;
        var result = SharedBuildContractTests.Process(fixture.Root, "/bin/bash", ["tools/scripts/preflight.sh"], environment, TestBudgets.WorkflowProcessHangGuard);
        ReleaseConsumerContractTests.Capture(fixture.Root, "cold-" + mode + "-" + resource, result);
        var root = fixture.Root;
        if (mode == "pr")
        {
            var bundle = result.Text.Split('\n').Single(line => line.StartsWith("PREFLIGHT_ARTIFACT bundle=", StringComparison.Ordinal))["PREFLIGHT_ARTIFACT bundle=".Length..];
            root = Path.Combine(fixture.Root, "build/retained");
            Directory.CreateDirectory(root);
            using var input = new GZipStream(File.OpenRead(bundle), CompressionMode.Decompress);
            TarFile.ExtractToDirectory(input, root, overwriteFiles: false);
            ReleaseConsumerContractTests.Capture(root, "cold-pr-" + resource + "-candidate", result);
        }
        var events = File.Exists(environment["CONTRACT_EVENTS"]) ? File.ReadAllLines(environment["CONTRACT_EVENTS"]) : [];
        if (resource == "none")
        {
            Assert.True(result.Exit == 0, result.Text);
            Assert.Empty(events);
            Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.BuildPath)));
        }
        else
        {
            Assert.True(result.Exit == (resource == "engineering" ? 2 : 0), result.Text);
            Assert.Equal(1, events.Count(s => s == "bootstrap-build"));
            Assert.Equal(1, events.Count(s => s.StartsWith("build " + ResourceRouteTests.ResourceFixture.Foo + " ", StringComparison.Ordinal)));
            Assert.Equal(1, events.Count(s => s.StartsWith("restore " + ResourceRouteTests.ResourceFixture.Foo + " ", StringComparison.Ordinal)));
            Assert.True(File.Exists(Path.Combine(root, CommonExecutionEvidence.BuildPath)));
            if (resource == "engineering")
            {
                // Stop at the actual engineering test executor: this fixture registers
                // no CI tests. It verifies build ownership without faking test/proof green.
                Assert.Contains("STAGE_PROCESS", result.Text, StringComparison.Ordinal);
                Assert.Equal("failed", Read(root, "engineering-result.json")["status"]!.ToString());
                Assert.DoesNotContain("filemap", events);
                return;
            }
            Assert.Single(events, s => s == CommonExecutionEvidence.CliPath + " filemap-conform");
            var current = Read(root, "current.json");
            Assert.Equal(Read(root, "build.json")["round"]!.ToString(), current["round"]!.ToString());
            Assert.Equal("filemap", Assert.Single(current["steps"]!.AsArray())!["name"]!.ToString());
            Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.ReportPath)));
        }
        Assert.Equal("not-required", Read(root, "engineering-result.json")["status"]!.ToString());
        Assert.Empty(Read(root, "engineering-result.json")["steps"]!.AsArray());
    }

    internal static void Configure(ResourceRouteTests.ResourceFixture fixture)
    {
        foreach (var path in new[] { "tools/scripts/preflight.sh", "tools/scripts/ci-stage.sh" })
            fixture.Write(path, File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), path)));
        // Explicit external adapters: empty seed preparation, supervisor pass-through,
        // and the bootstrap runner location. None supplies a build acceptance receipt.
        fixture.Write("tools/scripts/report/dotnet_producer.py", "import pathlib,sys\np=pathlib.Path(sys.argv[2])/'build/judge-seed/seed.targets'\np.parent.mkdir(parents=True,exist_ok=True)\np.write_text('<Project />')\n");
        fixture.Write("tools/scripts/report/report-supervisor.sh", "while [[ $1 != -- ]]; do shift; done\nshift\nexec \"$@\"\n");
        fixture.Write("NuGet.Config", "<configuration><packageSources><clear /></packageSources></configuration>\n");
        fixture.Write(ResourceRouteTests.ResourceFixture.Foo, """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
            <AssemblyName>StrataLint</AssemblyName><OutputType>Exe</OutputType>
            <BaseOutputPath>../StrataLint.Cli/bin/</BaseOutputPath>
            <RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup></Project>
            """);
        fixture.Write("tools/Foo/packages.lock.json", "{\"version\":1,\"dependencies\":{\"net10.0\":{}}}\n");
        fixture.Write("tools/Foo/Program.cs", """
            if (args.Length != 1 || args[0] != "filemap-conform") return 91;
            System.IO.File.AppendAllText("build/launched", "dotnet filemap-conform\n");
            System.Console.WriteLine("fixture filemap check reached");
            return 0;
            """);
        var registry = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path)))!;
        registry["projects"]!.AsArray().Single(p => p!["path"]!.ToString() == ResourceRouteTests.ResourceFixture.Foo)!["assembly"] = "StrataLint";
        fixture.Write(EngineeringRegistrationFixture.Path, registry.ToJsonString());
    }

    internal static Dictionary<string, string> EnvironmentFor(ResourceRouteTests.ResourceFixture fixture)
    {
        var bin = Path.Combine(fixture.Root, "build/cold-bin");
        Directory.CreateDirectory(bin);
        var realDotnet = SharedBuildContractTests.Process(fixture.Root, "/bin/bash", ["-c", "command -v dotnet"]).Text.Trim();
        File.WriteAllText(Path.Combine(bin, "dotnet"), """
            #!/bin/bash
            set -euo pipefail
            runner=tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll
            if [[ "$1" == "$runner" ]]; then shift; exec "$CONTRACT_NATIVE" "$@"; fi
            if [[ "${2:-}" == tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj ]]; then
              printf 'bootstrap-%s\n' "$1" >> "$CONTRACT_EVENTS"
              if [[ "$1" == build ]]; then mkdir -p "$(dirname "$runner")"; printf 'native runner location adapter\n' > "$runner"; fi
              exit 0
            fi
            printf '%s\n' "$*" >> "$CONTRACT_EVENTS"
            exec "$CONTRACT_DOTNET" "$@"
            """);
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(Path.Combine(bin, "dotnet"), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        return new() { ["PATH"] = bin + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"),
            ["CONTRACT_NATIVE"] = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope"),
            ["CONTRACT_DOTNET"] = realDotnet, ["CONTRACT_EVENTS"] = Path.Combine(fixture.Root, "build/cold-events"),
            ["CI_PLAN_PATH"] = "", ["CI_CHANGES_PATH"] = "", ["CI_PLAN_B64"] = "", ["CI_CHANGES_B64"] = "",
            ["CI_BUILD_ROUND"] = "", ["CANDIDATE_SHA"] = "", ["GITHUB_EVENT_NAME"] = "", ["CI_NEEDS"] = "{}", ["CI_WORKFLOW_INPUTS"] = "null" };
    }

    private static JsonNode Read(string root, string file) => JsonNode.Parse(File.ReadAllText(Path.Combine(root, "build/ci", file)))!;
}
