using System.Text;
using System.Text.Json.Nodes;
using System.Text.Json;
using StrataLint.Engine;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Tests;

internal sealed class FileMapPlanningFixture : IDisposable
{
    private readonly string scratch = TemporaryFileSystem.Directory.CreateTempSubdirectory("filemap-plan-").FullName;
    internal string Root => Path.Combine(scratch, "repository");
    internal string Manifest => Path.Combine(scratch, "changes.json");
    internal string Plan => Path.Combine(scratch, "plan.json");
    internal string Result => Path.Combine(scratch, "result.json");
    internal string Commit => Git("rev-parse", "HEAD").Trim();
    internal static JsonObject Canonical => JsonNode.Parse(TestRepositoryLayout.ReadAllText(
        RepositoryRelativePath.Create("tools/tests/StrataLint.Tests/Commands/FileMapPlanning/canonical.json")))!.AsObject();

    internal FileMapPlanningFixture(string? filemap = null)
    {
        TemporaryFileSystem.Directory.CreateDirectory(Root);
        var source = filemap ?? Canonical["filemap"]!.GetValue<string>();
        const string materials = "\"Meta/ci-checks.json\", \"Meta/ci-resources.json\", \"Meta/engineering-projects.json\"";
        source = source.Replace("materials = []", "materials = [" + materials + "]", StringComparison.Ordinal)
            .Replace("materials = [\"tools/", "materials = [" + materials + ", \"tools/", StringComparison.Ordinal);
        const string row = """
            [[files]]
            pattern = "Meta/*.json"
            require = ["engineering"]
            kind = "program"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["reader"]
            verified_by = ["dotnet-test"]
            artifact_id = "none"
            runtime_disposition = "committed-source"

            """;
        source = source.Replace("[[files]]\npattern = \"Meta/FILEMAP.toml\"", row + "\n[[files]]\npattern = \"Meta/FILEMAP.toml\"", StringComparison.Ordinal);
        Write("Meta/FILEMAP.toml", source);
        const string project = "tools/Fixture/Fixture.csproj";
        Write(project, "<Project />");
        Write(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(
            new EngineeringProjectFixture(project, "Fixture", "test-support", false, [])));
        Write("Meta/ci-checks.json", CommonCheckRegistrationFixture.Manifest(project));
        Write("Meta/ci-resources.json", JsonSerializer.Serialize(new { schema = "ci-resource-execution-v1",
            resources = new[] {
                new { id = "build", projects = new[] { project }, checks = Array.Empty<string>(), steps = Array.Empty<string>() },
                new { id = "engineering", projects = new[] { project }, checks = Array.Empty<string>(), steps = Array.Empty<string>() },
                new { id = "filemap", projects = new[] { project }, checks = new[] { "filemap" }, steps = new[] { "filemap" } },
                new { id = "lean-report", projects = new[] { project }, checks = Array.Empty<string>(), steps = new[] { "lean-report" } },
            } }));
        Write("README.md", "reference\n");
        Write("tools/owner.py", "# synthetic declared operation owner\n");
        Git("init", "-q");
        Git("config", "user.name", "Fixture");
        Git("config", "user.email", "fixture@example.invalid");
        Save();

    }

    internal static FileMapPlanningFixture LibraryPolicy()
    {
        var library = new TomlTable
        {
            ["pattern"] = "Library/*/*.md", ["require"] = new TomlArray { "filemap", "scribe" },
            ["kind"] = "data", ["admission_plane"] = "content", ["produced_by"] = "none",
            ["consumed_by"] = new TomlArray { "reader" }, ["verified_by"] = new TomlArray { "LibraryNoteCatalog" },
            ["artifact_id"] = "none", ["runtime_disposition"] = "committed-source",
        };
        var map = TomlSerializer.Deserialize<TomlTable>(Canonical["filemap"]!.GetValue<string>())!;
        ((TomlTableArray)map["files"]).Insert(1, library);
        ((TomlArray)map["resources"]).Add(new TomlTable
        {
            ["id"] = "scribe", ["stage"] = "current", ["owner"] = "tools/owner.py",
            ["prerequisites"] = new TomlArray { "build" }, ["tools"] = new TomlArray { "dotnet" },
            ["cache_layers"] = new TomlArray(), ["cache_activation"] = new TomlTable(), ["materials"] = new TomlArray(),
        });
        var fixture = new FileMapPlanningFixture(TomlSerializer.Serialize(map));
        var resources = Read(Path.Combine(fixture.Root, "Meta/ci-resources.json"));
        resources["resources"]!.AsArray().Add(new JsonObject
        {
            ["id"] = "scribe", ["projects"] = new JsonArray("tools/Fixture/Fixture.csproj"),
            ["checks"] = new JsonArray("scribe-describe", "scribe-markdown", "scribe-projections"),
            ["steps"] = new JsonArray("scribe"),
        });
        fixture.Write("Meta/ci-resources.json", resources.ToJsonString());
        var checks = Read(Path.Combine(fixture.Root, "Meta/ci-checks.json"));
        checks["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "filemap")!["delta_scope"] = JsonNode.Parse("""
            {"whole_tree_inputs":["Meta/FILEMAP.toml","Meta/domains.yaml"],
             "actor_inputs":["**/*.cs"],"inventory_inputs":["Blueprint/**"],"related":[]}
            """);
        fixture.Write("Meta/ci-checks.json", checks.ToJsonString());
        fixture.Write("Meta/domains.yaml", TestFileMap.Domains);
        fixture.Write(".gitignore", "build/\n.sshx-*\n.echo-review.md\n.caller-review-prompt.md\n/Generated/echo-residuals/\n");
        fixture.Save();
        return fixture;
    }

    internal void Write(string path, string text)
    {
        var full = Path.Combine(Root, path);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(full)!);
        TemporaryFileSystem.File.WriteAllText(full, text);
    }

    internal void Save() { Git("add", "."); Git("commit", "-qm", "fixture"); }
    internal string Git(params string[] args)
    {
        var result = Run("git", args);
        Assert.True(result.ExitCode == 0, Text(result));
        return Encoding.UTF8.GetString(result.StandardOutput);
    }

    internal ProcessOutput Cli(string command, params string[] args)
    {
        return Run("/usr/bin/env", [.. CiFixtureEnvironment.LocalAssignments,
            "PYTHONDONTWRITEBYTECODE=1",
            "python3", "-B", Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/workflow/ci.py"),
            command, "--repository", Root, .. args]);
    }

    internal ProcessOutput MakePlan(string? commit = null) => Cli("plan", "--commit", commit ?? Commit,
        "--changes", Manifest, "--output", Plan);
    internal static string Text(ProcessOutput result) => Encoding.UTF8.GetString(result.StandardOutput)
        + Encoding.UTF8.GetString(result.StandardError);
    internal static JsonObject Read(string path) => JsonNode.Parse(TemporaryFileSystem.File.ReadAllText(path))!.AsObject();
    private ProcessOutput Run(string executable, string[] args) => TestProcessRunner.Run(executable, args, Root,
        TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
    public void Dispose() => TemporaryFileSystem.Directory.Delete(scratch, recursive: true);
}
