using System.Text;
using System.Text.Json.Nodes;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed class FileMapPlanningFixture : IDisposable
{
    private readonly string scratch = TemporaryFileSystem.Directory.CreateTempSubdirectory("filemap-plan-").FullName;
    internal string Root => Path.Combine(scratch, "repository");
    internal string Manifest => Path.Combine(scratch, "changes.json");
    internal string Plan => Path.Combine(scratch, "plan.json");
    internal string Result => Path.Combine(scratch, "result.json");
    private string Bin => Path.Combine(scratch, "bin");
    internal string Calls => Path.Combine(scratch, "calls");
    internal string Commit => Git("rev-parse", "HEAD").Trim();
    internal static JsonObject Canonical => JsonNode.Parse(TestRepositoryLayout.ReadAllText(
        RepositoryRelativePath.Create("tools/tests/StrataLint.Tests/Commands/FileMapPlanning/canonical.json")))!.AsObject();

    internal FileMapPlanningFixture(string? filemap = null)
    {
        TemporaryFileSystem.Directory.CreateDirectory(Root);
        TemporaryFileSystem.Directory.CreateDirectory(Bin);
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
        foreach (var name in new[] { "dotnet", "lake", "elan", "cache", "curl" })
            Executable(name, "#!/bin/sh\nprintf '%s\\n' invoked >> \"$PLAN_CALLS\"\nexit 97\n");
        // Only pinned candidate object operations are allowed. A parent lookup,
        // remote access, or expensive operation must be observable even if ignored.
        Executable("git", """
            #!/bin/sh
            for arg do
              case "$arg" in *HEAD*|*^1*|fetch|remote|ls-remote|merge-base)
                printf 'forbidden-git:%s\n' "$arg" >> "$PLAN_CALLS"; exit 98 ;;
              esac
            done
            exec "$PLAN_REAL_GIT" "$@"
            """ + "\n");
    }

    private void Executable(string name, string source)
    {
        var path = Path.Combine(Bin, name);
        TemporaryFileSystem.File.WriteAllText(path, source);
        var result = Run("chmod", ["+x", path]);
        Assert.Equal(0, result.ExitCode);
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

    internal JsonObject Changes(params string[] paths)
    {
        foreach (var path in paths) Write(path, "candidate\n");
        if (paths.Length > 0) Save();
        var entries = new JsonArray();
        foreach (var path in paths)
            entries.Add(new JsonObject { ["status"] = "A", ["old"] = null,
                ["new"] = Endpoint(path) });
        return new JsonObject { ["schema_version"] = 1, ["mode"] = "current",
            ["candidate"] = new JsonObject { ["commit"] = Commit, ["tree"] = Git("rev-parse", "HEAD^{tree}").Trim() },
            ["base"] = null, ["head"] = null, ["complete"] = true,
            ["change_count"] = entries.Count, ["changes"] = entries };
    }

    internal JsonObject Endpoint(string path) => new() { ["path"] = path, ["mode"] = "100644",
        ["oid"] = Git("rev-parse", "HEAD:" + path).Trim() };
    internal void Supply(JsonObject manifest) => TemporaryFileSystem.File.WriteAllText(Manifest, manifest.ToJsonString());

    internal ProcessOutput Cli(string command, params string[] args)
    {
        var realGit = Encoding.UTF8.GetString(Run("/bin/sh", ["-c", "command -v git"]).StandardOutput).Trim();
        return Run("/usr/bin/env", ["PATH=" + Bin + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"),
            "PLAN_CALLS=" + Calls, "PLAN_REAL_GIT=" + realGit, "PYTHONDONTWRITEBYTECODE=1",
            "python3", "-B", Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/workflow/ci.py"),
            command, "--repository", Root, .. args]);
    }

    internal ProcessOutput MakePlan(string? commit = null) => Cli("plan", "--commit", commit ?? Commit,
        "--changes", Manifest, "--output", Plan);
    internal ProcessOutput NoWork(string? stage = null) => Cli("no-work", ["--commit", Commit,
        "--changes", Manifest, "--plan", Plan, "--output", Result,
        .. (stage is null ? Array.Empty<string>() : new[] { "--stage", stage })]);
    internal static string Text(ProcessOutput result) => Encoding.UTF8.GetString(result.StandardOutput)
        + Encoding.UTF8.GetString(result.StandardError);
    internal static JsonObject Read(string path) => JsonNode.Parse(TemporaryFileSystem.File.ReadAllText(path))!.AsObject();
    internal void AssertNoTools() => Assert.False(TemporaryFileSystem.File.Exists(Calls),
        TemporaryFileSystem.File.Exists(Calls) ? TemporaryFileSystem.File.ReadAllText(Calls) : "");
    private ProcessOutput Run(string executable, string[] args) => TestProcessRunner.Run(executable, args, Root,
        TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
    public void Dispose() => TemporaryFileSystem.Directory.Delete(scratch, recursive: true);
}
