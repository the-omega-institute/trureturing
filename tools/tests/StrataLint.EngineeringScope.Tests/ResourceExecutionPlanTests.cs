using System.Text.Json;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class ResourceExecutionPlanTests
{
    [Fact]
    public void ForgedCandidateIsRejectedBeforeStageExecution()
    {
        var root = RepositoryRoot();
        var path = Path.GetTempFileName();
        try
        {
            File.WriteAllText(path, JsonSerializer.Serialize(new { schema_version = 1, status = "planned",
                candidate = new { commit = new string('a', 40), tree = new string('b', 40) }, resources = Array.Empty<string>(),
                stages = Stages() }));
            Assert.Throws<InvalidDataException>(() => ResourceExecutionPlan.Load(root, path));
        }
        finally { File.Delete(path); }
    }

    [Fact]
    public void ResourceSubsetMustContainRegisteredPrerequisites()
    {
        var root = RepositoryRoot();
        var path = Path.GetTempFileName();
        try
        {
            var commit = Git(root, "rev-parse", "HEAD");
            var tree = Git(root, "rev-parse", "HEAD^{tree}");
            File.WriteAllText(path, JsonSerializer.Serialize(new { schema_version = 1, status = "planned",
                candidate = new { commit, tree }, resources = new[] { "filemap" },
                stages = Stages(("current", new[] { "filemap" }, "required"), ("build", Array.Empty<string>(), "not-required")) }));
            Assert.Throws<InvalidDataException>(() => ResourceExecutionPlan.Load(root, path));
        }
        finally { File.Delete(path); }
    }

    private static object Stages(params (string stage, string[] resources, string status)[] overrides)
    {
        var rows = new Dictionary<string, object>(StringComparer.Ordinal)
        {
            ["build"] = new { resources = Array.Empty<string>(), status = "not-required" },
            ["engineering"] = new { resources = Array.Empty<string>(), status = "not-required" },
            ["current"] = new { resources = Array.Empty<string>(), status = "not-required" },
            ["delta"] = new { resources = Array.Empty<string>(), status = "not-applicable" },
        };
        foreach (var (stage, resources, status) in overrides) rows[stage] = new { resources, status };
        return rows;
    }

    private static string Git(string root, params string[] args)
    {
        var start = new System.Diagnostics.ProcessStartInfo("git")
        {
            WorkingDirectory = root, RedirectStandardOutput = true, UseShellExecute = false,
        };
        start.ArgumentList.Add("--no-replace-objects");
        foreach (var arg in args) start.ArgumentList.Add(arg);
        var process = System.Diagnostics.Process.Start(start)!;
        process.WaitForExit();
        return process.StandardOutput.ReadToEnd().Trim();
    }

    private static string RepositoryRoot()
    {
        var path = Directory.GetCurrentDirectory();
        while (!Directory.Exists(Path.Combine(path, ".git")) && Directory.GetParent(path) is { } parent)
            path = parent.FullName;
        return path;
    }
}
