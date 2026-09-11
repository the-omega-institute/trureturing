using System.Diagnostics;
using System.Text.Json;

namespace StrataLint.EngineeringScope;

/// <summary>Validated output of tools/scripts/workflow/ci.py plan.</summary>
internal sealed class ResourceExecutionPlan
{
    private static readonly IReadOnlyDictionary<string, string[]> Prerequisites =
        new Dictionary<string, string[]>(StringComparer.Ordinal)
        {
            ["build"] = [], ["engineering"] = ["build"], ["filemap"] = ["build"],
            ["lean"] = ["build"], ["lean-report"] = ["lean"], ["scribe"] = ["build", "lean-report"],
            ["current"] = ["build", "lean-report"], ["delta"] = ["current", "engineering", "filemap", "scribe"],
        };

    internal string Commit { get; }
    internal IReadOnlySet<string> Resources { get; }
    internal IReadOnlyDictionary<string, string> StageStatus { get; }

    private ResourceExecutionPlan(string commit, IReadOnlySet<string> resources,
        IReadOnlyDictionary<string, string> stageStatus)
    {
        Commit = commit; Resources = resources; StageStatus = stageStatus;
    }

    internal bool Has(string id) => Resources.Contains(id);

    internal bool StageRequired(string stage) =>
        StageStatus.TryGetValue(stage, out var status) && status == "required";

    internal static ResourceExecutionPlan? Load(string root, string? path)
    {
        if (path is null) return null;
        var full = Path.GetFullPath(path);
        using var document = JsonDocument.Parse(File.ReadAllText(full));
        var node = document.RootElement;
        if (node.ValueKind != JsonValueKind.Object || node.GetProperty("schema_version").GetInt32() != 1
            || node.GetProperty("status").GetString() != "planned")
            throw new InvalidDataException("resource plan is not a validated planned result");
        var candidate = node.GetProperty("candidate");
        var commit = candidate.GetProperty("commit").GetString();
        var tree = candidate.GetProperty("tree").GetString();
        if (!IsSha(commit, 40) || !IsSha(tree, 40)) throw new InvalidDataException("resource plan candidate identity is malformed");
        var actualCommit = Git(root, "rev-parse", "HEAD");
        var actualTree = Git(root, "rev-parse", "HEAD^{tree}");
        if (!StringComparer.Ordinal.Equals(commit, actualCommit) || !StringComparer.Ordinal.Equals(tree, actualTree))
            throw new InvalidDataException("resource plan candidate does not match the checked out commit/tree");

        var resources = new HashSet<string>(StringComparer.Ordinal);
        foreach (var item in node.GetProperty("resources").EnumerateArray())
        {
            var id = item.GetString() ?? throw new InvalidDataException("resource plan contains a null resource");
            if (!Prerequisites.ContainsKey(id) || !resources.Add(id)) throw new InvalidDataException("unknown or duplicate planned resource: " + id);
        }
        foreach (var id in resources)
            foreach (var prerequisite in Prerequisites[id])
                if (!resources.Contains(prerequisite)) throw new InvalidDataException($"resource plan omits prerequisite {prerequisite} for {id}");

        var status = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var stage in new[] { "build", "engineering", "current", "delta" })
        {
            var row = node.GetProperty("stages").GetProperty(stage);
            var value = row.GetProperty("status").GetString();
            if (value is not ("required" or "not-required" or "not-applicable"))
                throw new InvalidDataException("invalid resource stage status: " + stage);
            status.Add(stage, value);
            var declared = row.GetProperty("resources").EnumerateArray().Select(v => v.GetString()!).ToArray();
            var expected = resources.Where(id => ResourceStage(id) == stage).Order(StringComparer.Ordinal).ToArray();
            if (!declared.SequenceEqual(expected) || (value == "required") != (expected.Length != 0))
                throw new InvalidDataException("resource stage declaration disagrees with resource closure: " + stage);
        }
        return new ResourceExecutionPlan(commit!, resources, status);
    }

    private static string ResourceStage(string id) => id switch
    {
        "build" => "build", "engineering" => "engineering", "delta" => "delta", _ => "current"
    };

    private static bool IsSha(string? value, int length) => value is not null && value.Length == length && value.All(char.IsAsciiHexDigit);

    private static string Git(string root, params string[] args)
    {
        var start = new ProcessStartInfo("git") { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true };
        start.ArgumentList.Add("--no-replace-objects");
        foreach (var arg in args) start.ArgumentList.Add(arg);
        using var process = Process.Start(start) ?? throw new IOException("cannot start git");
        var output = process.StandardOutput.ReadToEnd();
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        if (process.ExitCode != 0) throw new InvalidDataException(error.Trim());
        return output.Trim();
    }
}
