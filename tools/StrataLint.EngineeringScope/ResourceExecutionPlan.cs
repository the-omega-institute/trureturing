using System.Diagnostics;
using System.Text.Json;

namespace StrataLint.EngineeringScope;

internal sealed record ResourcePlanBinding(string Plan, string Changes);

/// <summary>The light planner owns scope and resource validation; native code consumes its exact result.</summary>
internal sealed class ResourceExecutionPlan
{
    internal JsonElement Document { get; }
    internal string Commit => Document.GetProperty("candidate").GetProperty("commit").GetString()!;
    internal string[] Projects => Strings(Document.GetProperty("execution").GetProperty("projects"));
    internal string[] CheckUnits => Strings(Document.GetProperty("execution").GetProperty("checks"));
    internal string[] CurrentSteps => Strings(Document.GetProperty("execution").GetProperty("steps"));
    internal string PlanPath { get; }
    internal string ChangesPath { get; }
    private ResourceExecutionPlan(JsonElement document, string plan, string changes)
    { Document = document; PlanPath = plan; ChangesPath = changes; }
    internal bool StageRequired(string stage) => Document.GetProperty("stages").GetProperty(stage).GetProperty("status").GetString() == "required";

    internal static ResourceExecutionPlan? Load(string root, string? path, string? changes = null)
    {
        if (path is null && changes is null) return null;
        if (path is null || changes is null) throw new InvalidDataException("--plan requires the exact --changes scope input");
        path = Path.GetFullPath(path, root);
        changes = Path.GetFullPath(changes, root);
        var commit = Run(root, "git", ["--no-replace-objects", "rev-parse", "HEAD"]).Trim();
        var validated = Run(root, "python3", ["-B", "tools/scripts/workflow/ci.py", "validate-plan",
            "--repository", root, "--commit", commit, "--changes", changes, "--plan", path]);
        using var document = JsonDocument.Parse(validated);
        return new(document.RootElement.Clone(), path, changes);
    }

    internal ResourcePlanBinding Retain(string root)
    {
        const string plan = CommonExecutionEvidence.RootPath + "/resource-plan.json";
        const string changes = CommonExecutionEvidence.RootPath + "/resource-scope.json";
        foreach (var (source, destination) in new[] { (PlanPath, plan), (ChangesPath, changes) })
        {
            var target = Path.Combine(root, destination);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            if (Path.GetFullPath(source) != target) File.Copy(source, target, overwrite: true);
        }
        return new(plan, changes);
    }

    internal static string[] Strings(JsonElement array) => array.EnumerateArray().Select(item => item.GetString()!).ToArray();
    internal static string Run(string root, string executable, string[] arguments)
        => new System.Text.UTF8Encoding(false, true).GetString(RunBytes(root, executable, arguments));

    private static byte[] RunBytes(string root, string executable, string[] arguments)
    {
        var start = new ProcessStartInfo(executable) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
        foreach (var argument in arguments) start.ArgumentList.Add(argument);
        using var process = Process.Start(start) ?? throw new IOException("cannot start " + executable);
        using var bytes = new MemoryStream();
        var stdout = process.StandardOutput.BaseStream.CopyToAsync(bytes);
        var stderr = process.StandardError.ReadToEndAsync();
        process.WaitForExit();
        stdout.GetAwaiter().GetResult();
        if (process.ExitCode != 0) throw new InvalidDataException(executable + " validation failed: " + stderr.GetAwaiter().GetResult().Trim());
        return bytes.ToArray();
    }
}
