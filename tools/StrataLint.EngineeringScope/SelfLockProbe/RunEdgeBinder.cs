using System.Text.Json;

namespace StrataLint.EngineeringScope;

internal sealed record BoundRunEdgeContract(
    int SchemaVersion,
    string TargetMergeSha,
    string LastGreenSha,
    long LastGreenRunId,
    long FirstRedRunId);

internal static class RunEdgeBinder
{
    internal static int Bind(IReadOnlyList<string> arguments)
    {
        try
        {
            var options = StrictOptions.Parse(
                arguments,
                [
                    "--repository", "--target-merge", "--last-green-runs",
                    "--first-red-runs", "--output",
                ]);
            var repository = ProcessTools.RequireRepositoryRoot(options["--repository"]);
            var target = options["--target-merge"];
            StrictArtifacts.EnsureObjectId(target, "target merge");
            var parents = ProcessTools.GitText(
                    repository, "rev-list", "--parents", "-n", "1", target)
                .Split(' ', StringSplitOptions.RemoveEmptyEntries);
            if (parents.Length < 3 || parents[0] != target)
                throw new InvalidDataException("target is not a merge commit");
            var lastGreen = parents[1];
            var greenRun = ReadSingleRun(
                options["--last-green-runs"], lastGreen, "success");
            var redRun = ReadSingleRun(
                options["--first-red-runs"], target, "failure");
            WriteAtomically(
                options["--output"],
                new BoundRunEdgeContract(1, target, lastGreen, greenRun, redRun));
            return 0;
        }
        catch (Exception exception) when (exception is
            IOException or UnauthorizedAccessException or InvalidDataException
            or JsonException or ArgumentException or InvalidOperationException)
        {
            Console.Error.WriteLine("SELF_LOCK_RED_EDGE_INVALID " + exception.GetType().Name);
            return 2;
        }
    }

    private static long ReadSingleRun(string path, string sha, string conclusion)
    {
        var root = StrictArtifacts.ReadJsonElement(path);
        if (root.ValueKind != JsonValueKind.Object
            || !root.TryGetProperty("total_count", out var total)
            || !total.TryGetInt32(out var totalCount)
            || !root.TryGetProperty("workflow_runs", out var runs)
            || runs.ValueKind != JsonValueKind.Array
            || totalCount != 1
            || runs.GetArrayLength() != 1)
        {
            throw new InvalidDataException("workflow run selection is not unique");
        }

        var run = runs[0];
        if (run.ValueKind != JsonValueKind.Object
            || !run.TryGetProperty("id", out var idElement)
            || !idElement.TryGetInt64(out var id)
            || id <= 0
            || ReadString(run, "head_sha") != sha
            || ReadString(run, "event") != "push"
            || ReadString(run, "status") != "completed"
            || ReadString(run, "conclusion") != conclusion)
        {
            throw new InvalidDataException("workflow run is not bound to the required edge");
        }
        return id;
    }

    private static string ReadString(JsonElement value, string name) =>
        value.TryGetProperty(name, out var property)
            && property.ValueKind == JsonValueKind.String
            && property.GetString() is { } text
            ? text
            : throw new InvalidDataException("workflow run field is absent: " + name);

    private static void WriteAtomically(string path, BoundRunEdgeContract value)
    {
        var fullPath = Path.GetFullPath(path);
        Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
        var temporary = fullPath + ".tmp-" + Environment.ProcessId;
        File.WriteAllBytes(
            temporary,
            JsonSerializer.SerializeToUtf8Bytes(value, ContractJson.Options));
        File.Move(temporary, fullPath, overwrite: true);
    }
}
