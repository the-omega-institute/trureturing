using System.Text.Json;

namespace StrataLint.EngineeringScope;

internal sealed record J0ControlContract(
    int SchemaVersion,
    string HeadSha,
    string BaseSha,
    string HeadTreeSha,
    string BaseTreeSha,
    string TargetsDigest,
    string EvaluatorDigest);

internal static class J0ControlSeal
{
    internal static int Write(IReadOnlyList<string> arguments)
    {
        try
        {
            var options = StrictOptions.Parse(
                arguments,
                ["--repository", "--targets", "--evaluator-digest", "--output"]);
            var contract = ReadLive(
                options["--repository"],
                options["--targets"],
                options["--evaluator-digest"]);
            var output = Path.GetFullPath(options["--output"]);
            Directory.CreateDirectory(Path.GetDirectoryName(output)!);
            var temporary = output + ".tmp-" + Environment.ProcessId;
            File.WriteAllBytes(
                temporary,
                JsonSerializer.SerializeToUtf8Bytes(contract, ContractJson.Options));
            File.Move(temporary, output, overwrite: true);
            return 0;
        }
        catch (Exception exception) when (IsInputFailure(exception))
        {
            Console.Error.WriteLine("SELF_LOCK_J0_CONTROL_INVALID " + exception.GetType().Name);
            return 2;
        }
    }

    internal static void Validate(
        string repository,
        string targets,
        string evaluatorDigest,
        string controlPath)
    {
        var control = Path.GetFullPath(controlPath);
        var digest = StrictArtifacts.DigestFile(control);
        if (Path.GetFileName(control) != digest[7..] + ".j0-control.json")
            throw new InvalidDataException("J0 control path is not content addressed");
        var expected = StrictArtifacts.ReadJson<J0ControlContract>(control);
        var actual = ReadLive(repository, targets, evaluatorDigest);
        if (expected != actual)
            throw new InvalidDataException("J0 control inputs changed after sealing");
    }

    private static J0ControlContract ReadLive(
        string repository,
        string targets,
        string evaluatorDigest)
    {
        var root = ProcessTools.RequireRepositoryRoot(repository);
        StrictArtifacts.EnsureDigest(evaluatorDigest, "evaluator digest");
        var contract = new J0ControlContract(
            1,
            ProcessTools.GitText(root, "rev-parse", "HEAD"),
            ProcessTools.GitText(root, "rev-parse", "HEAD^1"),
            ProcessTools.GitText(root, "rev-parse", "HEAD^{tree}"),
            ProcessTools.GitText(root, "rev-parse", "HEAD^1^{tree}"),
            StrictArtifacts.DigestFile(targets),
            evaluatorDigest);
        if (contract.HeadTreeSha != contract.BaseTreeSha)
            throw new InvalidDataException("J0 is not a tree-equal transition");
        return contract;
    }

    private static bool IsInputFailure(Exception exception) => exception is
        IOException or UnauthorizedAccessException or InvalidDataException or JsonException
        or ArgumentException or InvalidOperationException;
}
