using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal static class RefactorQuotientCommand
{
    private sealed record Mutation(string Path, string Content);
    private sealed record Observation(string Disposition, ImmutableArray<string> Obligations);

    internal static ExplicitCommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        if (!Pair(arguments, out var casePath, out var output))
            return new(2, string.Empty, "QUOTIENT_INVALID usage: refactor-quotient --case FILE --out FILE\n");
        try
        {
            var caseBytes = File.ReadAllBytes(casePath);
            using var document = JsonDocument.Parse(caseBytes);
            var root = document.RootElement;
            RunHandleJson.RequireFields(root, "case_id", "expected_gate_authority_sha256", "harness_argv",
                "mutations", "obligations", "old_build", "producer_argv", "schema");
            if (root.GetProperty("schema").GetString() != "refactor-quotient-case-v1")
                throw new FormatException("wrong quotient case schema");
            var oldBuild = root.GetProperty("old_build").GetString()!;
            if (oldBuild.Length != 40 || oldBuild.Any(static c => !Uri.IsHexDigit(c)))
                throw new FormatException("old_build must be a 40 digit Git commit");
            var caseId = Required(root, "case_id");
            var authoritySha = RequiredSha(root, "expected_gate_authority_sha256");
            var harness = Argv(root.GetProperty("harness_argv"));
            var producers = root.GetProperty("producer_argv").EnumerateArray().Select(Argv).ToArray();
            var mutations = root.GetProperty("mutations").EnumerateArray().Select(item =>
            {
                RunHandleJson.RequireFields(item, "content", "path");
                return new Mutation(Required(item, "path"), Required(item, "content"));
            }).ToArray();
            var obligations = root.GetProperty("obligations").EnumerateArray().Select(item =>
            {
                RunHandleJson.RequireFields(item, "root_id", "successor_verifier_id");
                return new QuotientObligation(Required(item, "root_id"), Required(item, "successor_verifier_id"));
            }).ToImmutableArray();
            var expected = GateAuthorityRootCatalogLoader.LoadRepository(repositoryRoot)
                .Select(static item => new QuotientObligation(item.RootId, "expected" )).ToImmutableArray();
            var currentCommit = Git(repositoryRoot, "rev-parse", "HEAD").Trim();

            Observation oldRaw = null!;
            Observation oldCanonical = null!;
            string[] diffPaths = null!;
            string oldBuildSha = null!;
            PrARealRebuildRunner.InPinnedCheckout(repositoryRoot, oldBuild, checkout =>
            {
                oldBuildSha = BuildSha(checkout);
                Apply(checkout, mutations);
                oldRaw = Observe(checkout, harness);
                foreach (var producer in producers) Execute(checkout, producer);
                oldCanonical = Observe(checkout, harness);
                diffPaths = Git(checkout, "diff", "--name-only", "--").Split('\n', StringSplitOptions.RemoveEmptyEntries);
                return true;
            });
            string newBuildSha = null!;
            var successor = PrARealRebuildRunner.InPinnedCheckout(repositoryRoot, currentCommit, checkout =>
            {
                newBuildSha = BuildSha(checkout);
                Apply(checkout, mutations);
                return Observe(checkout, harness);
            });
            var runLocalPaths = FileMapLoader.LoadRepository(repositoryRoot).Entries
                .Where(static item => item.RuntimeDisposition == "run-local")
                .Select(static item => item.Pattern).ToHashSet(StringComparer.Ordinal);
            var classified = RefactorQuotient.Classify(oldRaw.Disposition, oldCanonical.Disposition,
                successor.Disposition, diffPaths, runLocalPaths, oldRaw.Obligations,
                oldCanonical.Obligations, successor.Obligations, obligations, expected);
            var inputSha = Convert.ToHexStringLower(SHA256.HashData(caseBytes));
            var bytes = RunHandleJson.Write(new Dictionary<string, object?>
            {
                ["schema"] = "refactor-quotient-receipt-v1", ["case_id"] = caseId,
                ["input_sha256"] = inputSha, ["old_build_sha256"] = oldBuildSha,
                ["new_build_sha256"] = newBuildSha, ["old_raw"] = oldRaw.Disposition,
                ["old_canonical"] = oldCanonical.Disposition, ["new"] = successor.Disposition,
                ["classification"] = classified.Classification,
                ["expected_gate_authority_sha256"] = authoritySha,
                ["obligations"] = obligations.Select(static item => new Dictionary<string, object?>
                { ["root_id"] = item.RootId, ["successor_verifier_id"] = item.SuccessorVerifierId }).ToArray(),
                ["diff_paths"] = diffPaths.Order(StringComparer.Ordinal).ToArray(), ["pass"] = classified.Pass,
            });
            Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(output))!);
            File.WriteAllBytes(output, bytes);
            return new(classified.Pass ? 0 : 1, classified.Pass ? "QUOTIENT_OK\n" : string.Empty,
                classified.Pass ? string.Empty : string.Join('\n', classified.Diagnostics) + "\n");
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or FormatException or JsonException or InvalidOperationException or TimeoutException)
        {
            return new(2, string.Empty, "QUOTIENT_INVALID " + exception.Message + "\n");
        }
    }

    private static Observation Observe(string root, string[] argv)
    {
        var output = Execute(root, argv);
        using var document = JsonDocument.Parse(output.StandardOutput);
        RunHandleJson.RequireFields(document.RootElement, "disposition", "obligations");
        var disposition = Required(document.RootElement, "disposition");
        if (disposition is not ("admit" or "reject")) throw new FormatException("invalid harness disposition");
        return new(disposition, document.RootElement.GetProperty("obligations").EnumerateArray()
            .Select(static item => item.GetString() ?? throw new FormatException("invalid obligation"))
            .Order(StringComparer.Ordinal).ToImmutableArray());
    }

    private static ProcessOutput Execute(string root, IReadOnlyList<string> argv)
    {
        var result = BoundedProcessRunner.Run(argv[0], argv.Skip(1), root, TimeSpan.FromMinutes(20), 16 * 1024 * 1024);
        if (result.ExitCode != 0) throw new InvalidOperationException($"harness command failed exit={result.ExitCode}");
        return result;
    }

    private static void Apply(string root, IEnumerable<Mutation> mutations)
    {
        foreach (var mutation in mutations)
        {
            RunPath.Validate(mutation.Path);
            var path = RunPath.ResolveContained(root, mutation.Path, requireExists: false);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, mutation.Content, new UTF8Encoding(false));
        }
    }

    private static string Git(string root, params string[] args) =>
        Encoding.UTF8.GetString(Execute(root, ["git", .. args]).StandardOutput);
    private static string BuildSha(string root)
    {
        var project = Path.Combine("Meta", "StrataLint", "StrataLint.Cli", "StrataLint.Cli.csproj");
        var targetPath = Encoding.UTF8.GetString(Execute(root,
            ["dotnet", "msbuild", project, "-getProperty:TargetPath", "-property:Configuration=Release"])
            .StandardOutput).Trim();
        if (!Path.IsPathFullyQualified(targetPath)) targetPath = Path.Combine(root, targetPath);
        return Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(targetPath)));
    }
    private static string[] Argv(JsonElement element)
    {
        var result = element.EnumerateArray().Select(static item => item.GetString() ?? string.Empty).ToArray();
        if (result.Length == 0 || result.Any(string.IsNullOrWhiteSpace)) throw new FormatException("argv is invalid");
        return result;
    }
    private static string Required(JsonElement element, string name) =>
        element.GetProperty(name).GetString() is { Length: > 0 } value ? value : throw new FormatException(name + " is invalid");
    private static string RequiredSha(JsonElement element, string name)
    {
        var value = Required(element, name);
        RunRequest.RequireSha(value, name);
        return value;
    }
    private static bool Pair(IReadOnlyList<string> args, out string casePath, out string output)
    {
        casePath = output = string.Empty;
        if (args.Count != 4) return false;
        for (var index = 0; index < args.Count; index += 2)
        {
            if (args[index] == "--case") casePath = args[index + 1];
            else if (args[index] == "--out") output = args[index + 1];
            else return false;
        }
        return casePath.Length > 0 && output.Length > 0;
    }
}
