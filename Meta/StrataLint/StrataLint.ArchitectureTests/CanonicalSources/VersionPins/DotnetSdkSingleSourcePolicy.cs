using YamlDotNet.RepresentationModel;

namespace StrataLint.ArchitectureTests;

internal sealed record DotnetSdkSingleSourceFinding(string Path, string Message);

internal static class DotnetSdkSingleSourcePolicy
{
    internal static IReadOnlyList<DotnetSdkSingleSourceFinding> InspectRepository(
        string repositoryRoot)
    {
        const string ciPath = ".github/workflows/ci.yml";
        var workflowsRoot = Path.Combine(repositoryRoot, ".github", "workflows");
        var findings = new List<DotnetSdkSingleSourceFinding>();
        var sawCanonicalCi = false;
        foreach (var fullPath in Directory.EnumerateFiles(workflowsRoot)
                     .Where(static path =>
                         string.Equals(Path.GetExtension(path), ".yml", StringComparison.OrdinalIgnoreCase)
                         || string.Equals(Path.GetExtension(path), ".yaml", StringComparison.OrdinalIgnoreCase))
                     .Order(StringComparer.Ordinal))
        {
            var path = Path.GetRelativePath(repositoryRoot, fullPath).Replace('\\', '/');
            var isCanonicalCi = string.Equals(path, ciPath, StringComparison.Ordinal);
            sawCanonicalCi |= isCanonicalCi;
            findings.AddRange(InspectWorkflow(
                path,
                File.ReadAllText(fullPath),
                requireCandidateAndBaseline: isCanonicalCi));
        }

        if (!sawCanonicalCi)
        {
            findings.Add(new DotnetSdkSingleSourceFinding(
                ciPath,
                "canonical CI workflow is missing"));
        }

        return findings;
    }

    internal static IReadOnlyList<DotnetSdkSingleSourceFinding> InspectWorkflow(
        string path,
        string source) =>
        InspectWorkflow(path, source, requireCandidateAndBaseline: true);

    private static IReadOnlyList<DotnetSdkSingleSourceFinding> InspectWorkflow(
        string path,
        string source,
        bool requireCandidateAndBaseline)
    {
        var globalJsonFiles = new HashSet<string>(StringComparer.Ordinal);
        var stream = new YamlStream();
        stream.Load(new StringReader(source));
        var findings = new List<DotnetSdkSingleSourceFinding>();
        foreach (var step in MappingNodes(stream.Documents[0].RootNode))
        {
            if (!TryScalar(step, "uses", out var uses)
                || !uses!.StartsWith("actions/setup-dotnet@", StringComparison.OrdinalIgnoreCase))
            {
                continue;
            }

            if (!TryMapping(step, "with", out var configuration))
            {
                findings.Add(new DotnetSdkSingleSourceFinding(
                    path,
                    "setup-dotnet must read the SDK pin through global-json-file"));
                continue;
            }

            if (TryScalar(configuration, "dotnet-version", out _))
            {
                findings.Add(new DotnetSdkSingleSourceFinding(
                    path,
                    "setup-dotnet copies the SDK version instead of using global.json"));
            }

            if (!TryScalar(configuration, "global-json-file", out var globalJsonFile)
                || string.IsNullOrWhiteSpace(globalJsonFile))
            {
                findings.Add(new DotnetSdkSingleSourceFinding(
                    path,
                    "setup-dotnet must read the SDK pin through global-json-file"));
            }
            else
            {
                globalJsonFiles.Add(globalJsonFile);
            }
        }

        if (!requireCandidateAndBaseline)
        {
            return findings;
        }

        foreach (var required in new[] { "candidate/global.json", "baseline/global.json" })
        {
            if (!globalJsonFiles.Contains(required))
            {
                findings.Add(new DotnetSdkSingleSourceFinding(
                    path,
                    $"workflow is missing the required setup-dotnet reference {required}"));
            }
        }

        return findings;
    }

    private static IEnumerable<YamlMappingNode> MappingNodes(YamlNode node)
    {
        if (node is YamlMappingNode mapping)
        {
            yield return mapping;
            foreach (var child in mapping.Children.Values)
            {
                foreach (var descendant in MappingNodes(child)) yield return descendant;
            }
        }
        else if (node is YamlSequenceNode sequence)
        {
            foreach (var child in sequence.Children)
            {
                foreach (var descendant in MappingNodes(child)) yield return descendant;
            }
        }
    }

    private static bool TryScalar(
        YamlMappingNode mapping,
        string key,
        out string? value)
    {
        foreach (var pair in mapping.Children)
        {
            if (pair.Key is YamlScalarNode { Value: var actualKey }
                && string.Equals(actualKey, key, StringComparison.Ordinal)
                && pair.Value is YamlScalarNode scalar)
            {
                value = scalar.Value;
                return true;
            }
        }

        value = null;
        return false;
    }

    private static bool TryMapping(
        YamlMappingNode mapping,
        string key,
        out YamlMappingNode value)
    {
        foreach (var pair in mapping.Children)
        {
            if (pair.Key is YamlScalarNode { Value: var actualKey }
                && string.Equals(actualKey, key, StringComparison.Ordinal)
                && pair.Value is YamlMappingNode child)
            {
                value = child;
                return true;
            }
        }

        value = null!;
        return false;
    }
}
