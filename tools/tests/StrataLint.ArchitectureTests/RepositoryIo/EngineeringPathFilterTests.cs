using System.Text.RegularExpressions;
using YamlDotNet.RepresentationModel;

namespace StrataLint.ArchitectureTests;

public sealed class EngineeringPathFilterTests
{
    private static readonly string[] StructuralTriggerFloor =
    [
        "tools",
        "Makefile",
        ".github",
        "global.json",
        "Directory.Build.props",
        "Directory.Packages.props",
        "lean-toolchain",
        "lakefile.toml",
        "lake-manifest.json",
    ];

    // Blueprint documents are copied or scanned as corpus for emitter/document behavior. They are
    // also compiled into StrataLint.Scribe, but the always-on lean-inspect content lane restores the
    // exact Blueprint-addressed binary (or builds Scribe alone on a miss) and runs all four content
    // checks, so the engineering test suite adds no content verdict.
    // CLAUDE.md is an existing marker/read sample for typed repository-accessor tests.
    // D5 sources are copied into temporary emission trees as real-world Lean corpus.
    // Library notes are copied into temporary emission trees as citation corpus.
    // Digestion receipts are copied into temporary emission trees as ledger-shaped corpus.
    private static readonly IReadOnlyDictionary<string, string> IncidentalInputExclusions =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Blueprint"] = "emitter/document corpus; the content lane runs the complete Scribe checks",
            ["CLAUDE.md"] = "repository-root marker and typed accessor sample, not asserted policy text",
            ["D5"] = "real-tree Lean corpus copied into temporary emission fixtures",
            ["Library"] = "real-tree citation corpus copied into temporary emission fixtures",
            ["Meta/Digestion/backfill"] = "real-tree ledger corpus copied into temporary emission fixtures",
        };

    [Fact]
    public void WorkflowTriggerSetCoversDerivedRepositoryReadsExceptExplicitIncidentalInputs()
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var map = ScribeTestMapDeriver.DeriveRepository(repositoryRoot);
        var declaredReads = map.Methods
            .SelectMany(static method => method.Paths)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var triggers = EngineeringTriggers(repositoryRoot);

        Assert.All(
            IncidentalInputExclusions,
            exclusion =>
            {
                Assert.Contains(declaredReads, path => Covers(exclusion.Key, path));
                Assert.False(
                    triggers.Any(trigger => Covers(trigger, exclusion.Key)),
                    $"incidental input exclusion is still in the engineering trigger set: {exclusion.Key}");
                Assert.False(string.IsNullOrWhiteSpace(exclusion.Value));
            });

        var requiredReads = declaredReads
            .Where(path => !IncidentalInputExclusions.Keys.Any(exclusion => Covers(exclusion, path)))
            .ToArray();
        Assert.All(
            StructuralTriggerFloor.Concat(requiredReads),
            required => Assert.True(
                triggers.Any(trigger => Covers(trigger, required)),
                $"candidate-engineering trigger set does not cover required path: {required}"));

        Assert.Contains("Golden/Projection", triggers);
        Assert.Contains("Meta/FILEMAP.toml", triggers);
    }

    private static IReadOnlyList<string> EngineeringTriggers(string repositoryRoot)
    {
        var workflow = File.ReadAllText(Path.Combine(repositoryRoot, ".github", "workflows", "ci.yml"));
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var root = (YamlMappingNode)stream.Documents[0].RootNode;
        var jobs = (YamlMappingNode)root.Children[new YamlScalarNode("jobs")];
        var engineering = (YamlMappingNode)jobs.Children[new YamlScalarNode("candidate-engineering")];
        var steps = (YamlSequenceNode)engineering.Children[new YamlScalarNode("steps")];
        var scope = steps.Children.OfType<YamlMappingNode>().Single(step =>
            step.Children.TryGetValue(new YamlScalarNode("id"), out var id)
                && id is YamlScalarNode { Value: "scope" });
        var script = ((YamlScalarNode)scope.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
        var array = Regex.Match(
            script,
            @"(?ms)^[ \t]*engineering_triggers=\([ \t]*$\n(?<body>.*?)^[ \t]*\)[ \t]*$",
            RegexOptions.CultureInvariant);
        Assert.True(array.Success, "scope step must inline engineering_triggers as a shell array");
        var triggers = Regex.Matches(
                array.Groups["body"].Value,
                "^\\s*\"(?<path>[^\"]+)\"\\s*$",
                RegexOptions.Multiline | RegexOptions.CultureInvariant)
            .Select(static match => match.Groups["path"].Value)
            .ToArray();
        Assert.NotEmpty(triggers);
        Assert.Equal(triggers.Length, triggers.Distinct(StringComparer.Ordinal).Count());
        return triggers;
    }

    private static bool Covers(string root, string path) =>
        path == root || path.StartsWith(root + "/", StringComparison.Ordinal);
}
