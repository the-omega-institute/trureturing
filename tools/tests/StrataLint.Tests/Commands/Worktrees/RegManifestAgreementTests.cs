using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.EngineeringScope;

namespace StrataLint.Tests;

public sealed class RegManifestAgreementTests
{
    [Theory]
    [InlineData("rev", "REG-MANIFEST-GIT-AGREEMENT")]
    [InlineData("missing", "REG-MANIFEST-GIT-AGREEMENT")]
    [InlineData("extra", "REG-MANIFEST-GIT-AGREEMENT")]
    [InlineData("duplicate", "REG-MANIFEST-GIT-AGREEMENT")]
    [InlineData("url", "REG-MANIFEST-GIT-AGREEMENT")]
    [InlineData("inputRev", "REG-MANIFEST-GIT-AGREEMENT")]
    [InlineData("subDir", "REG-MANIFEST-GIT-AGREEMENT")]
    [InlineData("configFile", "REG-MANIFEST-GIT-AGREEMENT")]
    [InlineData("manifestFile", "REG-MANIFEST-GIT-AGREEMENT")]
    [InlineData("packagesDir", "REG-MANIFEST-PACKAGES-DIR")]
    [InlineData("fourth-path", "REG-MANIFEST-PATH-AGREEMENT")]
    [InlineData("path-dir", "REG-MANIFEST-PATH-AGREEMENT")]
    [InlineData("inherited", "REG-MANIFEST-INHERITED")]
    [InlineData("absent", "REG-MANIFEST-MISSING")]
    [InlineData("malformed", "REG-MANIFEST-INVALID")]
    public void DivergentManifestBlocksPinsAndCurrentPredicate(string mutation, string diagnostic)
    {
        using var repository = new TemporaryDirectory();
        var files = Files();
        var manifest = JsonNode.Parse(files["Reg/lake-manifest.json"])!;
        var packages = manifest["packages"]!.AsArray();
        var git = packages[3]!;
        switch (mutation)
        {
            case "missing": packages.RemoveAt(3); break;
            case "extra":
                var extra = git.DeepClone(); extra["name"] = "extra"; packages.Add(extra); break;
            case "duplicate": packages.Add(git.DeepClone()); break;
            case "packagesDir": manifest["packagesDir"] = ".lake/packages"; break;
            case "fourth-path":
                var path = packages[0]!.DeepClone(); path["name"] = "fourth"; packages.Add(path); break;
            case "path-dir": packages[0]!["dir"] = "../elsewhere"; break;
            case "inherited": git["inherited"] = false; break;
            case "absent": case "malformed": break;
            default: git[mutation] = mutation == "rev" ? new string('b', 40) : "different"; break;
        }
        files["Reg/lake-manifest.json"] = manifest.ToJsonString();
        if (mutation == "absent") files.Remove("Reg/lake-manifest.json");
        if (mutation == "malformed") files["Reg/lake-manifest.json"] = "{";
        Write(repository.Path, files);

        Assert.Null(LeanPinSet.TryReadWorktree(repository.Path, out var reason));
        Assert.Contains(diagnostic, reason, StringComparison.Ordinal);
        Assert.Contains(Current(files), finding => finding.Message.Contains(diagnostic, StringComparison.Ordinal));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EqualGitMultisetsPassRegardlessOfOrder(bool reverse)
    {
        using var repository = new TemporaryDirectory();
        var files = Files();
        if (reverse)
        {
            var manifest = JsonNode.Parse(files["Reg/lake-manifest.json"])!;
            manifest["packages"] = new JsonArray(manifest["packages"]!.AsArray()
                .Reverse().Select(item => item!.DeepClone()).ToArray());
            files["Reg/lake-manifest.json"] = manifest.ToJsonString();
        }
        Write(repository.Path, files);
        Assert.NotNull(LeanPinSet.TryReadWorktree(repository.Path, out var reason));
        Assert.Null(reason);
        Assert.Empty(Current(files));
    }

    [Theory]
    [InlineData("inputRev")]
    [InlineData("manifestFile")]
    [InlineData("subDir")]
    public void MatchingNullableLakeGitFieldsPass(string field)
    {
        using var repository = new TemporaryDirectory();
        var files = Files();
        foreach (var name in new[] { "lake-manifest.json", "Reg/lake-manifest.json" })
        {
            var manifest = JsonNode.Parse(files[name])!;
            var git = manifest["packages"]!.AsArray().Single(item => item!["type"]!.GetValue<string>() == "git")!;
            git[field] = null;
            files[name] = manifest.ToJsonString();
        }
        Write(repository.Path, files);
        Assert.NotNull(LeanPinSet.TryReadWorktree(repository.Path, out var reason));
        Assert.Null(reason);
        Assert.Empty(Current(files));
    }

    private static Dictionary<string, string> Files()
    {
        var git = JsonNode.Parse("""
            {"type":"git","name":"mathlib","url":"https://example.test/mathlib",
             "rev":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","inputRev":"v4.33.0",
             "subDir":null,"configFile":"lakefile.lean","manifestFile":"lake-manifest.json","inherited":true}
            """)!;
        var paths = new[] { ("trureturing", "..", "lakefile.toml"),
            ("leanInspectorInterface", "../tools/lean-inspector-interface", "lakefile.toml"),
            ("leanInspector", "../tools/lean-inspector", "lakefile.lean") };
        var packages = new JsonArray(paths.Select(item => (JsonNode)new JsonObject
        {
            ["type"] = "path", ["name"] = item.Item1, ["dir"] = item.Item2,
            ["configFile"] = item.Item3, ["manifestFile"] = "lake-manifest.json", ["inherited"] = false,
        }).ToArray());
        packages.Add(git.DeepClone());
        return new()
        {
            ["lean-toolchain"] = "leanprover/lean4:v4.33.0\n",
            ["lake-manifest.json"] = new JsonObject { ["packages"] = new JsonArray(git) }.ToJsonString(),
            ["Reg/lakefile.toml"] = "name = \"reg\"\n",
            ["Reg/lake-manifest.json"] = new JsonObject
                { ["packagesDir"] = "../.lake/packages", ["packages"] = packages }.ToJsonString(),
        };
    }

    private static void Write(string root, Dictionary<string, string> files)
    {
        foreach (var (path, text) in files)
        {
            var full = Path.Combine(root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            File.WriteAllText(full, text);
        }
    }

    private static IEnumerable<Diagnostic> Current(Dictionary<string, string> files)
    {
        var root = TestRepositoryLayout.FindRoot();
        var policy = RegistryLoadAssert.Accepted(RegistryLoader.Load(
            File.ReadAllBytes(Path.Combine(root, "Meta/registry.yaml")),
            File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml")))).Policy;
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(files.Select(item => RawRepositoryEntry.FromText(item.Key, item.Value))))).Snapshot;
        return RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(15),
            CurrentRuleContext.CreateWithoutLean(snapshot, policy, null, CurrentRuleSelection.Create(
                RuleCatalog.Default.CurrentPredicateIds.Select(id => id.Value).ToArray(), ["SL-015"]))).Diagnostics
            .Where(item => item.Message.Contains("REG-MANIFEST-", StringComparison.Ordinal));
    }
}
