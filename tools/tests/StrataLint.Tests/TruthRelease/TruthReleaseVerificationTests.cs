using System;
using System.IO;
using System.Linq;
using System.Text;
using Trureturing.Truth;
using Xunit;

namespace StrataLint.Tests;

public sealed class TruthReleaseVerificationTests
{
    // Independent golden: the release digest was computed by `shasum -a 256` over the SHA256SUMS
    // text below — NOT by the code under test — so a shared canonicalization mistake cannot make a
    // producer and this verifier agree on the same wrong value.
    private const string GoldenReleaseDigest =
        "sha256:80c40867fbd43a264a9e06c0bc6f53c02f438f6bc6a6ecbfaccaf0f7b4b52801";

    // (bundle filename, artifact content, independent sha256 hex of that content).
    private static readonly (string File, string Content, string Hex)[] Artifacts =
    {
        ("source-snapshot.v1.json", "source_snapshot",    "4c33b02e4e1cbbcb5b7ab7eaea55954bbb059fa83a441a5cea33ec2d6f3187f8"),
        ("truth-graph.v1.json",     "truth_graph",        "ea6a5d67f81cc7ed11e48fa3c8ffb5dcaf91ac43caf2f04a87d6202e3d2b6eb2"),
        ("raw-lean-report.json",    "raw_lean_report",    "dbff08d567cca96ed64661be9ca200a24a837be72509afb4afddf43feea8b485"),
        ("truth-export.v1.json",    "truth_export",       "4ce24fb9b65427638bab27c6e4c544907c805f5c31e9cd48a0c66be75a7be917"),
        ("blueprint-index.v1.json", "blueprint_index",    "fc28f2016b02fc70c246a5a90ea6c024c9771a16473f3e7e11725c786bb6d4e0"),
        ("frozen-ledger-head.json", "frozen_ledger_head", "a1093bc930cafe23695d760be1409c0ababffa6c04c3b233a8ac35d370309c3b"),
        ("echo-residual-summary.md","residual_frontier",  "3d4fb60a2574585db90a38194fb19d065b8a5952d3591b68e616f4fbe1477f63"),
    };

    // SHA256SUMS text built by hand here (sorted by name, "<hex>  <name>", trailing "\n") — independent
    // of Trureturing.Truth.Sha256Sums, which the verifier never invokes (it reads this file's bytes).
    private static string Sha256SumsText() =>
        string.Concat(Artifacts
            .OrderBy(static a => a.File, StringComparer.Ordinal)
            .Select(static a => a.Hex + "  " + a.File + "\n"));

    private const string ManifestJson = """
        {
          "schema": "truth-release.v1",
          "source": {
            "source_repo": "the-omega-institute/trureturing",
            "source_commit": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            "source_tree": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
          },
          "trust": {
            "commit_on_protected_dev": true,
            "required_checks": [
              { "name": "Candidate harness engineering checks", "conclusion": "success" },
              { "name": "Canonical Lean report production", "conclusion": "success" },
              { "name": "Content-addressed dev baseline admission", "conclusion": "success" }
            ]
          },
          "producer": {
            "package_repo": "the-omega-institute/trureturing-fkst-packages",
            "package_commit": "cccccccccccccccccccccccccccccccccccccccc",
            "read_only": true
          },
          "artifacts": {
            "source_snapshot":    { "file": "source-snapshot.v1.json", "sha256": "sha256:4c33b02e4e1cbbcb5b7ab7eaea55954bbb059fa83a441a5cea33ec2d6f3187f8" },
            "truth_graph":        { "file": "truth-graph.v1.json",     "sha256": "sha256:ea6a5d67f81cc7ed11e48fa3c8ffb5dcaf91ac43caf2f04a87d6202e3d2b6eb2" },
            "raw_lean_report":    { "file": "raw-lean-report.json",    "sha256": "sha256:dbff08d567cca96ed64661be9ca200a24a837be72509afb4afddf43feea8b485" },
            "truth_export":       { "file": "truth-export.v1.json",    "sha256": "sha256:4ce24fb9b65427638bab27c6e4c544907c805f5c31e9cd48a0c66be75a7be917" },
            "blueprint_index":    { "file": "blueprint-index.v1.json", "sha256": "sha256:fc28f2016b02fc70c246a5a90ea6c024c9771a16473f3e7e11725c786bb6d4e0" },
            "frozen_ledger_head": { "file": "frozen-ledger-head.json", "sha256": "sha256:a1093bc930cafe23695d760be1409c0ababffa6c04c3b233a8ac35d370309c3b" },
            "residual_frontier":  { "file": "echo-residual-summary.md","sha256": "sha256:3d4fb60a2574585db90a38194fb19d065b8a5952d3591b68e616f4fbe1477f63" }
          },
          "sha256sums_digest": "sha256:80c40867fbd43a264a9e06c0bc6f53c02f438f6bc6a6ecbfaccaf0f7b4b52801",
          "produced_at": "2026-08-20T00:00:00Z"
        }
        """;

    private static string BuildBundle()
    {
        var directory = Directory.CreateTempSubdirectory("truthverify").FullName;
        foreach (var artifact in Artifacts)
        {
            File.WriteAllText(Path.Combine(directory, artifact.File), artifact.Content, new UTF8Encoding(false));
        }

        File.WriteAllText(Path.Combine(directory, "SHA256SUMS"), Sha256SumsText(), new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(directory, "release-manifest.v1.json"), ManifestJson, new UTF8Encoding(false));
        return directory;
    }

    [Fact]
    public void VerifiesAWellFormedBundle()
    {
        var directory = BuildBundle();
        try
        {
            var verified = TruthReleaseVerification.Verify(directory, GoldenReleaseDigest);

            Assert.Equal(GoldenReleaseDigest, verified.ReleaseDigest);
            Assert.Equal("truth-export.v1.json", verified.Manifest.Artifacts.TruthExport.File);
            Assert.Equal("the-omega-institute/trureturing", verified.Manifest.Source.SourceRepo);
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void RejectsAnExpectedDigestThatDoesNotMatchTheBundle()
    {
        var directory = BuildBundle();
        try
        {
            var wrong = "sha256:" + new string('0', 64);
            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, wrong));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void RejectsATamperedArtifact()
    {
        var directory = BuildBundle();
        try
        {
            // Flip one artifact's bytes; SHA256SUMS and the manifest still claim the old hash.
            File.WriteAllText(Path.Combine(directory, "truth-export.v1.json"), "tampered", new UTF8Encoding(false));
            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, GoldenReleaseDigest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void RejectsAMissingArtifactFile()
    {
        var directory = BuildBundle();
        try
        {
            File.Delete(Path.Combine(directory, "truth-export.v1.json"));
            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, GoldenReleaseDigest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void RejectsATraversalFilenameInTheManifest()
    {
        var directory = BuildBundle();
        try
        {
            // Point an artifact at a path outside the bundle. Verify must refuse before reading it.
            var evil = ManifestJson.Replace("\"truth-export.v1.json\"", "\"../escape.json\"", StringComparison.Ordinal);
            File.WriteAllText(Path.Combine(directory, "release-manifest.v1.json"), evil, new UTF8Encoding(false));
            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, GoldenReleaseDigest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void RejectsADuplicateArtifactFilename()
    {
        var directory = BuildBundle();
        try
        {
            // Point two artifact slots at the same file. A mere count-of-seven check would pass, but the
            // seven required artifacts no longer map to seven distinct, individually-bound files.
            var dup = ManifestJson.Replace("\"truth-graph.v1.json\"", "\"truth-export.v1.json\"", StringComparison.Ordinal);
            File.WriteAllText(Path.Combine(directory, "release-manifest.v1.json"), dup, new UTF8Encoding(false));
            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, GoldenReleaseDigest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void RejectsASymlinkedArtifact()
    {
        var directory = BuildBundle();
        var externalDirectory = Directory.CreateTempSubdirectory("truthverify-ext").FullName;
        try
        {
            // A symlink whose target's bytes match the recorded hash would pass a lexical path check and
            // byte comparison, yet the file is not contained in the bundle. Verify must refuse the symlink.
            var external = Path.Combine(externalDirectory, "external.txt");
            File.WriteAllText(external, "truth_export", new UTF8Encoding(false));
            var artifact = Path.Combine(directory, "truth-export.v1.json");
            File.Delete(artifact);
            File.CreateSymbolicLink(artifact, external);
            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, GoldenReleaseDigest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
            Directory.Delete(externalDirectory, recursive: true);
        }
    }
}
