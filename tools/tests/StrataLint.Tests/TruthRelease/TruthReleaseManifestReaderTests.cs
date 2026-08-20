using System;
using Trureturing.Truth;
using Xunit;

namespace StrataLint.Tests;

public sealed class TruthReleaseManifestReaderTests
{
    private const string ValidManifest = """
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
            ],
            "blessed_by": "loning"
          },
          "producer": {
            "package_repo": "the-omega-institute/trureturing-fkst-packages",
            "package_commit": "cccccccccccccccccccccccccccccccccccccccc",
            "read_only": true
          },
          "artifacts": {
            "source_snapshot":    { "file": "source-snapshot.v1.json", "sha256": "sha256:1111111111111111111111111111111111111111111111111111111111111111" },
            "truth_graph":        { "file": "truth-graph.v1.json",     "sha256": "sha256:2222222222222222222222222222222222222222222222222222222222222222" },
            "raw_lean_report":    { "file": "raw-lean-report.json",    "sha256": "sha256:3333333333333333333333333333333333333333333333333333333333333333" },
            "declarations":       { "file": "declarations.v1.json",    "sha256": "sha256:4444444444444444444444444444444444444444444444444444444444444444" },
            "blueprint_index":    { "file": "blueprint-index.v1.json", "sha256": "sha256:5555555555555555555555555555555555555555555555555555555555555555" },
            "frozen_ledger_head": { "file": "frozen-ledger-head.json", "sha256": "sha256:6666666666666666666666666666666666666666666666666666666666666666" },
            "residual_frontier":  { "file": "echo-residual-summary.md","sha256": "sha256:7777777777777777777777777777777777777777777777777777777777777777" }
          },
          "sha256sums_digest": "sha256:8888888888888888888888888888888888888888888888888888888888888888",
          "produced_at": "2026-08-20T00:00:00Z"
        }
        """;

    [Fact]
    public void ParsesAValidV1Manifest()
    {
        var m = TruthReleaseManifestReader.Read(ValidManifest);

        Assert.Equal("the-omega-institute/trureturing", m.Source.SourceRepo);
        Assert.Equal("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", m.Source.SourceCommit);
        Assert.True(m.Trust.CommitOnProtectedDev);
        Assert.Equal(3, m.Trust.RequiredChecks.Length);
        Assert.Equal("Canonical Lean report production", m.Trust.RequiredChecks[1].Name);
        Assert.Equal("loning", m.Trust.BlessedBy);
        Assert.True(m.Producer.ReadOnly);
        Assert.Equal("declarations.v1.json", m.Artifacts.Declarations.File);
        Assert.Equal(
            "sha256:4444444444444444444444444444444444444444444444444444444444444444",
            m.Artifacts.Declarations.Sha256);
        Assert.Equal(
            "sha256:8888888888888888888888888888888888888888888888888888888888888888",
            m.Sha256SumsDigest);
        Assert.Equal("2026-08-20T00:00:00Z", m.ProducedAt);
    }

    [Fact]
    public void RejectsWrongSchemaTag()
    {
        var bad = ValidManifest.Replace("truth-release.v1", "truth-release.v2", StringComparison.Ordinal);
        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(bad));
    }

    [Fact]
    public void RejectsAMissingRequiredArtifact()
    {
        // Rename the required "declarations" artifact key → it is now absent.
        var bad = ValidManifest.Replace("\"declarations\":", "\"declarationz\":", StringComparison.Ordinal);
        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(bad));
    }

    [Fact]
    public void RejectsAMalformedDigest()
    {
        var bad = ValidManifest.Replace(
            "sha256:8888888888888888888888888888888888888888888888888888888888888888",
            "not-a-digest",
            StringComparison.Ordinal);
        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(bad));
    }
}
