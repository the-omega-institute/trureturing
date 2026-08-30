using System;
using Trureturing.Truth;
using Xunit;

namespace Trureturing.Truth.Tests;

public sealed class TruthReleaseManifestReaderTests
{
    private const string SourceCommit40 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string SourceTree40 = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    private const string PackageCommit40 = "cccccccccccccccccccccccccccccccccccccccc";

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
            "truth_export":       { "file": "truth-export.v1.json",    "sha256": "sha256:4444444444444444444444444444444444444444444444444444444444444444" },
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
        Assert.Equal("truth-export.v1.json", m.Artifacts.TruthExport.File);
        Assert.Equal(
            "sha256:4444444444444444444444444444444444444444444444444444444444444444",
            m.Artifacts.TruthExport.Sha256);
        Assert.Equal(
            "sha256:8888888888888888888888888888888888888888888888888888888888888888",
            m.Sha256SumsDigest);
        Assert.Equal("2026-08-20T00:00:00Z", m.ProducedAt);
    }

    [Fact]
    public void AcceptsMatchingSha256SourceGitObjectIds()
    {
        var manifest = ValidManifest
            .Replace(SourceCommit40, new string('a', 64), StringComparison.Ordinal)
            .Replace(SourceTree40, new string('b', 64), StringComparison.Ordinal);

        var actual = TruthReleaseManifestReader.Read(manifest);

        Assert.Equal(64, actual.Source.SourceCommit.Length);
        Assert.Equal(64, actual.Source.SourceTree.Length);
    }

    [Theory]
    [InlineData(40)]
    [InlineData(64)]
    public void PackageCommitIndependentlyAcceptsEitherGitObjectFormat(int length)
    {
        var manifest = ValidManifest.Replace(
            PackageCommit40,
            new string('c', length),
            StringComparison.Ordinal);

        Assert.Equal(length, TruthReleaseManifestReader.Read(manifest).Producer.PackageCommit.Length);
    }

    [Theory]
    [InlineData(39)]
    [InlineData(41)]
    [InlineData(63)]
    [InlineData(65)]
    public void RejectsInvalidSourceGitObjectLengths(int length)
    {
        var badCommit = ValidManifest.Replace(
            SourceCommit40,
            new string('a', length),
            StringComparison.Ordinal);
        var badTree = ValidManifest.Replace(
            SourceTree40,
            new string('b', length),
            StringComparison.Ordinal);

        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(badCommit));
        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(badTree));
    }

    [Fact]
    public void RejectsMismatchedSourceGitObjectFormats()
    {
        var bad = ValidManifest.Replace(
            SourceTree40,
            new string('b', 64),
            StringComparison.Ordinal);

        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(bad));
    }

    [Fact]
    public void RejectsUppercaseOrNonHexSourceGitObjectIds()
    {
        var uppercase = ValidManifest.Replace(SourceCommit40, new string('A', 40), StringComparison.Ordinal);
        var nonHex = ValidManifest.Replace(SourceTree40, new string('g', 40), StringComparison.Ordinal);

        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(uppercase));
        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(nonHex));
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
        // Rename the required "truth_export" artifact key → it is now absent.
        var bad = ValidManifest.Replace("\"truth_export\":", "\"truth_exportz\":", StringComparison.Ordinal);
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

    [Fact]
    public void RejectsReadOnlyFalse()
    {
        var bad = ValidManifest.Replace("\"read_only\": true", "\"read_only\": false", StringComparison.Ordinal);
        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(bad));
    }

    [Fact]
    public void RejectsAnUnexpectedTopLevelProperty()
    {
        var bad = ValidManifest.Replace(
            "\"produced_at\": \"2026-08-20T00:00:00Z\"",
            "\"produced_at\": \"2026-08-20T00:00:00Z\", \"rogue\": 1",
            StringComparison.Ordinal);
        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(bad));
    }

    [Fact]
    public void RejectsACheckThatIsNotSuccess()
    {
        var bad = ValidManifest.Replace(
            "{ \"name\": \"Canonical Lean report production\", \"conclusion\": \"success\" }",
            "{ \"name\": \"Canonical Lean report production\", \"conclusion\": \"failure\" }",
            StringComparison.Ordinal);
        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(bad));
    }

    [Fact]
    public void RejectsADuplicateJsonProperty()
    {
        // JsonDocument keeps both occurrences and TryGetProperty would silently pick one; a schema-exact
        // reader must reject the ambiguity instead.
        var bad = ValidManifest.Replace(
            "\"read_only\": true",
            "\"read_only\": true, \"read_only\": false",
            StringComparison.Ordinal);
        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(bad));
    }
}
