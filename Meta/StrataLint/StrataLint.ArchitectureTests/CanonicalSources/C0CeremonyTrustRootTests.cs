using System.Diagnostics;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed class C0CeremonyTrustRootTests
{
    private const string TowerPath = "Meta/StrataLint/TOWER.yaml";

    [Fact]
    public void CanonicalTowerJudgeGraphIsClosed()
    {
        var root = RepositoryLayout.FindRoot();
        var loaded = Assert.IsType<TowerManifestParseOutcome.Loaded>(
            TowerManifestParser.Parse(File.ReadAllBytes(Absolute(root, TowerPath))));

        var outcome = TowerManifestValidator.ValidateStructure(loaded.Syntax);

        var rejected = outcome as TowerValidationOutcome.Rejected;
        Assert.True(
            outcome is TowerValidationOutcome.Accepted,
            rejected is null
                ? "canonical TOWER returned an unknown validation outcome"
                : string.Join("; ", rejected.Findings.Select(static item =>
                    $"{item.Code} {item.Component}: {item.Message}")));
    }

    [Fact]
    public void CanonicalTowerC0EvidenceIsCanonical()
    {
        var root = RepositoryLayout.FindRoot();
        var snapshot = Repository(root);
        var loaded = Assert.IsType<TowerManifestParseOutcome.Loaded>(
            TowerManifestParser.Parse(File.ReadAllBytes(Absolute(root, TowerPath))));

        var actual = TowerActualValidator.Validate(
            loaded.Syntax,
            snapshot,
            RuleCatalog.Default);

        Assert.Empty(actual.Findings.Where(static item => string.Equals(
            item.Component,
            C0CeremonyProjection.ComponentId,
            StringComparison.Ordinal)));
    }

    [Fact]
    public void TowerC0AddressesMatchTheCanonicalPolicyAndPreimage()
    {
        var root = RepositoryLayout.FindRoot();
        var snapshot = Repository(root);
        var loaded = Assert.IsType<TowerManifestParseOutcome.Loaded>(
            TowerManifestParser.Parse(File.ReadAllBytes(Absolute(root, TowerPath))));
        var component = Assert.Single(
            loaded.Syntax.Components,
            static item => item.Id == C0CeremonyProjection.ComponentId);

        Assert.Equal("verified", component.Verification);
        Assert.True(C0CeremonyProjection.HasCanonicalShape(component.Members));
        Assert.Equal("open", loaded.Syntax.Bootstrap.Judge);
        Assert.Equal("ASSUMED-UNVERIFIED", loaded.Syntax.Bootstrap.Verification);

        var records = component.Members.Skip(2).Select(ParseRecord).ToArray();
        var anchors = C0CeremonyProjection.DiscoverAnchors(snapshot);
        Assert.Equal(anchors.Length + 5, records.Length);
        AssertAnchorPaths(records, anchors, C0AnchorKind.Controller, "c0/controller");
        AssertAnchorPaths(records, anchors, C0AnchorKind.Corpus, "c0/corpus");
        AssertAnchorPaths(records, anchors, C0AnchorKind.GateWiring, "c0/gate-wiring");

        var certificate = Assert.Single(records, static item =>
            item.Kind == "c0/inaugural-certificate");
        Assert.Equal(C0CeremonyProjection.CertificatePath, certificate.Path);
        var certificateBytes = File.ReadAllBytes(Absolute(
            root,
            C0CeremonyProjection.CertificatePath));

        var baseCommit = Assert.Single(records, static item => item.Kind == "c0/base-commit");
        Assert.Null(baseCommit.Path);
        var ceremonyCommit = Assert.Single(records, static item =>
            item.Kind == "c0/ceremony-commit");
        Assert.Equal("convention/this-pr-merge-commit", ceremonyCommit.Address);
        Assert.Null(ceremonyCommit.Path);
        var preimageCommit = Assert.Single(records, static item =>
            item.Kind == "c0/preimage-commit");
        Assert.Null(preimageCommit.Path);
        var preimageTree = Assert.Single(records, static item => item.Kind == "c0/preimage-tree");
        Assert.Null(preimageTree.Path);

        using var document = JsonDocument.Parse(certificateBytes);
        var certificateRoot = document.RootElement;
        Assert.Equal(
            "stratalint-conservative-certificate-v1",
            certificateRoot.GetProperty("schema").GetString());
        Assert.Equal("CORPUS_CONSERVATIVE", certificateRoot.GetProperty("status").GetString());
        Assert.Empty(certificateRoot.GetProperty("findings").EnumerateArray());
        Assert.Equal(119, certificateRoot.GetProperty("golden_case_count").GetInt32());
        var implication = certificateRoot.GetProperty("positive_implication");
        Assert.Equal(
            implication.GetProperty("baseline_admit_count").GetInt32(),
            implication.GetProperty("preserved_admit_count").GetInt32());
        Assert.Equal(
            "git-commit/" + certificateRoot.GetProperty("baseline")
                .GetProperty("commit_oid").GetString(),
            baseCommit.Address);
        Assert.Equal(
            certificateRoot.GetProperty("baseline").GetProperty("tree_oid").GetString(),
            "git-sha1:" + Git(
                root,
                "rev-parse",
                Untag(baseCommit.Address, "git-commit/") + "^{tree}"));

        var candidate = certificateRoot.GetProperty("candidate");
        Assert.Equal(
            "git-commit/" + candidate.GetProperty("commit_oid").GetString(),
            preimageCommit.Address);
        Assert.Equal(
            "git-tree/" + Untag(candidate.GetProperty("tree_oid").GetString()!, "git-sha1:"),
            preimageTree.Address);
        var preimageOid = Untag(preimageCommit.Address, "git-commit/");
        Assert.Equal(
            Untag(preimageTree.Address, "git-tree/"),
            Git(root, "rev-parse", preimageOid + "^{tree}"));
        Git(root, "merge-base", "--is-ancestor", preimageOid, "HEAD");
        AssertPreimageBlobs(root, records, preimageOid);
    }

    private static void AssertAnchorPaths(
        IEnumerable<C0Record> records,
        IEnumerable<C0Anchor> anchors,
        C0AnchorKind anchorKind,
        string recordKind)
    {
        var expected = anchors
            .Where(item => item.Kind == anchorKind)
            .Select(static item => item.Path)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var actual = records
            .Where(item => item.Kind == recordKind)
            .Select(item => item.Path
                ?? throw new InvalidOperationException($"{recordKind} record has no path"))
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.Equal(expected, actual);
    }

    private static void AssertPreimageBlobs(
        string root,
        IEnumerable<C0Record> records,
        string preimageCommit)
    {
        foreach (var record in records.Where(static item => item.Kind is
            "c0/controller" or "c0/corpus" or "c0/gate-wiring"))
        {
            Assert.Equal(
                record.Address,
                "git-sha1/" + Git(root, "rev-parse", $"{preimageCommit}:{record.Path}"));
        }
    }

    private static C0Record ParseRecord(string value)
    {
        var fields = value.Split(' ', StringSplitOptions.RemoveEmptyEntries);
        Assert.InRange(fields.Length, 2, 3);
        return new C0Record(
            fields[0],
            fields[1],
            fields.Length == 3 ? fields[2] : null);
    }

    private static string Git(string root, params string[] arguments)
    {
        var startInfo = new ProcessStartInfo("git")
        {
            WorkingDirectory = root,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var argument in arguments) startInfo.ArgumentList.Add(argument);
        using var process = Process.Start(startInfo)
            ?? throw new InvalidOperationException("could not start git");
        var output = process.StandardOutput.ReadToEnd();
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Assert.True(
            process.ExitCode == 0,
            $"git {string.Join(' ', arguments)} exited {process.ExitCode}: {error}");
        return output.TrimEnd('\r', '\n');
    }

    private static string Untag(string value, string prefix)
    {
        Assert.StartsWith(prefix, value, StringComparison.Ordinal);
        return value[prefix.Length..];
    }

    private static string Absolute(string root, string path) =>
        Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));

    private static RepositorySnapshot Repository(string root) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            GitRepositorySnapshotReader.ReadCurrent(root))).Snapshot;

    private sealed record C0Record(string Kind, string Address, string? Path);
}
