using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class FileMapIncludeTests
{
    private const string FragmentPath = "Meta/FILEMAP.docs.reports.toml";
    private const string Include = "include = [\"FILEMAP.docs.reports.toml\"]\n";
    private const string Residence = """
        [residence_policy]
        case_id = "RESIDENCE-EPOCH"
        desired = "data-must-live-outside-tools"
        known_violation_count = 0
        status = "closed"
        """ + "\n";

    [Fact]
    public void IncludedEntriesMatchAndEmitIdenticallyToAFlatManifest()
    {
        var root = Bytes("schema_version = 2\n" + Include + Residence + Entry("z.md"));
        var fragment = Bytes("schema_version = 2\n" + Entry("docs/reports/**/*.json"));
        var split = FileMapLoader.Parse(root, "root", path =>
        {
            Assert.Equal(FragmentPath, path);
            return fragment;
        });
        var flat = FileMapLoader.Parse(Bytes("schema_version = 2\n" + Residence
            + Entry("docs/reports/**/*.json") + Entry("z.md")), "flat");

        Assert.Equal("docs/reports/**/*.json", Assert.Single(split.Match("docs/reports/new/nested/result.json")).Pattern);
        Assert.Equal<byte>(FileMapProjectionWriter.Write(flat), FileMapProjectionWriter.Write(split));
    }

    [Fact]
    public void RootCanDelegateAllEntriesToIncludes()
    {
        var manifest = FileMapLoader.Parse(Bytes("schema_version = 2\n" + Include + Residence), "root",
            _ => Bytes("schema_version = 2\n" + Entry("docs/reports/**/*.json")));

        Assert.Single(manifest.Entries);
    }

    [Fact]
    public void MultipleFragmentsAreMergedWithoutFilenamePrecedence()
    {
        var root = Bytes("schema_version = 2\ninclude = [\"FILEMAP.a.toml\", \"FILEMAP.z.toml\"]\n" + Residence);
        var manifest = FileMapLoader.Parse(root, "root", path => Bytes("schema_version = 2\n"
            + Entry(path == "Meta/FILEMAP.a.toml" ? "z.md" : "a.md")));

        Assert.Equal(["a.md", "z.md"], manifest.Entries.Select(entry => entry.Pattern).ToArray());
    }

    [Theory]
    [InlineData("FILEMAP.docs-reports.toml")]
    [InlineData("FILEMAP.docs_reports.toml")]
    [InlineData("FILEMAP.Docs.toml")]
    [InlineData("FILEMAP.2docs.toml")]
    [InlineData("FILEMAP..docs.toml")]
    [InlineData("FILEMAP.toml")]
    [InlineData("../FILEMAP.docs.toml")]
    [InlineData("/FILEMAP.docs.toml")]
    [InlineData("Meta/FILEMAP.docs.toml")]
    [InlineData("FILEMAP.*.toml")]
    public void InvalidNamesAreRejectedBeforeReading(string name)
    {
        var bytes = Bytes("schema_version = 2\ninclude = [\"" + name + "\"]\n" + Residence);
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(bytes, "root", _ =>
            throw new InvalidOperationException("must not read an invalid name")));
    }

    [Theory]
    [InlineData("[]")]
    [InlineData("[1]")]
    [InlineData("\"FILEMAP.docs.toml\"")]
    [InlineData("[\"FILEMAP.docs.toml\", \"FILEMAP.docs.toml\"]")]
    [InlineData("[\"FILEMAP.z.toml\", \"FILEMAP.a.toml\"]")]
    public void MalformedOrDuplicateIncludeListsFailClosed(string includes)
    {
        var bytes = Bytes("schema_version = 2\ninclude = " + includes + "\n" + Residence);
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(bytes, "root", _ =>
            throw new InvalidOperationException("must not read an invalid include list")));
    }

    [Fact]
    public void IncludesCannotBeSilentlyIgnoredWithoutAReader()
    {
        var bytes = Bytes("schema_version = 2\n" + Include + Residence + Entry("z.md"));
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(bytes, "root"));
        Assert.Throws<FileMapParseException>(() => AdmissionPlaneFileMapLoader.Parse(bytes, "root"));
        Assert.Throws<FileMapParseException>(() => FileMapSymlinkPolicy.Parse(bytes, "root"));
    }

    [Theory]
    [InlineData("include = [\"FILEMAP.docs.reports.toml\"]\n")]
    [InlineData("include = [\"FILEMAP.other.toml\"]\n")]
    [InlineData("unknown = true\n")]
    [InlineData("[residence_policy]\nstatus = \"closed\"\n")]
    public void FragmentsRejectNestedIncludesAndPolicyOverrides(string extra)
    {
        var root = Bytes("schema_version = 2\n" + Include + Residence);
        var fragment = Bytes("schema_version = 2\n" + extra + Entry("docs/**"));
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(root, "root", _ => fragment));
    }

    [Fact]
    public void MissingIncludedFileIsAnAttributedParseFailure()
    {
        var exception = Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(
            Bytes("schema_version = 2\n" + Include + Residence), "root", _ => throw new FileNotFoundException()));
        Assert.Contains(FragmentPath, exception.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("schema_version = 1\n[[files]]\npattern = \"docs/**\"\n")]
    [InlineData("schema_version = 2\nfiles = []\n")]
    [InlineData("schema_version = 2\nfiles = [\n")]
    [InlineData("schema_version = 2\r\n")]
    [InlineData("schema_version = 2")]
    [InlineData("\uFEFFschema_version = 2\n")]
    public void InvalidFragmentSchemasAndBytesAreRejectedByAllConsumers(string fragment)
    {
        var bytes = Bytes("schema_version = 2\n" + Include + Residence);
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(bytes, "root", _ => Bytes(fragment)));
        Assert.ThrowsAny<FormatException>(() => AdmissionPlaneFileMapLoader.Parse(bytes, "root", _ => Bytes(fragment)));
        Assert.ThrowsAny<FormatException>(() => FileMapSymlinkPolicy.Parse(bytes, "root", _ => Bytes(fragment)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DuplicatePatternsAndArtifactIdsAreRejectedAcrossFiles(bool artifact)
    {
        var rootEntry = artifact ? GeneratedEntry("a.md") : Entry("docs/**");
        var fragmentEntry = artifact ? GeneratedEntry("z.md") : Entry("docs/**");
        var exception = Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(
            Bytes("schema_version = 2\n" + Include + Residence + rootEntry), "root",
            _ => Bytes("schema_version = 2\n" + fragmentEntry)));
        Assert.Contains(artifact ? "artifact_id" : "patterns", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void FragmentEntriesMustBeSortedBeforeMerging()
    {
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(
            Bytes("schema_version = 2\n" + Include + Residence), "root",
            _ => Bytes("schema_version = 2\n" + Entry("z.md") + Entry("a.md"))));
    }

    [Fact]
    public void SnapshotLoadingUsesSnapshotBytes()
    {
        var raw = Snapshot(Entry("docs/reports/**"));
        var decoded = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var manifest = FileMapLoader.LoadSnapshot(decoded);
        Assert.Single(manifest.Match("docs/reports/old/result.json"));
        Assert.Empty(manifest.Match("README.md"));
    }

    [Fact]
    public void AdmissionUsesEachEndpointsOwnIncludedManifest()
    {
        var baseline = Snapshot(Entry("docs/reports/old.json", "judge"));
        var candidate = Snapshot(Entry("docs/reports/new.json", "content"));
        var decision = AdmissionPlanePolicy.Evaluate(candidate, baseline, RawChangeSet.CreateWithKinds(
            [("docs/reports/old.json", RawChangeKind.Deleted), ("docs/reports/new.json", RawChangeKind.Added)]));

        Assert.False(decision.IsAdmissible);
        Assert.Equal(AdmissionPlaneClassification.Mixed, decision.Classification);
    }

    [Fact]
    public void MissingBaseIncludeCannotBeFilledFromCandidate()
    {
        var baseline = RawRepositorySnapshot.Create([Raw(AdmissionPlanePolicy.FileMapPath,
            "schema_version = 2\n" + Include + Residence)]);
        var candidate = Snapshot(Entry("docs/**"));
        var decision = AdmissionPlanePolicy.Evaluate(candidate, baseline,
            RawChangeSet.CreateWithKinds([("docs/retired.md", RawChangeKind.Deleted)]));

        Assert.False(decision.IsAdmissible);
        Assert.Contains(FragmentPath, decision.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IncludedPolicyCannotClassifyItselfAsContent()
    {
        var snapshot = Snapshot(Entry(FragmentPath));
        var decision = AdmissionPlanePolicy.Evaluate(snapshot, snapshot, RawChangeSet.Create([FragmentPath]));
        Assert.False(decision.IsAdmissible);
        Assert.Equal("FILEMAP-ADMISSION-PLANE-INVALID", decision.Code);
    }

    [Fact]
    public void IncludedSymlinkDeclarationIsReadFromTheSameSnapshot()
    {
        var declaration = Entry("AGENTS.md") + "symlink = { target = \"CLAUDE.md\", kind = \"file\" }\n";
        var snapshot = Snapshot(declaration + Entry("CLAUDE.md"));
        var entries = snapshot.Entries.Add(Raw("AGENTS.md", "CLAUDE.md")).Add(Raw("CLAUDE.md", "# Instructions\n"));
        FileMapSymlinkPolicy.ValidateSnapshot(entries, new HashSet<string> { "AGENTS.md" },
            entries.Select(entry => entry.Path).ToArray());
        Assert.Throws<InvalidOperationException>(() => FileMapSymlinkPolicy.ValidateSnapshot(entries,
            new HashSet<string> { "AGENTS.md", FragmentPath }, entries.Select(entry => entry.Path).ToArray()));
    }

    private static RawRepositorySnapshot Snapshot(string entries) => RawRepositorySnapshot.Create(
        [Raw(AdmissionPlanePolicy.FileMapPath, "schema_version = 2\n" + Include + Residence),
            Raw(FragmentPath, "schema_version = 2\n" + entries)]);

    private static RawRepositoryEntry Raw(string path, string text) => new(path, ImmutableArray.Create(Bytes(text)));
    private static byte[] Bytes(string text) => Encoding.UTF8.GetBytes(text);

    private static string Entry(string pattern, string plane = "content") => $$"""
        [[files]]
        pattern = "{{pattern}}"
        kind = "data"
        admission_plane = "{{plane}}"
        produced_by = "none"
        consumed_by = ["agent"]
        verified_by = ["SnapshotDecoder"]
        artifact_id = "none"
        runtime_disposition = "committed-source"
        """ + "\n";

    private static string GeneratedEntry(string path) => Entry(path)
        .Replace("kind = \"data\"", "kind = \"generated\"", StringComparison.Ordinal)
        .Replace("produced_by = \"none\"", "produced_by = \"OutputEmitter\"", StringComparison.Ordinal)
        .Replace("SnapshotDecoder", "OutputEmitter", StringComparison.Ordinal)
        .Replace("artifact_id = \"none\"", "artifact_id = \"A-OUTPUT\"", StringComparison.Ordinal)
        .Replace("committed-source", "run-local", StringComparison.Ordinal)
        + "mode = \"100644\"\nhistory_requirement = \"not-required\"\n";
}
