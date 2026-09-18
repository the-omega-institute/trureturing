using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class FileMapIncludeTests
{
    private const string FragmentPath = "Meta/FILEMAP.docs.reports.toml";
    private const string Schema = "schema_version = 4\n";
    private const string Resources = "resources = []\n";
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
        var root = Bytes(Schema + Include + Resources + Residence + Entry("z.md"));
        var fragment = Bytes(Schema + Entry("docs/reports/**/*.json"));
        var split = FileMapLoader.Parse(root, "root", path =>
        {
            Assert.Equal(FragmentPath, path);
            return fragment;
        });
        var flat = FileMapLoader.Parse(Bytes(Schema + Resources + Residence
            + Entry("docs/reports/**/*.json") + Entry("z.md")), "flat");

        Assert.Equal("docs/reports/**/*.json", Assert.Single(split.Match("docs/reports/new/nested/result.json")).Pattern);
        Assert.Equal<byte>(FileMapProjectionWriter.Write(flat), FileMapProjectionWriter.Write(split));
    }

    [Fact]
    public void RootCanDelegateAllEntriesToIncludes()
    {
        var manifest = FileMapLoader.Parse(Bytes(Schema + Include + Resources + Residence), "root",
            _ => Bytes(Schema + Entry("docs/reports/**/*.json")));

        Assert.Single(manifest.Entries);
    }

    [Fact]
    public void MultipleFragmentsAreMergedWithoutFilenamePrecedence()
    {
        var root = Bytes(Schema + "include = [\"FILEMAP.a.toml\", \"FILEMAP.z.toml\"]\n" + Resources + Residence);
        var manifest = FileMapLoader.Parse(root, "root", path => Bytes(Schema
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
        var bytes = Bytes(Schema + "include = [\"" + name + "\"]\n" + Resources + Residence);
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
        var bytes = Bytes(Schema + "include = " + includes + "\n" + Resources + Residence);
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(bytes, "root", _ =>
            throw new InvalidOperationException("must not read an invalid include list")));
    }

    [Fact]
    public void IncludesCannotBeSilentlyIgnoredWithoutAReader()
    {
        var bytes = Bytes(Schema + Include + Resources + Residence + Entry("z.md"));
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(bytes, "root"));
        Assert.Throws<FileMapParseException>(() => AdmissionPlaneFileMapLoader.Parse(bytes, "root"));
        Assert.Throws<FileMapParseException>(() => FileMapSymlinkPolicy.Parse(bytes, "root"));
    }

    [Theory]
    [InlineData("include = [\"FILEMAP.docs.reports.toml\"]\n")]
    [InlineData("include = [\"FILEMAP.other.toml\"]\n")]
    [InlineData("resources = []\n")]
    [InlineData("unknown = true\n")]
    [InlineData("[residence_policy]\nstatus = \"closed\"\n")]
    public void FragmentsRejectNestedIncludesAndPolicyOverrides(string extra)
    {
        var root = Bytes(Schema + Include + Resources + Residence);
        var fragment = Bytes(Schema + extra + Entry("docs/**"));
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(root, "root", _ => fragment));
    }

    [Fact]
    public void MissingIncludedFileIsAnAttributedParseFailure()
    {
        var exception = Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(
            Bytes(Schema + Include + Resources + Residence), "root", _ => throw new FileNotFoundException()));
        Assert.Contains(FragmentPath, exception.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("schema_version = 1\n[[files]]\npattern = \"docs/**\"\n")]
    [InlineData("schema_version = 2\nfiles = []\n")]
    [InlineData("schema_version = 4\nfiles = []\n")]
    [InlineData("schema_version = 4\nfiles = [\n")]
    [InlineData("schema_version = 4\r\n")]
    [InlineData("schema_version = 4")]
    [InlineData("\uFEFFschema_version = 4\n")]
    public void InvalidFragmentSchemasAndBytesAreRejectedByAllConsumers(string fragment)
    {
        var bytes = Bytes(Schema + Include + Resources + Residence);
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(bytes, "root", _ => Bytes(fragment)));
        Assert.ThrowsAny<FormatException>(() => AdmissionPlaneFileMapLoader.Parse(bytes, "root", _ => Bytes(fragment)));
        Assert.ThrowsAny<FormatException>(() => FileMapSymlinkPolicy.Parse(bytes, "root", _ => Bytes(fragment)));
    }

    [Fact]
    public void DuplicateFragmentKeysAreRejectedByTheStrictDecoder()
    {
        var root = Bytes(Schema + Include + Resources + Residence);
        var fragment = Bytes(Schema + "schema_version = 4\n" + Entry("docs/**"));

        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(root, "root", _ => fragment));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DuplicatePatternsAndArtifactIdsAreRejectedAcrossFiles(bool artifact)
    {
        var rootEntry = artifact ? GeneratedEntry("a.md") : Entry("docs/**");
        var fragmentEntry = artifact ? GeneratedEntry("z.md") : Entry("docs/**");
        var exception = Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(
            Bytes(Schema + Include + Resources + Residence + rootEntry), "root",
            _ => Bytes(Schema + fragmentEntry)));
        Assert.Contains(artifact ? "artifact_id" : "patterns", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void FragmentEntriesMustBeSortedBeforeMerging()
    {
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(
            Bytes(Schema + Include + Resources + Residence), "root",
            _ => Bytes(Schema + Entry("z.md") + Entry("a.md"))));
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
        var baseline = Snapshot(Entry("docs/reports/old.json", "judge"), "docs/reports/old.json");
        var candidate = Snapshot(Entry("docs/reports/new.json", "content"), "docs/reports/new.json");
        var decision = AdmissionPlanePolicy.Evaluate(candidate, baseline, RawChangeSet.CreateWithKinds(
            [("docs/reports/old.json", RawChangeKind.Deleted), ("docs/reports/new.json", RawChangeKind.Added)]));

        Assert.False(decision.IsAdmissible);
        Assert.Equal(AdmissionPlaneClassification.Mixed, decision.Classification);
    }

    [Fact]
    public void MissingBaseIncludeCannotBeFilledFromCandidate()
    {
        var baseline = RawRepositorySnapshot.Create([
            Raw(AdmissionPlanePolicy.FileMapPath, Schema + Include + Resources + Residence),
            Raw("docs/retired.md", string.Empty),
        ]);
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

    [Theory]
    [InlineData("judge")]
    [InlineData("content")]
    public void DeletedFileAndRegistrationUseProtectedBasePlane(string deletedPlane)
    {
        const string deletedPath = "retired/component.txt";
        var baseline = Snapshot(Entry(FragmentPath, "judge") + Entry(deletedPath, deletedPlane), deletedPath);
        var candidate = Snapshot(Entry(FragmentPath, "judge"));
        var decision = AdmissionPlanePolicy.Evaluate(candidate, baseline, RawChangeSet.CreateWithKinds(
            [(FragmentPath, RawChangeKind.Modified), (deletedPath, RawChangeKind.Deleted)]));

        Assert.Equal(deletedPlane == "judge", decision.IsAdmissible);
        Assert.Equal(deletedPlane == "judge" ? AdmissionPlaneClassification.JudgeOnly : AdmissionPlaneClassification.Mixed,
            decision.Classification);
        Assert.Equal(deletedPlane == "judge" ? string.Empty : AdmissionPlanePolicy.MixedCode, decision.Code);
    }

    [Theory]
    [InlineData(true, null, "ADMISSION-PLANE-FILEMAP-UNAVAILABLE")]
    [InlineData(true, "", "ADMISSION-PLANE-PATH-MATCH-COUNT")]
    [InlineData(true, "[[files]]\npattern = '**'\nrequire = []\nadmission_plane = 'judge'\n[[files]]\npattern = 'retired/*'\nrequire = []\nadmission_plane = 'content'", "ADMISSION-PLANE-PATH-MATCH-COUNT")]
    [InlineData(true, "files = [", "ADMISSION-PLANE-FILEMAP-INVALID")]
    [InlineData(true, "[[files]]\npattern = '**'\nrequire = []\nadmission_plane = 'observer'", "ADMISSION-PLANE-FILEMAP-INVALID")]
    [InlineData(false, null, "ADMISSION-PLANE-FILEMAP-UNAVAILABLE")]
    [InlineData(false, "files = [", "ADMISSION-PLANE-FILEMAP-INVALID")]
    [InlineData(false, "[[files]]\npattern = 'unrelated'\nrequire = []\nadmission_plane = 'observer'", "ADMISSION-PLANE-FILEMAP-INVALID")]
    public void DeletedPathWithInvalidManifestFailsClassification(
        bool invalidBaseline, string? invalidManifest, string expectedCode)
    {
        const string deletedPath = "retired/component.txt";
        var baseline = Snapshot(Entry(FragmentPath, "judge") + Entry(deletedPath, "judge"), deletedPath);
        var candidate = Snapshot(Entry(FragmentPath, "judge"));
        var invalidEntries = (invalidBaseline ? baseline : candidate).Entries
            .Where(entry => entry.Path != AdmissionPlanePolicy.FileMapPath);
        if (invalidManifest is not null)
            invalidEntries = invalidEntries.Append(Raw(AdmissionPlanePolicy.FileMapPath,
                Schema + Resources + Residence + invalidManifest));
        var invalid = RawRepositorySnapshot.Create(invalidEntries);
        var decision = AdmissionPlanePolicy.Evaluate(invalidBaseline ? candidate : invalid,
            invalidBaseline ? invalid : baseline, RawChangeSet.CreateWithKinds(
                [(FragmentPath, RawChangeKind.Modified), (deletedPath, RawChangeKind.Deleted)]));

        Assert.False(decision.IsAdmissible);
        Assert.Null(decision.Classification);
        Assert.Equal(expectedCode, decision.Code);
        Assert.Contains(invalidBaseline ? "protected-base" : "candidate", decision.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("judge")]
    [InlineData("content")]
    public void RenameClassifiesSourceFromBaselineAndDestinationFromCandidate(string destinationPlane)
    {
        const string source = "retired/source.txt";
        const string destination = "replacement/destination.txt";
        var baseline = Snapshot(Entry(FragmentPath, "judge") + Entry(source, "judge"), source);
        var candidate = Snapshot(Entry(FragmentPath, "judge") + Entry(destination, destinationPlane), destination);
        var decision = AdmissionPlanePolicy.Evaluate(candidate, baseline, RawChangeSet.CreateWithKinds(
            [(FragmentPath, RawChangeKind.Modified), (source, RawChangeKind.Deleted), (destination, RawChangeKind.Added)]));

        Assert.Equal(destinationPlane == "judge", decision.IsAdmissible);
        Assert.Equal(destinationPlane == "judge" ? AdmissionPlaneClassification.JudgeOnly : AdmissionPlaneClassification.Mixed,
            decision.Classification);
        Assert.Equal(destinationPlane == "judge" ? string.Empty : AdmissionPlanePolicy.MixedCode, decision.Code);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PresentPathCannotUseRemovedCandidateRegistration(bool baselineHasPath)
    {
        const string path = "component.txt";
        var baseline = Snapshot(Entry(FragmentPath, "judge") + Entry(path, "judge"), baselineHasPath ? [path] : []);
        var candidate = Snapshot(Entry(FragmentPath, "judge"), path);
        var decision = AdmissionPlanePolicy.Evaluate(candidate, baseline, RawChangeSet.CreateWithKinds(
            [(FragmentPath, RawChangeKind.Modified), (path, baselineHasPath ? RawChangeKind.Modified : RawChangeKind.Added)]));

        Assert.False(decision.IsAdmissible);
        Assert.Equal("ADMISSION-PLANE-PATH-MATCH-COUNT", decision.Code);
        Assert.Equal(path, decision.Path);
        Assert.Contains("manifest=candidate", decision.Message, StringComparison.Ordinal);
    }

    private static RawRepositorySnapshot Snapshot(string entries, params string[] paths) => RawRepositorySnapshot.Create(
        [Raw(AdmissionPlanePolicy.FileMapPath, Schema + Include + Resources + Residence),
            Raw(FragmentPath, Schema + entries),
            .. paths.Select(path => Raw(path, string.Empty))]);

    private static RawRepositoryEntry Raw(string path, string text) => new(path, ImmutableArray.Create(Bytes(text)));
    private static byte[] Bytes(string text) => Encoding.UTF8.GetBytes(text);

    private static string Entry(string pattern, string plane = "content") => $$"""
        [[files]]
        pattern = "{{pattern}}"
        require = []
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
