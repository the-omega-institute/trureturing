using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Security.Cryptography;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;
using Trureturing.Truth;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.TruthRelease.Tests;

public sealed partial class TruthReleaseCommandTests
{
    private const string ProducerCommit = "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
    private const string ProducerRepository = "the-omega-institute/trureturing";
    private const string BlueprintGid = "D5/S3/Midline/GoldenSpectralMarker";
    private const string Toolchain = "leanprover/lean4:v4.24.0\n";
    private const string Manifest =
        "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"4444444444444444444444444444444444444444\"}],\"version\":\"1.1.0\"}\n";

    [Fact]
    public void CommandProducesAndVerifiesAllSixArtifactsEndToEnd()
    {
        using var fixture = CreateFixture();
        using var output = new TemporaryDirectory();
        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments());

        Assert.True(exitCode == 0, console.Error);
        Assert.Equal(string.Empty, console.Error);
        var digest = Assert.Single(
            console.Output.Split(' ', StringSplitOptions.RemoveEmptyEntries),
            static part => part.StartsWith("release_digest=", StringComparison.Ordinal))
            ["release_digest=".Length..].TrimEnd();
        var verified = TruthReleaseVerification.Verify(output.Path, digest);
        var graph = verified.ReadTruthGraph();
        var export = verified.ReadTruthExport();

        Assert.Equal(2, graph.Truth.Nodes.Count(static node => node.State == "closed"));
        Assert.Single(graph.Truth.Edges);
        Assert.Equal(2, export.Nodes.Length);
        Assert.Equal(fixture.SourceCommit, export.SourceCommit);
        Assert.Equal(fixture.SourceTree, export.SourceTree);
        Assert.Equal(ProducerRepository, verified.Manifest.Producer.PackageRepo);
        Assert.Equal(fixture.ReportBytes.ToArray(), File.ReadAllBytes(
            Path.Combine(output.Path, TruthReleaseBundleWriter.RawLeanReportFileName)));
        Assert.Equal(6, verified.Manifest.Artifacts.GetType().GetProperties().Length);
        Assert.False(File.Exists(Path.Combine(output.Path, "echo-residual-summary.md")));
        using (var sourceSnapshot = JsonDocument.Parse(File.ReadAllBytes(
            Path.Combine(output.Path, TruthReleaseBundleWriter.SourceSnapshotFileName))))
        {
            Assert.False(sourceSnapshot.RootElement.TryGetProperty("residual_frontier_sha256", out _));
        }
        using (var head = JsonDocument.Parse(File.ReadAllBytes(
            Path.Combine(output.Path, TruthReleaseBundleWriter.FrozenLedgerHeadFileName))))
        {
            Assert.Equal(fixture.FrozenLedgerHeadHash,
                head.RootElement.GetProperty("head_hash").GetString());
            Assert.Equal(fixture.FrozenLedgerSequence,
                head.RootElement.GetProperty("sequence").GetInt32());
        }
        using (var index = JsonDocument.Parse(File.ReadAllBytes(
            Path.Combine(output.Path, TruthReleaseBundleWriter.BlueprintIndexFileName))))
        {
            var entry = Assert.Single(index.RootElement.GetProperty("entries").EnumerateArray());
            Assert.Equal(BlueprintGid, entry.GetProperty("gid").GetString());
            Assert.Equal("data",
                entry.GetProperty("filemap").GetProperty("source").GetProperty("kind").GetString());
            Assert.Equal("generated",
                entry.GetProperty("filemap").GetProperty("projection").GetProperty("kind").GetString());
        }
        Assert.Equal(0, fixture.MutableLeanReportSource.CallCount);
    }

    [Fact]
    public void MissingPrecomputedReportFailsClosedWithoutWritingABundle()
    {
        using var fixture = CreateFixture();
        using var output = new TemporaryDirectory();
        File.Delete(fixture.ReportPath);

        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments());

        Assert.Equal(2, exitCode);
        Assert.Contains("TRUTH_RELEASE_INVALID", console.Error, StringComparison.Ordinal);
        Assert.Empty(Directory.EnumerateFiles(output.Path));
    }

    [Fact]
    public void MissingTrustInputFailsClosedWithoutWritingABundle()
    {
        using var fixture = CreateFixture();
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path, []);

        Assert.Equal(1, exitCode);
        Assert.Contains("--commit-on-protected-dev true|false", console.Error, StringComparison.Ordinal);
        Assert.Contains("--required-check NAME=CONCLUSION", console.Error, StringComparison.Ordinal);
        Assert.Contains("--scribe-pack FILE --scribe-pack-digest HEX64", console.Error, StringComparison.Ordinal);
        Assert.Empty(Directory.EnumerateFiles(output.Path));
    }

    [Fact]
    public void MissingScribePackFailsClosedWithoutWritingABundle()
    {
        using var fixture = CreateFixture();
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), []);

        Assert.Equal(2, exitCode);
        Assert.Contains("--scribe-pack FILE --scribe-pack-digest HEX64", console.Error,
            StringComparison.Ordinal);
        Assert.Empty(Directory.EnumerateFiles(output.Path));
    }

    [Fact]
    public void DigestionReceiptIntegrityFailureDoesNotBlockVerifiedLeanRelease()
    {
        using var fixture = Fixture.Create(receiptIntegrityMismatch: true);
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments());

        Assert.True(exitCode == 0, console.Error);
        Assert.Empty(console.Error);
        var publication = TruthReleasePublicationReader.Read(File.ReadAllBytes(
            Path.Combine(output.Path, TruthReleaseBundleWriter.PublicationFileName)));
        var verified = TruthReleasePublicationVerification.Verify(output.Path, publication);
        Assert.Equal(2, verified.ReadTruthExport().Nodes.Length);
        Assert.False(File.Exists(Path.Combine(output.Path, "echo-residual-summary.md")));
    }

    [Fact]
    public void StreamedProvenanceProducesTheSameBundleAsAFullRevisionWithLargeDigestionBodies()
    {
        using var fixture = CreateFixture(largeDigestionBodies: true);
        using var streamedOutput = new TemporaryDirectory();
        using var fullOutput = new TemporaryDirectory();
        var capture = new CapturingScribeVerifier();
        var projectedEnvironment = new ProductionCliEnvironment(fixture.RepositoryRoot,
            fixture.Gateway, fixture.MutableLeanReportSource, capture);
        var fullEnvironment = new ProductionCliEnvironment(fixture.RepositoryRoot,
            new FullSnapshotGateway(fixture.Gateway), fixture.MutableLeanReportSource,
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var streamed = Run(fixture, streamedOutput.Path, GreenTrustArguments(), environment: projectedEnvironment);
        var full = Run(fixture, fullOutput.Path, GreenTrustArguments(), environment: fullEnvironment);

        Assert.True(streamed.ExitCode == 0, streamed.Console.Error);
        Assert.True(full.ExitCode == 0, full.Console.Error);
        var captured = Assert.IsType<RepositorySnapshot>(capture.Snapshot);
        Assert.All(captured.Files.Values.Where(static file => file.Path.Value.StartsWith("Meta/Digestion/", StringComparison.Ordinal)),
            static file => { Assert.Empty(file.RawBytes); Assert.False(file.ContentWasRead); });
        Assert.Contains(captured.Files.Values, static file => file.Path.Value.StartsWith("Meta/Digestion/atoms/", StringComparison.Ordinal));
        var expectedFiles = Directory.GetFiles(fullOutput.Path).Select(Path.GetFileName).Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(expectedFiles, Directory.GetFiles(streamedOutput.Path).Select(Path.GetFileName).Order(StringComparer.Ordinal));
        foreach (var path in expectedFiles)
            Assert.Equal(File.ReadAllBytes(Path.Combine(fullOutput.Path, path!)), File.ReadAllBytes(Path.Combine(streamedOutput.Path, path!)));
    }

    private static (int ExitCode, BufferedConsole Console) Run(
        Fixture fixture,
        string outputDirectory,
        IReadOnlyList<string> trustArguments,
        IReadOnlyList<string>? extraArguments = null,
        ICliEnvironment? environment = null)
    {
        var console = new BufferedConsole();
        var arguments = new List<string>
        {
            "truth-release",
            "--out", outputDirectory,
            "--candidate-lean-report", fixture.ReportPath,
            "--producer-package-commit", ProducerCommit,
            "--produced-at", "2026-08-23T00:00:00Z",
        };
        arguments.AddRange(trustArguments);
        string? generatedPack = null;
        if (extraArguments is not null)
        {
            arguments.AddRange(extraArguments);
        }
        else
        {
            generatedPack = Path.Combine(Path.GetTempPath(), $"scribe-pack-{Guid.NewGuid():N}.zip");
            var digest = ScribeResourcePack.Write(generatedPack, PackDefinitions(fixture)).TotalSha256;
            arguments.AddRange(PackArguments(generatedPack, digest));
        }

        try
        {
            var exitCode = CliApplication.Run(arguments, environment ?? fixture.Environment, console);
            return (exitCode, console);
        }
        finally
        {
            if (generatedPack is not null && File.Exists(generatedPack)) File.Delete(generatedPack);
        }
    }

    private static string[] GreenTrustArguments() =>
    [
        "--commit-on-protected-dev", "true",
        "--required-check", "engineering=success",
        "--required-check", "current=success",
    ];

    private static Fixture CreateFixture(bool receiptIntegrityMismatch = false, bool productionVerifier = false,
        bool additionalLocalSource = false, bool largeDigestionBodies = false)
    {
        var repositoryRoot = TestRepositoryLayout.FindRoot();
        var blueprintSourcePath = $"Blueprint/{BlueprintGid}.scribe.cs";
        var blueprintProjectionPath = $"Blueprint/{BlueprintGid}.md";
        var formalPath = BlueprintGid + ".lean";
        var dependencyPath = PathFor("Dependency");
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["lean-toolchain"] = Toolchain,
            ["lakefile.toml"] = "[package]\nname = \"fixture\"\n",
            ["lake-manifest.json"] = Manifest,
            [formalPath] = File.ReadAllText(Path.Combine(repositoryRoot, formalPath), Encoding.UTF8),
            [dependencyPath] = "theorem dependency : True := by trivial\n",
            [blueprintSourcePath] = File.ReadAllText(
                Path.Combine(repositoryRoot, blueprintSourcePath), Encoding.UTF8),
            [blueprintProjectionPath] = File.ReadAllText(
                Path.Combine(repositoryRoot, blueprintProjectionPath), Encoding.UTF8),
            ["Golden/Projection/statement-projection-pilot-v1.json"] = File.ReadAllText(
                Path.Combine(
                    repositoryRoot,
                    "Golden/Projection/statement-projection-pilot-v1.json"),
                Encoding.UTF8),
            ["Golden/Projection/statement-projection-expansion-v1.json"] = File.ReadAllText(
                Path.Combine(
                    repositoryRoot,
                    "Golden/Projection/statement-projection-expansion-v1.json"),
                Encoding.UTF8),
            [TheoryAtomizerDataLoader.DataPath] =
                Encoding.UTF8.GetString(DigestionTestSupport.RulesBytes),
            ["Meta/FILEMAP.toml"] = FileMap(),
            ["Meta/Digestion/backfill/fixture-source/source.toml"] =
                "source_id = \"fixture-source\"\n"
                + "path = \"docs/fixture.md\"\n"
                + "atomizer = \"none\"\n"
                + "genre_registry_check = \"no-registry\"\n"
                + "unregistered_genres = []\n",
            ["docs/fixture.md"] = "# Fixture\n",
        };
        var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [dependencyPath] = new(
                [],
                [Declaration("dependency")]),
            [formalPath] = new(
                ["D5.S0.Carrier.Dependency"],
                [Declaration("golden_spectral_marker")]),
        };
        if (receiptIntegrityMismatch)
        {
            AddReceiptIntegrityMismatch(files);
        }
        if (additionalLocalSource)
        {
            files["Blueprint/D5/S0/Carrier/LocalOnly.scribe.cs"] = "local definition outside the resource pack\n";
            files["Blueprint/D5/S0/Carrier/LocalOnly.md"] = "# Local projection\n";
        }
        var snapshotWithoutLedger = Decode(files);
        var report = LeanAxiomReport.Create(reports);
        if (productionVerifier)
        {
            files[blueprintSourcePath] = """
                using StrataLint.Scribe;

                return DocumentDefinition.Create(
                    ScribeDocument.Create(DefinitionDsl.Header("D5/S3/Midline/GoldenSpectralMarker", "Resource fixture"),
                        Heading.Create("Resource fixture"),
                        DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Body")))),
                    "Blueprint/D5/S3/Midline/GoldenSpectralMarker.scribe.cs");
                """;
            files[blueprintProjectionPath] = Encoding.UTF8.GetString(CanonicalMarkdownWriter.Write(
                SimpleDefinition(BlueprintGid).Document, DeclarationCatalog.Create(report)).AsSpan());
            files["Golden/Projection/statement-projection-pilot-v1.json"] =
                "{\"schema\":\"statement-projection-pilot-fixture-v1\",\"declarations\":[]}";
            files["Golden/Projection/statement-projection-expansion-v1.json"] =
                "{\"schema\":\"statement-projection-expansion-fixture-v1\",\"declarations\":[]}";
        }
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(snapshotWithoutLedger, report)).Capability;
        var dag = TruthDagProjectionAssembler.Build(snapshotWithoutLedger, lean);
        if (largeDigestionBodies)
        {
            for (var index = 0; index < 64; index++)
                files[$"Meta/Digestion/backfill/unused{index}/atoms.jsonl"] = new string('x', 8192) + "\n";
            var large = new string('z', 4 * 1024 * 1024);
            files["Meta/Digestion/atoms/sha256/" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(large)))] = large;
        }
        var temporary = new TemporaryDirectory();
        var gitRoot = Path.Combine(temporary.Path, "repository");
        Directory.CreateDirectory(gitRoot);
        InitializeGitRepository(gitRoot);
        WriteFiles(gitRoot, files);
        CommitAll(gitRoot, "fixture source");
        var originCommit = GitObject(gitRoot, "HEAD");
        var originTree = GitObject(gitRoot, "HEAD^{tree}");
        var generatorBlob = GitObject(gitRoot, "HEAD:lakefile.toml");
        var states = LeanTruthStates.Resolve(snapshotWithoutLedger, lean);
        var adjacency = LeanImportAdjacency.Build(snapshotWithoutLedger, lean);
        var realCatalog = Assert.IsType<FrozenMaterialOutcome.Accepted>(
            FrozenContentAddress.Build(
                snapshotWithoutLedger,
                lean,
                states,
                adjacency)).Capability;
        var ledgerFiles = EventFiles(realCatalog, "git-sha1:" + generatorBlob);
        AddLedgerFiles(files, ledgerFiles);
        WriteFiles(
            gitRoot,
            files.Where(static pair => pair.Key.StartsWith(
                FrozenLedgerChangeClassifier.AcceptedRoot + "/",
                StringComparison.Ordinal)));
        CommitAll(gitRoot, "fixture frozen ledger");
        var sourceCommit = GitObject(gitRoot, "HEAD");
        var sourceTree = GitObject(gitRoot, "HEAD^{tree}");
        var gateway = new GitRepositoryGateway(gitRoot);
        var rawRevision = gateway.ReadRevision(sourceCommit);
        var revisionSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(rawRevision)).Snapshot;
        var ledgerPrefix = FrozenLedgerChangeClassifier.AcceptedRoot + "/";
        var ledgerView = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            revisionSnapshot.Files.Values
                .Where(file => file.Path.Value.StartsWith(ledgerPrefix, StringComparison.Ordinal))
                .ToImmutableDictionary(static file => file.Path)));
        var reportPath = Path.Combine(temporary.Path, "candidate-lean-report.json");
        RawLeanReportArtifact.WriteFile(reportPath, revisionSnapshot, report);
        var reportBytes = ImmutableArray.CreateRange(File.ReadAllBytes(reportPath));
        File.WriteAllText(
            Path.Combine(gitRoot, formalPath),
            "-- mutable working tree bytes must be ignored\n" + files[formalPath],
            new UTF8Encoding(false));
        var mutableSource = new FakeLeanReportSource(null);
        var cli = new ProductionCliEnvironment(
            gitRoot,
            gateway,
            mutableSource,
            productionVerifier ? new ProductionScribeEmissionVerifier()
                : new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));
        return new Fixture(
            temporary,
            cli,
            gateway,
            mutableSource,
            reportPath,
            reportBytes,
            sourceCommit,
            sourceTree,
            ledgerView.EventSetRoot(),
            ledgerView.EventCount);
    }

    private static void AddReceiptIntegrityMismatch(IDictionary<string, string> files)
    {
        const string sourcePath = "docs/fixture.md";
        const string sourceText = "x";
        var sourceBytes = Encoding.UTF8.GetBytes(sourceText);
        var fingerprints = DigestionFingerprint.Compute(sourceBytes);
        var captured = DigestionCasStore.Capture(sourceBytes);
        var status = new DigestionStatus(
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed);
        var entry = new DigestionLedgerEntry(
            "fixture-source",
            sourcePath,
            AtomizerRegistry.NoAtomizerId,
            "receipt-mismatch",
            fingerprints,
            [new DigestionCoverageEdge(
                BlueprintGid + ".golden_spectral_marker",
                "sha256:" + new string('0', 64))],
            new DigestionReceipts([], [], null),
            status,
            captured.Reference);
        var document = DigestionTestSupport.Document(
            AtomizerRegistry.NoAtomizerId,
            [entry],
            "fixture-source",
            sourcePath,
            GenreRegistryCheck.NoGenreRegistry);
        files[sourcePath] = sourceText;
        files[captured.RelativePath] = sourceText;
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
    }

    private static LeanDeclaration Declaration(string name) => new(
        name,
        "theorem",
        "True",
        ["propext", "Classical.choice", "Quot.sound"])
    {
        NameKey = $"ns(n0,{name.Length}:{name})",
        IncludeInStatement = true,
    };

    private static RepositorySnapshot Decode(IReadOnlyDictionary<string, string> files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawSnapshot(files))).Snapshot;

    private static RawRepositorySnapshot RawSnapshot(IReadOnlyDictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(static pair =>
            RawRepositoryEntry.FromText(pair.Key, pair.Value)));

    private static void InitializeGitRepository(string repositoryRoot)
    {
        TestGit.Run(repositoryRoot, "init");
        TestGit.Run(
            repositoryRoot,
            "config",
            "user.email",
            "truth-release@example.invalid");
        TestGit.Run(
            repositoryRoot,
            "config",
            "user.name",
            "Truth Release Tests");
    }

    private static void WriteFiles(
        string repositoryRoot,
        IEnumerable<KeyValuePair<string, string>> files)
    {
        foreach (var (path, text) in files)
        {
            var destination = Path.Combine(repositoryRoot, path);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.WriteAllText(destination, text, new UTF8Encoding(false));
        }
    }

    private static void CommitAll(string repositoryRoot, string message)
    {
        TestGit.Run(repositoryRoot, "add", ".");
        TestGit.Run(repositoryRoot, "commit", "-m", message);
    }

    private static string GitObject(string repositoryRoot, string revision) =>
        TestGit.Run(repositoryRoot, "rev-parse", revision).Trim();

    private static string FileMap() => TestFileMap.Canonical[
        ..TestFileMap.Canonical.IndexOf("[[files]]", StringComparison.Ordinal)] + """
        [[files]]
        pattern = "Blueprint/**/*.md"
        kind = "generated"
        admission_plane = "content"
        produced_by = "ScribeEmitter"
        consumed_by = ["ScribeEmitter", "reader"]
        verified_by = ["ScribeEmitter"]
        artifact_id = "none"
        runtime_disposition = "committed-source"

        [[files]]
        pattern = "Blueprint/**/*.scribe.cs"
        kind = "data"
        admission_plane = "content"
        produced_by = "none"
        consumed_by = ["ScribeEmitter"]
        verified_by = ["ScribeCompiler"]
        artifact_id = "none"
        runtime_disposition = "committed-source"
        """ + "\n";

    private sealed class Fixture(
        TemporaryDirectory temporary,
        ProductionCliEnvironment environment,
        GitRepositoryGateway gateway,
        FakeLeanReportSource mutableLeanReportSource,
        string reportPath,
        ImmutableArray<byte> reportBytes,
        string sourceCommit,
        string sourceTree,
        string frozenLedgerHeadHash,
        int frozenLedgerSequence) : IDisposable
    {
        internal static Fixture Create(bool receiptIntegrityMismatch = false) =>
            CreateFixture(receiptIntegrityMismatch);

        internal ProductionCliEnvironment Environment { get; } = environment;

        internal string RepositoryRoot => Path.Combine(temporary.Path, "repository");

        internal GitRepositoryGateway Gateway { get; } = gateway;

        internal FakeLeanReportSource MutableLeanReportSource { get; } = mutableLeanReportSource;

        internal string ReportPath { get; } = reportPath;

        internal ImmutableArray<byte> ReportBytes { get; } = reportBytes;

        internal string SourceCommit { get; } = sourceCommit;

        internal string SourceTree { get; } = sourceTree;

        internal string FrozenLedgerHeadHash { get; } = frozenLedgerHeadHash;

        internal int FrozenLedgerSequence { get; } = frozenLedgerSequence;

        public void Dispose() => temporary.Dispose();
    }

    private sealed class CapturingScribeVerifier : IScribeEmissionVerifier
    {
        internal RepositorySnapshot? Snapshot { get; private set; }
        public VerifiedScribeEmissions Verify(RepositorySnapshot snapshot, LeanAxiomReport report,
            IReadOnlyList<DocumentDefinition> definitions)
        { Snapshot = snapshot; return VerifiedScribeEmissions.Empty; }
        public VerifiedScribeEmissions Verify(RepositorySnapshot snapshot, LeanAxiomReport report,
            RawChangeSet? changes = null, FrozenStateCatalog? frozenStates = null,
            FrozenStatementIndex? frozenStatements = null)
        { Snapshot = snapshot; return VerifiedScribeEmissions.Empty; }
    }

    private sealed class FullSnapshotGateway(IRepositoryGateway inner) : IRepositoryGateway
    {
        public AdmissionTopologyOutcome InspectAdmissionTopology() => inner.InspectAdmissionTopology();
        public PreparedRepository Prepare(string? protectedBase) => inner.Prepare(protectedBase);
        public FrozenRevisionIdentity ResolveCurrentRevision() => inner.ResolveCurrentRevision();
        public RawRepositorySnapshot ReadCurrent() => inner.ReadCurrent();
        public RawRepositorySnapshot ReadCurrent(IReadOnlyList<string> paths) => inner.ReadCurrent(paths);
        public IReadOnlyList<string> SearchCurrentPaths(IReadOnlyList<string> paths) => inner.SearchCurrentPaths(paths);
        public RawRepositorySnapshot ReadRevision(string revision) => inner.ReadRevision(revision);
        public RawRepositorySnapshot ReadRevisionProjection(string revision, Func<string, bool> readContents,
            Action<string, ReadOnlyMemory<byte>>? observeContentDigest = null)
        {
            var snapshot = inner.ReadRevision(revision);
            foreach (var entry in snapshot.Entries)
                observeContentDigest?.Invoke(entry.Path, SHA256.HashData(entry.Bytes.AsSpan()));
            return snapshot;
        }
        public RawChangeSet ReadCurrentChanges() => inner.ReadCurrentChanges();
        public RawChangeSet ReadChanges(string revision) => inner.ReadChanges(revision);
    }
}
