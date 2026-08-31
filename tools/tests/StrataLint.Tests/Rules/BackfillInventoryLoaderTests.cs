using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class BackfillInventoryLoaderTests
{
    [Fact]
    public void LegacySingleFileParserAndPreimageSupportDoNotExist()
    {
        var legacyLoad = typeof(BackfillInventoryLoader)
            .GetMethods(System.Reflection.BindingFlags.Static
                | System.Reflection.BindingFlags.Public
                | System.Reflection.BindingFlags.NonPublic)
            .SingleOrDefault(method => method.Name == "Load"
                && method.GetParameters() is [{ ParameterType: var parameterType }]
                && parameterType == typeof(string));
        var legacyWrite = typeof(BackfillInventoryWriter)
            .GetMethods(System.Reflection.BindingFlags.Static
                | System.Reflection.BindingFlags.Public
                | System.Reflection.BindingFlags.NonPublic)
            .SingleOrDefault(method => method.Name == "WriteForIngest");
        var aggregateWrite = typeof(BackfillInventoryWriter)
            .GetMethods(System.Reflection.BindingFlags.Static
                | System.Reflection.BindingFlags.Public
                | System.Reflection.BindingFlags.NonPublic)
            .SingleOrDefault(method => method.Name == "Write"
                && method.GetParameters() is [{ ParameterType: var parameterType }]
                && parameterType == typeof(BackfillInventoryDocument));
        var legacyPreimage = typeof(BackfillInventoryLoader).Assembly.GetType(
            "StrataLint.Engine.BackfillReceiptPreimage");

        Assert.Null(legacyLoad);
        Assert.Null(legacyWrite);
        Assert.Null(aggregateWrite);
        Assert.Null(legacyPreimage);
    }

    [Fact]
    public void RuntimeSnapshotRejectsLegacySingleFileLedger()
    {
        var fields = LoaderEntryFields().ToHashSet(StringComparer.Ordinal);
        fields.Remove("boundary");
        var text = EntryFixture(fields);

        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.Load(Snapshot((BackfillInventoryLoader.RelativePath, text))));

        Assert.Equal("legacy digestion ledger is unsupported; migrate to directory storage", exception.Message);
    }

    [Fact]
    public void DirectoryShapeProjectsTwoSourcesAtomsAndDerivedTask()
    {
        var snapshot = Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            Source("epsilon-v0.1", "docs/epsilon.md", "none"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"),
            Atom("epsilon-v0.1", "partial-closed", "epsilon-atom", "theorem/epsilon"),
            ("D5/X_Frontier/SyntheticDelta.lean", "/-- TASK D5-T0098 -/\ndef task : Unit := ()\n"));

        var document = BackfillInventoryLoader.Load(snapshot);

        Assert.Equal(["delta-v0.1", "epsilon-v0.1"],
            document.RequireDigestionSources().Select(static source => source.SourceId).ToArray());
        Assert.Equal([FixtureAtomId("theorem/delta"), FixtureAtomId("theorem/epsilon")],
            document.RequireDigestionEntries().Select(static entry => entry.AtomId).ToArray());
        var ticket = Assert.Single(document.RequireTickets());
        Assert.Equal("D5-T0098", ticket.CaseId);
        Assert.Equal("D5/X_Frontier/SyntheticDelta", ticket.Gid);
        Assert.Collection(
            document.RequireDigestionEntries(),
            entry =>
            {
                Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
                Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
            },
            entry =>
            {
                Assert.Equal(DigestionMigrationState.Partial, entry.ProjectedStatus.Migration);
                Assert.Equal(DigestionTruthState.Closed, entry.ProjectedStatus.Truth);
            });
    }

    [Fact]
    public void DirectoryAtomWriterPreservesLiveOptionalReceipts()
    {
        var atom = Atom("delta-v0.1", "absorbed-tail", "delta-atom", "theorem/delta");
        var authorizationPath = "Meta/Digestion/tail-authorizations/delta-atom.json";
        var authorizationSha = "sha256:1111111111111111111111111111111111111111111111111111111111111111";
        var liveAtom = atom.Text.Replace(
            "  chain_atoms: []\n  tail_authorization: null",
            "  chain_atoms:\n    - predecessor-atom\n"
            + $"  tail_authorization:\n    path: {authorizationPath}\n    sha256: {authorizationSha}",
            StringComparison.Ordinal);
        var document = BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, liveAtom)));

        var written = Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(
            Assert.Single(document.RequireDigestionEntries())).AsSpan());
        var roundTripped = BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, written)));

        var receipts = Assert.Single(roundTripped.RequireDigestionEntries()).Receipts;
        Assert.Equal(["predecessor-atom"], receipts.ChainAtoms.ToArray());
        Assert.Equal(authorizationPath, receipts.TailAuthorization?.Path);
        Assert.Equal(authorizationSha, receipts.TailAuthorization?.Sha256);
    }

    [Fact]
    public void BothStorageShapesAreRejected()
    {
        var text = EntryFixture(LoaderEntryFields().ToHashSet(StringComparer.Ordinal));
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            (BackfillInventoryLoader.RelativePath, text),
            Source("delta-v0.1", "docs/delta.md", "none"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"))));

        Assert.Equal("legacy digestion ledger is unsupported; migrate to directory storage", exception.Message);
    }

    [Fact]
    public void DiskRootRejectsBothStorageShapesWithSnapshotMessage()
    {
        using var temporary = new TemporaryDirectory();
        var legacyPath = Path.Combine(
            temporary.Path,
            BackfillInventoryLoader.RelativePath.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(legacyPath)!);
        File.WriteAllText(
            legacyPath,
            EntryFixture(LoaderEntryFields().ToHashSet(StringComparer.Ordinal)),
            new UTF8Encoding(false));
        var source = Source("delta-v0.1", "docs/delta.md", "none");
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        DirectoryLedgerTestSupport.Write(temporary.Path, new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [source.Path] = source.Text,
            [atom.Path] = atom.Text,
        });

        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.LoadRoot(temporary.Path));

        Assert.Equal("legacy digestion ledger is unsupported; migrate to directory storage", exception.Message);
    }

    [Fact]
    public void DiskRootRejectsLegacySingleFileLedger()
    {
        using var temporary = new TemporaryDirectory();
        var legacyPath = Path.Combine(
            temporary.Path,
            BackfillInventoryLoader.RelativePath.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(legacyPath)!);
        File.WriteAllText(
            legacyPath,
            EntryFixture(LoaderEntryFields().ToHashSet(StringComparer.Ordinal)),
            new UTF8Encoding(false));

        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.LoadRoot(temporary.Path));

        Assert.Equal("legacy digestion ledger is unsupported; migrate to directory storage", exception.Message);
    }

    [Fact]
    public void NeitherStorageShapeUsesExistingMissingMessage()
    {
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot()));

        Assert.Equal("required governance document is missing", exception.Message);
    }

    [Fact]
    public void CandidateDirectoryAtomWithUnknownEntryKeyIsRejected()
    {
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, atom.Text + "unexpected: value\n"))));

        Assert.Equal("source delta-v0.1 entry keys are not canonical", exception.Message);
    }

    [Fact]
    public void CanonicalAtomWithoutOwningSourceMetadataIsRejected()
    {
        var path = $"{BackfillInventoryLoader.RootPath}zeta-v0.1/residual-open/zeta-atom.yaml";
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"),
            (path, Atom("zeta-v0.1", "residual-open", "zeta-atom", "theorem/zeta").Text))));

        Assert.Equal($"backfill atom is not owned by exactly one source: {path}", exception.Message);
    }

    [Fact]
    public void SourceMetadataRejectsNoRegistryWithUnregisteredGenres()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            (sourcePath,
                "source_id = \"delta-v0.1\"\n"
                + "path = \"docs/delta.md\"\n"
                + "atomizer = \"none\"\n"
                + "genre_registry_check = \"no-registry\"\n"
                + "unregistered_genres = [\"未登记体\"]\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"))));

        Assert.Equal(
            $"no-registry requires empty unregistered_genres: {sourcePath}",
            exception.Message);
    }

    [Theory]
    [InlineData("[\"\"]")]
    [InlineData("[\"未登记体\", \"另一体\"]")]
    [InlineData("[\"未登记体\", \"未登记体\"]")]
    public void SourceMetadataRejectsBlankUnsortedOrDuplicateUnregisteredGenres(
        string unregisteredGenres)
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            (sourcePath,
                "source_id = \"delta-v0.1\"\n"
                + "path = \"docs/delta.md\"\n"
                + "atomizer = \"pzg-v1\"\n"
                + "genre_registry_check = \"collected\"\n"
                + $"unregistered_genres = {unregisteredGenres}\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"))));

        Assert.Equal(
            $"unregistered_genres must contain sorted unique nonempty tokens: {sourcePath}",
            exception.Message);
    }

    [Fact]
    public void SourceMetadataGenreProjectionRoundTripsCanonicalBytes()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var metadata =
            "source_id = \"delta-v0.1\"\n"
            + "path = \"docs/delta.md\"\n"
            + "atomizer = \"pzg-v1\"\n"
            + "genre_registry_check = \"collected\"\n"
            + "unregistered_genres = [\"另一体\", \"未登记体\"]\n"
            + "acknowledged_stale = [\"old-one\"]\n";
        var document = BackfillInventoryLoader.Load(Snapshot(
            (sourcePath, metadata),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta")));

        Assert.Equal(
            Encoding.UTF8.GetBytes(metadata),
            BackfillInventoryWriter.WriteSourceMetadata(
                Assert.Single(document.RequireDigestionSources())).ToArray());
    }

    [Theory]
    [InlineData("source_id = [\"delta-v0.1\"]\npath = \"docs/delta.md\"\natomizer = \"none\"\ngenre_registry_check = \"no-registry\"\nunregistered_genres = []\n")]
    [InlineData("source_id = \"delta-v0.1\"\npath = [\"docs/delta.md\", \"docs/epsilon.md\"]\natomizer = \"none\"\ngenre_registry_check = \"no-registry\"\nunregistered_genres = []\n")]
    [InlineData("source_id = \"delta-v0.1\"\npath = \"docs/delta.md\"\natomizer = []\ngenre_registry_check = \"no-registry\"\nunregistered_genres = []\n")]
    [InlineData("source_id = \"delta-v0.1\" trailing\npath = \"docs/delta.md\"\natomizer = \"none\"\ngenre_registry_check = \"no-registry\"\nunregistered_genres = []\n")]
    public void SourceMetadataRequiresExactlyOneQuotedScalarPerIdentityField(string metadata)
    {
        var path = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            (path, metadata),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"))));

        Assert.Equal($"source metadata identity fields must be single quoted strings: {path}", exception.Message);
    }

    [Fact]
    public void SourceMetadataRequiresAndLoadsTheGenreRegistryProjection()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var metadata = """
            source_id = "delta-v0.1"
            path = "docs/delta.md"
            atomizer = "pzg-v1"
            genre_registry_check = "collected"
            unregistered_genres = ["另一体", "未登记体"]
            """ + "\n";
        var document = BackfillInventoryLoader.Load(Snapshot(
            (sourcePath, metadata),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta")));

        var source = Assert.Single(document.RequireDigestionSources());
        Assert.Equal(
            metadata,
            Encoding.UTF8.GetString(BackfillInventoryWriter.WriteSourceMetadata(source).AsSpan()));
    }

    [Fact]
    public void SourceMetadataWithoutGenreRegistryProjectionIsRejected()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";

        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            (sourcePath, "source_id = \"delta-v0.1\"\npath = \"docs/delta.md\"\natomizer = \"none\"\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"))));

        Assert.Equal($"source metadata keys are not canonical: {sourcePath}", exception.Message);
    }

    [Fact]
    public void BaselineWithoutGenreProjectionIsUnavailableAndCannotBeReadAsNoRegistry()
    {
        var source = Source("delta-v0.1", "docs/delta.md", "none");
        var legacy = source.Text
            .Replace("genre_registry_check = \"no-registry\"\n", string.Empty, StringComparison.Ordinal)
            .Replace("unregistered_genres = []\n", string.Empty, StringComparison.Ordinal);
        var document = BackfillInventoryLoader.LoadBaseline(Snapshot(
            (source.Path, legacy),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta")));

        var loadedSource = Assert.Single(document.RequireDigestionSources());
        Assert.Equal(GenreRegistryProjection.Unavailable, loadedSource.GenreRegistryProjection);
        Assert.NotEqual(
            GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
            loadedSource.GenreRegistryProjection);
        var exception = Assert.Throws<InvalidOperationException>(
            () => loadedSource.GenreRegistryCheck);
        Assert.Equal("genre registry projection is unavailable", exception.Message);
    }

    [Fact]
    public void BaselineWithGenreMetadataStillExposesAnUnavailableProjection()
    {
        var source = Source("delta-v0.1", "docs/delta.md", "pzg-v1");
        var document = BackfillInventoryLoader.LoadBaseline(Snapshot(
            source,
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta")));

        var loadedSource = Assert.Single(document.RequireDigestionSources());
        Assert.Equal(GenreRegistryProjection.Unavailable, loadedSource.GenreRegistryProjection);
        var exception = Assert.Throws<InvalidOperationException>(
            () => loadedSource.GenreRegistryCheck);
        Assert.Equal("genre registry projection is unavailable", exception.Message);
    }

    [Fact]
    public void SourceMetadataRejectsInvalidGenreRegistryProjections()
    {
        var invalidProjections = new[]
        {
            "genre_registry_check = \"collected\"\nunregistered_genres = [\"未登记体\", \"另一体\"]\n",
            "genre_registry_check = \"collected\"\nunregistered_genres = [\"未登记体\", \"未登记体\"]\n",
            "genre_registry_check = \"collected\"\nunregistered_genres = [\"\"]\n",
            "genre_registry_check = \"collected\"\nunregistered_genres = \"未登记体\"\n",
            "genre_registry_check = [\"collected\"]\nunregistered_genres = []\n",
            "genre_registry_check = \"no-registry\"\nunregistered_genres = [\"未登记体\"]\n",
            "genre_registry_check = \"unknown\"\nunregistered_genres = []\n",
        };
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        foreach (var projection in invalidProjections)
        {
            Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
                (sourcePath,
                    "source_id = \"delta-v0.1\"\n"
                    + "path = \"docs/delta.md\"\n"
                    + "atomizer = \"pzg-v1\"\n"
                    + projection),
                Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"))));
        }
    }

    [Theory]
    [InlineData("zeta", "alpha")]
    [InlineData("same", "same")]
    [InlineData(" ", null)]
    public void SourceMetadataWriterRejectsInvalidGenreRegistryProjections(
        string first,
        string? second)
    {
        var source = Assert.Single(BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "pzg-v1")))
            .RequireDigestionSources());
        var tokens = second is null
            ? System.Collections.Immutable.ImmutableArray.Create(first)
            : System.Collections.Immutable.ImmutableArray.Create(first, second);
        source = source with
        {
            GenreRegistryProjection = GenreRegistryProjection.Available(
                GenreRegistryCheck.Collected(tokens)),
        };

        var exception = Assert.Throws<InvalidOperationException>(() =>
            BackfillInventoryWriter.WriteSourceMetadata(source));

        Assert.Contains("unregistered genres", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SourceMetadataMustUseCanonicalWriterEncoding()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var noncanonical = """
            path = "docs/delta.md"
            source_id = "delta-v0.1"
            atomizer = "pzg-v1"
            genre_registry_check = "collected"
            unregistered_genres = []
            """ + "\n";

        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            (sourcePath, noncanonical),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"))));

        Assert.Equal($"source metadata is not canonically encoded: {sourcePath}", exception.Message);
    }

    [Fact]
    public void CandidateDeltaUsesTrustedBaselineForUnchangedNoncanonicalMetadata()
    {
        var source = Source("delta-v0.1", "docs/delta.md", "none");
        var baseline = Snapshot(
            source,
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"));
        var candidate = Snapshot(
            (source.Path, source.Text.Replace(
                "unregistered_genres = []\n",
                "unregistered_genres = []\n\n",
                StringComparison.Ordinal)),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"));

        var loaded = BackfillInventoryLoader.LoadCandidateDelta(
            candidate,
            baseline,
            RawChangeSet.Create(["D5/S3/Probe/Unrelated.lean"]));

        Assert.Equal("delta-v0.1", Assert.Single(loaded.RequireDigestionSources()).SourceId);
    }

    [Fact]
    public void CandidateDeltaStillRejectsNoncanonicalMetadataWhenMetadataIsInDelta()
    {
        var source = Source("delta-v0.1", "docs/delta.md", "none");
        var baseline = Snapshot(
            source,
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"));
        var candidate = Snapshot(
            (source.Path, source.Text.Replace(
                "unregistered_genres = []\n",
                "unregistered_genres = []\n\n",
                StringComparison.Ordinal)),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"));

        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.LoadCandidateDelta(
                candidate,
                baseline,
                RawChangeSet.Create([source.Path])));

        Assert.Contains("not canonically encoded", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CandidateDeltaDoesNotRestoreBaselineAtomDeletedFromCandidate()
    {
        var source = Source("delta-v0.1", "docs/delta.md", "none");
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var baseline = Snapshot(
            source,
            (atom.Path, atom.Text + "ast_path: theorem/delta\n"));
        var candidate = Snapshot(source);

        var loaded = BackfillInventoryLoader.LoadCandidateDelta(
            candidate,
            baseline,
            RawChangeSet.Create(["D5/S3/Probe/Unrelated.lean"]));

        Assert.Empty(loaded.RequireDigestionEntries());
    }

    [Fact]
    public void SourceMetadataPreservesAcknowledgedStaleArray()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var document = BackfillInventoryLoader.Load(Snapshot(
            (sourcePath, "source_id = \"delta-v0.1\"\npath = \"docs/delta.md\"\natomizer = \"none\"\ngenre_registry_check = \"no-registry\"\nunregistered_genres = []\nacknowledged_stale = [\"old-one\", \"old-two\"]\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta")));

        Assert.Equal(
            ["old-one", "old-two"],
            Assert.Single(document.RequireDigestionSources()).AcknowledgedStale.ToArray());
    }

    [Fact]
    public void SourceMetadataRejectsNoncanonicalEmptyAcknowledgedStaleArray()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            (sourcePath, "source_id = \"delta-v0.1\"\npath = \"docs/delta.md\"\natomizer = \"none\"\ngenre_registry_check = \"no-registry\"\nunregistered_genres = []\nacknowledged_stale = []\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"))));
        Assert.Equal($"source metadata is not canonically encoded: {sourcePath}", exception.Message);
    }

    [Fact]
    public void HistoricalBaselineTrustsNoncanonicalEmptyAcknowledgedStaleArray()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var document = BackfillInventoryLoader.LoadBaseline(Snapshot(
            (sourcePath, "source_id = \"delta-v0.1\"\npath = \"docs/delta.md\"\natomizer = \"none\"\nacknowledged_stale = []\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta")));

        Assert.Empty(Assert.Single(document.RequireDigestionSources()).AcknowledgedStale);
    }

    [Theory]
    [InlineData("\"old-one\"")]
    [InlineData("[\"\"]")]
    [InlineData("[\"   \"]")]
    [InlineData("[\"old-one\", \"\"]")]
    public void AcknowledgedStaleRequiresNonemptyQuotedStringArray(string encoded)
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            (sourcePath, $"source_id = \"delta-v0.1\"\npath = \"docs/delta.md\"\natomizer = \"none\"\ngenre_registry_check = \"no-registry\"\nunregistered_genres = []\nacknowledged_stale = {encoded}\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"))));

        Assert.Equal($"acknowledged_stale must be a quoted string array without blank elements: {sourcePath}", exception.Message);
    }

    [Theory]
    [InlineData("residual-open", "delta-atom.txt")]
    [InlineData("pending-open", "delta-atom.yaml")]
    [InlineData("residual-frozen", "delta-atom.yaml")]
    [InlineData("residual-open/nested", "delta-atom.yaml")]
    public void NoncanonicalDirectoryFilesAreRejected(string state, string fileName)
    {
        var path = $"{BackfillInventoryLoader.RootPath}delta-v0.1/{state}/{fileName}";
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (path, "value: invalid\n"))));

        Assert.Equal($"noncanonical digestion ledger path: {path}", exception.Message);
    }

    [Theory]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/source.toml")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/residual-open/atom-0dca.yaml")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/partial-closed/atom-0f28.yaml")]
    [InlineData("Meta/Digestion/backfill/epsilon-v0.1/absorbed-tail/atom.yaml")]
    public void CanonicalDigestionLedgerPathsAreRecognized(string path)
        => Assert.True(BackfillInventoryLoader.IsCanonicalPath(path));

    [Theory]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/residual-open/atom.txt")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/pending-open/atom.yaml")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/residual-frozen/atom.yaml")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/residual-open/nested/atom.yaml")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/notes.toml")]
    [InlineData("Meta/Digestion/ticket-index.yaml")]
    [InlineData("Meta/BACKFILL.yaml")]
    public void NoncanonicalDigestionLedgerPathsAreRejected(string path)
        => Assert.False(BackfillInventoryLoader.IsCanonicalPath(path));

    [Fact]
    public void DirectoryReceiptsWithoutOptionalLiveKeysAreAccepted()
    {
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var withoutOptionalKeys = atom.Text
            .Replace("  chain_atoms: []\n", string.Empty, StringComparison.Ordinal)
            .Replace("  tail_authorization: null\n", string.Empty, StringComparison.Ordinal);

        var entry = Assert.Single(BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, withoutOptionalKeys))).RequireDigestionEntries());

        Assert.Empty(entry.Receipts.ChainAtoms);
        Assert.Null(entry.Receipts.TailAuthorization);
    }

    [Fact]
    public void DirectoryAtomWithoutCasRefIsRejected()
    {
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var fingerprint = "sha256:" + FixtureAtomId("theorem/delta");
        var withoutCasRef = atom.Text.Replace(
            $"cas_ref: {fingerprint}\n",
            string.Empty,
            StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, withoutCasRef))));

        Assert.Equal("source delta-v0.1 entry keys are not canonical", exception.Message);
    }

    [Fact]
    public void DirectoryCasRefRoundTripsCanonically()
    {
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var document = BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            atom));
        var entry = Assert.Single(document.RequireDigestionEntries());
        var written = Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan());
        var roundTripped = BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, written)));

        Assert.Equal(
            "sha256:" + FixtureAtomId("theorem/delta"),
            entry.CasRef);
        Assert.Equal(entry.CasRef, Assert.Single(roundTripped.RequireDigestionEntries()).CasRef);
    }

    [Fact]
    public void DirectoryAtomWriterQuotesMappingLikeQuarantineScalars()
    {
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var document = BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            atom));
        var entry = Assert.Single(document.RequireDigestionEntries());
        var expected = "missing prerequisite: tracked bridge";
        var quarantined = entry with
        {
            Receipts = entry.Receipts with
            {
                Quarantine = new DigestionQuarantine(expected, "bridge lands"),
            },
        };

        var written = Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(quarantined).AsSpan());
        var roundTripped = BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, written)));

        Assert.Contains("justification: 'missing prerequisite: tracked bridge'", written);
        Assert.Equal(
            expected,
            Assert.Single(roundTripped.RequireDigestionEntries()).Receipts.Quarantine?.Justification);
    }

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files)
    {
        var raw = RawRepositorySnapshot.Create(
            files.Select(static file => RawRepositoryEntry.FromText(file.Path, file.Text)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static void AssertGenreRegistryProjectionUnavailable(DigestionLedgerSource source)
    {
        Assert.Equal(GenreRegistryProjection.Unavailable, source.GenreRegistryProjection);
        Assert.NotEqual(
            GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
            source.GenreRegistryProjection);
        var exception = Assert.Throws<InvalidOperationException>(() => source.GenreRegistryCheck);
        Assert.Equal("genre registry projection is unavailable", exception.Message);
    }

    private static (string Path, string Text) Source(string sourceId, string path, string atomizer) =>
        ($"{BackfillInventoryLoader.RootPath}{sourceId}/source.toml",
            $"source_id = \"{sourceId}\"\npath = \"{path}\"\natomizer = \"{atomizer}\"\n"
            + $"genre_registry_check = \"{(atomizer == AtomizerRegistry.NoAtomizerId ? "no-registry" : "collected")}\"\n"
            + "unregistered_genres = []\n");

    private static (string Path, string Text) Atom(
        string sourceId,
        string state,
        string atomLabel,
        string content)
    {
        var fingerprint = DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(content)).RawSha256;
        var atomId = fingerprint["sha256:".Length..];
        return ($"{BackfillInventoryLoader.RootPath}{sourceId}/{state}/{atomId}.yaml", $$"""
            fingerprints:
              raw_sha256: {{fingerprint}}
              normalized_sha256: {{fingerprint}}
            cas_ref: {{fingerprint}}
            coverage_gids: []
            receipts:
              coverage: []
              scribe: []
              unresolved_subitems: []
              chain_atoms: []
              tail_authorization: null
            """ + "\n");
    }

    private static string FixtureAtomId(string content) =>
        DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(content)).RawSha256["sha256:".Length..];

    private static string[] LoaderEntryFields() =>
        BackfillInventoryDocument.EntryFieldUniverse.ToArray();

    private static string EntryFixture(IReadOnlySet<string> fields)
    {
        var entry = new StringBuilder();
        if (fields.Contains("atom_id"))
        {
            entry.AppendLine("      - atom_id: synthetic-atom");
        }
        else
        {
            entry.AppendLine("      - synthetic_placeholder: value");
        }

        if (fields.Contains("ast_path"))
        {
            entry.AppendLine("        ast_path: theorem/1.1");
        }

        if (fields.Contains("boundary"))
        {
            entry.AppendLine("        boundary:");
            entry.AppendLine("          ast_path: theorem/1.1");
            entry.AppendLine("          start_byte: 0");
            entry.AppendLine("          end_byte: 1");
        }

        if (fields.Contains("fingerprints"))
        {
            entry.AppendLine("        fingerprints:");
            entry.AppendLine("          raw_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000");
            entry.AppendLine("          normalized_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000");
        }

        if (fields.Contains("cas_ref"))
        {
            entry.AppendLine("        cas_ref: sha256:0000000000000000000000000000000000000000000000000000000000000000");
        }

        if (fields.Contains("coverage_gids"))
        {
            entry.AppendLine("        coverage_gids: []");
        }

        if (fields.Contains("receipts"))
        {
            entry.AppendLine("        receipts:");
            entry.AppendLine("          coverage: []");
            entry.AppendLine("          scribe: []");
            entry.AppendLine("          unresolved_subitems: []");
            entry.AppendLine("          chain_atoms: []");
            entry.AppendLine("          tail_authorization: null");
        }

        if (fields.Contains("status"))
        {
            entry.AppendLine("        status:");
            entry.AppendLine("          migration: residual");
            entry.AppendLine("          truth: open");
        }

        return """
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: synthetic-source
                path: docs/source.md
                atomizer: synthetic-v1
                entries:
            """ + "\n" + entry;
    }
}
