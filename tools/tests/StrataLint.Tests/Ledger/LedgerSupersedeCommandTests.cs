using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LedgerSupersedeCommandTests
{
    private static readonly ImmutableArray<string> RealSupportingBlobOids =
    [
        "git-sha1:1123096aedfa69a2db94d58b957a45f8dc0cc006",
        "git-sha1:18640c8b066b182147f324d3aefd8ee48ee45238",
    ];

    [Fact]
    public void RootUsageListsLedgerSupersedeCommand()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [],
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("ledger-supersede", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void LedgerSupersedeVerbDispatchesToTheEnvironment()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["ledger-supersede", "--candidate-lean-report", "report.json"],
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("ledger supersede is not configured", console.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("UNKNOWN_COMMAND", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionCommandAppendsSupersedeForPinBumpAndThenIsIdempotent()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(pinBump: true);
        var baselineLines = FrozenLedgerTestData.Lines(fixture.BaselineBytes);
        var arguments = new[] { "--candidate-lean-report", fixture.ReportPath };

        var first = fixture.Environment.SupersedeLedger(arguments);

        Assert.True(first.Success, first.Error);
        Assert.Contains("appended_supersedes=1", first.Output, StringComparison.Ordinal);
        var files = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        var view = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            files.ToImmutableDictionary(static file => file.Path)));
        Assert.Equal(baselineLines.Length + 1, view.EventCount);
        var active = Assert.Single(view.ActiveByCase.Values);
        Assert.NotNull(active.Environment);
        Assert.Equal(
            FrozenLedgerTestData.GitBlobOid("leanprover/lean4:v4.25.0\n"),
            active.Environment.LeanToolchainBlobOid);
        var references = Assert.Single(fixture.Gateway.FrozenReferenceValidations);
        Assert.Single(references.Inputs);
        Assert.Single(references.EnvironmentReferences);
        Assert.Single(references.CommitOids);
        Assert.Single(references.TreeOids);
        Assert.Equal(4, references.BlobOids.Length);
        var supersede = Assert.Single(view.Events, static item => item.EventType == "Supersede");
        Assert.False(
            supersede.Payload.GetProperty("input").TryGetProperty("supporting_blob_oids", out _),
            "Supersede input duplicated its named environment pins");

        var afterFirst = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);
        var second = fixture.Environment.SupersedeLedger(arguments);

        Assert.True(second.Success, second.Error);
        Assert.Contains("no changed environment pins", second.Output, StringComparison.Ordinal);
        Assert.Equal(afterFirst, FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
        Assert.Single(fixture.Gateway.FrozenReferenceValidations);
    }

    [Fact]
    public void ProductionSupersedeWriterEmitsCurrentSchemaV4()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(pinBump: true);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.True(result.Success, result.Error);
        var files = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        var view = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            files.ToImmutableDictionary(static file => file.Path)));
        var supersede = Assert.Single(view.Events, static item => item.EventType == "Supersede");
        Assert.Equal(FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion, supersede.SchemaVersion);
        Assert.Equal(4, supersede.SchemaVersion);
    }

    [Fact]
    public void SupersedeRejectsWeakerMeaningFromChangedImportedModule()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(
            currentAStatementMaterial: "ambiently-weakened-imported-expression",
            pinBump: true,
            aImportsB: true,
            reportBDriftInChangeSet: true);
        var before = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.False(result.Success, result.Output);
        Assert.Contains("import closure", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(before, FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    [Fact]
    public void SupersedeAcceptsPinBumpStatementDriftWhenRepositoryImportClosureIsByteUnchanged()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(
            currentAStatementMaterial: "ambiently-different-elaborated-expression",
            pinBump: true,
            aImportsB: true);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_supersedes=2", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void SupersedeAcceptsPinnedExternalImportElaborationDrift()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(
            currentAStatementMaterial: "ambiently-different-elaborated-expression",
            aImportsExternal: true,
            externalPackagePinned: true,
            externalPackagePinBump: true);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_supersedes=1", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void SupersedeRejectsWeakerMeaningFromPinnedExternalImport()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(
            currentAStatementMaterial: "True",
            pinBump: true,
            aImportsExternal: true,
            externalPackagePinned: true);
        var before = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.False(result.Success, result.Output);
        Assert.Contains("trivial truth", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(before, FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    [Fact]
    public void SupersedeRejectsStatementDriftWhenOnlyManifestMetadataChanges()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(
            currentAStatementMaterial: "ambiently-different-elaborated-expression",
            aImportsExternal: true,
            externalPackagePinned: true,
            externalPackageManifestOnlyDrift: true);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.False(result.Success, result.Output);
        Assert.Contains("semantic pin", result.Error, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void SupersedeRejectsWeakerMeaningFromAnUntrackedExternalImport()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(
            currentAStatementMaterial: "True",
            pinBump: true,
            aImportsExternal: true);
        var before = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.False(result.Success, result.Output);
        Assert.Contains("external import", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(before, FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    [Fact]
    public void ProtectedPinReadsDoNotGrowWithDistinctBaseCommitOids()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(
            currentAStatementMaterial: "Int",
            currentBStatementMaterial: "Int",
            pinBump: true,
            aImportsB: true);
        LedgerSupersedeFixtureFiles.RewriteFreezeInputs(
            fixture.LedgerPath,
            static (input, index) => input["base_commit_oid"] = FrozenLedgerTestData.GitOid(
                index == 0 ? '1' : '2'));

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.True(result.Success, result.Error);
        Assert.Empty(fixture.Gateway.ReadRevisionCalls);
        Assert.Single(fixture.Gateway.EnvironmentPinBlobReads);
    }

    [Fact]
    public void SupportingBlobPinSnapshotsMatchWholeProtectedTreeSemanticsForRealLedgerEntries()
    {
        using var repository = new SyntheticPinRepository();
        foreach (var fixtureContents in ReadRealFreezeFixtures())
        {
            using var document = JsonDocument.Parse(fixtureContents);
            var root = document.RootElement;
            var entry = FrozenLedgerBaseViewReader.ReadFreeze(
                root.GetProperty("payload"),
                root.GetProperty("event_hash").GetString()!);
            Assert.Equal(
                RealSupportingBlobOids.ToArray(),
                entry.Payload.Input.SupportingBlobOids.ToArray());
            entry = repository.Adapt(entry);
            var pinRaw = repository.Gateway.ReadEnvironmentPinBlobs(entry.Payload.Input);
            var pinSnapshot = Decode(pinRaw);
            var wholeSnapshot = repository.FullSnapshot;
            var changedCandidate = Decode(RawRepositorySnapshot.Create(pinRaw.Entries.Select(
                static item => item.Path == "lean-toolchain"
                    ? RawRepositoryEntry.FromText("lean-toolchain", "leanprover/lean4:v0.0.0\n")
                    : item)));
            var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(
                StringComparer.Ordinal)
            {
                [entry.Material.RepoPath.Value] = new(
                    ImmutableArray<string>.Empty,
                    ImmutableArray<LeanDeclaration>.Empty),
            });

            Assert.True(LeanImportClosure.ProtectedEnvironmentMatchesEntry(entry, pinSnapshot));
            Assert.Equal(
                LeanImportClosure.RelevantSemanticPinsChanged(
                    report,
                    entry.Material.RepoPath,
                    wholeSnapshot,
                    wholeSnapshot),
                LeanImportClosure.RelevantSemanticPinsChanged(
                    report,
                    entry.Material.RepoPath,
                    pinSnapshot,
                    wholeSnapshot));
            Assert.Equal(
                LeanImportClosure.RelevantSemanticPinsChanged(
                    report,
                    entry.Material.RepoPath,
                    wholeSnapshot,
                    changedCandidate),
                LeanImportClosure.RelevantSemanticPinsChanged(
                    report,
                    entry.Material.RepoPath,
                    pinSnapshot,
                    changedCandidate));
        }
    }

    [Fact]
    public void EnvironmentPinBlobReadFailsClosedWhenRecordedOidDoesNotNameAPinFile()
    {
        using var repository = new SyntheticPinRepository();
        using var document = JsonDocument.Parse(ReadPrimaryRealFreezeFixture());
        var payload = document.RootElement.GetProperty("payload");
        var entry = FrozenLedgerBaseViewReader.ReadFreeze(
            payload,
            document.RootElement.GetProperty("event_hash").GetString()!);
        Assert.Equal(
            RealSupportingBlobOids.ToArray(),
            entry.Payload.Input.SupportingBlobOids.ToArray());
        var input = repository.Adapt(entry).Payload.Input with
        {
            SupportingBlobOids =
            [
                entry.Payload.Input.SupportingBlobOids[0],
                FrozenLedgerTestData.GitOid('f'),
            ],
        };

        var exception = Assert.Throws<InvalidOperationException>(
            () => repository.Gateway.ReadEnvironmentPinBlobs(input));

        Assert.Contains("do not resolve", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ProtectedPinReadsFailClosedWhenSupportingBlobOidsAreMissing()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(
            currentAStatementMaterial: "Int",
            pinBump: true);
        LedgerSupersedeFixtureFiles.RewriteFreezeInputs(
            fixture.LedgerPath,
            static (input, _) => input.Remove("supporting_blob_oids"));
        var before = LedgerSupersedeFixtureFiles.ReadRawLedgerDirectory(fixture.LedgerPath);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.False(result.Success, result.Output);
        Assert.Contains("supporting_blob_oids is not an array", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, LedgerSupersedeFixtureFiles.ReadRawLedgerDirectory(fixture.LedgerPath));
    }

    [Fact]
    public void ProtectedPinReadsFailClosedForNamedEnvironmentEntriesWithoutSupportingBlobOids()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(pinBump: true);
        var supersede = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);
        Assert.True(supersede.Success, supersede.Error);
        var view = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath)
                .ToImmutableDictionary(static file => file.Path)));
        var entry = Assert.Single(view.ActiveByCase.Values);
        Assert.NotNull(entry.Environment);
        Assert.Empty(entry.Payload.Input.SupportingBlobOids);
        var reader = new ProtectedPinSnapshotReader(fixture.Gateway);

        var exception = Assert.Throws<InvalidOperationException>(() => reader.Read(entry));

        Assert.Contains("exactly two", exception.Message, StringComparison.Ordinal);
        Assert.Empty(fixture.Gateway.EnvironmentPinBlobReads);
    }

    [Theory]
    [MemberData(nameof(InvalidProtectedSupportingBlobOids))]
    public void ProtectedPinReadsFailClosedForInvalidSupportingBlobOids(
        string[] supportingBlobOids,
        string expectedError)
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(
            currentAStatementMaterial: "Int",
            pinBump: true);
        LedgerSupersedeFixtureFiles.RewriteFreezeInputs(
            fixture.LedgerPath,
            (input, _) => input["supporting_blob_oids"] = new JsonArray(
                supportingBlobOids.Select(static oid => JsonValue.Create(oid)).ToArray()));
        var before = LedgerSupersedeFixtureFiles.ReadRawLedgerDirectory(fixture.LedgerPath);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.False(result.Success, result.Output);
        Assert.Contains(expectedError, result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(supportingBlobOids.Length == 2 ? 1 : 0, fixture.Gateway.EnvironmentPinBlobReads.Count);
        Assert.Equal(before, LedgerSupersedeFixtureFiles.ReadRawLedgerDirectory(fixture.LedgerPath));
    }

    public static TheoryData<string[], string> InvalidProtectedSupportingBlobOids => new()
    {
        { [], "exactly two" },
        { [FrozenLedgerTestData.GitOid('1')], "exactly two" },
        {
            [
                FrozenLedgerTestData.GitOid('1'),
                FrozenLedgerTestData.GitOid('2'),
                FrozenLedgerTestData.GitOid('3'),
            ],
            "exactly two"
        },
        {
            [FrozenLedgerTestData.GitOid('1'), FrozenLedgerTestData.GitOid('2')],
            "repository could not be read"
        },
    };

    private static IReadOnlyList<string> ReadRealFreezeFixtures() =>
    [
        ReadPrimaryRealFreezeFixture(),
        TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
            "Golden/Frozen/accepted/6480513c972db6515b4fa8d19bd6778cf05e255a47df5de8b348d31526f26716.json")),
        TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
            "Golden/Frozen/accepted/451af39dac628e16c4040114872b4f607f7fe80e05d60fcec89b65e88dbbad6f.json")),
    ];

    private static string ReadPrimaryRealFreezeFixture() =>
        TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
            "Golden/Frozen/accepted/7b1891a1e3b89ad03abf0b55d5b46bc1a4c61b5d593133ef6e92e31ef27b7d3d.json"));

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

    private sealed class SyntheticPinRepository : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string commitOid;
        private readonly string treeOid;
        private readonly ImmutableArray<string> supportingBlobOids;

        internal SyntheticPinRepository()
        {
            ReviewRegressionTests.RunGit(temporary.Path, "init");
            ReviewRegressionTests.RunGit(
                temporary.Path,
                "config",
                "user.email",
                "stratalint@example.invalid");
            ReviewRegressionTests.RunGit(
                temporary.Path,
                "config",
                "user.name",
                "StrataLint Tests");
            File.WriteAllText(
                Path.Combine(temporary.Path, "lean-toolchain"),
                "leanprover/lean4:v4.31.0\n");
            File.WriteAllText(
                Path.Combine(temporary.Path, "lake-manifest.json"),
                "{\"packages\":[]}\n");
            File.WriteAllText(
                Path.Combine(temporary.Path, "unrelated.txt"),
                "unrelated historical bytes\n");
            ReviewRegressionTests.RunGit(temporary.Path, "add", ".");
            ReviewRegressionTests.RunGit(temporary.Path, "commit", "-m", "pin fixture");
            commitOid = ReviewRegressionTests.RunGit(temporary.Path, "rev-parse", "HEAD").Trim();
            treeOid = ReviewRegressionTests.RunGit(temporary.Path, "rev-parse", "HEAD^{tree}").Trim();
            supportingBlobOids = new[]
                {
                    "lake-manifest.json",
                    "lean-toolchain",
                }
                .Select(path => "git-sha1:" + ReviewRegressionTests.RunGit(
                    temporary.Path,
                    "hash-object",
                    path).Trim())
                .Order(StringComparer.Ordinal)
                .ToImmutableArray();
            Gateway = new GitRepositoryGateway(temporary.Path);
            FullSnapshot = Decode(Gateway.ReadRevision(commitOid));
        }

        internal GitRepositoryGateway Gateway { get; }

        internal RepositorySnapshot FullSnapshot { get; }

        internal FrozenActiveEntry Adapt(FrozenActiveEntry entry) => entry with
        {
            Payload = entry.Payload with
            {
                Input = entry.Payload.Input with
                {
                    BaseCommitOid = "git-sha1:" + commitOid,
                    BaseTreeOid = "git-sha1:" + treeOid,
                    SupportingBlobOids = supportingBlobOids,
                },
            },
        };

        public void Dispose() => temporary.Dispose();
    }
}

internal static class LedgerSupersedeFixtureFiles
{
    internal static void RewriteFreezeInputs(
        string ledgerPath,
        Action<JsonObject, int> rewrite)
    {
        var index = 0;
        foreach (var path in Directory.EnumerateFiles(ledgerPath, "*.json")
                     .Order(StringComparer.Ordinal))
        {
            var root = JsonNode.Parse(File.ReadAllText(path))?.AsObject()
                ?? throw new InvalidOperationException("ledger fixture event is not a JSON object");
            if (root["event_type"]?.GetValue<string>() != "Freeze")
            {
                continue;
            }

            var input = root["payload"]?["input"]?.AsObject()
                ?? throw new InvalidOperationException("ledger fixture Freeze input is absent");
            rewrite(input, index++);
            File.WriteAllText(path, root.ToJsonString(new JsonSerializerOptions
            {
                WriteIndented = false,
            }) + "\n");
        }

        Assert.True(index > 0, "ledger fixture contains no Freeze event");
    }

    internal static IReadOnlyDictionary<string, byte[]> ReadRawLedgerDirectory(string ledgerPath) =>
        Directory.EnumerateFiles(ledgerPath, "*.json")
            .Order(StringComparer.Ordinal)
            .ToDictionary(
                static path => Path.GetFileName(path),
                File.ReadAllBytes,
                StringComparer.Ordinal);
}
