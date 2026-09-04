using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class LedgerAlignWriterTests
{
    private const string ExpectedAddedModuleStatementPin =
        "sha256:2737dabb279d14181efe09f7531e5c4664421bdbc19bbcf8b588f8d71123954c";

    [Fact]
    public void RegisteredDriftIsAlignedAndSecondRunDoesNotWrite()
    {
        var original = ModuleWithReport("A", Source("A"), "True");
        var current = ModuleWithReport("A", Source("A"), "True = True");
        using var fixture = new AlignFixture(current);
        var originalCatalog = BuildCatalog(original);
        fixture.InstallAccepted(originalCatalog);
        fixture.InstallState("A", originalCatalog.ByPath[RepoPathFor("A")].StatementId);

        var first = fixture.Align();
        var bytesAfterFirst = fixture.AllPublishedBytes();
        var second = fixture.AlignWithAcceptedWritesDenied();

        Assert.True(first.Success, first.Error);
        Assert.Contains(
            "LEDGER_ALIGN selectors_considered=1 changed=1 added=0 unchanged=0 conflicts=0\n",
            first.Output,
            StringComparison.Ordinal);
        Assert.True(second.Success, second.Error);
        Assert.Contains(
            "LEDGER_ALIGN selectors_considered=1 changed=0 added=0 unchanged=1 conflicts=0\n",
            second.Output,
            StringComparison.Ordinal);
        Assert.Equal(bytesAfterFirst, fixture.AllPublishedBytes());
        Assert.Equal(fixture.StatePin("A"), fixture.EventPin("A"));
    }

    [Fact]
    public void SelectorAlignsOnlyTheNamedRegisteredMember()
    {
        var oldA = ModuleWithReport("A", Source("A"), "old-a");
        var oldB = ModuleWithReport("B", Source("B"), "old-b");
        var newA = oldA with { StatementMaterial = "new-a" };
        var newB = oldB with { StatementMaterial = "new-b" };
        using var fixture = new AlignFixture(newA, newB);
        var original = BuildCatalog(oldA, oldB);
        fixture.InstallAccepted(original);
        fixture.InstallState("A", original.ByPath[RepoPathFor("A")].StatementId);
        fixture.InstallState("B", original.ByPath[RepoPathFor("B")].StatementId);
        var oldBEvent = fixture.EventBytes("B");

        var result = fixture.Align("--selector", PathFor("A"));

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            "LEDGER_ALIGN selectors_considered=1 changed=1 added=0 unchanged=0 conflicts=0\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Equal(original.ByPath[RepoPathFor("B")].StatementId.Value, fixture.StatePin("B"));
        Assert.Equal(oldBEvent, fixture.EventBytes("B"));
        Assert.Equal(fixture.StatePin("A"), fixture.EventPin("A"));
    }

    [Fact]
    public void AddRegistersClosedModuleWithMatchingStateAndEventPins()
    {
        var module = ModuleWithReport("A", Source("A"), "True");
        using var fixture = new AlignFixture(module);

        var result = fixture.Align("--add", PathFor("A"));

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            "LEDGER_ALIGN selectors_considered=1 changed=0 added=1 unchanged=0 conflicts=0\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Equal(ExpectedAddedModuleStatementPin, fixture.StatePin("A"));
        Assert.Equal(ExpectedAddedModuleStatementPin, fixture.EventPin("A"));
    }

    [Fact]
    public void AddNamesMissingModuleAndWritesNothing()
    {
        var module = ModuleWithReport("A", Source("A"), "True");
        using var fixture = new AlignFixture(module);

        var result = fixture.Align("--add", PathFor("Missing"));

        Assert.False(result.Success);
        Assert.Contains(PathFor("Missing"), result.Error, StringComparison.Ordinal);
        Assert.Contains("does not exist", result.Error, StringComparison.Ordinal);
        Assert.Contains("LEDGER_ALIGN", result.Output, StringComparison.Ordinal);
        Assert.Empty(fixture.AcceptedFiles());
        Assert.False(fixture.StateExists("Missing"));
    }

    [Fact]
    public void AddNamesNonClosedModuleAndWritesNothing()
    {
        var open = ModuleWithReport(
            "A",
            "theorem a : True := by sorry\n",
            "True",
            axioms: ["sorryAx"]);
        using var fixture = new AlignFixture(open);

        var result = fixture.Align("--add", PathFor("A"));

        Assert.False(result.Success);
        Assert.Contains(PathFor("A"), result.Error, StringComparison.Ordinal);
        Assert.Contains("TruthState=Open", result.Error, StringComparison.Ordinal);
        Assert.Contains("LEDGER_ALIGN", result.Output, StringComparison.Ordinal);
        Assert.Empty(fixture.AcceptedFiles());
        Assert.False(fixture.StateExists("A"));
    }

    [Fact]
    public void FromAcceptedWritesExactlyTheMissingFragmentsFromEventPayloads()
    {
        var catalog = BuildCatalog(Module("A"), Module("B"), Module("C"));
        using var fixture = new AlignFixture();
        fixture.InstallAccepted(catalog);
        fixture.InstallState("A", catalog.ByPath[RepoPathFor("A")].StatementId);

        var result = fixture.FromAccepted();

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            "accepted_selectors=3 state_before=1 state_after=3 written=2 conflicts=0\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains(
            "LEDGER_ALIGN selectors_considered=3 changed=0 added=2 unchanged=1 conflicts=0\n",
            result.Output,
            StringComparison.Ordinal);
        foreach (var name in new[] { "A", "B", "C" })
        {
            Assert.Equal(fixture.EventPin(name), fixture.StatePin(name));
        }
    }

    [Fact]
    public void FromAcceptedConflictFailsBeforeWritingAnyMissingFragment()
    {
        var catalog = BuildCatalog(Module("A"), Module("B"));
        using var fixture = new AlignFixture();
        fixture.InstallAccepted(catalog);
        var conflict = StatementId.Create(Sha256("conflict"));
        fixture.InstallState("A", conflict);
        var acceptedBefore = fixture.AllPublishedBytes();

        var result = fixture.FromAccepted();

        Assert.False(result.Success);
        Assert.Contains(PathFor("A"), result.Error, StringComparison.Ordinal);
        Assert.Contains(
            "accepted_selectors=2 state_before=1 state_after=1 written=0 conflicts=1\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains(
            "LEDGER_ALIGN selectors_considered=2 changed=0 added=0 unchanged=0 conflicts=1\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Equal(conflict.Value, fixture.StatePin("A"));
        Assert.False(fixture.StateExists("B"));
        Assert.Equal(acceptedBefore, fixture.AllPublishedBytes());
    }

    [Fact]
    public void FromAcceptedCliReturnsZeroOnSuccessAndNonZeroOnConflict()
    {
        var catalog = BuildCatalog(Module("A"), Module("B"));
        using var successful = new AlignFixture();
        successful.InstallAccepted(catalog);
        var success = RunFromAcceptedCli(successful);

        using var conflicted = new AlignFixture();
        conflicted.InstallAccepted(catalog);
        conflicted.InstallState("A", StatementId.Create(Sha256("conflict")));
        var conflict = RunFromAcceptedCli(conflicted);

        Assert.Equal(0, success);
        Assert.NotEqual(0, conflict);
    }

    [Fact]
    public void AppendAliasAndExplicitAddPublishIdenticalBytes()
    {
        var module = ModuleWithReport("A", Source("A"), "True");
        using var aligned = new AlignFixture(module);
        using var aliased = new AlignFixture(module);

        var alignResult = aligned.Align("--add", PathFor("A"));
        var aliasResult = aliased.AppendAlias();

        Assert.True(alignResult.Success, alignResult.Error);
        Assert.True(aliasResult.Success, aliasResult.Error);
        Assert.StartsWith(
            "ledger-append is an alias of ledger-align --add <module> (expand phase; removed at contract)\n",
            aliasResult.Output,
            StringComparison.Ordinal);
        Assert.Equal(aligned.AllPublishedBytes(), aliased.AllPublishedBytes());
        Assert.Contains("ledger-align", CliApplication.ImplementedCommands);
    }

    private static string Source(string name) =>
        $"theorem {name.ToLowerInvariant()} : True := by trivial\n";

    private static int RunFromAcceptedCli(AlignFixture fixture)
    {
        return CliApplication.Run(
            ["ledger-align", "--from-accepted"],
            new LedgerAlignCliEnvironment(fixture),
            new BufferedConsole());
    }

    private sealed class LedgerAlignCliEnvironment : ICliEnvironment
    {
        private readonly AlignFixture fixture;

        internal LedgerAlignCliEnvironment(AlignFixture fixture)
        {
            this.fixture = fixture;
        }

        public CommandResult AlignLedger(IReadOnlyList<string> arguments) => fixture.Invoke(arguments);

        public ExplicitCommandResult CapacityAudit(IReadOnlyList<string> arguments) => throw Unsupported();
        public AdmissionOutcome Check(IReadOnlyList<string> arguments) => throw Unsupported();
        public AdmissionTopologyOutcome Topology(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult Coverage(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult DigestStatus(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult ShowAtom(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult EchoVerify(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult GateAuthority(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult FileMapConform(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult DepositHeaderCheck(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult Ingest(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult AlignDigestionStatus(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult CoverAtom(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult AlignScribeReceipt(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult Route(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult SelfTest(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult RenderDag(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult AppendLedger(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult RevokeLedger(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult ReanchorMathlibLedger(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult TruthExport(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult TruthRelease(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult CleanLanes(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult Worktree(IReadOnlyList<string> arguments) => throw Unsupported();

        private static NotSupportedException Unsupported() => new();
    }

    private sealed class AlignFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string reportPath;

        internal AlignFixture(params ModuleSpec[] modules)
        {
            var files = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n",
                ["lakefile.toml"] = "name = \"Fixture\"\n",
                ["lake-manifest.json"] = "{}\n",
            };
            var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal);
            foreach (var module in modules)
            {
                var path = PathFor(module.Name);
                var declarationName = module.Name.ToLowerInvariant();
                files[path] = module.Source;
                reports[path] = new LeanFileReport(
                    module.Imports.Select(name => $"D5.S0.Carrier.{name}").ToImmutableArray(),
                    [new LeanDeclaration(
                        declarationName,
                        module.Kind,
                        module.StatementMaterial,
                        module.Axioms)
                    {
                        NameKey = $"ns(n0,{Encoding.UTF8.GetByteCount(declarationName)}:{declarationName})",
                    }]);
            }

            var raw = RawRepositorySnapshot.Create(
                files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(raw)).Snapshot;
            var report = LeanAxiomReport.Create(reports);
            reportPath = Path.Combine(temporary.Path, "candidate-report.json");
            RawLeanReportArtifact.WriteFile(reportPath, snapshot, report);
            Repository = new FakeRepositoryGateway(
                RawChangeSet.CreateWithKinds(modules.Select(module =>
                    (PathFor(module.Name), RawChangeKind.Modified))),
                raw,
                null);
            Directory.CreateDirectory(AcceptedPath);
        }

        private FakeRepositoryGateway Repository { get; }

        private string AcceptedPath => Path.Combine(
            temporary.Path,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));

        internal CommandResult Align(params string[] options) =>
            Invoke([.. options, "--candidate-lean-report", reportPath]);

        internal CommandResult Invoke(IReadOnlyList<string> options) =>
            DagLedgerAlignWriter.Align(
                temporary.Path,
                Repository,
                options);

        internal CommandResult AlignWithAcceptedWritesDenied()
        {
            if (OperatingSystem.IsWindows())
            {
                return Align();
            }

            var original = File.GetUnixFileMode(AcceptedPath);
            File.SetUnixFileMode(
                AcceptedPath,
                UnixFileMode.UserRead
                    | UnixFileMode.UserExecute
                    | UnixFileMode.GroupRead
                    | UnixFileMode.GroupExecute
                    | UnixFileMode.OtherRead
                    | UnixFileMode.OtherExecute);
            try
            {
                return Align();
            }
            finally
            {
                File.SetUnixFileMode(AcceptedPath, original);
            }
        }

        internal CommandResult AppendAlias() =>
            DagLedgerAlignWriter.AppendAlias(
                temporary.Path,
                Repository,
                ["--candidate-lean-report", reportPath]);

        internal CommandResult FromAccepted() =>
            DagLedgerAlignWriter.Align(temporary.Path, Repository, ["--from-accepted"]);

        internal void InstallAccepted(FrozenMaterialCatalog catalog) =>
            WriteLedgerDirectory(AcceptedPath, EventFiles(catalog));

        internal void InstallState(string name, StatementId pin) =>
            Assert.True(FrozenStateWriter.Write(temporary.Path, RepoPathFor(name), pin));

        internal ImmutableArray<RepositoryFile> AcceptedFiles() =>
            DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(AcceptedPath);

        internal bool StateExists(string name) => File.Exists(StateFile(name));

        internal string StatePin(string name)
        {
            var module = RepoPathFor(name);
            var path = FrozenStatePath.FromModulePath(module);
            var absolute = StateFile(name);
            return FrozenStateRecordLoader.Load(new RepositoryFile(
                path,
                ImmutableArray.CreateRange(File.ReadAllBytes(absolute)),
                File.ReadAllText(absolute, Encoding.UTF8))).StatementId.Value;
        }

        internal string EventPin(string name) => Event(name).Payload
            .GetProperty("statement_id")
            .GetString()!;

        internal byte[] EventBytes(string name)
        {
            var sourcePath = Event(name).SourcePath;
            return AcceptedFiles().Single(file => file.Path == sourcePath).RawBytes.ToArray();
        }

        internal byte[] AllPublishedBytes() => AcceptedFiles()
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .SelectMany(static file => file.RawBytes)
            .Concat(Directory.Exists(Path.Combine(temporary.Path, "Golden", "Frozen", "state"))
                ? Directory.EnumerateFiles(
                        Path.Combine(temporary.Path, "Golden", "Frozen", "state"),
                        "*.json",
                        SearchOption.AllDirectories)
                    .Order(StringComparer.Ordinal)
                    .SelectMany(File.ReadAllBytes)
                : [])
            .ToArray();

        private DagLedgerFileEvent Event(string name) => Assert.Single(
            LoadEvents(AcceptedFiles()),
            item => item.DescriptorPath == RepoPathFor(name));

        private string StateFile(string name) => Path.Combine(
            temporary.Path,
            FrozenStatePath.FromModulePath(RepoPathFor(name)).Value.Replace(
                '/',
                Path.DirectorySeparatorChar));

        public void Dispose() => temporary.Dispose();
    }
}
