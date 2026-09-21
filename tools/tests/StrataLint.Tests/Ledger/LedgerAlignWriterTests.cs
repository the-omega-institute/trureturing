using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class LedgerAlignWriterTests
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
    public void FromAcceptedMaterializesPinsWhenPrerequisiteIdsDoNotResolve()
    {
        var catalog = BuildCatalog(Module("A"), Module("B"));
        var unresolvedPrerequisite = FrozenNodeId.Create(Sha256("not-an-accepted-event"));
        var events = catalog.ClosedNodes
            .Select(material => material.RepoPath == RepoPathFor("B")
                ? material with
                {
                    PrerequisiteFrozenNodeIds = [unresolvedPrerequisite],
                }
                : material)
            .Select(static material => EventFile(
                "Freeze",
                FrozenLedgerCanonicalWriter.FreezeElement(
                    FrozenLedgerCanonicalWriter.FreezePayload(material))))
            .ToImmutableArray();
        using var fixture = new AlignFixture();
        fixture.InstallAccepted(events);

        var exitCode = RunFromAcceptedCli(fixture);

        Assert.Equal(0, exitCode);
        Assert.Equal(2, fixture.StateFileCount());
        foreach (var name in new[] { "A", "B" })
        {
            Assert.Equal(fixture.EventPin(name), fixture.StatePin(name));
        }
    }

    [Fact]
    public void FromAcceptedMaterializesRootAndNestedRepositoryLeanModules()
    {
        var nested = BuildCatalog(Module("A"));
        var rootPath = RepoPath.CreateKnown("Trureturing.lean");
        var rootPin = StatementId.Create(Sha256("root-module-with-no-declarations"));
        var rootMaterial = new FrozenNodeMaterial(
            rootPath,
            [],
            rootPin,
            FrozenNodeId.Create(Sha256("unused-root-node-id")),
            [],
            []);
        var rootEvent = EventFile(
            "Freeze",
            FrozenLedgerCanonicalWriter.FreezeElement(
                FrozenLedgerCanonicalWriter.FreezePayload(rootMaterial)));
        using var fixture = new AlignFixture();
        fixture.InstallAccepted(EventFiles(nested).Append(rootEvent));

        var exitCode = RunFromAcceptedCli(fixture);

        Assert.Equal(0, exitCode);
        Assert.Equal(2, fixture.StateFileCount());
        Assert.Equal(fixture.EventPin("A"), fixture.StatePin("A"));
        Assert.Equal(rootPin.Value, fixture.StatePin(rootPath));
    }

    [Fact]
    public void FromAcceptedNamesContradictoryDuplicateSelectorAndWritesNothing()
    {
        var first = BuildCatalog(ModuleWithReport("A", Source("A"), "True"));
        var second = BuildCatalog(ModuleWithReport("A", Source("A"), "True = True"));
        using var fixture = new AlignFixture();
        fixture.InstallAccepted(EventFiles(first).Concat(EventFiles(second)));
        var acceptedBefore = fixture.AllPublishedBytes();

        var result = fixture.FromAccepted();

        Assert.False(result.Success);
        Assert.Contains(PathFor("A"), result.Error, StringComparison.Ordinal);
        Assert.False(fixture.StateExists("A"));
        Assert.Equal(acceptedBefore, fixture.AllPublishedBytes());
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

    [Fact]
    public void RetirementDeletesOnlyExplicitMissingAddressAndCannotBeResurrected()
    {
        var original = BuildCatalog(Module("A"), Module("B"));
        using var fixture = new AlignFixture(Module("B"));
        fixture.InstallAccepted(original);
        foreach (var name in new[] { "A", "B" })
            fixture.InstallState(name, original.ByPath[RepoPathFor(name)].StatementId);
        var retainedBytes = fixture.EventBytes("B");

        var result = fixture.Align("--retire-registration", PathFor("A"));

        Assert.True(result.Success, result.Error);
        Assert.Contains("LEDGER_RETIRE registrations=1", result.Output, StringComparison.Ordinal);
        Assert.False(fixture.StateExists("A"));
        Assert.Equal(retainedBytes, fixture.EventBytes("B"));
        Assert.Single(fixture.AcceptedFiles());
        Assert.All(ReadRepairEvents(fixture.AcceptedFiles()), item => Assert.Equal("Freeze", item.EventType));
        var after = fixture.AllPublishedBytes();
        Assert.True(fixture.FromAccepted().Success);
        Assert.True(fixture.AlignWithAcceptedWritesDenied().Success);
        Assert.Equal(after, fixture.AllPublishedBytes());
        Assert.False(fixture.StateExists("A"));
        // No tombstone or second ledger: an already retired selector is now unknown.
        var repeated = fixture.Align("--retire-registration", PathFor("A"));
        Assert.False(repeated.Success);
        Assert.Contains("not a registered frozen-state member", repeated.Error, StringComparison.Ordinal);
        Assert.Equal(after, fixture.AllPublishedBytes());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MissingPinnedSourceRequiresExplicitRetirementEvenWithSelector(bool scoped)
    {
        var original = BuildCatalog(Module("A"), Module("B"));
        using var fixture = new AlignFixture(Module("B"));
        fixture.InstallAccepted(original);
        foreach (var name in new[] { "A", "B" })
            fixture.InstallState(name, original.ByPath[RepoPathFor(name)].StatementId);
        var before = fixture.AllPublishedBytes();

        var result = scoped ? fixture.Align("--selector", PathFor("B")) : fixture.Align();

        Assert.False(result.Success);
        Assert.Contains(PathFor("A"), result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());
    }

    [Theory]
    [InlineData("existing")]
    [InlineData("unknown")]
    [InlineData("duplicate")]
    [InlineData("selector-conflict")]
    [InlineData("add-conflict")]
    [InlineData("pin-conflict")]
    [InlineData("missing-event")]
    [InlineData("root")]
    [InlineData("reg")]
    public void RetirementRejectsInvalidRequestsWithoutPublishing(string variant)
    {
        var original = BuildCatalog(Module("A"), Module("B"));
        using var fixture = new AlignFixture(variant == "existing"
            ? [Module("A"), Module("B")] : [Module("B")]);
        if (variant != "missing-event") fixture.InstallAccepted(original);
        fixture.InstallState("A", variant == "pin-conflict"
            ? StatementId.Create(Sha256("wrong pin")) : original.ByPath[RepoPathFor("A")].StatementId);
        fixture.InstallState("B", original.ByPath[RepoPathFor("B")].StatementId);
        var options = new List<string> { "--retire-registration", variant switch
        {
            "unknown" => PathFor("Unknown"),
            "root" => "Trureturing.lean",
            "reg" => "Reg/" + PathFor("A"),
            _ => PathFor("A"),
        } };
        if (variant is "duplicate" or "selector-conflict" or "add-conflict")
            options.AddRange([variant switch
            {
                "duplicate" => "--retire-registration",
                "selector-conflict" => "--selector",
                _ => "--add",
            }, PathFor("A")]);
        var before = fixture.AllPublishedBytes();

        var result = fixture.Align(options.ToArray());

        Assert.False(result.Success);
        Assert.DoesNotContain("USAGE:", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void RetirementRebuildsRetainedDescendantsAndRepinsChangedContent(bool detachDescendant, bool drift)
    {
        var oldModules = RepairModules();
        var original = BuildCatalog(oldModules);
        var currentB = Module("B") with { StatementMaterial = drift ? "changed content" : oldModules[1].StatementMaterial };
        var currentC = detachDescendant ? Module("C") : oldModules[2];
        using var fixture = new AlignFixture(currentB, currentC, Module("D"));
        fixture.InstallAccepted(original);
        foreach (var module in oldModules)
            fixture.InstallState(module.Name, original.ByPath[RepoPathFor(module.Name)].StatementId);
        var oldB = fixture.EventBytes("B");
        var oldC = fixture.EventBytes("C");
        var untouchedD = fixture.EventBytes("D");

        // The selected unrelated module must not hide the affected retained descendants.
        var result = fixture.Align("--retire-registration", PathFor("A"), "--selector", PathFor("D"));

        Assert.True(result.Success, result.Error);
        var events = ReadRepairEvents(fixture.AcceptedFiles());
        Assert.Equal(3, events.Length);
        Assert.Equal(3, fixture.StateFileCount());
        Assert.True(DagLedgerLoader.TryOrderClosedDag(events, [], out _));
        Assert.NotEqual(oldB, fixture.EventBytes("B"));
        Assert.NotEqual(oldC, fixture.EventBytes("C"));
        Assert.Equal(untouchedD, fixture.EventBytes("D"));
        if (!detachDescendant) AssertPrerequisite(events, "C", "B");
        foreach (var name in new[] { "B", "C", "D" }) Assert.Equal(fixture.EventPin(name), fixture.StatePin(name));
        var expected = BuildCatalog(currentB, currentC, Module("D"));
        Assert.Equal(expected.ByPath[RepoPathFor("B")].StatementId.Value, fixture.StatePin("B"));
        var after = fixture.AllPublishedBytes();
        Assert.True(fixture.AlignWithAcceptedWritesDenied().Success);
        Assert.True(fixture.FromAccepted().Success);
        Assert.Equal(after, fixture.AllPublishedBytes());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RetirementRejectsRemainingReportImportWithoutPublishing(bool regImporter)
    {
        var original = BuildCatalog(Module("A"), Module("B", imports: ["A"]));
        var importer = regImporter ? "Reg/" + PathFor("B") : PathFor("B");
        using var fixture = regImporter
            ? new AlignFixture([Module("B")], new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                [importer] = new LeanFileReport(["D5.S0.Carrier.A"], []),
            })
            : new AlignFixture(Module("B", imports: ["A"]));
        fixture.InstallAccepted(original);
        foreach (var name in new[] { "A", "B" })
            fixture.InstallState(name, original.ByPath[RepoPathFor(name)].StatementId);
        var before = fixture.AllPublishedBytes();

        var result = fixture.Align("--retire-registration", PathFor("A"));

        Assert.False(result.Success);
        Assert.Contains("still imports retired registration", result.Error, StringComparison.Ordinal);
        Assert.Contains(importer, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());
    }

    [Fact]
    public void RetirementCanRemoveAWholeObsoleteChainInOnePublication()
    {
        var original = BuildCatalog(Module("A"), Module("B", imports: ["A"]), Module("C", imports: ["B"]));
        using var fixture = new AlignFixture(Module("C"));
        fixture.InstallAccepted(original);
        foreach (var name in new[] { "A", "B", "C" })
            fixture.InstallState(name, original.ByPath[RepoPathFor(name)].StatementId);
        var before = fixture.AllPublishedBytes();
        var incomplete = fixture.Align("--retire-registration", PathFor("A"));
        Assert.False(incomplete.Success);
        Assert.Contains(PathFor("B"), incomplete.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());

        var result = fixture.Align("--retire-registration", PathFor("A"), "--retire-registration", PathFor("B"));

        Assert.True(result.Success, result.Error);
        Assert.Contains("registrations=2 retained_descendants=1", result.Output, StringComparison.Ordinal);
        Assert.False(fixture.StateExists("A"));
        Assert.False(fixture.StateExists("B"));
        Assert.Equal(fixture.StatePin("C"), fixture.EventPin("C"));
        Assert.Single(fixture.AcceptedFiles());
        Assert.True(fixture.FromAccepted().Success);
        Assert.Equal(1, fixture.StateFileCount());
    }

    [Fact]
    public void RetirementIsNotAvailableWithoutCandidateReportOrThroughOtherModes()
    {
        using var fixture = new AlignFixture();
        foreach (var arguments in new string[][]
        {
            ["--retire-registration", PathFor("A")],
            ["--from-accepted", "--retire-registration", PathFor("A")],
        })
        {
            var result = fixture.Invoke(arguments);
            Assert.False(result.Success);
            Assert.Contains("USAGE:", result.Error, StringComparison.Ordinal);
        }
        var alias = fixture.AppendAlias("--retire-registration", PathFor("A"));
        Assert.False(alias.Success);
        Assert.Contains("USAGE:", alias.Error, StringComparison.Ordinal);
        Assert.Empty(fixture.AcceptedFiles());
    }

    [Fact]
    public void RetirementRejectsUnclosedResultingLedgerWithoutPublishing()
    {
        var original = BuildCatalog(Module("A"), Module("B"), Module("D"));
        using var fixture = new AlignFixture(Module("B"), Module("D"));
        fixture.InstallAccepted(original.ClosedNodes.Select(material => EventFile(
            "Freeze", FrozenLedgerCanonicalWriter.FreezeElement(FrozenLedgerCanonicalWriter.FreezePayload(
                material.RepoPath == RepoPathFor("B") ? material with
                {
                    PrerequisiteFrozenNodeIds = [FrozenNodeId.Create(Sha256("unresolved unrelated edge"))],
                } : material)))));
        foreach (var name in new[] { "A", "B", "D" })
            fixture.InstallState(name, original.ByPath[RepoPathFor(name)].StatementId);
        var before = fixture.AllPublishedBytes();

        var result = fixture.Align("--retire-registration", PathFor("A"), "--selector", PathFor("D"));

        Assert.False(result.Success);
        Assert.Contains("does not form a closed dependency DAG", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());
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
        public ExplicitCommandResult CheckCurrent(IReadOnlyList<string> arguments) => throw new NotSupportedException();

        public ExplicitCommandResult CheckDelta(IReadOnlyList<string> arguments) => throw new NotSupportedException();

        public AdmissionOutcome Check(IReadOnlyList<string> arguments) => throw Unsupported();
        public AdmissionTopologyOutcome Topology(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult Coverage(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult DigestStatus(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult ShowAtom(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult AtomContext(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult EchoVerify(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult GateAuthority(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult FileMapConform(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult DepositHeaderCheck(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult LeanUtilityInput(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult LedgerFrozen(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult Ingest(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult AlignDigestionStatus(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult CoverAtom(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult CoverBatch(IReadOnlyList<string> arguments) => throw Unsupported();

        public CommandResult QuarantineAtom(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult SettleBatch(IReadOnlyList<string> arguments) =>
            new(false, string.Empty, "settle-batch is not configured in this fixture");

        public CommandResult SettleAtom(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult DecomposeAtom(IReadOnlyList<string> arguments) => throw Unsupported();
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

        internal AlignFixture(params ModuleSpec[] modules) : this(modules, []) { }

        internal AlignFixture(ModuleSpec[] modules, Dictionary<string, LeanFileReport> additionalReports)
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
            foreach (var (path, additionalReport) in additionalReports)
            {
                files[path] = "-- declaration data fixture\n";
                reports[path] = additionalReport;
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

        internal CommandResult AppendAlias(params string[] options) =>
            DagLedgerAlignWriter.AppendAlias(
                temporary.Path,
                Repository,
                [.. options, "--candidate-lean-report", reportPath]);

        internal CommandResult FromAccepted() =>
            DagLedgerAlignWriter.Align(temporary.Path, Repository, ["--from-accepted"]);

        internal void InstallAccepted(FrozenMaterialCatalog catalog) =>
            WriteLedgerDirectory(AcceptedPath, EventFiles(catalog));

        internal void InstallAccepted(IEnumerable<RepositoryFile> events) =>
            WriteLedgerDirectory(AcceptedPath, events);

        internal void InstallState(string name, StatementId pin) =>
            Assert.True(FrozenStateWriter.Write(temporary.Path, RepoPathFor(name), pin));

        internal ImmutableArray<RepositoryFile> AcceptedFiles() =>
            DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(AcceptedPath);

        internal bool StateExists(string name) => File.Exists(StateFile(name));

        internal int StateFileCount()
        {
            var stateRoot = Path.Combine(temporary.Path, "Golden", "Frozen", "state");
            return Directory.Exists(stateRoot)
                ? Directory.EnumerateFiles(stateRoot, "*.json", SearchOption.AllDirectories).Count()
                : 0;
        }

        internal string StatePin(string name)
            => StatePin(RepoPathFor(name));

        internal string StatePin(RepoPath module)
        {
            var path = FrozenStatePath.FromModulePath(module);
            var absolute = StateFile(module);
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

        private DagLedgerFileEvent Event(string name)
        {
            var loaded = Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(
                FrozenAcceptedEventLoader.LoadFiles(AcceptedFiles()));
            return Assert.Single(
                loaded.Events,
                item => item.DescriptorPath == RepoPathFor(name));
        }

        private string StateFile(string name) => StateFile(RepoPathFor(name));

        private string StateFile(RepoPath module) => Path.Combine(
            temporary.Path,
            FrozenStatePath.FromModulePath(module).Value.Replace(
                '/',
                Path.DirectorySeparatorChar));

        public void Dispose() => temporary.Dispose();
    }
}
