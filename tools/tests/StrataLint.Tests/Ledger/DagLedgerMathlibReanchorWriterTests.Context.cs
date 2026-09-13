using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

// Truthful Inspector materials, current-compiler source queries, and the actual writer.
// ProbeExternal and pin fields are controlled source fixtures, not a Mathlib migration.
public sealed partial class DagLedgerMathlibReanchorWriterTests : IDisposable
{
    private readonly TemporaryDirectory qualifiedReports = new();

    public void Dispose() => qualifiedReports.Dispose();

    [Fact]
    public void Q1ProducerHelperValueDrifts()
    {
        var before = QLoad("registered_g");
        var after = QLoad("absent_a");
        var oldDef = Assert.Single(before.Report.Files[RepoPathFor("Helper")].Declarations);
        var newDef = Assert.Single(after.Report.Files[RepoPathFor("Helper")].Declarations);
        Assert.Equal("def", oldDef.Kind);
        Assert.True(oldDef.IncludeInStatement);
        Assert.Contains(",value=", oldDef.LoadTypeRepresentation(), StringComparison.Ordinal);
        Assert.Contains("ln(103)", oldDef.LoadTypeRepresentation(), StringComparison.Ordinal);
        Assert.Contains("ln(97)", newDef.LoadTypeRepresentation(), StringComparison.Ordinal);
        Assert.NotEqual(oldDef.LoadTypeRepresentation(), newDef.LoadTypeRepresentation());
        Assert.NotEqual(before.Catalog.ByPath[RepoPathFor("Helper")].StatementId,
            after.Catalog.ByPath[RepoPathFor("Helper")].StatementId);
    }

    [Fact]
    public void Q1ProducerRegistrationOnlyKeepsHelper()
    {
        var before = QLoad("registered_g");
        var after = QLoad("absent_g");
        Assert.Equal(QMaterial(before, "Helper"), QMaterial(after, "Helper"));
        Assert.Equal(before.Catalog.ByPath[RepoPathFor("Helper")].StatementId,
            after.Catalog.ByPath[RepoPathFor("Helper")].StatementId);
    }

    [Fact]
    public void Q1ProducerConsumerContextDrifts()
    {
        var before = QLoad("registered_g");
        var after = QLoad("absent_a");
        var unchanged = QLoad("absent_g");
        Assert.Equal(before.Snapshot.Files[RepoPathFor("A")].Text,
            after.Snapshot.Files[RepoPathFor("A")].Text);
        Assert.Contains("6:Helper", QMaterial(before, "A"), StringComparison.Ordinal);
        Assert.DoesNotContain("6:Helper", QMaterial(after, "A"), StringComparison.Ordinal);
        Assert.Equal(QMaterial(after, "A"), QMaterial(unchanged, "A"));
        Assert.NotEqual(before.Catalog.ByPath[RepoPathFor("A")].StatementId,
            after.Catalog.ByPath[RepoPathFor("A")].StatementId);
    }

    [Fact]
    public void Q1ProducerEmptyAxioms()
    {
        foreach (var name in new[] { "registered_g", "absent_a", "absent_g" })
        {
            var data = QLoad(name);
            Assert.Equal(2, data.Report.Files.Count);
            Assert.All(data.Report.Files.Values.SelectMany(file => file.Declarations),
                declaration => Assert.Empty(declaration.Axioms));
        }
    }

    [Fact]
    public void Q1OmittedDriftedHelperFailsRecognition()
    {
        var pair = QPair("registered_g", "absent_a", ["A"]);
        Assert.Equal(new[] { PathFor("A"), PathFor("Helper") }, QDrift(pair));
        Assert.Single(pair.Delta);
        Assert.Equal(RepoPathFor("A"), pair.Delta[0].DescriptorPath);
        Assert.Null(pair.Recognition);
    }

    [Fact]
    public void Q1IncludedDriftedHelperRejectsDirectLiteral()
    {
        var pair = QPair("registered_g", "absent_a", ["Helper", "A"]);
        var recognition = Assert.IsType<FrozenLedgerIncrementalReplacementRecognition>(pair.Recognition);
        Assert.Equal(new[] { PathFor("A"), PathFor("Helper") },
            recognition.ChangedStatementModulePaths.Select(path => path.Value).Order().ToArray());
        Assert.False(LeanPropositionSourceComparer.AreEquivalent(pair.Before, pair.After,
            ImmutableHashSet.Create(RepoPathFor("Helper")), pair.BaseView, pair.CandidateCatalog, pair.Input));
        Assert.False(QAuthorized(pair));
    }

    [Fact]
    public void Q1NonActiveImportedHelperFailsReadiness()
    {
        var old = QLoad("registered_g");
        var next = QLoad("absent_a");
        var events = EventFiles(old.Catalog);
        var activeAOnly = QSnapshot(old.Snapshot.Files.Values.Concat(
            new[] { EventFor(events, "A") }));
        var baseView = FrozenLedgerBaseViewReader.Read(activeAOnly);
        Assert.Single(baseView.ActiveByPath);
        Assert.Contains(RepoPathFor("Helper"), next.Adjacency[RepoPathFor("A")]);
        var error = Assert.Throws<FormatException>(() => FrozenContentAddress.BuildAdmissionCatalog(
            next.Snapshot, next.Lean, next.States, next.Adjacency,
            ImmutableHashSet.Create(RepoPathFor("A")), baseView.ActiveByPath));
        Assert.Contains("dependency-not-ready", error.Message, StringComparison.Ordinal);
        Assert.Contains(PathFor("Helper"), error.Message, StringComparison.Ordinal);
        Assert.Contains("no active accepted Freeze", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Q2ProducerParenthesesPreserveHelperIdentity()
    {
        var before = QLoad("registered_g");
        foreach (var name in new[] { "registered_parentheses", "absent_parentheses" })
        {
            var after = QLoad(name);
            Assert.Equal(QMaterial(before, "Helper"), QMaterial(after, "Helper"));
            Assert.Equal(before.Catalog.ByPath[RepoPathFor("Helper")].StatementId,
                after.Catalog.ByPath[RepoPathFor("Helper")].StatementId);
            Assert.NotEqual(before.Snapshot.Files[RepoPathFor("Helper")].Text,
                after.Snapshot.Files[RepoPathFor("Helper")].Text);
            Assert.All(after.Report.Files.Values.SelectMany(file => file.Declarations),
                declaration => Assert.Empty(declaration.Axioms));
        }
    }

    [Fact]
    public void Q2ParenthesizedDependencyChangesPresentSourceRelation()
    {
        var pair = QPair("registered_g", "absent_parentheses", ["A"]);
        var recognition = Assert.IsType<FrozenLedgerIncrementalReplacementRecognition>(pair.Recognition);
        Assert.Equal(new[] { PathFor("A") }, QDrift(pair));
        Assert.Equal(RepoPathFor("A"), Assert.Single(recognition.ReanchoredModulePaths));
        var sources = QSources(pair, "A");
        Assert.Contains("dependency-path", sources.Before, StringComparison.Ordinal);
        Assert.Contains(PathFor("Helper"), sources.Before, StringComparison.Ordinal);
        Assert.Contains(PathFor("Helper"), sources.After, StringComparison.Ordinal);
        Assert.NotEqual(sources.Before, sources.After);
        Assert.False(QEquivalent(pair, "A"));
        Assert.False(QEquivalent(pair, "Helper"));
        Assert.False(QAuthorized(pair));
    }

    [Fact]
    public void QualifiedParenthesesDependencyRejectsWithSourceSupportedInterpretation()
    {
        var pair = QPair("registered_g", "absent_parentheses", ["A"]);
        Assert.NotNull(pair.Recognition);
        Assert.Equal(new[] { PathFor("A") }, QDrift(pair));
        var comparison = LeanPropositionSourceComparer.Compare(pair.Before, pair.After,
            ImmutableHashSet.Create(RepoPathFor("A")), pair.BaseView, pair.CandidateCatalog, pair.Input);
        var failure = Assert.Single(comparison.Failures);
        Assert.Equal(RepoPathFor("A"), failure.Path);
        Assert.Equal(4, failure.Line);
        Assert.Contains("Source-supported", failure.Message, StringComparison.Ordinal);
        Assert.False(QAuthorized(pair));
    }

    [Theory]
    [InlineData("absent_g")]
    [InlineData("absent_proof")]
    [InlineData("absent_whitespace")]
    [InlineData("absent_helper_whitespace")]
    public void Q2CrossContextControls(string after)
    {
        var pair = QPair("registered_g", after, ["A"]);
        Assert.NotNull(pair.Recognition);
        Assert.Equal(new[] { PathFor("A") }, QDrift(pair));
        Assert.True(QEquivalent(pair, "Helper"));
        Assert.True(QEquivalent(pair, "A"));
        Assert.True(QAuthorized(pair));
    }

    [Theory]
    [InlineData("absent_a")]
    [InlineData("absent_parentheses")]
    public void Q2NoRegistrationCharComparison(string after)
    {
        var pair = QPair("absent_g", after, ["A"]);
        Assert.Null(pair.Recognition);
        Assert.True(QEquivalent(pair, "A"));
        Assert.False(QEquivalent(pair, "Helper"));
        Assert.Equal(pair.BaseView.ActiveByPath[RepoPathFor("A")].Material.StatementId,
            pair.CandidateCatalog.ByPath[RepoPathFor("A")].StatementId);
    }

    [Fact]
    public void Q3LiteralWriterRejects()
    {
        using var fixture = QWriter("registered_g", "absent_a");
        var before = QLedgerBytes(fixture);
        var result = QRunWriter(fixture);
        Assert.False(result.Success);
        Assert.Contains("replacement_modules=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("drift_seed_modules=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION incremental_replacement=pass", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION effective_lean_pins_changed=pass", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION standard_axiom_closure=pass", result.Output, StringComparison.Ordinal);
        Assert.Contains("PROPOSITION_SOURCE_FAILURE " + PathFor("Helper"), result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION overall=fail", result.Output, StringComparison.Ordinal);
        Assert.Equal(before, QLedgerBytes(fixture));
    }

    [Fact]
    public void QualifiedWriterDiagnosticsUsesCanonicalComparison()
    {
        var pair = QPair("registered_g", "absent_parentheses", ["A"]);
        var comparison = LeanPropositionSourceComparer.Compare(pair.Before, pair.After,
            pair.Recognition!.ChangedStatementModulePaths, pair.BaseView, pair.CandidateCatalog, pair.Input);
        Assert.Equal(RepoPathFor("A"), Assert.Single(MathlibUpgradePropositionSourceDiagnostics.FindFailures(comparison)));
        Assert.False(new MathlibUpgradeFrozenLedgerReplacementAuthorization(pair.Before, pair.After, pair.Input, comparison)
            .IsAuthorized(new FrozenLedgerReplacementAuthorizationContext(pair.Recognition, pair.BaseView, pair.CandidateCatalog)));
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("revision")]
    [InlineData("path")]
    [InlineData("blob")]
    [InlineData("duplicate")]
    public void QualifiedDemandedOriginBindingRejectsTampering(string mutation)
    {
        var pair = QPair("registered_g", "absent_parentheses", ["A"]);
        var json = System.Text.Json.Nodes.JsonNode.Parse(QualifiedSourceContextFixture.Bytes(
            pair.After, pair.Before, "registered_g", "absent_parentheses"))!;
        foreach (var row in json["registrations"]!.AsArray())
        {
            var origins = row!["origins"]!.AsArray();
            var origin = origins[0]!;
            switch (mutation)
            {
                case "missing": origins.Clear(); break;
                case "revision": origin["revision"] = new string('c', 40); break;
                case "path": origin["path"] = "Another.lean"; break;
                case "blob": origin["blob"] = new string('c', 40); break;
                case "duplicate": origins.Add(origin.DeepClone()); break;
            }
        }
        var input = LeanSourceContextInput.Load(Encoding.UTF8.GetBytes(json.ToJsonString()), pair.After, pair.Before);
        var failure = Assert.Single(LeanPropositionSourceComparer.Compare(pair.Before, pair.After,
            ImmutableHashSet.Create(RepoPathFor("A")), pair.BaseView, pair.CandidateCatalog, input).Failures);
        Assert.Equal(RepoPathFor("A"), failure.Path);
        Assert.Contains("malformed or stale registration context", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void QualifiedParenthesesWriterRejectsAndPreservesLedgerAndPins()
    {
        using var fixture = QWriter("registered_g", "absent_parentheses");
        var bytes = QLedgerBytes(fixture);
        var baseHelper = EventFor(fixture.BaseEvents, "Helper");
        var result = QRunWriter(fixture);
        Assert.False(result.Success);
        Assert.Contains("replacement_modules=1", result.Output, StringComparison.Ordinal);
        Assert.Contains("drift_seed_modules=1", result.Output, StringComparison.Ordinal);
        Assert.Contains("PROPOSITION_SOURCE_LOCATION " + PathFor("A") + ":4:", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION overall=fail", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("diagnostics disagree", result.Error, StringComparison.Ordinal);
        Assert.Equal(bytes, QLedgerBytes(fixture));
        var persisted = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        var persistedHelper = Assert.Single(persisted, file => file.Path == baseHelper.Path);
        Assert.True(baseHelper.RawBytes.AsSpan().SequenceEqual(persistedHelper.RawBytes.AsSpan()));
    }

    [Theory]
    [InlineData("absent_g")]
    [InlineData("absent_proof")]
    [InlineData("absent_whitespace")]
    [InlineData("absent_helper_whitespace")]
    public void Q3WriterControls(string after)
    {
        using var fixture = QWriter("registered_g", after);
        var result = QRunWriter(fixture);
        Assert.True(result.Success, result.Error);
        Assert.Contains("replacement_modules=1", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION overall=pass", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void Q3NoRegistrationParenthesesWriterNoop()
    {
        using var fixture = QWriter("absent_g", "absent_parentheses");
        var before = QLedgerBytes(fixture);
        var result = QRunWriter(fixture);
        Assert.True(result.Success, result.Error);
        Assert.Contains("replacement_modules=0 drift_seed_modules=0 recognition=not-required",
            result.Output, StringComparison.Ordinal);
        Assert.Equal(before, QLedgerBytes(fixture));
    }

    [Fact]
    public void Q3NoRegistrationValueWriterRejectsHelper()
    {
        using var fixture = QWriter("absent_g", "absent_a");
        var before = QLedgerBytes(fixture);
        var result = QRunWriter(fixture);
        Assert.False(result.Success);
        Assert.Contains("replacement_modules=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("drift_seed_modules=1", result.Output, StringComparison.Ordinal);
        Assert.Contains("PROPOSITION_SOURCE_FAILURE " + PathFor("Helper"), result.Output, StringComparison.Ordinal);
        Assert.Equal(before, QLedgerBytes(fixture));
    }

    [Fact]
    public void Q3NonActiveImportedHelperFailsEventGeneration()
    {
        using var fixture = QWriter("registered_g", "absent_a", nonActiveHelper: true);
        var before = QLedgerBytes(fixture);
        var result = QRunWriter(fixture);
        Assert.False(result.Success);
        Assert.Contains("reanchored module " + PathFor("A") + " depends on non-active " + PathFor("Helper"),
            result.Error, StringComparison.Ordinal);
        Assert.Equal(before, QLedgerBytes(fixture));
    }

    [Fact]
    public void Q3StrictLoaderRejectsStaleHelperSource()
    {
        using var fixture = QWriter("registered_g", "absent_parentheses");
        var stale = QLoad("absent_g");
        var error = Assert.Throws<FormatException>(() => RawLeanReportArtifact.ReadFile(
            stale.ReportPath, fixture.Current.Snapshot));
        Assert.Contains("source hash does not match " + PathFor("Helper"), error.Message, StringComparison.Ordinal);
        var before = QLedgerBytes(fixture);
        var result = DagLedgerMathlibReanchorWriter.Reanchor(fixture.Root.Path, fixture.Repository,
            new DagLedgerCommandPreparation.FileLeanReportSource(stale.ReportPath), ["--base", BaseRevision]);
        Assert.False(result.Success);
        Assert.Contains("raw Lean report is unusable", result.Error, StringComparison.Ordinal);
        Assert.Contains(PathFor("Helper"), result.Error, StringComparison.Ordinal);
        Assert.Equal(before, QLedgerBytes(fixture));
    }

    private QWriterFixture QWriter(string beforeName, string afterName, bool nonActiveHelper = false)
    {
        var old = QLoad(beforeName, 'a');
        var next = QLoad(afterName, 'b');
        var allBaseEvents = EventFiles(old.Catalog);
        var baseEvents = nonActiveHelper ? ImmutableArray.Create(EventFor(allBaseEvents, "A")) : allBaseEvents;
        var baseline = QSnapshot(old.Snapshot.Files.Values.Concat(baseEvents));
        var current = QSnapshot(next.Snapshot.Files.Values.Concat(baseEvents));
        var changes = RawChangeSet.CreateWithKinds(next.Snapshot.Files.Values
            .Where(file => !old.Snapshot.Files[file.Path].RawBytes.AsSpan().SequenceEqual(file.RawBytes.AsSpan()))
            .Select(file => (file.Path.Value, RawChangeKind.Modified)));
        var gateway = new FakeRepositoryGateway(changes, QRaw(current), QRaw(baseline),
            changesForBase: _ => changes);
        var temporary = new TemporaryDirectory();
        foreach (var file in current.Files.Values)
        {
            var target = Path.Combine(temporary.Path, file.Path.Value);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.WriteAllBytes(target, file.RawBytes.AsSpan().ToArray());
        }
        foreach (var material in old.Catalog.ClosedNodes.Where(material =>
            !nonActiveHelper || material.RepoPath == RepoPathFor("A")))
        {
            Assert.True(FrozenStateWriter.Write(temporary.Path, material.RepoPath, material.StatementId));
        }
        var report = Path.Combine(temporary.Path, "current-report.json");
        File.Copy(next.ReportPath, report);
        File.Copy(next.ReportPath + ".materials.zip", report + ".materials.zip");
        File.WriteAllBytes(report + ".source-context.json",
            QualifiedSourceContextFixture.Bytes(current, baseline, beforeName, afterName));
        return new QWriterFixture(temporary, gateway, next with { ReportPath = report }, baseEvents,
            Path.Combine(temporary.Path, FrozenLedgerChangeClassifier.AcceptedRoot));
    }

    private static RawRepositorySnapshot QRaw(RepositorySnapshot snapshot) =>
        RawRepositorySnapshot.Create(snapshot.Files.Values.Select(file =>
            new RawRepositoryEntry(file.Path.Value, file.RawBytes)));

    private static byte[] QLedgerBytes(QWriterFixture fixture) =>
        ReadLedgerDirectory(fixture.LedgerPath).Concat(
            Directory.EnumerateFiles(Path.Combine(fixture.Root.Path, "Golden/Frozen/state"), "*.json",
                SearchOption.AllDirectories).Order(StringComparer.Ordinal).SelectMany(File.ReadAllBytes)).ToArray();

    private static CommandResult QRunWriter(QWriterFixture fixture) =>
        DagLedgerMathlibReanchorWriter.Reanchor(fixture.Root.Path, fixture.Repository,
            new DagLedgerCommandPreparation.FileLeanReportSource(fixture.Current.ReportPath), ["--base", BaseRevision]);

    private sealed record QWriterFixture(TemporaryDirectory Root, FakeRepositoryGateway Repository,
        QCase Current, ImmutableArray<RepositoryFile> BaseEvents, string LedgerPath) : IDisposable
    {
        public void Dispose() => Root.Dispose();
    }

    private static bool QEquivalent(QReplacement pair, string module) =>
        LeanPropositionSourceComparer.AreEquivalent(pair.Before, pair.After,
            ImmutableHashSet.Create(RepoPathFor(module)), pair.BaseView, pair.CandidateCatalog, pair.Input);

    private static (string Before, string After) QSources(QReplacement pair, string module)
    {
        var path = RepoPathFor(module);
        return (Encoding.UTF8.GetString(LeanSourceCatalog.Parse(pair.Before, pair.Input, "protected", sourceReference: "protected")
                .ExtractPropositionSource(path, pair.BaseView.ActiveByPath[path].Material.DeclarationStatementIds).AsSpan()),
            Encoding.UTF8.GetString(LeanSourceCatalog.Parse(pair.After, pair.Input, "current", sourceReference: "protected")
                .ExtractPropositionSource(path, pair.CandidateCatalog.ByPath[path].DeclarationStatementIds).AsSpan()));
    }

    private QCase QLoad(string name, char pin = 'a')
    {
        using var packet = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(TestRepositoryLayout.FindRoot(),
            "tools/tests/StrataLint.Tests/Ledger/Fixtures/ContextQualification/reports.json")));
        var encodedReport = packet.RootElement.GetProperty(name);
        var files = new[] { PathFor("A"), PathFor("Helper"), "ProbeExternal/Equality.lean" }
            .Select(path => QText(path, QualifiedSourceContextFixture.Source(name, path)))
            .Concat(new[]
            {
                QText("lean-toolchain", CandidateToolchain),
                // Synthetic eligibility pin, not a claim that these sources came from Mathlib.
                QText("lake-manifest.json", Manifest(pin).Replace("\"type\":\"git\"", "\"type\":\"git\",\"url\":\"https://github.com/leanprover-community/mathlib4\"", StringComparison.Ordinal)),
                QText("lakefile.toml", "name = \"qualification\"\n"),
            });
        var snapshot = QSnapshot(files);
        // Repository snapshots require UTF-8. Decode the unchanged archive bytes
        // only into this test's disposable bundle, then use the strict file loader.
        var reportDirectory = Path.Combine(qualifiedReports.Path, name);
        Directory.CreateDirectory(reportDirectory);
        var reportPath = Path.Combine(reportDirectory, "raw-report.json");
        File.WriteAllText(reportPath, encodedReport.GetProperty("report").GetString()!, new UTF8Encoding(false));
        File.WriteAllBytes(reportPath + ".materials.zip", Convert.FromBase64String(
            encodedReport.GetProperty("materials").GetString()!));
        var report = RawLeanReportArtifact.ReadFile(reportPath, snapshot);
        // Exercise lazy archive loading and compare the current compactor with the real .NET writer.
        foreach (var (path, file) in report.Files)
        {
            foreach (var declaration in file.Declarations)
            {
                var material = declaration.LoadTypeRepresentation();
                var unaddressed = new LeanDeclaration(declaration.Name, declaration.Kind,
                    material, declaration.Axioms)
                {
                    NameKey = declaration.NameKey,
                    IncludeInStatement = declaration.IncludeInStatement,
                };
                Assert.Equal(CanonicalStatementWriter.DeclarationStatementId(path, unaddressed),
                    declaration.PrecomputedStatementId);
            }
        }
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(snapshot, report)).Capability;
        var states = LeanTruthStates.Resolve(snapshot, lean);
        var adjacency = LeanImportAdjacency.Build(snapshot, lean);
        var catalog = Assert.IsType<FrozenMaterialOutcome.Accepted>(
            FrozenContentAddress.Build(snapshot, lean, states, adjacency)).Capability;
        Assert.Equal(2, catalog.ClosedNodes.Length);
        var data = new QCase(snapshot, report, lean, states, adjacency, catalog, reportPath);
        return data;
    }

    private QReplacement QPair(string beforeName, string afterName, string[] replaced)
    {
        var beforeData = QLoad(beforeName, 'a');
        var afterData = QLoad(afterName, 'b');
        var baseEvents = EventFiles(beforeData.Catalog);
        var before = QSnapshot(beforeData.Snapshot.Files.Values.Concat(baseEvents));
        var baseView = FrozenLedgerBaseViewReader.Read(before);
        var replacementPaths = replaced.Select(RepoPathFor).ToImmutableHashSet();
        var generated = ImmutableArray.CreateBuilder<RepositoryFile>();
        var eventIds = new Dictionary<RepoPath, string>();
        foreach (var path in LeanImportAdjacency.DependenciesFirst(replacementPaths,
            afterData.Adjacency).Where(replacementPaths.Contains))
        {
            var original = afterData.Catalog.ByPath[path];
            var prerequisites = afterData.Adjacency[path].Select(dependency =>
                FrozenNodeId.Create(eventIds.TryGetValue(dependency, out var eventId)
                    ? eventId : baseView.ActiveByPath[dependency].EventHash))
                .OrderBy(identity => identity.Value, StringComparer.Ordinal).ToImmutableArray();
            var material = original with
            {
                FrozenNodeId = FrozenContentAddress.ComputeFrozenNodeId(path, original.StatementId, prerequisites),
                PrerequisiteFrozenNodeIds = prerequisites,
            };
            var file = EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
                FrozenLedgerCanonicalWriter.FreezePayload(material)));
            var loaded = Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(DagLedgerLoader.LoadFiles([file]));
            eventIds.Add(path, loaded.Events[0].EventHash);
            generated.Add(file);
        }
        var removed = baseView.Events.Where(item => item.FreezePayload is not null
                && replacementPaths.Contains(RepoPath.CreateKnown(item.FreezePayload.DescriptorSelector)))
            .Select(item => item.SourcePath).ToImmutableHashSet();
        var after = QSnapshot(afterData.Snapshot.Files.Values
            .Concat(baseEvents.Where(file => !removed.Contains(file.Path))).Concat(generated));
        var candidateView = FrozenLedgerBaseViewReader.Read(after);
        var catalog = FrozenContentAddress.BuildAdmissionCatalog(after, afterData.Lean,
            afterData.States, afterData.Adjacency,
            baseView.ActiveByPath.Keys.ToImmutableHashSet(), candidateView.ActiveByPath);
        var changes = RawChangeSet.CreateWithKinds(
            removed.Select(path => (path.Value, RawChangeKind.Deleted))
                .Concat(generated.Select(file => (file.Path.Value, RawChangeKind.Added)))
                .Concat(afterData.Snapshot.Files.Values.Where(file =>
                    beforeData.Snapshot.Files.TryGetValue(file.Path, out var old)
                    && !old.RawBytes.AsSpan().SequenceEqual(file.RawBytes.AsSpan()))
                    .Select(file => (file.Path.Value, RawChangeKind.Modified))));
        var delta = DagLedgerCommandPreparation.ValidateGeneratedEventFiles(baseView,
            generated.ToImmutable(), "qualification generated events");
        var recognition = FrozenLedgerIncrementalReplacementRecognition.Recognize(
            baseView, after, changes, delta, catalog);
        return new QReplacement(before, after, baseView, catalog, recognition, delta,
            LeanSourceContextInput.Load(QualifiedSourceContextFixture.Bytes(after, before, beforeName, afterName), after, before));
    }

    private static string[] QDrift(QReplacement pair) => pair.BaseView.ActiveByPath
        .Where(item => pair.CandidateCatalog.ByPath[item.Key].StatementId != item.Value.Material.StatementId)
        .Select(item => item.Key.Value).Order(StringComparer.Ordinal).ToArray();

    private static bool QAuthorized(QReplacement pair) => pair.Recognition is not null
        && new MathlibUpgradeFrozenLedgerReplacementAuthorization(pair.Before, pair.After, pair.Input)
            .IsAuthorized(new FrozenLedgerReplacementAuthorizationContext(pair.Recognition,
                pair.BaseView, pair.CandidateCatalog));

    private static string QMaterial(QCase data, string module) =>
        Assert.Single(data.Report.Files[RepoPathFor(module)].Declarations).LoadTypeRepresentation();

    private static RepositoryFile QText(string path, string text) => new(
        RepoPath.CreateKnown(path), ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(text)), text);

    private static RepositorySnapshot QSnapshot(IEnumerable<RepositoryFile> files) =>
        RepositorySnapshot.Create(files.ToImmutableDictionary(file => file.Path));

    private sealed record QCase(RepositorySnapshot Snapshot, LeanAxiomReport Report,
        AcceptedLeanClosure Lean, ImmutableDictionary<RepoPath, TruthState> States,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> Adjacency,
        FrozenMaterialCatalog Catalog, string ReportPath);

    private sealed record QReplacement(RepositorySnapshot Before, RepositorySnapshot After,
        FrozenLedgerBaseView BaseView, FrozenMaterialCatalog CandidateCatalog,
        FrozenLedgerIncrementalReplacementRecognition? Recognition,
        ImmutableArray<DagLedgerFileEvent> Delta, LeanSourceContextInput Input);
}
