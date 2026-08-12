using System.Text.Json;
using StrataLint.Engine;
using Xunit;

namespace StrataLint.Scribe.Tests;

public sealed class StatementProjectionPilotTests
{
    [Fact]
    public void Authored_is_rejected_when_LeanDerived_is_available_exclusively()
    {
        var declaration = LeanDeclarationRef.Create(
            "D5/S1/Solenoid/HiddenFiberCompact.hiddenFiber_closed_compact_seqCompact");

        var error = Assert.Throws<InvalidOperationException>(() => StatementSource.Materialize(
            StatementSource.FromAuthor(FormulaDsl.Disp(FormulaDsl.D(1))), declaration));

        Assert.Contains("projection is available", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Authored_is_legal_when_projection_is_unavailable()
    {
        var declaration = LeanDeclarationRef.Create("D5/S0/Test/Missing.claim");

        var materialized = StatementSource.Materialize(
            StatementSource.FromAuthor(FormulaDsl.Disp(FormulaDsl.D(1))), declaration);

        Assert.IsType<StatementSource.Authored>(materialized.Source);
    }

    [Fact]
    public void Authored_never_impersonates_LeanDerived_provenance()
    {
        var declaration = LeanDeclarationRef.Create("D5/S0/Test/Missing.claim");
        var materialized = StatementSource.Materialize(
            StatementSource.FromAuthor(FormulaDsl.Disp(FormulaDsl.D(1))), declaration);

        Assert.IsType<StatementSource.Authored>(materialized.Source);
        Assert.IsNotType<StatementSource.LeanDerived>(materialized.Source);
    }

    [Fact]
    public void ProjectionGap_is_recomputed_from_current_declaration_content()
    {
        var declaration = LeanDeclarationRef.Create("D5/S0/Test/Missing.claim");

        var first = Assert.IsType<StatementSource.Authored>(StatementSource.Materialize(
            StatementSource.FromAuthor(FormulaDsl.Disp(FormulaDsl.D(1))), declaration).Source);
        var second = Assert.IsType<StatementSource.Authored>(StatementSource.Materialize(
            StatementSource.FromAuthor(FormulaDsl.Disp(FormulaDsl.D(2))), declaration).Source);

        Assert.NotNull(first.ProjectionGap);
        Assert.Equal(first.ProjectionGap, second.ProjectionGap);
        Assert.Equal(StatementProjectionFixtureLoader.ProjectorEpoch, first.ProjectionGap!.ProjectorEpoch);
        Assert.Equal(64, first.ProjectionGap.DeclarationContentDigest.Length);
    }

    [Fact]
    public void Author_cannot_self_fill_or_freeze_a_ProjectionGap()
    {
        Assert.Empty(typeof(ProjectionGap).GetConstructors());
        var authoredFactory = typeof(StatementSource).GetMethod(nameof(StatementSource.FromAuthor));
        Assert.Equal([typeof(Formula)], authoredFactory!.GetParameters().Select(p => p.ParameterType));
    }

    [Fact]
    public void DocumentDefinitionsLoadFromExplicitRepositoryRoot()
    {
        var repositoryRoot = RepositoryAccessor.Discover(RepositoryRootCriterion.LakefileInvalidOperation).Root.FullPath;
        var definitions = DocumentDefinitions.Discover(
            typeof(DocumentDefinitions).Assembly,
            repositoryRoot);

        Assert.NotEmpty(definitions);
    }

    [Fact]
    public void DocumentDefinitionsFailClosedWithFixturePathForExplicitRepository()
    {
        var repositoryRoot = TemporaryFileSystem.Directory.CreateTempSubdirectory("stratalint-scribe-missing-");
        try
        {
            var exception = Assert.Throws<FileNotFoundException>(() =>
                DocumentDefinitions.Discover(
                    typeof(DocumentDefinitions).Assembly,
                    repositoryRoot.FullName));

            Assert.Contains(repositoryRoot.FullName, exception.Message, StringComparison.Ordinal);
            Assert.Contains(
                "statement-projection-pilot-v1.json",
                exception.Message,
                StringComparison.Ordinal);
        }
        finally
        {
            repositoryRoot.Delete(recursive: true);
        }
    }

    [Fact]
    public void DecoderCoversEveryInspectorExpressionConstructor()
    {
        const string encoded = "statement-v1(uparams=[ns(n0,1:u)],type=ee(0,es(l0),ei(ln(7)),ej(ns(n0,1:S),0,ed(el(bd,ef(ns(n0,1:x)),ea(em(ns(n0,1:m)),eb(0)))))))";
        var statement = StatementV1Decoder.Decode(encoded);

        Assert.Single(statement.UniverseParameters);
        Assert.IsType<LeanExpr.Let>(statement.Type);
    }

    [Theory]
    [InlineData("")]
    [InlineData("statement-v2(uparams=[],type=es(l0))")]
    [InlineData("statement-v1(uparams=[],type=unknown())")]
    [InlineData("statement-v1(uparams=[],type=es(l0))junk")]
    public void DecoderFailsClosedOnMalformedOrUnknownInput(string encoded) =>
        Assert.Throws<FormatException>(() => StatementV1Decoder.Decode(encoded));

    [Fact]
    public void ProjectorMapsBindingAndPropositionCore()
    {
        const string encoded = "statement-v1(uparams=[],type=ep(bd,ec(ns(n0,4:Real),[]),ea(ea(ea(ec(ns(n0,2:Eq),[]),ec(ns(n0,4:Real),[])),eb(0)),eb(0))))";
        var result = StatementProjector.Project(StatementV1Decoder.Decode(encoded).Type);

        var formula = Assert.IsType<ProjectionOutcome.Projected>(result).Formula;
        Assert.Equal("\\forall x0 \\in \\mathrm{Real},\\; \\mathit{x0} = \\mathit{x0}", LatexWriter.Write(formula));
    }

    [Fact]
    public void PropPiToImplicationProjectsNondependentPropositionDomains()
    {
        const string encoded = "statement-v1(uparams=[],type=ep(bd,ea(ea(ea(ec(ns(n0,2:Eq),[]),ec(ns(n0,4:Real),[])),ei(ln(0))),ei(ln(0))),ea(ea(ea(ec(ns(n0,2:Eq),[]),ec(ns(n0,4:Real),[])),ei(ln(1))),ei(ln(1)))))";

        var result = StatementProjector.Project(StatementV1Decoder.Decode(encoded).Type);

        var formula = Assert.IsType<ProjectionOutcome.Projected>(result).Formula;
        Assert.Equal("0 = 0 \\Rightarrow 1 = 1", LatexWriter.Write(formula));
    }

    [Fact]
    public void PropPiToImplicationDoesNotRewriteDependentPiDomains()
    {
        const string encoded = "statement-v1(uparams=[],type=ep(bd,ec(ns(n0,4:Real),[]),ea(ea(ea(ec(ns(n0,2:Eq),[]),ec(ns(n0,4:Real),[])),eb(0)),eb(0))))";

        var result = StatementProjector.Project(StatementV1Decoder.Decode(encoded).Type);

        var formula = Assert.IsType<ProjectionOutcome.Projected>(result).Formula;
        Assert.Equal("\\forall x0 \\in \\mathrm{Real},\\; \\mathit{x0} = \\mathit{x0}", LatexWriter.Write(formula));
    }

    [Fact]
    public void DenoiserStripsOnlyRegisteredElaborationArguments()
    {
        const string encoded = "statement-v1(uparams=[],type=ea(ea(ec(ns(ns(ns(ns(ns(n0,2:D5),2:S3),4:Weil),11:LabeledZeta),12:LedgerLength),[]),es(l0)),ec(ns(n0,9:AddMonoid),[])))";

        var result = StatementProjector.Project(StatementV1Decoder.Decode(encoded).Type);

        var formula = Assert.IsType<ProjectionOutcome.Projected>(result).Formula;
        Assert.Equal("\\mathrm{LedgerLength}", LatexWriter.Write(formula));
    }

    [Fact]
    public void DenoiserFailsClosedForUnknownElaborationShape()
    {
        const string encoded = "statement-v1(uparams=[],type=ea(ea(ec(ns(n0,13:Unknown.noise),[]),ec(ns(n0,4:Real),[])),ei(ln(7))))";

        var result = Assert.IsType<ProjectionOutcome.Unprojectable>(
            StatementProjector.Project(StatementV1Decoder.Decode(encoded).Type));

        Assert.Contains("Unknown.noise", result.Reason, StringComparison.Ordinal);
    }

    [Fact]
    public void IsClosedTopologyInstanceFamilyProjectsFaithfullyFromFixture()
    {
        using var fixture = LoadPinnedFixture("statement-projection-pilot-v1.json");
        using var expansion = LoadPinnedFixture("statement-projection-expansion-v1.json");
        var result = Assert.Single(ProjectionPilot.Run(ReadFixtureDeclarations(fixture, expansion)).Cases,
            item => item.Name.EndsWith("hiddenFiber_closed_compact_seqCompact", StringComparison.Ordinal));

        Assert.Empty(result.Unprojectable);
        Assert.IsNotType<Formula.Placeholder>(result.Formula);
    }

    [Fact]
    public void AddSubgroupFiniteSumCoercionFamilyProjectsFaithfullyFromFixture()
    {
        using var fixture = LoadPinnedFixture("statement-projection-pilot-v1.json");
        using var expansion = LoadPinnedFixture("statement-projection-expansion-v1.json");
        var result = Assert.Single(ProjectionPilot.Run(ReadFixtureDeclarations(fixture, expansion)).Cases,
            item => item.Name.EndsWith("finite_poisson_summation", StringComparison.Ordinal));

        Assert.Empty(result.Unprojectable);
        Assert.IsNotType<Formula.Placeholder>(result.Formula);
    }

    [Fact]
    public void PropPiToImplicationProjectsGlobalFactorClearingFixture()
    {
        using var fixture = LoadPinnedFixture("statement-projection-pilot-v1.json");
        using var expansion = LoadPinnedFixture("statement-projection-expansion-v1.json");
        var declaration = Assert.Single(ReadFixtureDeclarations(fixture, expansion), item =>
            item.Key.EndsWith("global_factor_clearing_forces_critical_line", StringComparison.Ordinal));

        var outcome = StatementProjector.Project(
            StatementV1Decoder.Decode(declaration.Value.GetProperty("type").GetString()!).Type);

        var formula = Assert.IsType<ProjectionOutcome.Projected>(outcome).Formula;
        Assert.Equal(
            "\\forall x2 \\in \\mathrm{LedgerLength},\\; \\left(\\exists x3 \\in \\mathord{\\cdot},\\; \\mathit{x2}\\left(\\mathit{x3}\\right) \\ne 0\\right) \\Rightarrow \\left(\\forall x4 \\in \\mathrm{Complex},\\; \\forall x5 \\in \\mathrm{Complex},\\; \\left(\\forall x6 \\in \\mathord{\\cdot},\\; \\left\\lVert \\mathit{x5} \\cdot \\mathrm{halfDensityReading}\\left(\\mathit{x2}, \\mathit{x4}, \\mathit{x6}\\right) \\right\\rVert = 1\\right) \\Rightarrow \\mathrm{re}\\left(\\mathit{x4}\\right) = \\mathrm{criticalAbscissa}\\right)",
            LatexWriter.Write(formula));
    }

    [Fact]
    public void PilotProjectsTenOfTenRealDeclarationsAndPinsTheComparisonReport()
    {
        using var fixture = LoadPinnedFixture("statement-projection-pilot-v1.json");
        using var expansion = LoadPinnedFixture("statement-projection-expansion-v1.json");
        var results = ProjectionPilot.Run(ReadFixtureDeclarations(fixture, expansion));

        Assert.Equal(10, results.Cases.Length);
        Assert.Empty(results.Report);
        Assert.Equal(ProjectionNotation.Entries.Count, results.NotationSize);
        Assert.All(results.Cases.Where(item => item.Unprojectable.IsEmpty),
            item => Assert.IsNotType<Formula.Placeholder>(item.Formula));
        Assert.All(results.Cases.Where(item => !item.Unprojectable.IsEmpty),
            item => Assert.IsType<Formula.Placeholder>(item.Formula));
        Assert.Equal(10, results.Cases.Count(item => item.Unprojectable.IsEmpty));
        Assert.Empty(results.Cases.Where(item => !item.Unprojectable.IsEmpty));
    }

    [Fact]
    public void EveryExistingPilotDescribeFormulaIsProjectionDerivedWithoutHandwrittenDisp()
    {
        using var fixture = LoadPinnedFixture("statement-projection-pilot-v1.json");
        using var expansion = LoadPinnedFixture("statement-projection-expansion-v1.json");
        var names = ReadFixtureDeclarations(fixture, expansion).Keys.ToArray();
        var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.LakefileInvalidOperation);
        var sources = repository.EnumerateFiles(RepositoryRelativePath.Create("Blueprint"), "*.scribe.cs")
            .Select(repository.ReadAllText).ToArray();

        // Projection-derived statements are written two ways while the migration runs:
        // the legacy loader call, and StatementSource.FromLean() on the report-derived entry.
        // Both count.
        var projected = sources.Sum(source =>
            source.Split("StatementProjectionFixtureLoader.FromLean(", StringSplitOptions.None).Length - 1
            + source.Split("StatementSource.FromLean()", StringSplitOptions.None).Length - 1);

        // A floor, not an equality. Within a fixed exclusivity domain the quantity only grows:
        // an authored statement is illegal wherever the projector can produce one, so migrations
        // and projector improvements move declarations in and none leave. Correcting the domain
        // itself does shrink it — that happened once, when non-theorem declarations were judged
        // unprojectable because the projector projects a declaration's type and a definition's type
        // is only its signature. The floor is therefore re-derived from the current domain rather
        // than presented as monotone. The real enforcement is the emit-time exclusivity check,
        // which is stronger than any count; this test only catches regression.
        Assert.True(
            projected >= 7,
            $"projection-derived statements regressed to {projected}, below the floor of 7");
    }

    [LiveReportFact]
    public void LiveReportMatchesPinnedFixtureWhenAvailable()
    {
        var repositoryRoot = RepositoryAccessor
            .Discover(RepositoryRootCriterion.LakefileInvalidOperation).Root.FullPath;
        StatementProjectionReconciliation.Verify(
            repositoryRoot,
            DeclarationCatalog.Create(LeanCompiledArtifactReports.InspectRepository(repositoryRoot)));
    }

    [Fact]
    public void ReconciliationCatalogFailsClosedWhenDeclarationKindIsMissing()
    {
        using var repository = TemporaryRepository.WithReport(
            type: "statement-v1(uparams=[],type=es(l0))");

        Assert.Throws<InvalidOperationException>(() => repository.Catalog(kind: ""));
    }

    [Fact]
    public void RequiredLiveReportPassesWhenReportMatchesPinnedFixture()
    {
        using var repository = TemporaryRepository.WithReport(type: "statement-v1(uparams=[],type=es(l0))");

        StatementProjectionReconciliation.Verify(repository.Path, repository.Catalog());
    }

    [Fact]
    public void RequiredLiveReportFailsWhenReportDiffersFromPinnedFixture()
    {
        using var repository = TemporaryRepository.WithReport(type: "statement-v1(uparams=[],type=es(l1))");

        Assert.Throws<InvalidDataException>(() =>
            StatementProjectionReconciliation.Verify(repository.Path, repository.Catalog()));
    }

    [Fact]
    public void EveryPinnedFixtureDeclarationCarriesTheoremKind()
    {
        using var pilot = LoadPinnedFixture("statement-projection-pilot-v1.json");
        using var expansion = LoadPinnedFixture("statement-projection-expansion-v1.json");

        // The engineering CI job runs without a raw Lean report and decides projectability from
        // these files alone. If a non-theorem were pinned here it would be judged projectable
        // without a report and unprojectable with one, so the same tree would emit two different
        // documents depending on which machine built it.
        foreach (var declaration in ReadFixtureDeclarations(pilot, expansion))
        {
            Assert.True(
                declaration.Value.TryGetProperty("kind", out var kind),
                $"pinned declaration has no kind: {declaration.Key}");
            Assert.Equal("theorem", kind.GetString());
        }
    }

    [LiveReportFact]
    public void NonTheoremDeclarationsAreUnprojectableWhenTheReportIsAvailable()
    {
        var repositoryRoot = RepositoryAccessor
            .Discover(RepositoryRootCriterion.LakefileInvalidOperation).Root.FullPath;

        // hellingerSq is a def: its type is the signature (ι → ℝ) → (ι → ℝ) → ℝ, and its defining
        // body never reaches the projector. Projecting it would render the arrows as nested
        // quantifiers and present that as the definition.
        var outcome = StatementProjectionFixtureLoader.WithRepositoryRoot(
            repositoryRoot,
            () => StatementProjectionFixtureLoader.Project(
                LeanDeclarationRef.Create("D5/S3/TotalVariation/Hellinger.hellingerSq")));

        var failed = Assert.IsType<ProjectionOutcome.Unprojectable>(outcome);
        Assert.Equal("non-propositional-declaration", failed.Reason.Split(':', 2)[0]);
        Assert.Equal("def", failed.Reason.Split(':', 2)[1]);
    }

    [Fact]
    public void TheoremDeclarationsRemainProjectable()
    {
        var repositoryRoot = RepositoryAccessor
            .Discover(RepositoryRootCriterion.LakefileInvalidOperation).Root.FullPath;

        // The companion to the test above: narrowing the exclusivity domain to theorems must not
        // narrow it past theorems. Without this, judging everything unprojectable would pass.
        // The subject is pinned, so this holds with or without a raw report.
        var outcome = StatementProjectionFixtureLoader.WithRepositoryRoot(
            repositoryRoot,
            () => StatementProjectionFixtureLoader.Project(
                LeanDeclarationRef.Create("D5/S1/Solenoid/HiddenFiberCompact.hiddenFiber_closed_compact_seqCompact")));

        Assert.IsType<ProjectionOutcome.Projected>(outcome);
    }

    private static JsonDocument LoadPinnedFixture(string name) => JsonDocument.Parse(
        RepositoryAccessor.Discover(RepositoryRootCriterion.LakefileInvalidOperation).ReadAllBytes(RepositoryRelativePath.Create(
            $"Golden/Projection/{name}")));

    private static Dictionary<string, JsonElement> ReadFixtureDeclarations(params JsonDocument[] fixtures)
    {
        Assert.Equal("statement-projection-pilot-fixture-v1", fixtures[0].RootElement.GetProperty("schema").GetString());
        Assert.Equal("statement-projection-expansion-fixture-v1", fixtures[1].RootElement.GetProperty("schema").GetString());
        return fixtures.SelectMany(fixture => fixture.RootElement.GetProperty("declarations").EnumerateArray())
            .ToDictionary(item => item.GetProperty("name").GetString()!, StringComparer.Ordinal);
    }

    private sealed class LiveReportFactAttribute : FactAttribute
    {
        public LiveReportFactAttribute()
        {
            var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.LakefileInvalidOperation);
            var requireLiveReport = Environment.GetEnvironmentVariable("STRATALINT_REQUIRE_LIVE_REPORT") == "1";
            if (!requireLiveReport && !repository.FileExists(RepositoryRelativePath.Create(
                    ".lake/build/stratalint/raw-lean-report.json")))
            {
                Skip = "Live raw Lean report is absent; pinned statement-v1 fixture remains the self-contained verifier asset.";
                return;
            }
            if (!requireLiveReport)
            {
                try
                {
                    _ = LeanCompiledArtifactReports.InspectRepository(repository.Root.FullPath);
                }
                catch (FormatException)
                {
                    Skip = "Live raw Lean report is stale; pinned statement-v1 fixture remains the self-contained verifier asset.";
                }
            }
        }
    }

    private sealed class TemporaryRepository : IDisposable
    {
        private readonly DirectoryInfo root = TemporaryFileSystem.Directory.CreateTempSubdirectory("stratalint-statement-reconciliation-");

        public string Path => root.FullName;

        public static TemporaryRepository WithReport(string type)
        {
            var repository = new TemporaryRepository();
            TemporaryFileSystem.Directory.CreateDirectory(System.IO.Path.Combine(repository.Path, "Golden", "Projection"));
            TemporaryFileSystem.Directory.CreateDirectory(System.IO.Path.Combine(repository.Path, ".lake", "build", "stratalint"));
            TemporaryFileSystem.File.WriteAllText(
                System.IO.Path.Combine(repository.Path, "Golden", "Projection", "statement-projection-pilot-v1.json"),
                $$"""{"schema":"statement-projection-pilot-fixture-v1","declarations":[{"name":"D5.Test.declaration","type":"{{type}}"}]}""");
            TemporaryFileSystem.File.WriteAllText(
                System.IO.Path.Combine(repository.Path, "Golden", "Projection", "statement-projection-expansion-v1.json"),
                """{"schema":"statement-projection-expansion-fixture-v1","declarations":[]}""");
            TemporaryFileSystem.File.WriteAllText(
                System.IO.Path.Combine(repository.Path, ".lake", "build", "stratalint", "raw-lean-report.json"),
                """{"modules":[{"declarations":[{"name":"D5.Test.declaration","type":"statement-v1(uparams=[],type=es(l0))"}]}]}""");
            return repository;
        }

        public DeclarationCatalog Catalog(string kind = "theorem") => DeclarationCatalog.Create(
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
            {
                ["D5/Test.lean"] = new(
                    [],
                    [new LeanDeclaration(
                        "D5.Test.declaration",
                        kind,
                        "statement-v1(uparams=[],type=es(l0))",
                        [])]),
            }));

        public void Dispose() => root.Delete(recursive: true);
    }
}
