using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Tests;

public sealed partial class CoverBatchCommandTests
{
    private const string ProblemPath = "Problems/batch-problem.md";
    private const string FrozenPath = "Golden/Frozen/state/D5/S0/Carrier/Probe.lean.json";

    [Fact]
    public void ProductionScribeReusesFrozenLoadsAndMatchesSequentialBytes()
    {
        using var sequential = new BatchWorld();
        using var batch = new BatchWorld();
        WriteProblem(sequential.Root);
        WriteProblem(batch.Root);
        var verifier = new ProductionScribeEmissionVerifier(typeof(BatchClaimDefinition).Assembly);
        FrozenLoadCounter sequentialLoads;
        using (sequentialLoads = new FrozenLoadCounter()) sequential.RunSingles(verifier);
        FrozenLoadCounter batchLoads;
        using var ledgerLoads = new LedgerLoadCounter();
        CommandResult result;
        using (batchLoads = new FrozenLoadCounter())
            result = batch.Run(Row(First, Gid) + Row(Second, OtherGid), verifier);

        Assert.True(result.Success, result.Error + result.Output);
        Assert.Equal(sequential.LedgerImage(), batch.LedgerImage());
        Assert.Equal(["applied", "applied"], Results(result).Select(item => item.Status).ToArray());
        Assert.Equal(1, batch.EmitCount);
        output.WriteLine("FROZEN_LOADS session_only sequential_catalog={0} sequential_index={1} batch_catalog={2} batch_index={3}",
            sequentialLoads.Catalogs, sequentialLoads.Indexes, batchLoads.Catalogs, batchLoads.Indexes);
        Assert.Equal(1, batchLoads.Catalogs);
        Assert.Equal(1, batchLoads.Indexes);
        Assert.Equal(2, sequentialLoads.Catalogs);
        Assert.Equal(2, sequentialLoads.Indexes);
        WriteLoadCounts("production-scribe-parser-owner", ledgerLoads);
        Assert.Equal(1, ledgerLoads.BaselineLoads);
        Assert.Equal([1, 1, 1], ledgerLoads.CandidateSnapshotLoads);
    }

    [Fact]
    public void ProductionScribeRejectsMissingResolutionDossierForEveryItem()
    {
        using var world = new BatchWorld();
        WriteProblem(world.Root);
        TemporaryFileSystem.File.Delete(Path.Combine(world.Root, ProblemPath));
        var before = world.LedgerImage();
        var verifier = new ProductionScribeEmissionVerifier(typeof(BatchClaimDefinition).Assembly);

        var result = world.Run(Row(First, Gid) + Row(Second, OtherGid), verifier);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(["failed", "failed"], Results(result).Select(item => item.Status).ToArray());
        Assert.All(Results(result), item =>
            Assert.Contains("dangling-problem-slug", item.Reason, StringComparison.Ordinal));
        Assert.Equal(before, world.LedgerImage());
        Assert.Equal(1, world.EmitCount);
    }

    [Theory]
    [InlineData(FrozenPath)]
    [InlineData(ProblemPath)]
    [InlineData("D5/S0/Carrier/Probe.lean")]
    public void ProductionScribeCannotHideChangedSharedInputsAfterOneSuccess(string changedPath)
    {
        using var world = new BatchWorld();
        WriteProblem(world.Root);
        var verifier = new ProductionScribeEmissionVerifier(typeof(BatchClaimDefinition).Assembly);
        var calls = 0;
        BatchClaimDefinition.Creating.Value = () =>
        {
            if (++calls == 2)
                TemporaryFileSystem.File.AppendAllText(Path.Combine(world.Root, changedPath), "\n");
        };
        try
        {
            var result = world.Run(Row(First, Gid) + Row(Second, OtherGid) + Row("missing-atom", Gid), verifier);

            Assert.Equal(1, result.ExitCode);
            Assert.Equal(["applied", "failed", "blocked"], Results(result).Select(item => item.Status).ToArray());
            Assert.Contains("shared cover context changed: " + changedPath, result.Error, StringComparison.Ordinal);
            Assert.Single(world.Entry(First).Coverage);
            Assert.Empty(world.Entry(Second).Coverage);
            Assert.Equal(2, calls);
            Assert.Equal(0, world.EmitCount);
        }
        finally
        {
            BatchClaimDefinition.Creating.Value = null;
        }
    }

    private sealed class FrozenLoadCounter : IDisposable
    {
        private readonly Action? previousCatalog = FrozenStateCatalog.Loading.Value;
        private readonly Action? previousIndex = FrozenStatementIndex.Creating.Value;
        internal int Catalogs { get; private set; }
        internal int Indexes { get; private set; }

        internal FrozenLoadCounter()
        {
            FrozenStateCatalog.Loading.Value = () => Catalogs++;
            FrozenStatementIndex.Creating.Value = () => Indexes++;
        }

        public void Dispose()
        {
            FrozenStateCatalog.Loading.Value = previousCatalog;
            FrozenStatementIndex.Creating.Value = previousIndex;
        }
    }

    private sealed class BatchClaimDefinition : IScribeDocumentDefinition
    {
        internal static readonly AsyncLocal<Action?> Creating = new();

        public DocumentDefinition Create()
        {
            Creating.Value?.Invoke();
            var statement = FormulaDsl.In(
                DefinitionDsl.Equal(DefinitionDsl.Id("x"), DefinitionDsl.Id("x")));
            var claim = Describe.Lean(DescribeId.Create("resolution"), DeclarationHandle.Create(Gid),
                Heading.Create("Resolution"), StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
                DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Resolution fixture."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("batch-problem"), ResolutionKind.Proved));
            var document = ScribeDocument.Create(DefinitionDsl.Header("D5/S0/Carrier/Probe", "Batch fixture."),
                Heading.Create("Batch resolution"), DefinitionDsl.Blocks(claim));
            return DocumentDefinition.Create(document, "Blueprint/D5/S0/Carrier/Probe.scribe.cs");
        }
    }

    private static void WriteProblem(string root)
    {
        WriteScribeFixture(root, "Golden/Projection/statement-projection-pilot-v1.json", """
            {"schema":"statement-projection-pilot-fixture-v1","declarations":[]}
            """);
        WriteScribeFixture(root, "Golden/Projection/statement-projection-expansion-v1.json", """
            {"schema":"statement-projection-expansion-fixture-v1","declarations":[]}
            """);
        WriteScribeFixture(root, "Library/notes/batch2026fixture.md", """
            ---
            bibkey: batch2026fixture
            authors: Fixture Author
            year: 2026
            title: Batch fixture
            doi: 10.48550/arXiv.2305.08349
            claim: Synthetic resolution fixture.
            strata_touched: []
            license: citation-only
            triage: anchor
            ---

            """);
        WriteScribeFixture(root, ProblemPath, """
            ---
            slug: batch-problem
            bibkey: batch2026fixture
            doi: 10.48550/arXiv.2305.08349
            triage: theorem
            motivation_gids:
              - D5/S0/Carrier/Probe
            ---

            # Batch problem

            ## Problem
            Prove the fixture statement.
            ## Motivation
            The frozen carrier supplies the setup.
            ## Gap
            The source leaves this question open.
            ## Route
            Prove the statement.
            ## Falsifier
            A counterexample.
            ## Evidence
            Synthetic problem dossier.
            ## Triage
            A theorem.
            ## ASSUMED-UNVERIFIED
            - Fixture only.

            """);
    }

    private static void WriteScribeFixture(string root, string path, string text)
    {
        var fullPath = Path.Combine(root, path);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
        TemporaryFileSystem.File.WriteAllText(fullPath, text);
    }
}
