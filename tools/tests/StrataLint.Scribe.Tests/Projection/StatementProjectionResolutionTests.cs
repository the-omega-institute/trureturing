using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class StatementProjectionResolutionTests
{
    private const string GeneratedPath =
        "D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.lean";
    private const string GeneratedName =
        "D5.S3.ConceptDynamics.InformationEscape.Catalog.GeneratedKernel.ext";
    private const string TotalCodePath = "D5/S0/Conventions/TotalCode.lean";
    private const string TotalCodeName = "D5.S0.Conventions.TotalCode.TotalCode.ext";
    private static LeanDeclarationRef Generated => LeanDeclarationRef.Create(GeneratedPath[..^5] + ".ext");

    [Fact]
    public void GeneratedKernelExtDoesNotResolvePinnedTotalCodeExt()
    {
        using var repository = new StatementProjectionTestRepository(
            new StatementProjectionTestRepository.Pin(TotalCodeName, TotalCodePath, Equality(2)));

        repository.Run(() => AssertUnavailable(Generated, "missing"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SameModuleShortNameProjectsDespiteNamespaceFileMismatch(bool reverse)
    {
        StatementProjectionTestRepository.Pin[] pins =
        [new(GeneratedName, GeneratedPath, Equality(1)), new(TotalCodeName, TotalCodePath, Equality(2))];
        using var repository = new StatementProjectionTestRepository(reverse ? pins.Reverse().ToArray() : pins);

        repository.Run(() => AssertProjected(Generated, "1 = 1", Equality(1)));
    }

    [Fact]
    public void ForeignExactDottedNameCannotOverrideSourcePath()
    {
        using var repository = new StatementProjectionTestRepository(
            new(Generated.Value.Replace('/', '.'), TotalCodePath, Equality(2)),
            new(GeneratedName, GeneratedPath, Equality(1)));

        repository.Run(() => AssertProjected(Generated, "1 = 1", Equality(1)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MissingModuleDoesNotSearchOtherModules(bool reverse)
    {
        StatementProjectionTestRepository.Pin[] pins =
        [new(TotalCodeName, TotalCodePath, Equality(2)), new("Other.unrelated", "D5/S0/Test/Other.lean", Equality(1))];
        using var repository = new StatementProjectionTestRepository(reverse ? pins.Reverse().ToArray() : pins);

        repository.Run(() => AssertUnavailable(Generated, "missing"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DuplicateShortNamesInOneModuleAreAmbiguous(bool reverse)
    {
        StatementProjectionTestRepository.Pin[] pins =
        [new(Generated.Value.Replace('/', '.'), GeneratedPath, Equality(2)), new(GeneratedName, GeneratedPath, Equality(1))];
        using var repository = new StatementProjectionTestRepository(reverse ? pins.Reverse().ToArray() : pins);

        repository.Run(() => AssertUnavailable(Generated, "ambiguous"));
    }

    [Fact]
    public void AssessmentIgnoresAmbientReportPresenceAndContent()
    {
        var unpinned = LeanDeclarationRef.Create(GeneratedPath[..^5] + ".unpinned");
        var observations = new List<(Observation Pinned, Observation Unpinned)>();
        foreach (var liveNumber in new int?[] { null, 2, 3 })
        {
            // Each corpus is loaded in a fresh root so the loader cache cannot mask report reads.
            using var repository = new StatementProjectionTestRepository(
                new StatementProjectionTestRepository.Pin(GeneratedName, GeneratedPath, Equality(1)));
            if (liveNumber is int number)
            {
                repository.WriteReport(
                    new(GeneratedName, GeneratedPath, Equality(number)),
                    new("Other.unpinned", GeneratedPath, Equality(number + 1)));
            }
            observations.Add(repository.Run(() => (Observe(Generated), Observe(unpinned))));
        }

        Assert.Equal("1 = 1", observations[0].Pinned.Formula);
        Assert.Equal("missing", observations[0].Unpinned.Verdict);
        foreach (var observation in observations.Skip(1))
            Assert.Equal(observations[0], observation);
    }

    [Theory]
    [InlineData("foreign-module")]
    [InlineData("missing-module")]
    [InlineData("foreign-name")]
    [InlineData("kind-mismatch")]
    [InlineData("duplicate")]
    public void PinnedOwnershipReconciliationRejectsForeignModule(string mismatch)
    {
        var pin = new StatementProjectionTestRepository.Pin(GeneratedName, GeneratedPath, Equality(1));
        using var repository = new StatementProjectionTestRepository(pin);
        var live = mismatch switch
        {
            "foreign-module" => new[] { pin with { SourcePath = TotalCodePath } },
            "missing-module" => [],
            "foreign-name" => [pin with { Name = "Other.ext" }],
            "kind-mismatch" => [pin with { Kind = "def" }],
            "duplicate" => [pin, pin],
            _ => throw new ArgumentOutOfRangeException(nameof(mismatch)),
        };
        var catalog = StatementProjectionTestRepository.Catalog(live);

        var finding = Assert.Single(StatementProjectionReconciliation.Check(repository.Path, catalog));

        Assert.Contains(GeneratedName, finding, StringComparison.Ordinal);
        Assert.Contains(mismatch == "duplicate" ? "ambiguous" : mismatch == "kind-mismatch" ? "differs" : "missing",
            finding, StringComparison.Ordinal);
        Assert.Throws<InvalidDataException>(() => StatementProjectionReconciliation.Verify(repository.Path, catalog));
    }

    [Fact]
    public void ReconciliationMatchesOnlyTheOwnedFullNameAndIgnoresForeignDuplicates()
    {
        var pin = new StatementProjectionTestRepository.Pin(GeneratedName, GeneratedPath, Equality(1));
        using var repository = new StatementProjectionTestRepository(pin);
        var catalog = StatementProjectionTestRepository.Catalog(
            pin, pin with { SourcePath = TotalCodePath, Type = Equality(2), Kind = "def" });

        Assert.Empty(StatementProjectionReconciliation.Check(repository.Path, catalog));
        StatementProjectionReconciliation.Verify(repository.Path, catalog);
    }

    [Theory]
    [InlineData("def", "non-propositional-declaration")]
    [InlineData("malformed-theorem", "unregistered-elaboration-shape")]
    public void LegacyFromLeanUsesTheSelectedEntryKindAndDecoder(string variant, string reason)
    {
        using var repository = new StatementProjectionTestRepository(
            new StatementProjectionTestRepository.Pin(GeneratedName, GeneratedPath, variant == "def" ? Equality(1) : "invalid statement",
                variant == "def" ? "def" : "theorem"));

        repository.Run(() => AssertUnavailable(Generated, reason));
    }

    [Fact]
    public void UnselectedStatementMaterialIsNotDecoded()
    {
        using var repository = new StatementProjectionTestRepository(
            new(GeneratedName, GeneratedPath, Equality(1)),
            new("Other.bad", GeneratedPath, "invalid statement"),
            new(TotalCodeName, TotalCodePath, "invalid statement", "def"));

        repository.Run(() => AssertProjected(Generated, "1 = 1", Equality(1)));
    }

    internal static string Equality(int number) =>
        $"statement-v1(uparams=[],type=ea(ea(ea(ec(ns(n0,2:Eq),[]),ec(ns(n0,3:Nat),[])),ei(ln({number}))),ei(ln({number}))))";

    internal static void AssertProjected(LeanDeclarationRef declaration, string latex, string encoded)
    {
        var assessment = StatementProjectionFixtureLoader.Assess(declaration);
        Assert.Equal(latex, LatexWriter.Write(Assert.IsType<ProjectionOutcome.Projected>(assessment.Outcome).Formula));
        Assert.Equal(Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(encoded))),
            assessment.DeclarationContentDigest);
        var materialized = StatementSource.Materialize(StatementSource.FromLean(), declaration);
        Assert.IsType<StatementSource.LeanDerived>(materialized.Source);
        Assert.Equal(latex, LatexWriter.Write(materialized.Formula!));
        var legacy = StatementProjectionFixtureLoader.FromLean(declaration);
        Assert.Equal(latex, LatexWriter.Write(legacy));
        Assert.True(StatementProjectionFixtureLoader.IsDerivedFrom(legacy, declaration));
        Assert.Throws<InvalidOperationException>(() => StatementSource.Materialize(
            StatementSource.FromAuthor(FormulaDsl.D(9)), declaration));
        Assert.Throws<InvalidOperationException>(() => StatementSource.Materialize(
            StatementSource.WithoutFormula(), declaration));
    }

    private static void AssertUnavailable(LeanDeclarationRef declaration, string reason)
    {
        var assessment = StatementProjectionFixtureLoader.Assess(declaration);
        var outcome = Assert.IsType<ProjectionOutcome.Unprojectable>(assessment.Outcome);
        Assert.StartsWith(reason + ":", outcome.Reason, StringComparison.Ordinal);
        var authored = StatementSource.Materialize(StatementSource.FromAuthor(FormulaDsl.D(9)), declaration);
        var gap = Assert.IsType<StatementSource.Authored>(authored.Source).ProjectionGap;
        Assert.Equal(reason, gap!.ReasonCode);
        Assert.Equal(assessment.DeclarationContentDigest, gap.DeclarationContentDigest);
        var omitted = StatementSource.Materialize(StatementSource.WithoutFormula(), declaration);
        Assert.Equal(gap, Assert.IsType<StatementSource.NoFormula>(omitted.Source).ProjectionGap);
        Assert.Null(omitted.Formula);
        Assert.Throws<InvalidOperationException>(() => StatementSource.Materialize(StatementSource.FromLean(), declaration));
        var error = Assert.Throws<InvalidOperationException>(() => StatementProjectionFixtureLoader.FromLean(declaration));
        Assert.Contains(reason + ":", error.Message, StringComparison.Ordinal);
    }

    private static Observation Observe(LeanDeclarationRef declaration)
    {
        var assessment = StatementProjectionFixtureLoader.Assess(declaration);
        var formula = assessment.Outcome is ProjectionOutcome.Projected projected
            ? LatexWriter.Write(projected.Formula) : null;
        return new Observation(
            assessment.Outcome is ProjectionOutcome.Unprojectable failed
                ? StatementProjectionFixtureLoader.ReasonCode(failed.Reason) : "projected",
            formula, assessment.DeclarationContentDigest,
            Legal(StatementSource.FromLean()), Legal(StatementSource.FromAuthor(FormulaDsl.D(9))),
            Legal(StatementSource.WithoutFormula()), Legacy());

        bool Legal(StatementSource source)
        {
            try { _ = StatementSource.Materialize(source, declaration); return true; }
            catch (InvalidOperationException) { return false; }
        }

        string? Legacy()
        {
            try { return LatexWriter.Write(StatementProjectionFixtureLoader.FromLean(declaration)); }
            catch (InvalidOperationException) { return null; }
        }
    }

    private sealed record Observation(string Verdict, string? Formula, string Digest,
        bool LeanLegal, bool AuthorLegal, bool NoFormulaLegal, string? LegacyFormula);
}

internal sealed class StatementProjectionTestRepository : IDisposable
{
    private readonly DirectoryInfo root = TemporaryFileSystem.Directory.CreateTempSubdirectory("stratalint-projection-resolution-");
    internal sealed record Pin(string Name, string? SourcePath, string Type, string Kind = "theorem");
    internal string Path => root.FullName;

    internal StatementProjectionTestRepository(params Pin[] pins)
    {
        WriteFixture("pilot", pins);
        WriteFixture("expansion", []);
    }

    internal void WriteFixture(string group, params Pin[] pins)
    {
        var directory = System.IO.Path.Combine(Path, "Golden", "Projection");
        TemporaryFileSystem.Directory.CreateDirectory(directory);
        var declarations = pins.Select(pin =>
        {
            var fields = new Dictionary<string, object?> { ["name"] = pin.Name, ["kind"] = pin.Kind, ["type"] = pin.Type };
            if (pin.SourcePath is not null) fields.Add("source_path", pin.SourcePath);
            return fields;
        });
        TemporaryFileSystem.File.WriteAllText(
            System.IO.Path.Combine(directory, $"statement-projection-{group}-v1.json"),
            JsonSerializer.Serialize(new { schema = $"statement-projection-{group}-fixture-v1", declarations }));
    }

    internal T Run<T>(Func<T> action) => StatementProjectionFixtureLoader.WithRepositoryRoot(Path, action);
    internal void Run(Action action) => Run(() => { action(); return true; });

    internal static DeclarationCatalog Catalog(params Pin[] declarations) => DeclarationCatalog.Create(Report(declarations));

    private static LeanAxiomReport Report(Pin[] declarations) => LeanAxiomReport.Create(declarations
        .GroupBy(pin => pin.SourcePath!, StringComparer.Ordinal)
        .ToDictionary(group => group.Key, group => new LeanFileReport([], group
            .Select(pin => new LeanDeclaration(pin.Name, pin.Kind, pin.Type, [])).ToImmutableArray()),
            StringComparer.Ordinal));

    internal void WriteReport(params Pin[] declarations)
    {
        var raw = RawRepositorySnapshot.Create(declarations.Select(pin => pin.SourcePath!)
            .Distinct(StringComparer.Ordinal).Select(path => RawRepositoryEntry.FromText(path, "theorem probe : True := True.intro\n")));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var reportPath = System.IO.Path.Combine(Path, ".lake", "build", "stratalint", "raw-lean-report.json");
        RawLeanReportArtifact.WriteFile(reportPath, snapshot, Report(declarations));
        var loaded = RawLeanReportArtifact.ReadFile(reportPath, snapshot);
        foreach (var pin in declarations)
        {
            var module = Assert.Single(loaded.Files, entry => entry.Key.Value == pin.SourcePath).Value;
            Assert.Equal(pin.Type, Assert.Single(module.Declarations, declaration => declaration.Name == pin.Name).LoadTypeRepresentation());
        }
        Assert.True(TemporaryFileSystem.File.Exists(reportPath + ".materials.zip"));
    }

    public void Dispose() => root.Delete(recursive: true);
}
