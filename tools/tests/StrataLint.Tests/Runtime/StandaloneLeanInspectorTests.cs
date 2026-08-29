using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class StandaloneLeanInspectorTests
{
    private const string Lakefile = """
        name = "snapshot_probe"
        version = "0.1.0"
        defaultTargets = ["Trureturing"]

        [[lean_lib]]
        name = "Trureturing"
        """;

    private const string LakefileWithD5 = """
        name = "snapshot_probe"
        version = "0.1.0"
        defaultTargets = ["Trureturing"]

        [[lean_lib]]
        name = "Trureturing"
        roots = ["Trureturing", "D5"]
        globs = ["Trureturing", "D5.+"]
        """;

    [Fact]
    public void InspectorBuildsAndReadsTheProvidedSnapshotInsteadOfCandidateDiskState()
    {
        using var repository = new TemporaryDirectory();
        File.WriteAllText(Path.Combine(repository.Path, "lakefile.toml"), Lakefile + "\n");
        File.WriteAllText(Path.Combine(repository.Path, "lean-toolchain"), "leanprover/lean4:v4.31.0\n");
        File.WriteAllText(Path.Combine(repository.Path, "Trureturing.lean"), "def diskOnly : Nat := 1\n");
        var build = TestProcessRunner.Run(
            "lake",
            new[] { "build" },
            repository.Path,
            TestBudgets.LeanProcessHangGuard,
            4 * 1024 * 1024);
        Assert.Equal(0, build.ExitCode);
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("lakefile.toml", Lakefile + "\n"),
            RawRepositoryEntry.FromText("lean-toolchain", "leanprover/lean4:v4.31.0\n"),
            RawRepositoryEntry.FromText("Trureturing.lean", "axiom snapshotOnly : False\n"),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

        var report = new TestLeanReportProducer(repository.Path).Inspect(snapshot);

        var file = report.Files.Single(static item => item.Key.Value == "Trureturing.lean").Value;
        Assert.Contains(file.Declarations, static item => item.Name == "snapshotOnly" && item.Kind == "axiom");
        Assert.DoesNotContain(file.Declarations, static item => item.Name == "diskOnly");
    }

    [Fact]
    public void InspectorRoundTripsDirectModuleImportsFromModuleData()
    {
        using var repository = new TemporaryDirectory();
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("lakefile.toml", LakefileWithD5 + "\n"),
            RawRepositoryEntry.FromText("lean-toolchain", "leanprover/lean4:v4.31.0\n"),
            RawRepositoryEntry.FromText(
                "D5/S0/Carrier/Dependency.lean",
                "def dependency : Nat := 7\n"),
            RawRepositoryEntry.FromText(
                "Trureturing.lean",
                "import D5.S0.Carrier.Dependency\n\ndef importer : Nat := dependency\n"),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

        var report = new TestLeanReportProducer(repository.Path).Inspect(snapshot);

        var importer = report.Files.Single(static item => item.Key.Value == "Trureturing.lean").Value;
        Assert.Contains("D5.S0.Carrier.Dependency", importer.Imports);
    }

    [Fact]
    public void InspectorEmitsStructuralStatementMaterialThatIgnoresProofsAndBinderNames()
    {
        using var repository = new TemporaryDirectory();
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("lakefile.toml", Lakefile + "\n"),
            RawRepositoryEntry.FromText("lean-toolchain", "leanprover/lean4:v4.31.0\n"),
            RawRepositoryEntry.FromText(
                "Trureturing.lean",
                """
                theorem proofA : forall x : Nat, x = x := by
                  intro x
                  rfl

                theorem proofB : forall y : Nat, y = y := fun _ => rfl
                """ + "\n"),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

        var report = new TestLeanReportProducer(repository.Path).Inspect(snapshot);

        var declarations = report.Files.Single().Value.Declarations;
        var proofA = declarations.Single(static item => item.Name == "proofA");
        var proofB = declarations.Single(static item => item.Name == "proofB");
        Assert.StartsWith("statement-v1(", proofA.LoadTypeRepresentation(), StringComparison.Ordinal);
        Assert.Equal(proofA.LoadTypeRepresentation(), proofB.LoadTypeRepresentation());
    }

    [Fact]
    public void ModuleStatementIsStableAcrossProofAndBinderNameRewrites()
    {
        var first = InspectSingleModule(
            "theorem same : forall x : Nat, x = x := by intro x; rfl\n");
        var second = InspectSingleModule(
            "theorem same : forall renamed : Nat, renamed = renamed := fun _ => rfl\n");
        Assert.True(RepoPath.TryCreate("Trureturing.lean", out var path));

        var firstDeclarations = CanonicalStatementWriter.DeclarationStatementIds(path, first);
        var secondDeclarations = CanonicalStatementWriter.DeclarationStatementIds(path, second);
        Assert.True(firstDeclarations.SequenceEqual(secondDeclarations));

        Assert.True(
            CanonicalStatementWriter.WriteModule(path, firstDeclarations).AsSpan()
                .SequenceEqual(CanonicalStatementWriter.WriteModule(path, secondDeclarations).AsSpan()));
    }

    [Fact]
    public void DefinitionStatementMaterialChangesWhenItsBodyChangesAtTheSameType()
    {
        var first = InspectSingleModule("def same : Nat := 1\n");
        var second = InspectSingleModule("def same : Nat := 2\n");

        Assert.NotEqual(
            first.Declarations.Single(static declaration => declaration.Name == "same")
                .LoadTypeRepresentation(),
            second.Declarations.Single(static declaration => declaration.Name == "same")
                .LoadTypeRepresentation());
    }

    [Fact]
    public void GeneratedProofAuxiliariesAreExcludedFromModuleStatementReferences()
    {
        var report = InspectSingleModule(
            """
            structure Laws where
              value : Nat
              addZero : value + 0 = value
              zeroAdd : 0 + value = value
              addAssoc : (value + 0) + 0 = value + (0 + 0)

            noncomputable def laws : Laws where
              value := 7
              addZero := by simp
              zeroAdd := by simp
              addAssoc := by simp
            """ + "\n");
        Assert.True(RepoPath.TryCreate("Trureturing.lean", out var path));
        var generated = report.Declarations
            .Where(static declaration =>
                declaration.Kind == "theorem"
                && declaration.Name.Contains("_proof_", StringComparison.Ordinal))
            .ToArray();

        Assert.NotEmpty(generated);
        var references = CanonicalStatementWriter.DeclarationStatementIds(path, report);
        Assert.DoesNotContain(
            references,
            static declaration => declaration.DeclarationNameKey.Contains("_proof_", StringComparison.Ordinal));
    }

    [Fact]
    public void AxiomsAreAttributedPerDeclarationAcrossTheSharedCollectionCache()
    {
        // Regression guard for the run-shared axiom-collection cache: each
        // declaration must report exactly its own transitive axiom closure. A
        // naive shared-visited cache would either drop the axiom from a later
        // declaration that shares the dependency, or leak it onto an unrelated
        // axiom-free declaration processed afterwards. Both are excluded here.
        var report = InspectSingleModule(
            """
            axiom groundless : False

            theorem consumesAxiom : True := False.elim groundless
            def axiomFree : Nat := 1
            theorem alsoConsumesAxiom : True := False.elim groundless
            """ + "\n");

        var consumes = report.Declarations.Single(static d => d.Name == "consumesAxiom");
        var free = report.Declarations.Single(static d => d.Name == "axiomFree");
        var alsoConsumes = report.Declarations.Single(static d => d.Name == "alsoConsumesAxiom");

        Assert.Contains("groundless", consumes.Axioms);
        Assert.Contains("groundless", alsoConsumes.Axioms);
        Assert.DoesNotContain("groundless", free.Axioms);
        Assert.Empty(free.Axioms);
    }

    private static LeanFileReport InspectSingleModule(string source)
    {
        using var repository = new TemporaryDirectory();
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("lakefile.toml", Lakefile + "\n"),
            RawRepositoryEntry.FromText("lean-toolchain", "leanprover/lean4:v4.31.0\n"),
            RawRepositoryEntry.FromText("Trureturing.lean", source),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var report = new TestLeanReportProducer(repository.Path).Inspect(snapshot).Files.Single().Value;
        return new LeanFileReport(
            report.Imports,
            report.Declarations.Select(declaration => new LeanDeclaration(
                declaration.Name,
                declaration.Kind,
                declaration.LoadTypeRepresentation(),
                declaration.Axioms)
            {
                IncludeInStatement = declaration.IncludeInStatement,
                NameKey = declaration.NameKey,
            }).ToImmutableArray(),
            report.Error);
    }

    private sealed class TestLeanReportProducer(string repositoryRoot)
    {
        internal LeanAxiomReport Inspect(RepositorySnapshot snapshot)
        {
            foreach (var (path, file) in snapshot.Files)
            {
                var destination = Path.Combine(repositoryRoot, path.Value);
                Directory.CreateDirectory(Path.GetDirectoryName(destination)
                    ?? throw new InvalidOperationException("test snapshot path has no parent"));
                File.WriteAllBytes(destination, file.RawBytes.AsSpan());
            }

            var build = TestProcessRunner.Run(
                "lake",
                ["build"],
                repositoryRoot,
                TestBudgets.LeanProcessHangGuard,
                8 * 1024 * 1024);
            Assert.True(
                build.ExitCode == 0,
                Encoding.UTF8.GetString(build.StandardOutput) + Encoding.UTF8.GetString(build.StandardError));

            var output = Path.Combine(repositoryRoot, "raw-lean-report.json");
            var spoolReport = output + ".spool.json";
            var spoolMaterials = output + ".spool-materials";
            var arguments = new List<string>
            {
                "env",
                "lean",
                "--run",
                Path.Combine(
                    TestRepositoryLayout.FindRoot(),
                    "tools", "lean-inspector",
                    "Inspector.lean"),
                "--output",
                spoolReport,
                "--material-spool",
                spoolMaterials,
            };
            foreach (var (path, file) in snapshot.Files
                         .Where(static item => LeanClosureValidator.IsManagedLean(item.Key.Value))
                         .OrderBy(static item => item.Key.Value, StringComparer.Ordinal))
            {
                arguments.Add(path.Value == "Trureturing.lean"
                    ? "Trureturing"
                    : path.Value[..^5].Replace('/', '.'));
                arguments.Add(path.Value);
                arguments.Add("sha256:" + Convert.ToHexStringLower(SHA256.HashData(file.RawBytes.AsSpan())));
            }

            var inspection = TestProcessRunner.Run(
                "lake",
                arguments,
                repositoryRoot,
                TestBudgets.LeanProcessHangGuard,
                8 * 1024 * 1024);
            Assert.True(
                inspection.ExitCode == 0,
                Encoding.UTF8.GetString(inspection.StandardOutput)
                    + Encoding.UTF8.GetString(inspection.StandardError));
            var compacted = TestProcessRunner.Run(
                "python3",
                [
                    Path.Combine(
                        TestRepositoryLayout.FindRoot(),
                        "tools", "lean-inspector", "materials.py"),
                    "compact", spoolReport, spoolMaterials, output,
                ],
                repositoryRoot,
                TestBudgets.LeanProcessHangGuard,
                8 * 1024 * 1024);
            Assert.True(
                compacted.ExitCode == 0,
                Encoding.UTF8.GetString(compacted.StandardOutput)
                    + Encoding.UTF8.GetString(compacted.StandardError));
            return RawLeanReportArtifact.ReadFile(output, snapshot);
        }
    }

}
