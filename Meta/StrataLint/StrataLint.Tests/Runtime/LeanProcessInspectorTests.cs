using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanProcessInspectorTests
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
        var build = BoundedProcessRunner.Run(
            "lake",
            new[] { "build" },
            repository.Path,
            TimeSpan.FromSeconds(120),
            4 * 1024 * 1024);
        Assert.Equal(0, build.ExitCode);
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("lakefile.toml", Lakefile + "\n"),
            RawRepositoryEntry.FromText("lean-toolchain", "leanprover/lean4:v4.31.0\n"),
            RawRepositoryEntry.FromText("Trureturing.lean", "axiom snapshotOnly : False\n"),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

        var report = new LeanProcessInspector(repository.Path).Inspect(snapshot);

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

        var report = new LeanProcessInspector(repository.Path).Inspect(snapshot);

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

        var report = new LeanProcessInspector(repository.Path).Inspect(snapshot);

        var declarations = report.Files.Single().Value.Declarations;
        var proofA = declarations.Single(static item => item.Name == "proofA");
        var proofB = declarations.Single(static item => item.Name == "proofB");
        Assert.StartsWith("statement-v1(", proofA.TypeRepresentation, StringComparison.Ordinal);
        Assert.Equal(proofA.TypeRepresentation, proofB.TypeRepresentation);
    }

    [Fact]
    public void ModuleStatementIsStableAcrossProofAndBinderNameRewrites()
    {
        var first = InspectSingleModule(
            "theorem same : forall x : Nat, x = x := by intro x; rfl\n");
        var second = InspectSingleModule(
            "theorem same : forall renamed : Nat, renamed = renamed := fun _ => rfl\n");
        Assert.True(RepoPath.TryCreate("Trureturing.lean", out var path));

        Assert.True(
            CanonicalStatementWriter.DeclarationStatementIds(path, first)
                .SequenceEqual(CanonicalStatementWriter.DeclarationStatementIds(path, second)));

        Assert.True(
            CanonicalStatementWriter.WriteModule(path, first).AsSpan()
                .SequenceEqual(CanonicalStatementWriter.WriteModule(path, second).AsSpan()));
    }

    [Fact]
    public void DefinitionStatementMaterialChangesWhenItsBodyChangesAtTheSameType()
    {
        var first = InspectSingleModule("def same : Nat := 1\n");
        var second = InspectSingleModule("def same : Nat := 2\n");

        Assert.NotEqual(
            first.Declarations.Single(static declaration => declaration.Name == "same").TypeRepresentation,
            second.Declarations.Single(static declaration => declaration.Name == "same").TypeRepresentation);
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
    public void InspectorDiscardsLegacyMemoAndRecomputesMatchingOleanReport()
    {
        using var repository = new TemporaryDirectory();
        File.WriteAllText(Path.Combine(repository.Path, "lakefile.toml"), Lakefile + "\n");
        File.WriteAllText(Path.Combine(repository.Path, "lean-toolchain"), "leanprover/lean4:v4.31.0\n");
        File.WriteAllText(Path.Combine(repository.Path, "Trureturing.lean"), "def liveDeclaration : Nat := 1\n");
        var build = BoundedProcessRunner.Run(
            "lake",
            new[] { "build" },
            repository.Path,
            TimeSpan.FromSeconds(120),
            4 * 1024 * 1024);
        Assert.Equal(0, build.ExitCode);
        var olean = Path.Combine(repository.Path, ".lake", "build", "lib", "lean", "Trureturing.olean");
        var oleanSha256 = Convert.ToHexStringLower(
            System.Security.Cryptography.SHA256.HashData(File.ReadAllBytes(olean)));
        File.WriteAllText(
            Path.Combine(repository.Path, ".lake", "build", "stratalint-inspection-v1.json"),
            $$$$"""
            {"version":1,"entries":{"Trureturing":{"olean_sha256":"{{{{oleanSha256}}}}","imports":[],"declarations":[{"name":"legacy.memo","kind":"def","type":"Nat","axioms":[]}]}}}
            """ + "\n");
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("lakefile.toml", Lakefile + "\n"),
            RawRepositoryEntry.FromText("lean-toolchain", "leanprover/lean4:v4.31.0\n"),
            RawRepositoryEntry.FromText("Trureturing.lean", "def liveDeclaration : Nat := 1\n"),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

        var report = new LeanProcessInspector(repository.Path).Inspect(snapshot).Files.Single().Value;

        Assert.Contains(report.Declarations, static item => item.Name == "liveDeclaration");
        Assert.DoesNotContain(report.Declarations, static item => item.Name == "legacy.memo");
    }

    [Fact]
    public void InspectionMemoRoundTripsStatementIdentityMetadataForItsFormatVersion()
    {
        using var repository = new TemporaryDirectory();
        const string formatVersion = "test-harness-format-v2";
        var memo = InspectionMemo.Load(repository.Path, formatVersion);
        memo.Put(
            "Trureturing",
            "abc123",
            new LeanFileReport(
                [],
                [new LeanDeclaration("private._proof_1", "theorem", "statement-v1(test)", [])
                {
                    NameKey = "ns(n0,4:test)",
                    IncludeInStatement = false,
                }]));

        memo.Save(repository.Path);
        var reloaded = InspectionMemo.Load(repository.Path, formatVersion);

        Assert.True(reloaded.TryGet("Trureturing", "abc123", out var report));
        var declaration = Assert.Single(report.Declarations);
        Assert.Equal("ns(n0,4:test)", declaration.NameKey);
        Assert.False(declaration.IncludeInStatement);
        Assert.False(
            InspectionMemo.Load(repository.Path, formatVersion + "-changed")
                .TryGet("Trureturing", "abc123", out _));
        Assert.Contains(
            "\"harness_format_version\":\"test-harness-format-v2\"",
            File.ReadAllText(Path.Combine(
                repository.Path,
                ".lake",
                "build",
                "stratalint-inspection-v1.json")),
            StringComparison.Ordinal);
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
        return new LeanProcessInspector(repository.Path).Inspect(snapshot).Files.Single().Value;
    }
}
