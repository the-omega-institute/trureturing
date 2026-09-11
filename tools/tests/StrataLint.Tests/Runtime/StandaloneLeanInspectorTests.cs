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
        Assert.All(generated, static declaration =>
        {
            Assert.False(declaration.IncludeInStatement);
            Assert.StartsWith("statement-v1(", declaration.LoadTypeRepresentation(), StringComparison.Ordinal);
        });
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

    [Fact]
    public void EncoderPreservesCanonicalConstructorFramingAndUtf8Bytes()
    {
        // These fixed spellings are independent of the encoder, including its
        // byte lengths. Asymmetric children detect accidental reordering.
        var cases = new (string Name, string Expression, string Bytes)[]
        {
            ("bvar", ".bvar 0", "eb(0)"),
            ("decimal-index", ".bvar 120", "eb(120)"),
            ("fvar", ".fvar ⟨.num (.str .anonymous \"f\") 12⟩", "ef(nn(ns(n0,1:f),12))"),
            ("mvar", ".mvar ⟨.str .anonymous \"m\"⟩", "em(ns(n0,1:m))"),
            ("zero", ".sort .zero", "es(l0)"),
            ("succ", ".sort (.succ .zero)", "es(ls(l0))"),
            ("max", ".sort (.max (.succ .zero) .zero)", "es(lm(ls(l0),l0))"),
            ("imax", ".sort (.imax .zero (.succ (.succ .zero)))", "es(li(l0,ls(ls(l0))))"),
            ("param", ".sort (.param (.str .anonymous \"u\"))", "es(lp(ns(n0,1:u)))"),
            ("level-mvar", ".sort (.mvar ⟨.num .anonymous 42⟩)", "es(lv(nn(n0,42)))"),
            ("const-empty", ".const .anonymous []", "ec(n0,[])"),
            ("const-single", ".const (.str .anonymous \"\") [.zero]", "ec(ns(n0,0:),[l0])"),
            ("const-multiple", ".const (.num (.str .anonymous \"C\") 0) [.succ .zero, .zero]", "ec(nn(ns(n0,1:C),0),[ls(l0),l0])"),
            ("app", ".app (.bvar 2) (.sort (.succ .zero))", "ea(eb(2),es(ls(l0)))"),
            ("lam-default", ".lam `ignored (.bvar 1) (.bvar 2) .default", "el(bd,eb(1),eb(2))"),
            ("lam-renamed", ".lam `renamed (.bvar 1) (.bvar 2) .default", "el(bd,eb(1),eb(2))"),
            ("lam-implicit", ".lam .anonymous (.bvar 1) (.bvar 2) .implicit", "el(bi,eb(1),eb(2))"),
            ("lam-strict", ".lam .anonymous (.bvar 1) (.bvar 2) .strictImplicit", "el(bs,eb(1),eb(2))"),
            ("lam-instance", ".lam .anonymous (.bvar 1) (.bvar 2) .instImplicit", "el(bc,eb(1),eb(2))"),
            ("forall-default", ".forallE `ignored (.bvar 1) (.bvar 2) .default", "ep(bd,eb(1),eb(2))"),
            ("forall-renamed", ".forallE `renamed (.bvar 1) (.bvar 2) .default", "ep(bd,eb(1),eb(2))"),
            ("forall-implicit", ".forallE .anonymous (.bvar 1) (.bvar 2) .implicit", "ep(bi,eb(1),eb(2))"),
            ("forall-strict", ".forallE .anonymous (.bvar 1) (.bvar 2) .strictImplicit", "ep(bs,eb(1),eb(2))"),
            ("forall-instance", ".forallE .anonymous (.bvar 1) (.bvar 2) .instImplicit", "ep(bc,eb(1),eb(2))"),
            ("let-dependent", ".letE `ignored (.bvar 1) (.bvar 2) (.bvar 3) false", "ee(0,eb(1),eb(2),eb(3))"),
            ("let-renamed", ".letE `renamed (.bvar 1) (.bvar 2) (.bvar 3) false", "ee(0,eb(1),eb(2),eb(3))"),
            ("let-nondependent", ".letE `renamed (.bvar 1) (.bvar 2) (.bvar 3) true", "ee(1,eb(1),eb(2),eb(3))"),
            ("nat-zero", ".lit (.natVal 0)", "ei(ln(0))"),
            ("nat-large", ".lit (.natVal 18446744073709551616)", "ei(ln(18446744073709551616))"),
            ("str-empty", ".lit (.strVal \"\")", "ei(lt(0:))"),
            ("str-ascii", ".lit (.strVal \"a\")", "ei(lt(1:a))"),
            ("str-two-byte", ".lit (.strVal \"é\")", "ei(lt(2:é))"),
            ("str-three-byte", ".lit (.strVal \"界\")", "ei(lt(3:界))"),
            ("str-four-byte", ".lit (.strVal \"𝒪\")", "ei(lt(4:𝒪))"),
            ("str-combining", ".lit (.strVal \"é\")", "ei(lt(3:é))"),
            ("str-mixed", ".lit (.strVal \"aé界𝒪é\")", "ei(lt(13:aé界𝒪é))"),
            ("str-control", ".lit (.strVal \"\\x00\\n\\r\\n,:()[]=\")", "ei(lt(11:\0\n\r\n,:()[]=))"),
            ("metadata", ".mdata {} (.bvar 8)", "ed(eb(8))"),
            ("metadata-payload", ".mdata (KVMap.empty.insert `ignored (DataValue.ofNat 37)) (.bvar 8)", "ed(eb(8))"),
            ("projection", ".proj (.str .anonymous \"𝒪\") 120 (.bvar 3)", "ej(ns(n0,4:𝒪),120,eb(3))"),
            ("name-mixed", ".const (.str (.num .anonymous 18446744073709551616) \"aé界𝒪é\") []", "ec(ns(nn(n0,18446744073709551616),13:aé界𝒪é),[])"),
            ("name-control", ".const (.str .anonymous \"\\x00\\n\\r\\n,:()[]=\") []", "ec(ns(n0,11:\0\n\r\n,:()[]=),[])"),
        };
        using var temporary = new TemporaryDirectory();
        var entries = string.Join(",\n", cases.Select(static item => $"(\"{item.Name}\", {item.Expression})"));
        RunEncoderProbe(temporary.Path, $$"""
            #eval show IO Unit from do
              let cases : Array (String × Expr) := #[{{entries}}]
              for (name, expression) in cases do
                let info : ConstantInfo := .axiomInfo {
                  name := .anonymous, levelParams := [], type := expression, isUnsafe := false }
                IO.FS.withFile (name ++ ".statement") .write fun handle => do
                  handle.putStr (encodeStatement info)
                  handle.flush
            """);
        foreach (var item in cases)
            Assert.Equal(
                Encoding.UTF8.GetBytes("statement-v1(uparams=[],type=" + item.Bytes + ")"),
                File.ReadAllBytes(Path.Combine(temporary.Path, item.Name + ".statement")));
    }

    [Fact]
    public void EncoderPreservesUniverseOrderAndDeclarationValueBranches()
    {
        using var temporary = new TemporaryDirectory();
        RunEncoderProbe(temporary.Path, """
            #eval show IO Unit from do
              let base : ConstantVal := { name := `ignored, levelParams := [], type := .bvar 1 }
              let definition : DefinitionVal := {
                toConstantVal := base, value := .bvar 2, hints := .opaque, safety := .safe }
              let cases : Array (String × ConstantInfo) := #[
                ("def", .defnInfo definition),
                ("opaque", .opaqueInfo { toConstantVal := base, value := .bvar 3, isUnsafe := false }),
                ("theorem", .thmInfo { toConstantVal := base, value := .bvar 4 }),
                ("theorem-other-proof", .thmInfo { toConstantVal := base, value := .bvar 99 }),
                ("single", .defnInfo { definition with levelParams := [.anonymous] }),
                ("multiple", .defnInfo { definition with
                  levelParams := [.str .anonymous "z", .num .anonymous 0, .str .anonymous "é"] }),
                ("axiom", .axiomInfo { toConstantVal := base, isUnsafe := false }),
                ("quotient", .quotInfo { (default : QuotVal) with toConstantVal := base }),
                ("constructor", .ctorInfo { (default : ConstructorVal) with toConstantVal := base }),
                ("recursor", .recInfo { (default : RecursorVal) with toConstantVal := base }),
                ("inductive", .inductInfo { (default : InductiveVal) with toConstantVal := base })]
              for (name, info) in cases do
                IO.FS.withFile (name ++ ".statement") .write fun handle => do
                  handle.putStr (encodeStatement info)
                  handle.flush
            """);
        var expected = new Dictionary<string, string>
        {
            ["def"] = "statement-v1(uparams=[],type=eb(1),value=eb(2))",
            ["opaque"] = "statement-v1(uparams=[],type=eb(1),value=eb(3))",
            ["theorem"] = "statement-v1(uparams=[],type=eb(1))",
            ["theorem-other-proof"] = "statement-v1(uparams=[],type=eb(1))",
            ["single"] = "statement-v1(uparams=[n0],type=eb(1),value=eb(2))",
            ["multiple"] = "statement-v1(uparams=[ns(n0,1:z),nn(n0,0),ns(n0,2:é)],type=eb(1),value=eb(2))",
        };
        foreach (var kind in new[] { "axiom", "quotient", "constructor", "recursor", "inductive" })
            expected[kind] = "statement-v1(uparams=[],type=eb(1))";
        foreach (var (name, bytes) in expected)
            Assert.Equal(Encoding.UTF8.GetBytes(bytes), File.ReadAllBytes(Path.Combine(temporary.Path, name + ".statement")));
    }

    [Fact]
    public void EncoderPreservesLargeSharedExpressionBytes()
    {
        using var temporary = new TemporaryDirectory();
        RunEncoderProbe(temporary.Path, """
            #eval show IO Unit from do
              let mut expression := Expr.lit (.strVal "𝒪")
              for _ in [:16] do expression := .app expression expression
              let info : ConstantInfo := .axiomInfo {
                name := .anonymous, levelParams := [], type := expression, isUnsafe := false }
              IO.FS.withFile "shared.statement" .write fun handle => do
                handle.putStr (encodeStatement info)
                handle.flush
            """);
        var observed = File.ReadAllBytes(Path.Combine(temporary.Path, "shared.statement"));
        // Each app adds five framing bytes around two shared children.
        var expandedBytes = (14 + 5) * (1 << 16) - 5;
        Assert.Equal(expandedBytes + Encoding.UTF8.GetByteCount("statement-v1(uparams=[],type=)"), observed.Length);
        // Fixed from the independent constructor spellings above.
        Assert.Equal("0420803024e82cb51146bed06fb931d0f61a37d9e342e0aae71915de073f5f54",
            Convert.ToHexString(SHA256.HashData(observed)).ToLowerInvariant());
    }

    [Fact]
    public void EncoderPreservesLargeLiteralBytes()
    {
        using var temporary = new TemporaryDirectory();
        RunEncoderProbe(temporary.Path, """
            #eval show IO Unit from do
              let payload := String.ofList (List.replicate 65536 'é')
              let info : ConstantInfo := .axiomInfo {
                name := .anonymous, levelParams := [], type := .lit (.strVal payload), isUnsafe := false }
              IO.FS.withFile "literal.statement" .write fun handle => do
                handle.putStr (encodeStatement info)
                handle.flush
            """);
        Assert.Equal(
            Encoding.UTF8.GetBytes("statement-v1(uparams=[],type=ei(lt(131072:" + new string('é', 65536) + ")))"),
            File.ReadAllBytes(Path.Combine(temporary.Path, "literal.statement")));
    }

    [Fact]
    public void InspectorPreservesPrivateAndOpaqueValuesAndCanonicalNameOrder()
    {
        var report = InspectSingleModule("""
            private def hidden : String := "é"
            private theorem hiddenProof : True := True.intro
            def zz : String := hidden
            def a : Nat := 1
            opaque opaqueValue : String := "𝒪"
            """ + "\n");
        var hidden = Assert.Single(report.Declarations, static declaration => declaration.Name.EndsWith(".hidden", StringComparison.Ordinal));
        Assert.Equal("statement-v1(uparams=[],type=ec(ns(n0,6:String),[]),value=ei(lt(2:é)))", hidden.LoadTypeRepresentation());
        var opaque = Assert.Single(report.Declarations, static declaration => declaration.Name == "opaqueValue");
        Assert.Equal("opaque", opaque.Kind);
        Assert.Equal("statement-v1(uparams=[],type=ec(ns(n0,6:String),[]),value=ei(lt(4:𝒪)))", opaque.LoadTypeRepresentation());
        var proof = Assert.Single(report.Declarations, static declaration => declaration.Name.EndsWith(".hiddenProof", StringComparison.Ordinal));
        Assert.True(proof.IncludeInStatement);
        Assert.Equal("statement-v1(uparams=[],type=ec(ns(n0,4:True),[]))", proof.LoadTypeRepresentation());
        // The decimal length prefix sorts lexically: "11:" precedes "1:".
        Assert.Equal(["opaqueValue", "a", "zz"], report.Declarations
            .Where(static declaration => declaration.Name is "a" or "zz" or "opaqueValue")
            .Select(static declaration => declaration.Name));
    }

    private static void RunEncoderProbe(string directory, string probe)
    {
        var root = TestRepositoryLayout.FindRoot();
        File.Copy(Path.Combine(root, "lean-toolchain"), Path.Combine(directory, "lean-toolchain"));
        var source = File.ReadAllText(Path.Combine(root, "tools", "lean-inspector", "Inspector.lean"));
        File.WriteAllText(Path.Combine(directory, "EncodingProbe.lean"), source + "\n" + probe + "\n");
        var result = TestProcessRunner.Run("lean", ["EncodingProbe.lean"], directory,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
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
