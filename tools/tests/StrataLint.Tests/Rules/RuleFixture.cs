using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed partial class RuleFixture
{
    internal const string FixtureDigestionSourcePath = "docs/GOVERNANCE.md";
    internal const string FixtureDigestionSource = "x";
    internal const string FixtureAtomId = "fixture-atom";
    internal const string FixtureCasReference =
        "sha256:2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881";
    internal const string FixtureCasPath =
        "Meta/Digestion/atoms/sha256/2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881";
    internal const string FixtureBackfillSourcePath =
        "Meta/Digestion/backfill/fixture-source/source.toml";
    internal const string FixtureBackfillAtomPath =
        "Meta/Digestion/backfill/fixture-source/partial-closed/fixture-atom.yaml";
    internal const string FixtureBackfill = """
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: fixture-source
            path: docs/GOVERNANCE.md
            atomizer: none
            entries:
              - atom_id: fixture-atom
                boundary:
                  ast_path: manual/fixture
                  start_byte: 0
                  end_byte: 1
                fingerprints:
                  raw_sha256: sha256:2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881
                  normalized_sha256: sha256:2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881
                cas_ref: sha256:2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881
                coverage_gids:
                  - D5/S0/Carrier/BackfillTarget
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: []
                  chain_atoms: []
                  tail_authorization: null
                status:
                  migration: partial
                  truth: closed
        ticket_index:
          - case_id: D5-T0001
            gid: D5/X_Frontier/HeartsDraft
          - case_id: D5-T0002
            gid: D5/X_Frontier/StrataLintLeanEnvironment
          - case_id: D5-T0003
            gid: D5/X_Frontier/ValuesProducer
          - case_id: D5-T0004
            gid: D5/X_Frontier/SplitTool
          - case_id: D5-T0005
            gid: D5/X_Frontier/PaperGenerator
          - case_id: D5-T0006
            gid: D5/X_Frontier/D5P001
          - case_id: D5-T0007
            gid: D5/X_Frontier/RequiredChecks
          - case_id: D5-T0008
            gid: D5/X_Frontier/GoldenUnitsUFD
          - case_id: D5-T0009
            gid: D5/X_Frontier/FutureInstances
          - case_id: D5-T0010
            gid: D5/X_Frontier/ToolchainUpgrade
          - case_id: D5-T0011
            gid: D5/X_Frontier/GovernanceDeferrals
          - case_id: D5-T0012
            gid: D5/X_Frontier/GovernanceDeferrals
          - case_id: D5-T0013
            gid: D5/X_Frontier/GovernanceDeferrals
          - case_id: D5-T0014
            gid: D5/X_Frontier/GovernanceDeferrals
          - case_id: D5-T0015
            gid: D5/X_Frontier/GovernanceDeferrals
          - case_id: D5-T0016
            gid: D5/X_Frontier/GovernanceDeferrals
          - case_id: D5-T0017
            gid: D5/X_Frontier/RequiredChecks
          - case_id: D5-T0018
            gid: D5/X_Frontier/HeartsDraft
        """ + "\n";
    internal const string FixtureBackfillSource = """
        source_id = "fixture-source"
        path = "docs/GOVERNANCE.md"
        atomizer = "none"
        """ + "\n";
    internal const string FixtureBackfillAtom = """
        boundary:
          ast_path: manual/fixture
          start_byte: 0
          end_byte: 1
        fingerprints:
          raw_sha256: sha256:2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881
          normalized_sha256: sha256:2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881
        cas_ref: sha256:2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881
        coverage_gids:
          - D5/S0/Carrier/BackfillTarget
        receipts:
          coverage: []
          scribe: []
          unresolved_subitems: []
          chain_atoms: []
          tail_authorization: null
        """ + "\n";
    internal const string FixtureTicketIndex = """
        D5-T0001 = "D5/X_Frontier/HeartsDraft"
        D5-T0002 = "D5/X_Frontier/StrataLintLeanEnvironment"
        D5-T0003 = "D5/X_Frontier/ValuesProducer"
        D5-T0004 = "D5/X_Frontier/SplitTool"
        D5-T0005 = "D5/X_Frontier/PaperGenerator"
        D5-T0006 = "D5/X_Frontier/D5P001"
        D5-T0007 = "D5/X_Frontier/RequiredChecks"
        D5-T0008 = "D5/X_Frontier/GoldenUnitsUFD"
        D5-T0009 = "D5/X_Frontier/FutureInstances"
        D5-T0010 = "D5/X_Frontier/ToolchainUpgrade"
        D5-T0011 = "D5/X_Frontier/GovernanceDeferrals"
        D5-T0012 = "D5/X_Frontier/GovernanceDeferrals"
        D5-T0013 = "D5/X_Frontier/GovernanceDeferrals"
        D5-T0014 = "D5/X_Frontier/GovernanceDeferrals"
        D5-T0015 = "D5/X_Frontier/GovernanceDeferrals"
        D5-T0016 = "D5/X_Frontier/GovernanceDeferrals"
        D5-T0017 = "D5/X_Frontier/RequiredChecks"
        D5-T0018 = "D5/X_Frontier/HeartsDraft"
        """ + "\n";

    internal const string RingPath = "D5/S0/Carrier/Ring.lean";
    internal const string ValuesBindingPath = "D5/S0/Carrier/ValuesBinding.lean";
    internal const string BlueprintPath = "Blueprint/D5/S0/Carrier/Ring.md";
    internal const string BlueprintSourcePath = "Blueprint/D5/S0/Carrier/Ring.scribe.cs";
    internal const string NotationPath = "D5/S0/Conventions/Notation.lean";
    internal const string AssumptionDebtPath = "D5/X_Assumptions/AxiomDebt.lean";
    internal const string HeartsPath = "D5/X_Frontier/Hearts.lean";
    internal const string HeartsDraftPath = "D5/X_Frontier/HeartsDraft.lean";
    internal const string ThreeDistancePath = "D5/S1/Phase/ThreeDistance.lean";
    internal const string TowerManifestPath = RepositoryRules.TowerManifestPath;
    internal const string ValuesProjectionPath = RepositoryPathPolicy.ValuesProjectionPath;
    internal const string WorkflowPath = RepositoryPathPolicy.WorkflowPath;
    internal const string HarnessGatePath = RepositoryPathPolicy.HarnessGatePath;
    internal const string SyntheticProtectedPath =
        "tools/StrataLint.Engine/SyntheticProtected.cs";

    private const string Header = """
        /- GID: D5/S0/Carrier/Ring
           generality: G
           mirror-B: D5/B/S0/Carrier/Ring
           mirror-E: none(waiver:pure-definition)
           anchors: []
           digest: StrataLint fixture. -/
        """;

    internal RuleFixture()
    {
        var repositoryRoot = TestRepositoryLayout.FindRoot();
        Files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Meta/domains.yaml"] = TestRegistry.Domains,
            [FixtureBackfillSourcePath] = FixtureBackfillSource,
            [FixtureBackfillAtomPath] = FixtureBackfillAtom,
            [BackfillInventoryLoader.TicketIndexPath] = FixtureTicketIndex,
            [TheoryAtomizerDataLoader.DataPath] = File.ReadAllText(
                Path.Combine(repositoryRoot, TheoryAtomizerDataLoader.DataPath), Encoding.UTF8),
            ["Meta/registry.yaml"] = TestRegistry.Canonical,
            ["Library/queries.yaml"] = "schema_version: 1\nqueries: []\n",
            [RingPath] = Header + "def goldenRing : Nat := 0\n",
            [ValuesBindingPath] = HeaderFor("D5/S0/Carrier/ValuesBinding", "I")
                + "def fixtureValue : Nat := 0\n",
            [BlueprintPath] = "# Golden ring\n",
            [BlueprintSourcePath] = "// synthetic Scribe definition\n",
            [FixtureDigestionSourcePath] = FixtureDigestionSource,
            [FixtureCasPath] = FixtureDigestionSource,
        };
        Baseline = new Dictionary<string, string>(Files, StringComparer.Ordinal);
        Reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [RingPath] = Report(
                declarations: new[] { new LeanDeclaration("goldenRing", "def", "Nat", ImmutableArray<string>.Empty) }),
            [ValuesBindingPath] = Report(
                declarations:
                [
                    new LeanDeclaration(
                        "fixtureValue",
                        "def",
                        "Nat",
                        ImmutableArray.Create("Classical.choice", "Quot.sound", "propext")),
                ]),
        };
        var bindingPath = RepoPath.CreateKnown(ValuesBindingPath);
        var statement = Assert.Single(CanonicalStatementWriter.DeclarationStatementIds(
            bindingPath,
            Reports[ValuesBindingPath]));
        Files[ValuesKernelBindingValidator.RelativePath] = $"""
            schema_version = 1

            [[constants]]
            id = "D5/test"
            lean_gid = "D5/S0/Carrier/ValuesBinding.fixtureValue"
            lean_statement_sha256 = "{statement.StatementId.Value["sha256:".Length..]}"
            """ + "\n";
        BaselineReports = new Dictionary<string, LeanFileReport>(Reports, StringComparer.Ordinal);
        Baseline[ValuesKernelBindingValidator.RelativePath] = Files[ValuesKernelBindingValidator.RelativePath];
        ForkPoint = new Dictionary<string, string>(Baseline, StringComparer.Ordinal);
        Changes = new List<string> { BlueprintPath };
    }

    internal Dictionary<string, string> Files { get; }

    internal Dictionary<string, string> Baseline { get; }

    internal Dictionary<string, string> ForkPoint { get; }

    internal Dictionary<string, LeanFileReport> Reports { get; }

    internal Dictionary<string, LeanFileReport> BaselineReports { get; }

    internal List<string> Changes { get; }

    internal void UseLegacyBackfill()
    {
        foreach (var files in new[] { Files, Baseline })
        {
            RemoveDigestionLedger(files);
            files[BackfillInventoryLoader.RelativePath] = FixtureBackfill;
        }
    }

    internal void UseSyntheticDirectoryBackfill(string ticketIndex)
    {
        RemoveDigestionLedger(Files);
        Files[$"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml"] =
            $"source_id = \"delta-v0.1\"\npath = \"{FixtureDigestionSourcePath}\"\natomizer = \"none\"\n";
        Files[$"{BackfillInventoryLoader.RootPath}delta-v0.1/residual-open/delta-atom.yaml"] = """
            boundary:
              ast_path: manual/delta
              start_byte: 0
              end_byte: 1
            fingerprints:
              raw_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000
              normalized_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000
            cas_ref: sha256:0000000000000000000000000000000000000000000000000000000000000000
            coverage_gids: []
            receipts:
              coverage: []
              scribe: []
              unresolved_subitems: []
              chain_atoms: []
              tail_authorization: null
            """ + "\n";
        Files[BackfillInventoryLoader.TicketIndexPath] = ticketIndex;
    }

    internal void UseValidDirectoryBackfill()
    {
        var document = BackfillInventoryLoader.Load(Decode(Files));
        var ticketIndex = string.Concat(document.RequireTickets().Select(static ticket =>
            $"{ticket.CaseId} = \"{ticket.Gid}\"\n"));
        const string sourcePath = "delta-v0.1/source.toml";
        const string atomPath = "delta-v0.1/partial-closed/delta-atom.yaml";
        var source = $"source_id = \"delta-v0.1\"\npath = \"{FixtureDigestionSourcePath}\"\natomizer = \"none\"\n";
        var atom = $"""
            boundary:
              ast_path: manual/fixture
              start_byte: 0
              end_byte: 1
            fingerprints:
              raw_sha256: {FixtureCasReference}
              normalized_sha256: {FixtureCasReference}
            cas_ref: {FixtureCasReference}
            coverage_gids:
              - D5/S0/Carrier/BackfillTarget
            receipts:
              coverage: []
              scribe: []
              unresolved_subitems: []
              chain_atoms: []
              tail_authorization: null
            """ + "\n";

        foreach (var files in new[] { Files, Baseline, ForkPoint })
        {
            RemoveDigestionLedger(files);
            files[BackfillInventoryLoader.RootPath + sourcePath] = source;
            files[BackfillInventoryLoader.RootPath + atomPath] = atom;
            files[BackfillInventoryLoader.TicketIndexPath] = ticketIndex;
        }
    }

    internal void AddSyntheticUnregisteredFrontierTask(string caseId)
    {
        var path = $"D5/X_Frontier/Synthetic{caseId}.lean";
        Files[path] = $"/-- TASK {caseId} | fixture -/\ndef synthetic{caseId.Replace("-", "", StringComparison.Ordinal)} : Unit := ()\n";
        Reports[path] = Report(declarations:
            [new LeanDeclaration($"synthetic{caseId.Replace("-", "", StringComparison.Ordinal)}", "def", "Unit", [])]);
    }

    internal void Apply(string mutation)
    {
        switch (mutation)
        {
            case "upward-import": AddUpwardImport(); break;
            case "sorry": SetRingDeclaration("unfinished", "theorem", "sorryAx"); break;
            case "file-capacity": Files[RingPath] += string.Concat(Enumerable.Repeat("-- pad\n", 801)); break;
            case "mirror": Files.Remove(BlueprintPath); break;
            case "chronicle": RewriteChronicle(); break;
            case "badge": Files[BlueprintPath] = "status: proven\n"; break;
            case "heart": ChangeHeartSignature(); break;
            case "generality": AddInstanceImport(); break;
            case "domain": AddUnknownDomain(); break;
            case "header": Files[RingPath] = "def noHeader : Nat := 0\n"; break;
            case "formula": AddIllegalFormula(); break;
            case "backfill": Files[FixtureBackfillSourcePath] = Files[FixtureBackfillSourcePath].Replace("source_id = \"fixture-source\"", "source_id = [\"fixture-source\"]", StringComparison.Ordinal); break;
            case "query": Files["Library/queries.yaml"] = "schema_version: 1\nqueries:\n  - id: D5-Q0099\n    target_gid: D5/S0/Carrier/Ring\n"; break;
            case "values": Files["Evidence/D5/values.result.json"] = "{\"D5/sample\": {\"status\": \"verified\"}}\n"; break;
            case "anomaly": Files["Evidence/D5/S0/Carrier/Result.run.json"] = "{\"anomaly\": \"fixture drift\"}\n"; break;
            case "axiom": SetRingDeclaration("invented", "axiom", "invented"); break;
            case "future": AddFutureTheory(); break;
            default: throw new ArgumentOutOfRangeException(nameof(mutation));
        }
    }

    internal RuleEvaluationContext Build(
        ValidatedPolicy? suppliedPolicy = null,
        VerifiedScribeEmissions? verifiedScribeEmissions = null) =>
        Build(RawChangeSet.Create(Changes), suppliedPolicy, verifiedScribeEmissions);

    internal RuleEvaluationContext Build(
        RawChangeSet changes,
        ValidatedPolicy? suppliedPolicy = null,
        VerifiedScribeEmissions? verifiedScribeEmissions = null)
    {
        var current = Decode(Files);
        var baseline = Decode(Baseline);
        var forkPoint = Decode(ForkPoint);
        var policy = suppliedPolicy;
        if (policy is null)
        {
            var policyOutcome = RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains));
            policy = RegistryLoadAssert.Accepted(policyOutcome).Policy;
        }
        var lean = AcceptLean(current, Reports);
        var bootstrap = BootstrapGate.Evaluate(changes);
        var meta = bootstrap switch
        {
            BootstrapOutcome.Clear clear => MetaEvaluationProfile.ForClear(clear.Capability),
            BootstrapOutcome.ProtectedSurfaceVerificationRequired protectedSurface =>
                MetaEvaluationProfile.ForProtectedSurface(protectedSurface.ChangeSet),
            BootstrapOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
            _ => throw new InvalidOperationException("unknown bootstrap outcome"),
        };
        return RuleEvaluationContext.Create(
            current,
            baseline,
            policy,
            lean,
            changes,
            meta,
            verifiedScribeEmissions,
            forkPoint);
    }

    internal RuleEvaluationContext BuildForRuleCompatibility()
    {
        var current = Decode(Files);
        var baseline = Decode(Baseline);
        var forkPoint = Decode(ForkPoint);
        var policyOutcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes(TestRegistry.Domains));
        var policy = RegistryLoadAssert.Accepted(policyOutcome).Policy;
        var bootstrap = BootstrapGate.Evaluate(RawChangeSet.Create(Changes));
        var meta = Assert.IsType<BootstrapOutcome.Clear>(bootstrap).Capability;
        return RuleEvaluationContext.Create(
            current,
            baseline,
            policy,
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(Reports)),
            RawChangeSet.Create(Changes),
            meta,
            forkPoint: forkPoint);
    }

    internal RuleEvaluationContext BuildForProtectedRuleCompatibility()
    {
        var current = Decode(Files);
        var baseline = Decode(Baseline);
        var forkPoint = Decode(ForkPoint);
        var policyOutcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes(TestRegistry.Domains));
        var policy = RegistryLoadAssert.Accepted(policyOutcome).Policy;
        var bootstrap = BootstrapGate.Evaluate(RawChangeSet.Create(Changes));
        var meta = Assert.IsType<BootstrapOutcome.ProtectedSurfaceVerificationRequired>(bootstrap).ChangeSet;
        return RuleEvaluationContext.Create(
            current,
            baseline,
            policy,
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(Reports)),
            RawChangeSet.Create(Changes),
            MetaEvaluationProfile.ForProtectedSurface(meta),
            forkPoint: forkPoint);
    }

    internal void AddUpwardImport()
    {
        const string highPath = "D5/S1/Upper/High.lean";
        Files[highPath] = HeaderFor("D5/S1/Upper/High", "G") + "def high : Nat := 1\n";
        Reports[highPath] = Report(declarations: new[]
        {
            new LeanDeclaration("high", "def", "Nat", ImmutableArray<string>.Empty),
        });
        Reports[RingPath] = Report(imports: new[] { "D5.S1.Upper.High" });
    }

    // A stratum content file carrying a classical theorem via a registered
    // assumption: importing the X_Assumptions foundation is allowed (SL-001).
    internal void AddAssumptionImport()
    {
        Files[AssumptionDebtPath] = HeaderFor("D5/X_Assumptions/AxiomDebt", "G") + "axiom classicalDebt : True\n";
        Reports[AssumptionDebtPath] = Report(declarations: new[]
        {
            new LeanDeclaration("classicalDebt", "axiom", "True", ImmutableArray.Create("classicalDebt")),
        });
        Reports[RingPath] = Report(imports: new[] { "D5.X_Assumptions.AxiomDebt" });
    }

    // The X_Assumptions foundation may not import content: keeping it a sink
    // makes the import partial order acyclic (SL-001).
    internal void AddAssumptionImportingStratum()
    {
        Files[AssumptionDebtPath] = HeaderFor("D5/X_Assumptions/AxiomDebt", "G") + "axiom classicalDebt : True\n";
        Reports[AssumptionDebtPath] = Report(imports: new[] { "D5.S0.Carrier.Ring" });
    }

    internal void SetRingDeclaration(string name, string kind, string axiom)
    {
        Reports[RingPath] = Report(declarations: new[]
        {
            new LeanDeclaration(name, kind, "False", ImmutableArray.Create(axiom)),
        });
    }

    internal void RewriteChronicle()
    {
        const string path = "Chronicle/2026/07/10-old.md";
        Baseline[path] = "old\n";
        ForkPoint[path] = "old\n";
        Files[path] = "changed\n";
    }

    internal void ChangeHeartSignature()
    {
        const string path = HeartsPath;
        // 新 SL-008 只看 changeset 状态:红 fixture 必须把 Hearts 标记为 Modified。
        Changes.Add(path);
        var baselineText = HeaderFor("D5/X_Frontier/Hearts", "E") + "theorem heart : True := by sorry\n";
        Baseline[path] = baselineText;
        ForkPoint[path] = baselineText;
        Files[path] = HeaderFor("D5/X_Frontier/Hearts", "E") + "theorem heart : False := by sorry\n";
        BaselineReports[path] = Report(declarations: new[]
        {
            new LeanDeclaration("heart", "theorem", "True", ImmutableArray.Create("sorryAx")),
        });
        Reports[path] = Report(declarations: new[]
        {
            new LeanDeclaration("heart", "theorem", "False", ImmutableArray.Create("sorryAx")),
        });
    }

    internal void AddInstanceImport()
    {
        const string path = NotationPath;
        Files[path] = HeaderFor("D5/S0/Conventions/Notation", "I") + "def instanceFact : Nat := 1\n";
        Reports[path] = Report(declarations: new[]
        {
            new LeanDeclaration("instanceFact", "def", "Nat", ImmutableArray<string>.Empty),
        });
        Reports[RingPath] = Report(imports: new[] { "D5.S0.Conventions.Notation" });
    }

    internal void AddUnknownDomain()
    {
        const string path = "D5/S0/Unknown/Bad.lean";
        Files[path] = HeaderFor("D5/S0/Unknown/Bad", "G") + "def bad : Nat := 0\n";
        Reports[path] = Report();
    }

    internal void AddIllegalFormula() =>
        Files["Evidence/D5/S0/Carrier/Formula.check.json"] = "{\"formula\": \"sqrt@5\", \"refs\": {}}\n";

    internal void AddFutureTheory() =>
        Files["D8/S0/Carrier/Ring.lean"] = "future\n";

    internal void AddTask(string path, string gid, string code, string? history = null)
    {
        Files[path] = HeaderFor(gid, "E")
            + $"/-- TASK {code}\n"
            + "    Fixture task."
            + (history is null ? "" : $"\n    {history}")
            + " -/\n"
            + "def fixtureTask : Unit := ()\n";
        Reports[path] = Report();
    }

    internal void AddBackfillTargets()
    {
        var inventory = BackfillInventoryLoader.Load(Decode(Files));
        var ticketsByGid = inventory.RequireTickets()
            .GroupBy(static ticket => ticket.Gid, StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => group.Select(static ticket => ticket.CaseId).ToArray(),
                StringComparer.Ordinal);
        foreach (var gidText in inventory.RequireReferencedGids())
        {
            if (!Gid.TryParse(gidText, out var gid))
            {
                throw new FormatException($"canonical BACKFILL contains invalid GID {gidText}");
            }

            var path = gid.Path.Value;
            if (!path.EndsWith(".lean", StringComparison.Ordinal))
            {
                if (path == ValuesProjectionPath)
                {
                    AddValuesProjection();
                }

                continue;
            }

            if (!Files.TryGetValue(path, out var text))
            {
                text = HeaderFor(gidText, path.Contains("/S0/", StringComparison.Ordinal) ? "G" : "E")
                    + (path.Contains("/X_Frontier/", StringComparison.Ordinal) ? "-- D5-T9999\n" : string.Empty)
                    + "def protectedTargetFixture : Unit := ()\n";
                Reports[path] = Report();
                if (path == ThreeDistancePath)
                {
                    const string debtGid = "D5/X_Assumptions/AxiomDebt";
                    const string debtModule = "D5.X_Assumptions.AxiomDebt";
                    const string debtAxiom = "D5.X_Assumptions.AxiomDebt.three_gap_classic";
                    Files[AssumptionDebtPath] = HeaderFor(debtGid, "G")
                        + "axiom three_gap_classic : True\n";
                    Reports[AssumptionDebtPath] = Report(declarations:
                    [
                        new LeanDeclaration(
                            debtAxiom,
                            "axiom",
                            "True",
                            [debtAxiom]),
                    ]);
                    text = HeaderFor(gidText, "E")
                        + $"import {debtModule}\n\n"
                        + $"-- {debtGid}\n"
                        + "theorem three_gap : True := by trivial\n";
                    Reports[path] = Report(
                        imports: [debtModule],
                        declarations:
                    [
                        new LeanDeclaration(
                            "three_gap",
                            "theorem",
                            "True",
                            [debtAxiom]),
                    ]);
                }
            }

            if (ticketsByGid.TryGetValue(gidText, out var cases))
            {
                text += string.Concat(cases.Where(caseId =>
                        !text.Contains($"TASK {caseId}", StringComparison.Ordinal))
                    .Select(static caseId =>
                    $"/-- TASK {caseId}\n"
                    + "    Fixture task. -/\n"
                    + $"def fixtureTask{caseId[4..]} : Unit := ()\n"));
            }

            Files[path] = text;
            if (path == HeartsPath)
            {
                Baseline[path] = text;
                ForkPoint[path] = text;
                BaselineReports[path] = Reports[path];
            }
        }
    }

    internal void AddValuesProjection()
    {
        var repositoryRoot = TestRepositoryLayout.FindRoot();
        Files[ValuesProjectionPath] = File.ReadAllText(
            Path.Combine(repositoryRoot, ValuesProjectionPath),
            Encoding.UTF8);
    }

    internal void AddNormalizedBackfillTicketTarget()
    {
        const string gid = "D5/X_Frontier/BackfillTasks";
        var path = gid + ".lean";
        Files[path] = HeaderFor(gid, "E")
            + string.Concat(Enumerable.Range(1, 18).Select(static number =>
                $"/-- TASK D5-T{number:0000}\n"
                + "    Fixture task. -/\n"
                + $"def fixtureTask{number:0000} : Unit := ()\n"));
        Reports[path] = Report();
    }

    private static RepositorySnapshot Decode(IReadOnlyDictionary<string, string> files)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static void RemoveDigestionLedger(IDictionary<string, string> files)
    {
        files.Remove(BackfillInventoryLoader.RelativePath);
        foreach (var path in files.Keys
                     .Where(BackfillInventoryLoader.IsCanonicalPath)
                     .ToArray())
        {
            files.Remove(path);
        }
    }

    private static AcceptedLeanClosure AcceptLean(
        RepositorySnapshot snapshot,
        IReadOnlyDictionary<string, LeanFileReport> reports)
    {
        var report = LeanAxiomReport.Create(reports);
        var outcome = LeanClosureValidator.Validate(snapshot, report);
        return Assert.IsType<LeanValidationOutcome.Accepted>(outcome).Capability;
    }

    private static LeanFileReport Report(
        IEnumerable<string>? imports = null,
        IEnumerable<LeanDeclaration>? declarations = null) =>
        new(
            (imports ?? Array.Empty<string>()).ToImmutableArray(),
            (declarations ?? Array.Empty<LeanDeclaration>()).ToImmutableArray());

    private static string HeaderFor(string gid, string generality) => $"""
        /- GID: {gid}
           generality: {generality}
           mirror-B: none(waiver:test-fixture)
           mirror-E: none(waiver:test-fixture)
           anchors: []
           digest: StrataLint fixture. -/
        """;

}
