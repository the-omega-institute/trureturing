using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TheoristFrontierContractTests
{
    public static TheoryData<string> HistoricalCandidates => new()
    {
        "finite-depth-metric",
        "prime-norm-irreducibility",
    };

    public static TheoryData<string, string> ContractMutations => new()
    {
        { "missing-contract", "theorist contract is required" },
        { "duplicate-contract", "duplicate theorist contracts are forbidden" },
        { "missing-closing-marker", "contract closing marker is missing" },
        { "malformed-json", "contract is not valid JSON" },
        { "unknown-field", "contract keys are not canonical" },
        { "missing-field", "contract keys are not canonical" },
        { "duplicate-field", "contract keys are not canonical" },
        { "wrong-schema", "contract schema must be" },
        { "blank-falsifier", "falsifier must be non-empty" },
        { "wrong-statement-gid", "exact_statement.gid must select the open declaration" },
        { "unknown-statement-field", "exact_statement keys are not canonical" },
        { "wrong-statement-address", "exact_statement.statement_sha256 does not match" },
        { "closed-statement", "exact statement must be open via sorryAx" },
        { "excluded-statement", "exact statement must be open via sorryAx" },
        { "second-open-statement", "contract must bind the module's only open declaration" },
        { "empty-motivations", "motivation_gids must be a non-empty sorted unique string array" },
        { "duplicate-motivations", "motivation_gids must be a non-empty sorted unique string array" },
        { "unsorted-motivations", "motivation_gids must be a non-empty sorted unique string array" },
        { "bad-motivation-gid", "motivation_gids[0] is not a canonical formal GID" },
        { "bad-motivation-plane", "motivation_gids[0] is not a canonical formal GID" },
        { "unfrozen-motivation", "motivation_gids[0] is not an active frozen member" },
        { "empty-search-receipts", "search_receipt_gids must be a non-empty sorted unique string array" },
        { "duplicate-search-receipts", "search_receipt_gids must be a non-empty sorted unique string array" },
        { "bad-search-plane", "search_receipt_gids[0] must be a Library GID" },
        { "missing-search-receipt", "search_receipt_gids[0] does not resolve" },
        { "empty-computation-receipts", "computation_receipt_gids must be a non-empty sorted unique string array" },
        { "duplicate-computation-receipts", "computation_receipt_gids must be a non-empty sorted unique string array" },
        { "bad-computation-plane", "computation_receipt_gids[0] must be an Evidence GID" },
        { "missing-computation-receipt", "computation_receipt_gids[0] does not resolve" },
        { "unknown-triage", "triage_class must be one of theorem, window, wall" },
        { "claimed-truth-status", "contract keys are not canonical" },
    };

    [Theory]
    [MemberData(nameof(HistoricalCandidates))]
    public void HistoricalTheorySelfGrowthCandidateCarriesAValidOpenContract(string fixtureName)
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(fixtureName);
        var context = fixture.Build();
        var mission = MissionFileLoader.Load(context.Current);
        Assert.True(
            mission is MissionLoadOutcome.Loaded,
            mission is MissionLoadOutcome.Invalid invalid ? invalid.Error.Message : "unknown MISSION outcome");

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(2),
            context).Diagnostics;

        Assert.Empty(diagnostics);
    }

    [Theory]
    [MemberData(nameof(HistoricalCandidates))]
    public void HistoricalTheorySelfGrowthCandidateWithoutContractIsRejected(string fixtureName)
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(fixtureName, includeContract: false);

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains("theorist contract is required", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(HistoricalCandidates))]
    public void HistoricalTheorySelfGrowthCandidateWithBrokenReferenceIsRejected(string fixtureName)
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(fixtureName);
        fixture.MutateTheoristTarget("unfrozen-motivation");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains("is not an active frozen member", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(ContractMutations))]
    public void EveryTheoristContractGuardFailsClosed(string mutation, string expectedPredicate)
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget("prime-norm-irreducibility");
        fixture.MutateTheoristTarget(mutation);

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains(expectedPredicate, diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingTypedOwnerIsUnknownRatherThanInferredFromTaskOrSorrySyntax()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            ownerKind: null,
            includeContract: false);

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains("Frontier owner is unknown", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void GovernanceOwnerDoesNotBecomeTheoryGenerationFromTaskOrSorrySyntax()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            ownerKind: "governance",
            includeContract: false);

        Assert.Empty(Evaluate(fixture));
    }

    [Fact]
    public void GovernanceOwnerCannotCarryATheoristContract()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            ownerKind: "governance");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains(
            "contract requires declaration-ready-mathematical-open ownership",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void MathematicalNotYetStatedOwnerCannotCarryAnElaboratedOpenDeclaration()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            ownerKind: "mathematical-not-yet-stated",
            includeContract: false,
            baselineOwnerKind: "mathematical-not-yet-stated");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains(
            "mathematical-not-yet-stated owner cannot carry an elaborated sorryAx declaration",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void BaselineWithoutTheNewContractRemainsLoadableUntilTypedOwnerTransition()
    {
        var grandfathered = new RuleFixture();
        grandfathered.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            includeContract: false,
            baselineOwnerKind: "declaration-ready-mathematical-open");
        Assert.Empty(Evaluate(grandfathered));

        var transitioned = new RuleFixture();
        transitioned.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            includeContract: false,
            baselineOwnerKind: "governance");
        var diagnostic = Assert.Single(Evaluate(transitioned));
        Assert.Contains("theorist contract is required", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void GrandfatheredModuleOptInIsValidatedInTheCandidateTree()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            baselineOwnerKind: "declaration-ready-mathematical-open");
        fixture.MutateTheoristTarget("wrong-statement-address");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains(
            "exact_statement.statement_sha256 does not match",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void MigratedContractCannotBeDeletedAfterItEntersTheBaseline()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            includeContract: false,
            baselineOwnerKind: "declaration-ready-mathematical-open",
            baselineIncludeContract: true);

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains("theorist contract is required", diagnostic.Message, StringComparison.Ordinal);
    }

    private static ImmutableArray<Diagnostic> Evaluate(RuleFixture fixture) =>
        RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(2), fixture.Build()).Diagnostics;
}

internal sealed partial class RuleFixture
{
    private const string TheoristTargetPath = "D5/X_Frontier/PrimeNormIrreducibility.lean";
    private const string SearchReceiptGid = "D5/L/Carrier/fixture2026contract";
    private const string SearchReceiptPath = "Library/Carrier/fixture2026contract.md";
    private const string ComputationReceiptGid = "D5/E/S0/Carrier/Probe.result--json";
    private const string ComputationReceiptPath = "Evidence/D5/S0/Carrier/Probe.result.json";

    private string currentTheoristPath = TheoristTargetPath;
    private string currentTheoristDeclaration = "prime_norm_irreducible";
    private string currentMotivationGid = "D5/S0/Carrier/Ring";
    private string currentMotivationPath = RingPath;

    internal void AddHistoricalTheoristTarget(
        string fixtureName,
        string? ownerKind = "declaration-ready-mathematical-open",
        bool includeContract = true,
        string? baselineOwnerKind = null,
        bool baselineIncludeContract = false)
    {
        var historical = fixtureName switch
        {
            "finite-depth-metric" => HistoricalFiniteDepthMetric,
            "prime-norm-irreducibility" => HistoricalPrimeNormIrreducibility,
            _ => throw new ArgumentOutOfRangeException(nameof(fixtureName)),
        };
        currentTheoristPath = historical.Path;
        currentTheoristDeclaration = historical.Declaration;
        currentMotivationGid = historical.MotivationGid;
        currentMotivationPath = historical.MotivationPath;

        var declaration = new LeanDeclaration(
            historical.QualifiedDeclaration,
            "theorem",
            historical.StatementMaterial,
            ["sorryAx"]);
        Reports[historical.Path] = Report(declarations: [declaration]);
        var statement = Assert.Single(CanonicalStatementWriter.DeclarationStatementIds(
            RepoPath.CreateKnown(historical.Path),
            Reports[historical.Path]));
        var contract = TheoristContract(
            historical.ModuleGid + "." + historical.Declaration,
            statement.StatementId.Value,
            historical.MotivationGid);
        Files[historical.Path] = historical.Source.Replace(
            "__THEORIST_CONTRACT__",
            includeContract ? contract : string.Empty,
            StringComparison.Ordinal);
        Changes.Add(historical.Path);

        AddTheoristSupportFiles();
        Files[MissionFileLoader.RelativePath] = Mission(ownerKind);

        if (baselineOwnerKind is not null)
        {
            Baseline[historical.Path] = historical.Source.Replace(
                "__THEORIST_CONTRACT__",
                baselineIncludeContract ? contract : string.Empty,
                StringComparison.Ordinal);
            ForkPoint[historical.Path] = Baseline[historical.Path];
            BaselineReports[historical.Path] = Reports[historical.Path];
            Baseline[MissionFileLoader.RelativePath] = Mission(baselineOwnerKind);
            ForkPoint[MissionFileLoader.RelativePath] = Baseline[MissionFileLoader.RelativePath];
            const string ticketPath = "D5/X_Frontier/MissionTickets.lean";
            Baseline[ticketPath] = Files[ticketPath];
            ForkPoint[ticketPath] = Files[ticketPath];
            BaselineReports[ticketPath] = Reports[ticketPath];
        }
    }

    internal void MutateTheoristTarget(string mutation)
    {
        switch (mutation)
        {
            case "missing-contract":
                RemoveContract();
                break;
            case "duplicate-contract":
                Files[currentTheoristPath] += ExtractContract() + "\n";
                break;
            case "missing-closing-marker":
                ReplaceContract("\n-/", "\n--/");
                break;
            case "malformed-json":
                ReplaceContract("\"falsifier\":", "\"falsifier\"");
                break;
            case "unknown-field":
                ReplaceContract("\"schema\":", "\"unexpected\":true,\"schema\":");
                break;
            case "missing-field":
                ReplaceContract("\"falsifier\":\"a finite counterexample fiber\",", string.Empty);
                break;
            case "duplicate-field":
                ReplaceContract(
                    "\"triage_class\":\"theorem\"",
                    "\"triage_class\":\"theorem\",\"triage_class\":\"theorem\"");
                break;
            case "wrong-schema":
                ReplaceContract(
                    "trureturing-theorist-frontier-v1",
                    "trureturing-theorist-frontier-v2");
                break;
            case "blank-falsifier":
                ReplaceContract("\"falsifier\":\"a finite counterexample fiber\"", "\"falsifier\":\" \"");
                break;
            case "wrong-statement-gid":
                ReplaceContract(
                    $".{currentTheoristDeclaration}\"",
                    ".different_declaration\"");
                break;
            case "unknown-statement-field":
                ReplaceContract(
                    "\"statement_sha256\":",
                    "\"unexpected\":true,\"statement_sha256\":");
                break;
            case "wrong-statement-address":
                ReplaceContract(
                    "\"statement_sha256\":\"sha256:",
                    "\"statement_sha256\":\"sha256:0");
                break;
            case "closed-statement":
                Reports[currentTheoristPath] = Report(declarations:
                [
                    new LeanDeclaration(
                        "D5.X_Frontier.PrimeNormIrreducibility.prime_norm_irreducible",
                        "theorem",
                        "statement-v1(prime-norm-irreducibility)",
                        []),
                ]);
                break;
            case "excluded-statement":
                Reports[currentTheoristPath] = Report(declarations:
                [
                    Reports[currentTheoristPath].Declarations[0] with
                    {
                        IncludeInStatement = false,
                    },
                ]);
                break;
            case "second-open-statement":
                Reports[currentTheoristPath] = Report(declarations:
                [
                    Reports[currentTheoristPath].Declarations[0],
                    new LeanDeclaration(
                        "D5.X_Frontier.PrimeNormIrreducibility.second_open",
                        "theorem",
                        "statement-v1(second-open)",
                        ["sorryAx"]),
                ]);
                break;
            case "empty-motivations":
                ReplaceContract($"[\"{currentMotivationGid}\"]", "[]");
                break;
            case "duplicate-motivations":
                ReplaceContract(
                    $"[\"{currentMotivationGid}\"]",
                    $"[\"{currentMotivationGid}\",\"{currentMotivationGid}\"]");
                break;
            case "unsorted-motivations":
                ReplaceContract(
                    $"[\"{currentMotivationGid}\"]",
                    $"[\"D5/S0/Carrier/ValuesBinding\",\"{currentMotivationGid}\"]");
                break;
            case "bad-motivation-gid":
                ReplaceContract(currentMotivationGid, "not-a-gid");
                break;
            case "bad-motivation-plane":
                ReplaceContract(currentMotivationGid, SearchReceiptGid);
                break;
            case "unfrozen-motivation":
                ReplaceContract(currentMotivationGid, "D5/S0/Carrier/ValuesBinding");
                break;
            case "empty-search-receipts":
                ReplaceContract($"[\"{SearchReceiptGid}\"]", "[]");
                break;
            case "duplicate-search-receipts":
                ReplaceContract(
                    $"[\"{SearchReceiptGid}\"]",
                    $"[\"{SearchReceiptGid}\",\"{SearchReceiptGid}\"]");
                break;
            case "bad-search-plane":
                ReplaceContract(SearchReceiptGid, "D5/S0/Carrier/Ring");
                break;
            case "missing-search-receipt":
                Files.Remove(SearchReceiptPath);
                break;
            case "empty-computation-receipts":
                ReplaceContract($"[\"{ComputationReceiptGid}\"]", "[]");
                break;
            case "duplicate-computation-receipts":
                ReplaceContract(
                    $"[\"{ComputationReceiptGid}\"]",
                    $"[\"{ComputationReceiptGid}\",\"{ComputationReceiptGid}\"]");
                break;
            case "bad-computation-plane":
                ReplaceContract(ComputationReceiptGid, SearchReceiptGid);
                break;
            case "missing-computation-receipt":
                Files.Remove(ComputationReceiptPath);
                break;
            case "unknown-triage":
                ReplaceContract("\"triage_class\":\"theorem\"", "\"triage_class\":\"interesting\"");
                break;
            case "claimed-truth-status":
                ReplaceContract("\"triage_class\":", "\"truth_status\":\"proved\",\"triage_class\":");
                break;
            default:
                throw new ArgumentOutOfRangeException(nameof(mutation));
        }
    }

    internal void AddElaboratedTheoristTarget(string source, LeanFileReport report)
    {
        const string module = "ElaborationProbe";
        const string ownerKind = "declaration-ready-mathematical-open";
        currentTheoristPath = $"D5/X_Frontier/{module}.lean";
        currentTheoristDeclaration = "generated_open";
        currentMotivationGid = "D5/S0/Carrier/Ring";
        currentMotivationPath = RingPath;
        Files[currentTheoristPath] = source;
        Reports[currentTheoristPath] = report;
        Changes.Add(currentTheoristPath);
        AddTheoristSupportFiles();
        Files[MissionFileLoader.RelativePath] = Mission(ownerKind);
    }

    private void AddTheoristSupportFiles()
    {
        Files[SearchReceiptPath] = "# Search receipt fixture\n";
        Files[ComputationReceiptPath] = "{}\n";
        AddFrozenMotivationMembership();

        const string ticketPath = "D5/X_Frontier/MissionTickets.lean";
        Files[ticketPath] = HeaderFor("D5/X_Frontier/MissionTickets", "E")
            + "\n"
            + string.Concat(Enumerable.Range(40, 4).Select(static number =>
                $"/-- TASK D5-T{number:0000}\n    Measurement contract remains open. -/\n"
                + $"def missionTicket{number:0000} : Unit := ()\n"));
        Reports[ticketPath] = Report();
    }

    private void AddFrozenMotivationMembership()
    {
        var genesis = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Genesis",
            JsonSerializer.SerializeToElement(new
            {
                generator_blob_oid = FrozenLedgerTestData.GitOid('1'),
                origin_commit_oid = FrozenLedgerTestData.GitOid('2'),
                origin_tree_oid = FrozenLedgerTestData.GitOid('3'),
                protocol_version = 1,
                rule_catalog_root = RuleCatalog.Default.RootSha256,
            }));
        const string frozenId =
            "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        var freeze = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Freeze",
            JsonSerializer.SerializeToElement(new
            {
                axiom_closure = Array.Empty<string>(),
                case_class = "active-frozen",
                case_id = "active-frozen/theorist-contract-fixture",
                declaration_statement_ids = Array.Empty<object>(),
                evaluation = "admission",
                expected = new
                {
                    allowed_dispositions = new[] { "admit" },
                    diagnostic_match = "none",
                    required_diagnostics = Array.Empty<object>(),
                },
                frozen_node_id = frozenId,
                input = new
                {
                    base_commit_oid = FrozenLedgerTestData.GitOid('4'),
                    base_tree_oid = FrozenLedgerTestData.GitOid('5'),
                    descriptor_blob_oid = FrozenLedgerTestData.GitOid('6'),
                    descriptor_selector = currentMotivationPath,
                    materializer = "repository-snapshot-v1",
                    supporting_blob_oids = Array.Empty<string>(),
                },
                input_fingerprint =
                    "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
                node_path = currentMotivationPath,
                prerequisite_frozen_node_ids = Array.Empty<string>(),
                semantic_receipt = frozenId,
                statement_id =
                    "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
                truth_state = "Closed",
                witness_id =
                    "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
            }));
        var entries = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [FrozenLedgerChangeClassifier.AcceptedRoot + "/fixture-genesis.json"] =
                Encoding.UTF8.GetString(genesis.Bytes.AsSpan()),
            [FrozenLedgerChangeClassifier.AcceptedRoot + "/fixture-freeze.json"] =
                Encoding.UTF8.GetString(freeze.Bytes.AsSpan()),
        };
        foreach (var (path, text) in entries)
        {
            Files[path] = text;
            Baseline[path] = text;
            ForkPoint[path] = text;
        }
    }

    private string Mission(string? targetOwnerKind)
    {
        var eligibility = new List<object>();
        if (targetOwnerKind is not null)
        {
            eligibility.Add(new
            {
                source_ref = currentTheoristPath[..^5],
                kind = targetOwnerKind,
            });
        }
        eligibility.Add(new
        {
            source_ref = "D5/X_Frontier/MissionTickets",
            kind = "governance",
        });
        var json = JsonSerializer.Serialize(new
        {
            schema = "trureturing-mission-v1",
            north_star = new
            {
                target = "two hearts",
                policy = "aspirational-not-direct",
            },
            value_order = new[]
            {
                "understanding-over-quantity",
                "honesty-over-speed",
                "negative-knowledge-equals-positive-results",
            },
            worth_vector = new
            {
                novelty = new { state = "open", case_id = "D5-T0040" },
                dependency_readiness = new { state = "open", case_id = "D5-T0041" },
                structural_realization = new { state = "open", case_id = "D5-T0042" },
                receipt_potential = new { state = "open", case_id = "D5-T0043" },
            },
            frontier_eligibility = eligibility
                .OrderBy(static item => JsonSerializer.Serialize(item), StringComparer.Ordinal),
            selection = new
            {
                order_kind = "bootstrap eligibility order",
                tie_break = "canonical candidate id",
            },
            prohibitions = new[]
            {
                "sorry-count optimization",
                "trivial-lemma accumulation",
                "citation chasing",
            },
        });
        return $"# Mission fixture\n\n```mission-v1\n{json}\n```\n";
    }

    private static string TheoristContract(
        string gid,
        string statementSha256,
        string motivationGid)
    {
        var json = JsonSerializer.Serialize(new
        {
            schema = "trureturing-theorist-frontier-v1",
            exact_statement = new
            {
                gid,
                statement_sha256 = statementSha256,
            },
            motivation_gids = new[] { motivationGid },
            falsifier = "a finite counterexample fiber",
            search_receipt_gids = new[] { SearchReceiptGid },
            computation_receipt_gids = new[] { ComputationReceiptGid },
            triage_class = "theorem",
        });
        return $"/- THEORIST_FRONTIER_CONTRACT_V1\n{json}\n-/";
    }

    private string ExtractContract()
    {
        var source = Files[currentTheoristPath];
        var start = source.IndexOf("/- THEORIST_FRONTIER_CONTRACT_V1", StringComparison.Ordinal);
        var end = source.IndexOf("\n-/", start, StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start);
        return source[start..(end + 3)];
    }

    private void RemoveContract() =>
        Files[currentTheoristPath] = Files[currentTheoristPath].Replace(
            ExtractContract(),
            string.Empty,
            StringComparison.Ordinal);

    private void ReplaceContract(string oldValue, string newValue)
    {
        var contract = ExtractContract();
        var replaced = contract.Replace(oldValue, newValue, StringComparison.Ordinal);
        Assert.NotEqual(contract, replaced);
        Files[currentTheoristPath] = Files[currentTheoristPath].Replace(
            contract,
            replaced,
            StringComparison.Ordinal);
    }

    private sealed record HistoricalTheoristFixture(
        string Path,
        string ModuleGid,
        string Declaration,
        string QualifiedDeclaration,
        string StatementMaterial,
        string MotivationGid,
        string MotivationPath,
        string Source);

    private static readonly HistoricalTheoristFixture HistoricalFiniteDepthMetric = new(
        "D5/X_Frontier/FiniteDepthMetric.lean",
        "D5/X_Frontier/FiniteDepthMetric",
        "finite_depth_metric_exists",
        "D5.X_Frontier.FiniteDepthMetric.finite_depth_metric_exists",
        "statement-v1(finite-depth-metric-exists)",
        "D5/S1/Depth/JointCoordinates",
        "D5/S1/Depth/JointCoordinates.lean",
        """
        /- GID: D5/X_Frontier/FiniteDepthMetric
           generality: I
           mirror-B: none(waiver:frontier-generation-task)
           mirror-E: none(waiver:theorem-not-numeric)
           anchors: []
           digest: Frontier obligation for a finite-depth fiber metric with separation and triangle laws. -/

        import D5.S1.Depth.JointCoordinates

        namespace D5.X_Frontier.FiniteDepthMetric

        open D5.S1.Depth

        __THEORIST_CONTRACT__

        /- Frontier-generation audit:
           selected GID: D5/S1/Depth/Finite.depthMetricL2Open
           stable key: frontier-gen:D5/S1/Depth/Finite.depthMetricL2Open
           derived Open node: D5/S1/Depth/Finite.lean
           dependency GIDs: D5/S1/Depth/JointCoordinates
           dependency states: Closed by the fresh TruthDagConstruction.DeriveState-backed coverage run
             over raw Lean report sha256:4d170596669817c7cbc667707c6a364e46ef6d72068e2f2e84cd86203cef143d
           worth vector: novelty=1, dependency-readiness=1, structural-payoff=1, receipt-potential=1
           runner-up: none after excluding existing X_Frontier task-ledger nodes as already-owned
           downstream issue title: Deliver ONE NEW D5 result: finite-depth fiber metric
           downstream issue body: Deliver ONE NEW D5 result as a single increment: prove
             D5.X_Frontier.FiniteDepthMetric.finite_depth_metric_exists in the Lean F-layer
             and mirror it in Blueprint. Provenance marker:
             frontier-gen:D5/S1/Depth/Finite.depthMetricL2Open.
         -/

        /-- Nat-valued metric laws for one finite-depth fiber. -/
        def FiberDistanceSpec {q0 : ℤ} {n : ℕ+}
            (d : DepthValue q0 n -> DepthValue q0 n -> ℕ) : Prop :=
          (∀ x y, d x y = 0 ↔ x = y) ∧
            (∀ x y, d x y = d y x) ∧
            (∀ x y z, d x z ≤ d x y + d y z)

        /-- TASK D5-T0022 | 难度:3 | 依赖:就绪✓(D5/S1/Depth/JointCoordinates) | 尝试:0
            提示:frontier-gen:D5/S1/Depth/Finite.depthMetricL2Open; prove fiber metric laws.
            尸检:none -/
        theorem finite_depth_metric_exists (q0 : ℤ) (n : ℕ+) :
            ∃ d : DepthValue q0 n -> DepthValue q0 n -> ℕ, FiberDistanceSpec d := by
          sorry

        end D5.X_Frontier.FiniteDepthMetric
        """ + "\n");

    private static readonly HistoricalTheoristFixture HistoricalPrimeNormIrreducibility = new(
        TheoristTargetPath,
        "D5/X_Frontier/PrimeNormIrreducibility",
        "prime_norm_irreducible",
        "D5.X_Frontier.PrimeNormIrreducibility.prime_norm_irreducible",
        "statement-v1(prime-norm-irreducibility)",
        "D5/S0/Carrier/Euclidean",
        "D5/S0/Carrier/Euclidean.lean",
        """
        /- GID: D5/X_Frontier/PrimeNormIrreducibility
           generality: I
           mirror-B: none(waiver:frontier-generation-task)
           mirror-E: none(waiver:theorem-not-numeric)
           anchors: []
           digest: Frontier obligation for prime-norm irreducibility in the golden integers. -/

        import D5.S0.Carrier.Euclidean
        import Mathlib.Data.Nat.Prime.Basic

        namespace D5.X_Frontier.PrimeNormIrreducibility

        open D5.S0.Carrier

        __THEORIST_CONTRACT__

        /- Frontier-generation audit:
           selected GID: D5/S0/Carrier/Euclidean.prime_norm_irreducible
           stable key: frontier-gen:D5/S0/Carrier/Euclidean.prime_norm_irreducible
           derived Open node: new X_Frontier obligation over the closed carrier Euclidean node
           dependency GIDs: D5/S0/Carrier/Euclidean
           dependency states: Closed by the fresh TruthDagConstruction.DeriveState-backed coverage run
             over raw Lean report sha256:a387b1e7e0499a7bdd0c9a767b3a64dfd1af9db5f07544fbe0a7e7f11afa9b28
           worth vector: novelty=1, dependency-readiness=1, structural-payoff=1, receipt-potential=1
           runner-up: D5/S1/Depth/Finite.depthMetricL2Open with vector
             novelty=0, dependency-readiness=1, structural-payoff=1, receipt-potential=1
             because frontier-gen:D5/S1/Depth/Finite.depthMetricL2Open already owns
             D5/X_Frontier/FiniteDepthMetric.
           downstream issue title: Deliver ONE NEW D5 result: prime-norm irreducibility for GoldenInt
           downstream issue body: Deliver ONE NEW D5 result as a single increment: prove
             D5.X_Frontier.PrimeNormIrreducibility.prime_norm_irreducible in the Lean
             F-layer and mirror it in Blueprint. Provenance marker:
             frontier-gen:D5/S0/Carrier/Euclidean.prime_norm_irreducible.
         -/

        /-- TASK D5-T0023 | 难度:2 | 依赖:就绪✓(D5/S0/Carrier/Euclidean) | 尝试:0
            提示:frontier-gen:D5/S0/Carrier/Euclidean.prime_norm_irreducible; use
            norm_mul, Int.natAbs_mul, and Nat.Prime.eq_one_or_self_of_dvd to rule out
            nonunit factorizations.
            尸检:none -/
        theorem prime_norm_irreducible {x : GoldenInt}
            (hprime : (norm x).natAbs.Prime) : Irreducible x := by
          sorry

        end D5.X_Frontier.PrimeNormIrreducibility
        """ + "\n");
}
