using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed partial class RuleFixture
{
    private const string TheoristTargetPath = "D5/X_Frontier/PrimeNormIrreducibility.lean";
    private const string AuditBlockMarker = "/- Frontier-generation audit:";
    private const string SearchReceiptGid = "D5/L/Carrier/fixture2026contract";
    private const string SearchReceiptPath = "Library/Carrier/fixture2026contract.md";
    private const string ComputationReceiptGid = "D5/E/S0/Carrier/Probe.result--json";
    private const string ComputationReceiptPath = "Evidence/D5/S0/Carrier/Probe.result.json";
    private const string BackfillTargetPath = "D5/S0/Carrier/BackfillTarget.lean";
    private const string RetiredDeliveryGid = "D5/S0/Carrier/Euclidean.golden_division";
    private const string ParentV1StatementAddress =
        "sha256:a20f6bafe7333a1146e6de8e1ff1c70b6167907eee609faee07c45650b7595f3";
    private const string ParentV1Contract =
        "/- THEORIST_FRONTIER_CONTRACT_V1\n"
        + "{\"schema\":\"trureturing-theorist-frontier-v1\",\"exact_statement\":{\"gid\":\"D5/X_Frontier/PrimeNormIrreducibility.prime_norm_irreducible\",\"statement_sha256\":\""
        + ParentV1StatementAddress
        + "\"},\"motivation_gids\":[\"D5/S0/Carrier/Euclidean\"],\"falsifier\":\"a finite counterexample fiber\",\"search_receipt_gids\":[\"D5/L/Carrier/fixture2026contract\"],\"computation_receipt_gids\":[\"D5/E/S0/Carrier/Probe.result--json\"],\"triage_class\":\"theorem\"}\n-/";

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
        var contract = TheoristContract(
            historical.ModuleGid + "." + historical.Declaration,
            CanonicalStatementWriter.StatementTypeAddress(declaration.TypeRepresentation),
            historical.MotivationGid);
        Files[historical.Path] = includeContract
            ? InsertContract(historical.Source, contract)
            : historical.Source;
        Changes.Add(historical.Path);

        AddTheoristSupportFiles();
        Files[MissionFileLoader.RelativePath] = Mission(ownerKind);

        if (baselineOwnerKind is not null)
        {
            Baseline[historical.Path] = baselineIncludeContract
                ? InsertContract(historical.Source, contract)
                : historical.Source;
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

    internal void CorruptMission() =>
        Files[MissionFileLoader.RelativePath] = "# Mission fixture without a mission-v1 fence\n";

    internal void CorruptBaselineMission() =>
        Baseline[MissionFileLoader.RelativePath] =
            "# Baseline Mission fixture without a mission-v1 fence\n";

    internal void DeleteTheoristTargetAndOwner()
    {
        Files.Remove(currentTheoristPath);
        Reports.Remove(currentTheoristPath);
        Files[MissionFileLoader.RelativePath] = Mission(null);
    }

    internal void DeleteTheoristTargetWithOwner(string ownerKind)
    {
        Files.Remove(currentTheoristPath);
        Reports.Remove(currentTheoristPath);
        Files[MissionFileLoader.RelativePath] = Mission(ownerKind);
    }

    internal void RetireTheoristTarget(string deliveryGid = RetiredDeliveryGid)
    {
        RetireTheoristTargetWithDeliveries(deliveryGid);
    }

    internal void RetireTheoristTargetWithDeliveries(params string[] deliveryGids)
    {
        Files.Remove(currentTheoristPath);
        Reports.Remove(currentTheoristPath);
        Files[MissionFileLoader.RelativePath] = Mission("retired", deliveryGids);
    }

    internal void RemoveRetiredBaselineContract()
    {
        var source = Baseline[currentTheoristPath];
        var start = source.IndexOf("/- THEORIST_FRONTIER_CONTRACT_V2", StringComparison.Ordinal);
        var end = source.IndexOf("\n-/", start, StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start);
        Baseline[currentTheoristPath] = source.Remove(start, end + 3 - start);
    }

    internal void MalformedRetiredBaselineContract()
    {
        var source = Baseline[currentTheoristPath];
        var malformed = source.Replace("\"falsifier\":", "\"falsifier\"", StringComparison.Ordinal);
        Assert.NotEqual(source, malformed);
        Baseline[currentTheoristPath] = malformed;
    }

    internal void ReplaceRetiredBaselineWithLiteralParentV1Contract()
    {
        var parentStatement = Assert.Single(CanonicalStatementWriter.DeclarationStatementIds(
            RepoPath.CreateKnown(currentTheoristPath),
            BaselineReports[currentTheoristPath]));
        Assert.Equal(ParentV1StatementAddress, parentStatement.StatementId.Value);

        ReplaceRetiredBaselineContract(ParentV1Contract);
    }

    internal void ReplaceCurrentContractWithLiteralParentV1Contract()
    {
        var parentStatement = Assert.Single(CanonicalStatementWriter.DeclarationStatementIds(
            RepoPath.CreateKnown(currentTheoristPath),
            Reports[currentTheoristPath]));
        Assert.Equal(ParentV1StatementAddress, parentStatement.StatementId.Value);

        var source = Files[currentTheoristPath];
        var start = source.IndexOf("/- THEORIST_FRONTIER_CONTRACT_", StringComparison.Ordinal);
        var end = source.IndexOf("\n-/", start, StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start);
        Files[currentTheoristPath] = source[..start]
            + ParentV1Contract
            + source[(end + 3)..];
    }

    internal void AddMismatchingFrozenRetiredDelivery()
    {
        Reports[currentMotivationPath] = Report(
            declarations: Reports[currentMotivationPath].Declarations.Append(
                new LeanDeclaration(
                    "D5.S0.Carrier.mismatched_delivery",
                    "theorem",
                    "statement-v1(mismatched-retired-delivery)",
                    [])
                {
                    NameKey = "fixture-mismatched-retired-delivery",
                }));
        AddFrozenMotivationMembership();
    }

    internal void MutateRetiredDeliveryStatement(string mutation)
    {
        var type = mutation switch
        {
            "weakened" => "statement-v1(retired-delivery-with-extra-hypothesis)",
            _ => throw new ArgumentOutOfRangeException(nameof(mutation)),
        };
        Reports[currentMotivationPath] = Report(
            declarations: Reports[currentMotivationPath].Declarations
                .Select(declaration => declaration with { TypeRepresentation = type }));
    }

    internal void AddUnfrozenRetiredDeliveryDeclaration()
    {
        Reports[currentMotivationPath] = Report(
            declarations: Reports[currentMotivationPath].Declarations.Append(
                new LeanDeclaration(
                    "D5.S0.Carrier.unfrozen_delivery",
                    "theorem",
                    "statement-v1(unfrozen-delivery)",
                    [])));
    }

    internal void RemoveTheoristTargetReport() => Reports.Remove(currentTheoristPath);

    internal void RemoveCurrentFrontierReports()
    {
        foreach (var path in Reports.Keys
                     .Where(static path => path.StartsWith("D5/X_Frontier/", StringComparison.Ordinal))
                     .ToArray())
        {
            Reports.Remove(path);
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
                    "trureturing-theorist-frontier-v2",
                    "trureturing-theorist-frontier-v3");
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
        var backfillTarget = HeaderFor("D5/S0/Carrier/BackfillTarget", "G")
            + "def theoristBackfillTargetFixture : Unit := ()\n";
        Files[BackfillTargetPath] = backfillTarget;
        Baseline[BackfillTargetPath] = backfillTarget;
        ForkPoint[BackfillTargetPath] = backfillTarget;
        Reports[BackfillTargetPath] = Report();
        BaselineReports[BackfillTargetPath] = Report();
        Files[SearchReceiptPath] = "# Search receipt fixture\n";
        Files[ComputationReceiptPath] = "{}\n";
        Files[currentMotivationPath] = HeaderFor(currentMotivationGid, "G");
        Reports[currentMotivationPath] = currentMotivationPath
                is "D5/S0/Carrier/Euclidean.lean"
            ? Report(declarations:
            [
                new LeanDeclaration(
                    "D5.S0.Carrier.golden_division",
                    "theorem",
                    "statement-v1(retired-delivery)",
                    [])
                {
                    NameKey = "fixture-retired-delivery",
                },
            ])
            : Report();
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
        foreach (var path in Files.Keys
                     .Where(FrozenLedgerChangeClassifier.IsAcceptedEventPath)
                     .ToArray())
        {
            Files.Remove(path);
            Baseline.Remove(path);
            ForkPoint.Remove(path);
        }

        var freeze = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Freeze",
            JsonSerializer.SerializeToElement(new
            {
                declaration_statement_ids = Reports[currentMotivationPath].Declarations
                    .OrderBy(static declaration => declaration.NameKey, StringComparer.Ordinal)
                    .Select(static declaration => new
                    {
                        declaration_name_key = declaration.NameKey,
                        kind = declaration.Kind,
                        statement_id =
                            "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
                    }).ToArray(),
                descriptor_selector = currentMotivationPath,
                prerequisite_frozen_node_ids = Array.Empty<string>(),
                statement_id =
                    "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
            }));
        var entries = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [FrozenLedgerChangeClassifier.AcceptedRoot + "/" + freeze.Hash[7..] + ".json"] =
                Encoding.UTF8.GetString(freeze.Bytes.AsSpan()),
        };
        foreach (var (path, text) in entries)
        {
            Files[path] = text;
            Baseline[path] = text;
            ForkPoint[path] = text;
        }
    }

    private string Mission(string? targetOwnerKind, string[]? deliveryGids = null)
    {
        var eligibility = new List<object>();
        if (targetOwnerKind is not null)
        {
            eligibility.Add(targetOwnerKind == "retired"
                ? new
                {
                    source_ref = currentTheoristPath[..^5],
                    kind = targetOwnerKind,
                    delivery_gids = deliveryGids ?? [],
                }
                : new
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

    internal static (string Source, string BlobOid) HistoricalTheoristBlob(string fixtureName) =>
        fixtureName switch
        {
            "finite-depth-metric" =>
                (HistoricalFiniteDepthMetric.Source, HistoricalFiniteDepthMetric.BlobOid),
            "prime-norm-irreducibility" =>
                (HistoricalPrimeNormIrreducibility.Source, HistoricalPrimeNormIrreducibility.BlobOid),
            _ => throw new ArgumentOutOfRangeException(nameof(fixtureName)),
        };

    private static string InsertContract(string pristine, string contract)
    {
        var index = pristine.IndexOf(AuditBlockMarker, StringComparison.Ordinal);
        Assert.True(index > 0, $"historical fixture has no {AuditBlockMarker} block");
        return pristine[..index] + contract + "\n\n" + pristine[index..];
    }

    private static string TheoristContract(
        string gid,
        string statementSha256,
        string motivationGid)
    {
        var json = JsonSerializer.Serialize(new
        {
            schema = "trureturing-theorist-frontier-v2",
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
        return $"/- THEORIST_FRONTIER_CONTRACT_V2\n{json}\n-/";
    }

    private string ExtractContract()
    {
        var source = Files[currentTheoristPath];
        var start = source.IndexOf("/- THEORIST_FRONTIER_CONTRACT_V2", StringComparison.Ordinal);
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

    private void ReplaceBaselineContract(string property, string replacement)
    {
        var source = Baseline[currentTheoristPath];
        var start = source.IndexOf("statement_sha256\":\"", StringComparison.Ordinal);
        Assert.True(start >= 0, $"baseline contract has no {property}");
        start += "statement_sha256\":\"".Length;
        var end = source.IndexOf('"', start);
        Assert.True(end > start);
        Baseline[currentTheoristPath] = source[..start] + replacement + source[end..];
    }

    private void ReplaceRetiredBaselineContract(string replacement)
    {
        var source = Baseline[currentTheoristPath];
        var start = source.IndexOf("/- THEORIST_FRONTIER_CONTRACT_", StringComparison.Ordinal);
        var end = source.IndexOf("\n-/", start, StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start);
        Baseline[currentTheoristPath] = source[..start] + replacement + source[(end + 3)..];
    }

    private sealed record HistoricalTheoristFixture(
        string Path,
        string ModuleGid,
        string Declaration,
        string QualifiedDeclaration,
        string StatementMaterial,
        string MotivationGid,
        string MotivationPath,
        string BlobOid,
        string Source);

    // Source is the verbatim theory-selfgrowth output; BlobOid is the Git object it came from
    // (`git rev-parse <commit>:<path>`). HistoricalFixtureMatchesTheRecordedTheorySelfGrowthBlob
    // keeps the two bound, so the provenance claim cannot silently drift into a paraphrase.
    private static readonly HistoricalTheoristFixture HistoricalFiniteDepthMetric = new(
        "D5/X_Frontier/FiniteDepthMetric.lean",
        "D5/X_Frontier/FiniteDepthMetric",
        "finite_depth_metric_exists",
        "D5.X_Frontier.FiniteDepthMetric.finite_depth_metric_exists",
        "statement-v1(finite-depth-metric-exists)",
        "D5/S1/Depth/JointCoordinates",
        "D5/S1/Depth/JointCoordinates.lean",
        "git-sha1:b63331738d33edfc62fb0ca095e9d2e4fd32a5b8",
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
        "git-sha1:5c997521182be82f34ece80264d342081bfbc870",
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
