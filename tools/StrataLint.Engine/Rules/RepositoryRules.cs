using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static readonly Regex HeaderPattern = new(
        "\\A/- GID: (?<gid>[^\\n]+)\\n"
        + "   generality: (?<generality>[GIE])\\n"
        + "   mirror-B: (?<mirrorB>[^\\n]+)\\n"
        + "   mirror-E: (?<mirrorE>[^\\n]+)\\n"
        + "   anchors: \\[(?<anchors>[^\\n]*)\\]\\n"
        + "   digest: (?<digest>[^\\n]+) -/\\n?",
        RegexOptions.CultureInvariant);

    private static readonly Regex BadgePattern = new(
        "(?:status\\s*:\\s*(?:proven|admitted|conditional|open)|"
        + "状态\\s*[:：]\\s*(?:已证|承典|条件|开放)|〔(?:已证|承典|条件|开放)〕)",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    private static readonly Regex SafeFieldPattern = new(
        "^[A-Za-z0-9_/.-]+$",
        RegexOptions.CultureInvariant);

    private static readonly Regex CasePattern = new(
        "^D5-T[0-9]{4}$",
        RegexOptions.CultureInvariant);

    private static readonly Regex QueryPattern = new(
        "^D5-Q[0-9]{4}$",
        RegexOptions.CultureInvariant);

    private static readonly Regex ArxivPattern = new(
        "^(?:arXiv:)?[0-9]{4}\\.[0-9]{4,5}(?:v[0-9]+)?$",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    private static readonly Regex AnomalyKindPattern = new(
        "^(?:[a-z0-9]+-)*(?:anomaly|exception|failure|tension)(?:-[a-z0-9]+)*$",
        RegexOptions.CultureInvariant);

    private static readonly Regex AnomalyBearingPattern = new(
        "anomal|exception|failure|(?<!ex)tension",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    private static readonly ImmutableHashSet<string> AnomalySchemaKeys =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "anomaly", "anomalies", "case", "case_id", "category", "exception", "exceptions",
            "evidence_type", "failure", "failures", "kind", "record_type", "resolution", "state", "tension",
            "tensions", "type", "unresolved");

    internal static ImmutableArray<RuleRegistration> CreateRegistrations() =>
    [
        Register(1, "Stratum import closure", new RepositoryRule(ManagedLean, Imports, LeanReportAffected)),
        Register(2, "Sorry closure", new RepositoryRule(ManagedLean, Sorry, SorryAffected)),
        Register(3, "Capacity pressure", new RepositoryRule(CapacityScoped, Capacity, CapacityAffected)),
        Register(4, "Mirror completeness", new RepositoryRule(Formal, Mirrors, MirrorsAffected)),
        Register(5, "Chronicle append only", new RepositoryRule(ChronicleScoped, Chronicle, ChronicleAffected)),
        Register(6, "Generated status", new RepositoryRule(StatusScoped, Badges, StatusAffected)),
        Register(
            7,
            "Conflict-of-interest gate",
            new RepositoryRule(RepositoryScoped, NoFindings),
            AdmissionEffect.HumanGate,
            CaseId.CreateKnown("D5-T0011"),
            "trust"),
        Register(8, "Frozen Hearts semantics", new RepositoryRule(HeartsScoped, Hearts, HeartsAffected)),
        Register(
            9,
            "Provenance gate",
            new RepositoryRule(RepositoryScoped, NoFindings),
            AdmissionEffect.HumanGate,
            CaseId.CreateKnown("D5-T0012"),
            "trust"),
        Register(10, "Generality closure", new RepositoryRule(GeneralSource, Generality, LeanReportAffected)),
        Register(11, "Controlled domains", new RepositoryRule(DomainScoped, Domains, DomainsAffected)),
        Register(12, "Six-line Lean header", new RepositoryRule(Formal, Headers, FormalSourceAffected)),
        // SL-013 remains deferred and has no rejection predicate. Keep this descriptor in place:
        // positional consumers would silently bind later registrations to the wrong rule otherwise.
        Register(
            13,
            "Permanent task ledger",
            new RepositoryRule(Formal, NoFindings),
            deferredCase: CaseId.CreateKnown("D5-T0013")),
        Register(
            14,
            "Toolchain upgrade compatibility",
            new RepositoryRule(ToolchainScoped, NoFindings),
            deferredCase: CaseId.CreateKnown("D5-T0010")),
        Register(
            15,
            "Machine field and GID grammar",
            RepositoryRule.FromDiscoveredEdges(
                typeof(RepositoryRules),
                AllArtifacts,
                RepositoryShapeAffected)),
        Register(
            16,
            "Digestion ledger",
            new RepositoryRule(
                BackfillScoped,
                BackfillInventoryRule.Evaluate,
                BackfillInventoryRule.IsAffectedBy,
                BackfillInventoryRule.EvaluateCandidateDelta)),
        Register(
            17,
            "Typed anchor membership",
            new RepositoryRule(AnchorReferenceScoped, ResolvableAnchors, AnchorsAffected)),
        Register(
            18,
            "Machine-produced values",
            new RepositoryRule(ValuesScoped, Values, ValuesAffected, ValuesCandidateDelta)),
        Register(
            19,
            "Balanced anomaly ledger",
            new RepositoryRule(StructuredOrChronicle, Ledger, LedgerAffected)),
        Register(20, "Lean axiom closure", new RepositoryRule(ManagedLean, Axioms, LeanReportAffected)),
        Register(
            21,
            "Instantiated coordinate gate",
            new RepositoryRule(InstantiationScoped, Instantiation, InstantiationAffected)),
        Register(
            22,
            "Meta bootstrap gate",
            new RepositoryRule(BootstrapScoped, Bootstrap, BootstrapAffected),
            AdmissionEffect.HumanGate,
            category: "trust"),
        Register(
            23,
            "Describe LaTeX statement",
            new RepositoryRule(
                ScribeDefinitionScoped,
                DescribeLatex,
                DescribeLatexAffected,
                DescribeLatexCandidateDelta),
            AdmissionEffect.Observe),
        Register(
            25,
            "Blueprint source-projection skeleton",
            new RepositoryRule(RepositoryScoped, BlueprintProjectionSkeleton, BlueprintSkeletonAffected)),
        Register(
            26,
            "Scribe legacy constructor budget",
            new RepositoryRule(RepositoryScoped, ScribeLegacyConstructorBudget, ScribeSourceAffected)),
        Register(
            28,
            "Duplicate statement advisory",
            new RepositoryRule(
                ManagedLean,
                DuplicateStatementAdvisory.Evaluate,
                DuplicateStatementAdvisory.IsAffectedBy),
            AdmissionEffect.Observe),
        Register(
            29,
            "Theory volume append only",
            new RepositoryRule(TheoryVolumeScoped, TheoryAppendOnly, TheoryVolumeAffected)),
    ];

    private static RuleRegistration Register(
        int number,
        string title,
        IRepositoryRule rule,
        AdmissionEffect effect = AdmissionEffect.Block,
        CaseId? deferredCase = null,
        string category = "repository") =>
        new(
            new RuleDescriptor(
                RuleId.CreateKnown(number),
                title,
                effect is AdmissionEffect.Block ? DisplaySeverity.Error : DisplaySeverity.Warning,
                category,
                effect,
                deferredCase is null ? RuleLifecycle.Active : RuleLifecycle.Deferred,
                deferredCase),
            rule);

    private static ImmutableArray<RuleFinding> DescribeLatex(RuleEvaluationContext context) =>
        context.VerifiedScribeEmissions is null
            ? []
            : context.VerifiedScribeEmissions.DescribeLatexRecords
                .Where(static item => ScribeDescribeContract.RequiresLatex(item.Kind)
                    && item.ProjectionFailureReason is null
                    && item.FormulaProvenance != "lean-derived")
                .Select(static item => new RuleFinding(
                    item.DefinitionPath,
                    $"theorem-class Describe {item.NodeId} is projectable and its formula must be Lean-derived",
                    AdmissionEffect.Block))
                .ToImmutableArray();

    private static ImmutableArray<RuleFinding> DescribeLatexCandidateDelta(
        RuleEvaluationContext context) =>
        DescribeLatex(context)
            .Where(finding => DescribeLatexFactAffected(context, finding.Path))
            .ToImmutableArray();

    private static bool DescribeLatexFactAffected(
        RuleEvaluationContext context,
        string definitionPath) =>
        context.IsBaseFactAffected(definitionPath)
        || context.Changes.Paths.Any(path =>
            path.Value.StartsWith("tools/StrataLint.Scribe/", StringComparison.Ordinal)
            || RepositoryPathPolicy.IsBlueprintContentCompositionBuildFile(path.Value));

    private static ImmutableArray<RuleFinding> NoFindings(RuleEvaluationContext context) =>
        ImmutableArray<RuleFinding>.Empty;
}
