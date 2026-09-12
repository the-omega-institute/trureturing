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
        + "(?:   utility: (?<utility>[^\\n]*)\\n)?"
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
        Register(1, "Stratum import closure", new RepositoryRule(ManagedLean, Imports)),
        Register(2, "Sorry closure", new RepositoryRule(ManagedLean, Sorry)),
        Register(3, "Capacity pressure", new RepositoryRule(CapacityScoped, CurrentCapacity, CapacityAffected, Capacity)),
        Register(4, "Mirror completeness", new RepositoryRule(Formal, Mirrors)),
        Register(6, "Generated status", new RepositoryRule(StatusScoped, Badges)),
        Register(
            7,
            "Conflict-of-interest gate",
            new RepositoryRule(RepositoryScoped, NoFindings),
            AdmissionEffect.HumanGate,
            CaseId.CreateKnown("D5-T0011"),
            "trust"),
        Register(8, "Frozen Hearts semantics", new RepositoryRule(HeartsScoped, CurrentHearts, HeartsAffected, Hearts)),
        Register(
            9,
            "Provenance gate",
            new RepositoryRule(RepositoryScoped, NoFindings),
            AdmissionEffect.HumanGate,
            CaseId.CreateKnown("D5-T0012"),
            "trust"),
        Register(10, "Generality closure", new RepositoryRule(GeneralSource, Generality)),
        Register(11, "Controlled domains", new RepositoryRule(DomainScoped, Domains)),
        Register(12, "Canonical Lean header", new RepositoryRule(Formal, Headers)),
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
                AllArtifacts)),
        Register(
            16,
            "Digestion ledger",
            new RepositoryRule(
                BackfillScoped,
                null,
                BackfillInventoryRule.IsAffectedBy,
                BackfillInventoryRule.EvaluateCandidateDelta)),
        Register(
            17,
            "Typed anchor membership",
            new RepositoryRule(AnchorReferenceScoped, ResolvableAnchors)),
        Register(
            18,
            "Machine-produced values",
            new RepositoryRule(ValuesScoped, Values)),
        Register(
            19,
            "Balanced anomaly ledger",
            new RepositoryRule(StructuredOrChronicle, Ledger)),
        Register(20, "Lean axiom closure", new RepositoryRule(ManagedLean, Axioms)),
        Register(
            21,
            "Instantiated coordinate gate",
            new RepositoryRule(InstantiationScoped, Instantiation)),
        Register(
            22,
            "Meta bootstrap gate",
            new RepositoryRule(BootstrapScoped, null, BootstrapAffected, Bootstrap),
            AdmissionEffect.HumanGate,
            category: "trust"),
        Register(
            23,
            "Describe LaTeX statement",
            new RepositoryRule(
                ScribeDefinitionScoped,
                DescribeLatex),
            AdmissionEffect.Observe),
        Register(
            25,
            "Blueprint source-projection skeleton",
            new RepositoryRule(RepositoryScoped, BlueprintProjectionSkeleton, BlueprintSkeletonAffected, ProtectedBlueprintSkeleton)),
        Register(
            26,
            "Scribe legacy constructor budget",
            new RepositoryRule(RepositoryScoped, ScribeLegacyConstructorBudget)),
        Register(
            28,
            "Duplicate statement advisory",
            new RepositoryRule(
                ManagedLean,
                null,
                DuplicateStatementAdvisory.IsAffectedBy,
                DuplicateStatementAdvisory.Evaluate),
            AdmissionEffect.Observe),
        Register(
            30,
            "Judge surface reads no other revision",
            new RepositoryRule(
                JudgeSurfaceScoped,
                null,
                JudgeSurfaceAffected,
                JudgeSurfaceRevisionMaterialization),
            category: "trust"),
        Register(
            31,
            "Computational utility admission",
            new RepositoryRule(
                Formal,
                null,
                UtilityAdmissionRule.IsAffectedBy,
                UtilityAdmissionRule.Evaluate)),
        Register(
            32,
            "Scribe narrative provenance",
            new RepositoryRule(ScribeDefinitionScoped, null, ScribeSourceAffected, ScribeNarrativeProvenance)),
        Register(
            33,
            "Frozen state and accepted Freeze pairing",
            new RepositoryRule(
                (artifact, _) => FrozenPairRule.IsPairPath(artifact.Path.Value),
                null,
                FrozenPairRule.IsAffectedBy,
                FrozenPairRule.Evaluate)),
        Register(
            34,
            "Closed Lean modules missing frozen state",
            new RepositoryRule(
                ModuleStateGateRule.IsApplicable,
                null,
                ModuleStateGateRule.IsAffectedBy,
                ModuleStateGateRule.Evaluate),
            AdmissionEffect.Observe,
            recheckOnImplementationChange: false),
    ];

    private static RuleRegistration Register(
        int number,
        string title,
        IRepositoryRule rule,
        AdmissionEffect effect = AdmissionEffect.Block,
        CaseId? deferredCase = null,
        string category = "repository",
        bool recheckOnImplementationChange = true) =>
        new(
            new RuleDescriptor(
                RuleId.CreateKnown(number),
                title,
                effect is AdmissionEffect.Block ? DisplaySeverity.Error : DisplaySeverity.Warning,
                category,
                effect,
                deferredCase is null ? RuleLifecycle.Active : RuleLifecycle.Deferred,
                deferredCase),
            rule,
            recheckOnImplementationChange);

    private static ImmutableArray<RuleFinding> DescribeLatex(CurrentRuleContext context) =>
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

    private static ImmutableArray<RuleFinding> NoFindings(CurrentRuleContext context) =>
        ImmutableArray<RuleFinding>.Empty;
}
