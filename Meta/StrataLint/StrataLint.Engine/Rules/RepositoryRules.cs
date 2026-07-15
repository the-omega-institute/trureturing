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

    private static readonly Regex TaskTokenPattern = new(
        "TASK\\s+(D[0-9]+-T[0-9]{4})",
        RegexOptions.CultureInvariant);

    private static readonly Regex TaskPattern = new(
        "/-- TASK (?<code>D5-T[0-9]{4}) \\| 难度:[1-5] \\| 依赖:[^\\n|]+ \\| 尝试:[0-9]+\\n"
        + "\\s+提示:[^\\n]+\\n\\s+尸检:(?<autopsy>[^\\n]+) -/",
        RegexOptions.CultureInvariant);

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

    private static readonly Regex Sha256Pattern = new(
        "^[0-9a-f]{64}$",
        RegexOptions.CultureInvariant);

    private static readonly ImmutableHashSet<string> AnomalySchemaKeys =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "anomaly", "anomalies", "case", "case_id", "category", "exception", "exceptions",
            "failure", "failures", "kind", "record_type", "resolution", "state", "tension",
            "tensions", "type", "unresolved");

    internal static ImmutableArray<IRepositoryRule> CreateRuleSet() =>
    [
        new RepositoryRule(ManagedLean, Imports),
        new RepositoryRule(ManagedLean, Sorry),
        new RepositoryRule(CapacityScoped, Capacity),
        new RepositoryRule(Formal, Mirrors),
        new RepositoryRule(ChronicleScoped, Chronicle),
        new RepositoryRule(StatusScoped, Badges),
        new RepositoryRule(RepositoryScoped, NoFindings),
        new RepositoryRule(HeartsScoped, Hearts),
        new RepositoryRule(RepositoryScoped, NoFindings),
        new RepositoryRule(GeneralSource, Generality),
        new RepositoryRule(DomainScoped, Domains),
        new RepositoryRule(Formal, Headers),
        new RepositoryRule(Formal, Tasks),
        new RepositoryRule(ToolchainScoped, NoFindings),
        new RepositoryRule(AllArtifacts, AddressesAndFormulas),
        new RepositoryRule(BackfillScoped, BackfillInventoryRule.Evaluate),
        new RepositoryRule(AnchorReferenceScoped, ResolvableAnchors),
        new RepositoryRule(ValuesScoped, Values),
        new RepositoryRule(StructuredOrChronicle, Ledger),
        new RepositoryRule(ManagedLean, Axioms),
        new RepositoryRule(InstantiationScoped, Instantiation),
        new RepositoryRule(BootstrapScoped, Bootstrap),
    ];

    private static ImmutableArray<RuleFinding> NoFindings(RuleEvaluationContext context) =>
        ImmutableArray<RuleFinding>.Empty;
}
