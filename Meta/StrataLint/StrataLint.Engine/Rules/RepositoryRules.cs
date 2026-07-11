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

    private static readonly Regex DoiPattern = new(
        "^10\\.[0-9]{4,9}/\\S+$",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    private static readonly Regex ArxivPattern = new(
        "^(?:arXiv:)?[0-9]{4}\\.[0-9]{4,5}(?:v[0-9]+)?$",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    private static readonly Regex AnomalyKindPattern = new(
        "^(?:[a-z0-9]+-)*(?:anomaly|exception|failure|tension)(?:-[a-z0-9]+)*$",
        RegexOptions.CultureInvariant);

    private static readonly Regex AnomalyBearingPattern = new(
        "anomal|exception|failure|tension",
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

    internal static ImmutableArray<RuleFinding> Evaluate(int number, RuleEvaluationContext context) =>
        number switch
        {
            1 => Imports(context),
            2 => Sorry(context),
            3 => Capacity(context),
            4 => Mirrors(context),
            5 => Chronicle(context),
            6 => Badges(context),
            7 => ImmutableArray<RuleFinding>.Empty,
            8 => Hearts(context),
            9 => ImmutableArray<RuleFinding>.Empty,
            10 => Generality(context),
            11 => Domains(context),
            12 => Headers(context),
            13 => Tasks(context),
            14 => ImmutableArray<RuleFinding>.Empty,
            15 => AddressesAndFormulas(context),
            16 => BackfillInventoryRule.Evaluate(context),
            17 => Literature(context),
            18 => Values(context),
            19 => Ledger(context),
            20 => Axioms(context),
            21 => Instantiation(context),
            22 => Bootstrap(context),
            _ => throw new InvalidOperationException($"Unknown rule number {number}."),
        };
}
