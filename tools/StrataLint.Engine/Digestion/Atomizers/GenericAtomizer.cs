using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

/// <summary>
/// The default digestion path: the atomizer a volume gets when nobody has written one for
/// it. Where a dialect is a lexicon — this volume says 定理, that one says 命题 — this is a
/// rule, and the difference is the whole point. Three clauses, applied to the Markdown
/// block AST every atomizer shares:
/// <list type="number">
///   <item>a heading whose lead is 〈word〉〈number〉 addresses a claim of that genre, the
///     genre token taken verbatim;</item>
///   <item>any other heading addresses its section, by a slug of its own text;</item>
///   <item>a bolded paragraph lead of the same shape addresses a claim, and one that is
///     numbered without naming a genre addresses an item.</item>
/// </list>
/// Two properties follow, and both are load-bearing. First, <b>no shape of Markdown is a
/// format failure</b>: an unrecognised lead is simply not a claim, never an exception, so
/// a volume in an unforeseen shape still digests — the anomaly becomes a node rather than
/// a crash. Second, <b>the locator is a function of the source bytes alone</b>: no loaded
/// vocabulary is consulted, so editing one volume's dialect cannot churn another volume's
/// receipts, and an insertion moves only the atoms whose own bytes moved.
/// </summary>
internal static class GenericAtomizer
{
    internal const string ResidualPrefix = "generic";

    /// <summary>〈word〉 then 〈number〉: the lead shape every numbered dialect already shares.</summary>
    private const string GenreLead = "(?<kind>\\p{L}[\\p{L}\\p{N}_-]*)[\\s\\u00A0]*(?<number>[0-9]+(?:\\.[0-9A-Za-z]+)*)";

    private static readonly Regex HeadingClaim = new(
        "^" + GenreLead + "(?![0-9A-Za-z.])",
        RegexOptions.CultureInvariant);

    private static readonly Regex ParagraphClaim = new(
        "^\\*\\*[\\s]*(?:" + GenreLead + ")(?![0-9A-Za-z.])",
        RegexOptions.CultureInvariant);

    private static readonly Regex ParagraphItem = new(
        "^\\*\\*[\\s]*(?<number>[0-9]+(?:\\.[0-9A-Za-z]+)+)(?![0-9A-Za-z.])",
        RegexOptions.CultureInvariant);

    /// <summary>Runs of anything that is neither a letter nor a digit collapse to one dash.</summary>
    private static readonly Regex SlugSeparators = new(
        "[^\\p{L}\\p{N}]+",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes, TheoryAtomizerRules _) =>
        MarkdownAstAtomizer.Atomize(
            bytes,
            IdentifyParagraph,
            identifyHeading: IdentifyHeading);

    private static string? IdentifyHeading(string heading)
    {
        var claim = HeadingClaim.Match(heading);
        return claim.Success
            ? claim.Groups["kind"].Value + "/" + claim.Groups["number"].Value
            : "section/" + Slug(heading);
    }

    private static string? IdentifyParagraph(string paragraph)
    {
        var claim = ParagraphClaim.Match(paragraph);
        if (claim.Success)
        {
            return claim.Groups["kind"].Value + "/" + claim.Groups["number"].Value;
        }

        var item = ParagraphItem.Match(paragraph);
        return item.Success ? "item/" + item.Groups["number"].Value : null;
    }

    /// <summary>
    /// A locator has to survive being written to YAML and read back, so the slug keeps only
    /// letters and digits — of any script, since these volumes are written in Chinese — and
    /// joins them with dashes. An empty result would make a locator that addresses nothing,
    /// so a heading with no letters or digits at all falls back to its content hash.
    /// </summary>
    private static string Slug(string heading)
    {
        var slug = SlugSeparators.Replace(heading.Normalize(NormalizationForm.FormC), "-").Trim('-');
        return slug.Length > 0 ? slug : DigestionFingerprint.ShortHash(heading);
    }
}
