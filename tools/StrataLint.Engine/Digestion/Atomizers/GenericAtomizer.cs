using System.Collections.Immutable;
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
    /// <summary>
    /// 〈word〉 then 〈number〉: the lead shape every numbered dialect already shares. A genre
    /// is a word, so the token holds letters and digits and nothing else — no dash, no
    /// underscore. That is not cosmetic: with a dash admitted, this volume's own title,
    /// <c>ENTROPY-INFO-PRIMES-O5:热层卷宗</c>, reads as genre ENTROPY-INFO-PRIMES-O numbered
    /// 5, and its whole preamble is filed under an address that means nothing.
    /// </summary>
    private const string GenreLead = "(?<kind>\\p{L}[\\p{L}\\p{N}]*)[\\s\\u00A0]*(?<number>[0-9]+(?:\\.[0-9A-Za-z]+)*)";

    private static readonly Regex HeadingClaim = new(
        "^" + GenreLead + "(?![0-9A-Za-z.])",
        RegexOptions.CultureInvariant);

    private static readonly Regex ParagraphClaim = new(
        "^\\*\\*[\\s]*(?:" + GenreLead + ")(?![0-9A-Za-z.])",
        RegexOptions.CultureInvariant);

    private static readonly Regex ParagraphItem = new(
        "^\\*\\*[\\s]*(?<number>[0-9]+(?:\\.[0-9A-Za-z]+)+)(?![0-9A-Za-z.])",
        RegexOptions.CultureInvariant);

    /// <summary>Where a slugged heading stops being a readable address and starts being a copy of the prose.</summary>
    private const int SlugRuneLimit = 48;

    /// <summary>Runs of anything that is neither a letter nor a digit collapse to one dash.</summary>
    private static readonly Regex SlugSeparators = new(
        "[^\\p{L}\\p{N}]+",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes, TheoryAtomizerRules _)
    {
        var document = MarkdownAstAtomizer.Atomize(
            bytes,
            IdentifyParagraph,
            static () => GenreRegistryCheck.NoGenreRegistry,
            identifyHeading: IdentifyHeading,
            parse: MarkdigBlockAst.Parse,
            identifyTableRow: IdentifyTableRow,
            dropEmptyHeadingClaims: true,
            identifyHeadingClaim: IsHeadingClaim);
        // 分解生产侧与 pzg 同一实现:08-15 的吸收分解门对全部方言执法,
        // generic-v1 的多子句 claim 同样必须能产出 clause plan(#3499)。
        return new AtomizedTheoryDocument(
            document.Claims,
            document.Slices,
            document.Claims
                .Select(PzgAtomizer.PlanClauses)
                .Where(static plan => plan is not null)
                .Select(static plan => plan!)
                .ToImmutableArray(),
            document.GenreRegistryCheck);
    }

    /// <summary>
    /// A claim table states one proposition per row — each with its own attestation and its
    /// own truth status, 定理级 beside open — so a row is a claim and the table is not. The
    /// header row names the columns rather than stating anything, and is not a claim.
    /// </summary>
    private static string? IdentifyTableRow(MarkdownTableRow row) =>
        row.IsHeader || row.FirstCellText.Length == 0
            ? null
            : "row/" + Slug(row.FirstCellText);

    private static string? IdentifyHeading(string heading)
    {
        var claim = HeadingClaim.Match(heading);
        return claim.Success
            ? claim.Groups["kind"].Value + "/" + claim.Groups["number"].Value
            : "section/" + Slug(heading);
    }

    private static bool IsHeadingClaim(string heading) => HeadingClaim.IsMatch(heading);

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
    /// joins them with dashes. Two degenerate headings are handled rather than assumed away,
    /// because the input is arbitrary prose and both shapes exist in this repository's
    /// volumes: a heading with no letters or digits at all would slug to the empty string,
    /// which addresses nothing, and a heading that runs to a paragraph would put an
    /// unbounded field in the ledger. Both fall back to the heading's own content hash —
    /// still a function of the bytes, so the locator keeps that property either way.
    /// </summary>
    private static string Slug(string heading)
    {
        var slug = SlugSeparators.Replace(heading.Normalize(NormalizationForm.FormC), "-").Trim('-');
        if (slug.Length == 0)
        {
            return DigestionFingerprint.ShortHash(heading);
        }

        var runes = slug.EnumerateRunes().Take(SlugRuneLimit + 1).ToArray();
        return runes.Length <= SlugRuneLimit
            ? slug
            : string.Concat(runes.Take(SlugRuneLimit).Select(static rune => rune.ToString()))
                .TrimEnd('-')
                + "-" + DigestionFingerprint.ShortHash(heading);
    }
}
