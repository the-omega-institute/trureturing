using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record DigestionFingerprints(string RawSha256, string NormalizedSha256);

internal sealed record DigestionContext(int Level, string Text);

internal sealed record DigestionAtom(
    string AstPath,
    int StartByte,
    int EndByte,
    ImmutableArray<byte> RawBytes,
    DigestionFingerprints Fingerprints,
    ImmutableArray<DigestionContext> Context);

internal sealed record DigestionSlice(bool IsClaim, ImmutableArray<byte> RawBytes);

internal sealed class AtomizedTheoryDocument
{
    internal AtomizedTheoryDocument(
        ImmutableArray<DigestionAtom> claims,
        ImmutableArray<DigestionSlice> slices)
    {
        Claims = claims;
        Slices = slices;
    }

    internal ImmutableArray<DigestionAtom> Claims { get; }

    internal ImmutableArray<DigestionSlice> Slices { get; }

    internal DigestionAtom ResolveClaim(string astPath)
    {
        var exact = Claims.Where(atom => atom.AstPath == astPath).ToArray();
        if (exact.Length == 1)
        {
            return exact[0];
        }

        var prefix = astPath + "/occurrence/";
        var qualified = Claims.Where(atom => atom.AstPath.StartsWith(prefix, StringComparison.Ordinal)).ToArray();
        return qualified.Length switch
        {
            1 => qualified[0],
            0 => throw new FormatException($"Markdown claim locator is absent: {astPath}"),
            _ => throw new FormatException($"ambiguous Markdown claim locator: {astPath}"),
        };
    }

    internal ImmutableArray<byte> Reassemble()
    {
        var length = Slices.Sum(static slice => slice.RawBytes.Length);
        var builder = ImmutableArray.CreateBuilder<byte>(length);
        foreach (var slice in Slices)
        {
            builder.AddRange(slice.RawBytes);
        }

        return builder.MoveToImmutable();
    }
}

internal static class DigestionFingerprint
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static DigestionFingerprints Compute(ReadOnlySpan<byte> rawBytes)
    {
        var raw = Sha256(rawBytes);
        var text = StrictUtf8.GetString(rawBytes);
        if (text.StartsWith('\uFEFF'))
        {
            text = text[1..];
        }

        var normalized = text
            .Replace("\r\n", "\n", StringComparison.Ordinal)
            .Replace('\r', '\n')
            .Normalize(NormalizationForm.FormC);
        return new DigestionFingerprints(raw, Sha256(StrictUtf8.GetBytes(normalized)));
    }

    internal static bool IsCanonicalSha256(string value) =>
        value.Length == 71
        && value.StartsWith("sha256:", StringComparison.Ordinal)
        && value.AsSpan(7).IndexOfAnyExcept("0123456789abcdef") < 0;

    internal static DigestionFingerprints ComputeOpaque(ReadOnlySpan<byte> rawBytes)
    {
        var raw = Sha256(rawBytes);
        return new DigestionFingerprints(raw, raw);
    }

    private static string Sha256(ReadOnlySpan<byte> bytes) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes));
}

internal static class GictAtomizer
{
    private static readonly Regex ClaimPattern = new(
        "^\\*\\*(?<kind>定理|定义|命题|引理|推论|观察|勘察|注)\\s*(?<number>[0-9]+\\.[0-9]+)",
        RegexOptions.CultureInvariant);
    private static readonly Regex UnknownNumberedClaimPattern = new(
        "^\\*\\*(?<kind>\\p{L}+)\\s*[0-9]+\\.[0-9]+",
        RegexOptions.CultureInvariant);
    private static readonly Regex AppendixClaimPattern = new(
        "^\\*\\*(?<number>E\\.[0-9]+)\\s+[^\\r\\n*]+\\*\\*",
        RegexOptions.CultureInvariant);
    private static readonly Regex LineagePattern = new(
        "^>\\s*\\*\\*谱系\\*\\*:",
        RegexOptions.CultureInvariant);
    private static readonly Regex HeartsPattern = new(
        "^\\*\\*心脏 O-5.*O-6",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes) =>
        MarkdownAstAtomizer.Atomize(bytes, Identify, IdentifyConstant);

    private static string? Identify(string paragraph)
    {
        var match = ClaimPattern.Match(paragraph);
        if (match.Success)
        {
            return Kind(match.Groups["kind"].Value) + "/" + match.Groups["number"].Value;
        }

        var appendix = AppendixClaimPattern.Match(paragraph);
        if (appendix.Success)
        {
            return "appendix/" + appendix.Groups["number"].Value;
        }

        var unknown = UnknownNumberedClaimPattern.Match(paragraph);
        if (unknown.Success)
        {
            throw new TheorySourceFormatException(
                $"unknown GICT numbered claim kind {unknown.Groups["kind"].Value}");
        }

        if (HeartsPattern.IsMatch(paragraph))
        {
            return "open/O-5-O-6";
        }

        return LineagePattern.IsMatch(paragraph) ? "metadata/lineage" : null;
    }

    private static string Kind(string value) => value switch
    {
        "定理" => "theorem",
        "定义" => "definition",
        "命题" => "proposition",
        "引理" => "lemma",
        "推论" => "corollary",
        "观察" => "observation",
        "勘察" => "survey",
        "注" => "note",
        _ => throw new InvalidOperationException($"unknown GICT claim kind {value}"),
    };

    private static string? IdentifyConstant(string value) => value switch
    {
        "κ" => "constant/kappa",
        "C₀" => "constant/C0",
        "c*" => "constant/cstar",
        "h̄" => "constant/hbar",
        "s₁" => "constant/s1",
        "A_h" => "constant/Ah",
        "E" => "constant/E",
        "C_φ" => "constant/Cphi",
        "T₀" => "constant/T0",
        "δ̄" => "constant/delta-mean",
        "T₁" => "constant/T1",
        "B_h" => "constant/Bh",
        "c₁" => "constant/c1",
        "c₂" => "constant/c2",
        _ => null,
    };
}

internal static class PeriodicTreeAtomizer
{
    private static readonly Regex SectionHeadingPattern = new(
        "^(?<number>[0-9]+)\\.\\s+",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes) =>
        MarkdownAstAtomizer.Atomize(bytes, static _ => null, identifyHeading: IdentifyHeading);

    private static string? IdentifyHeading(string heading)
    {
        var match = SectionHeadingPattern.Match(heading);
        return match.Success ? "section/" + match.Groups["number"].Value : null;
    }
}

internal static class PzgAtomizer
{
    private static readonly Regex ClaimPattern = new(
        "^\\*\\*(?<kind>前沿引注|定理形|定理|定义|命题|引理|推论|观察|评注|账目|条目|公理|范例|判据|后果|原则|规格|契约|延表|路线)\\s*(?<number>[0-9]+\\.[0-9]+[′″]*)",
        RegexOptions.CultureInvariant);
    private static readonly Regex TraceNotePattern = new(
        "^\\*\\*〔(?<number>[0-9]+\\.[0-9]+)\\s+追注",
        RegexOptions.CultureInvariant);
    private static readonly Regex UnknownNumberedClaimPattern = new(
        "^\\*\\*(?<kind>\\p{L}+)\\s*[0-9]+\\.[0-9]+",
        RegexOptions.CultureInvariant);
    private static readonly Regex OpenPattern = new(
        "^\\*\\*(?<id>O-[0-9]+)\\*\\*",
        RegexOptions.CultureInvariant);
    private static readonly Regex SupplementHeadingPattern = new(
        "^PZG_BEDC 增补册:第\\s*(?<version>[0-9]+)\\s*版",
        RegexOptions.CultureInvariant);
    private static readonly Regex RemarkHeadingPattern = new(
        "^评注\\s+(?<range>[0-9]+\\.[0-9]+(?:[–—-][0-9]+\\.[0-9]+)?)",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes) =>
        MarkdownAstAtomizer.Atomize(bytes, Identify, identifyHeading: IdentifyHeading);

    private static string? Identify(string paragraph)
    {
        var match = ClaimPattern.Match(paragraph);
        if (match.Success)
        {
            return Kind(match.Groups["kind"].Value) + "/" + match.Groups["number"].Value;
        }

        var trace = TraceNotePattern.Match(paragraph);
        if (trace.Success)
        {
            return "trace-note/" + trace.Groups["number"].Value;
        }

        var open = OpenPattern.Match(paragraph);
        if (open.Success)
        {
            return "open/" + open.Groups["id"].Value;
        }

        var unknown = UnknownNumberedClaimPattern.Match(paragraph);
        if (unknown.Success)
        {
            throw new TheorySourceFormatException(
                $"unknown PZG numbered claim kind {unknown.Groups["kind"].Value}");
        }

        return null;
    }

    private static string? IdentifyHeading(string heading)
    {
        var supplement = SupplementHeadingPattern.Match(heading);
        if (supplement.Success)
        {
            return "metadata/supplement/" + supplement.Groups["version"].Value;
        }

        var remark = RemarkHeadingPattern.Match(heading);
        if (remark.Success)
        {
            return "remark/" + remark.Groups["range"].Value
                .Replace('–', '-')
                .Replace('—', '-');
        }

        if (heading.StartsWith("判负册", StringComparison.Ordinal))
        {
            return "negative-register/batch";
        }

        if (heading.StartsWith("候查清单", StringComparison.Ordinal))
        {
            return "research-queue/batch";
        }

        return heading.StartsWith("本批收束", StringComparison.Ordinal)
            ? "verdict/batch"
            : null;
    }

    private static string Kind(string value) => value switch
    {
        "定理" => "theorem",
        "定义" => "definition",
        "命题" => "proposition",
        "引理" => "lemma",
        "推论" => "corollary",
        "观察" => "observation",
        "评注" => "remark",
        "账目" => "ledger",
        "条目" => "entry",
        "公理" => "axiom",
        "范例" => "example",
        "判据" => "criterion",
        "后果" => "consequence",
        "原则" => "principle",
        "规格" => "specification",
        "契约" => "contract",
        "定理形" => "theorem-form",
        "前沿引注" => "frontier-note",
        "延表" => "extension-table",
        "路线" => "route",
        _ => throw new InvalidOperationException($"unknown PZG claim kind {value}"),
    };
}

internal static partial class WmAtomizer
{
    private const string Title = "世界模型账本卷:公理纲要(BEDC-WM)";
    private const string AppendixHeading = "§7-附 尸检账(只增不删)";
    private const string AuditHeading = "校核记录(append-only,按版分块)";
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly Regex VersionPattern = new(
        "^-\\s+\\*\\*(?<version>v0(?:\\.1|\\.2)?)\\*\\*",
        RegexOptions.CultureInvariant);
    private static readonly Regex VersionLeadPattern = new(
        "^-\\s+\\*\\*v[^*]+\\*\\*",
        RegexOptions.CultureInvariant);
    private static readonly Regex V02AuditLeadPattern = new(
        "^\\*\\*v0\\.2 校核\\*\\*",
        RegexOptions.CultureInvariant);
    private static readonly Regex V02AuditClosurePattern = new(
        "^\\*\\*v0\\.2 校核\\*\\*\\([^\\r\\n]+\\):[^\\r\\n]*旧块不改。\\z",
        RegexOptions.CultureInvariant);
    private static readonly Regex CurrentTodoClosurePattern = new(
        "^\\*\\*当前待办\\*\\*\\(随版滚动\\):[^\\r\\n]*"
        + "\\*\\*v0\\.2\\*\\*\\(新行追加于版本账,本节追加 v0\\.2 校核块\\)。\\z",
        RegexOptions.CultureInvariant);
    private static readonly Regex DisciplinePattern = new(
        "^> 一句话:[^\\r\\n]+(?:\\r\\n|\\r|\\n)> 纪律:[^\\r\\n]+\\z",
        RegexOptions.CultureInvariant);
    private static readonly Regex SectionHeadingPattern = new(
        "^(?<number>0|[1-9][0-9]*)\\.\\s+",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes)
    {
        var scaffold = MarkdownAstAtomizer.Atomize(
            bytes,
            Identify,
            identifyHeading: IdentifyHeading);
        var raw = bytes.ToArray();
        var text = StrictUtf8.GetString(raw);
        ValidateStructure(text, scaffold);

        var claims = scaffold.Claims.ToList();
        ExtendLastVersionLineEnding(raw, claims);
        ShiftV02AuditSeparator(raw, claims);
        var lastVersion = claims.Last(static atom => atom.AstPath.StartsWith("version/", StringComparison.Ordinal));
        var sectionZero = claims.Single(static atom => atom.AstPath == "section/0");
        claims.Add(CreateAtom(
            raw,
            "metadata/discipline",
            lastVersion.EndByte,
            sectionZero.StartByte,
            [new DigestionContext(1, Title)]));
        claims.Sort(static (left, right) => left.StartByte.CompareTo(right.StartByte));

        var slices = ImmutableArray.CreateBuilder<DigestionSlice>(claims.Count);
        var cursor = 0;
        foreach (var claim in claims)
        {
            if (claim.StartByte != cursor)
            {
                throw new TheorySourceFormatException(
                    $"WM atom spans do not assign byte {cursor} to exactly one primary atom");
            }

            slices.Add(new DigestionSlice(true, claim.RawBytes));
            cursor = claim.EndByte;
        }

        if (cursor != raw.Length)
        {
            throw new TheorySourceFormatException(
                $"WM atom spans stop at byte {cursor} before source byte {raw.Length}");
        }

        return new AtomizedTheoryDocument(claims.ToImmutableArray(), slices.MoveToImmutable());
    }

    private static string? Identify(string paragraph)
    {
        var version = VersionPattern.Match(paragraph);
        if (version.Success)
        {
            return "version/" + version.Groups["version"].Value;
        }

        return V02AuditLeadPattern.IsMatch(paragraph) ? "audit/v0.2" : null;
    }

    private static string? IdentifyHeading(string heading)
    {
        if (heading == Title)
        {
            return "metadata/preamble";
        }

        var section = SectionHeadingPattern.Match(heading);
        if (section.Success)
        {
            return "section/" + section.Groups["number"].Value;
        }

        if (heading == AppendixHeading)
        {
            return "section/7-appendix";
        }

        return heading == AuditHeading ? "audit" : null;
    }

    private static void ValidateStructure(string text, AtomizedTheoryDocument scaffold)
    {
        var blocks = MarkdownBlockAst.Parse(text);
        var headings = blocks.OfType<MarkdownHeading>().ToArray();
        if (headings.Length == 0
            || headings[0].Start != 0
            || headings[0].Level != 1
            || headings[0].Text != Title)
        {
            throw new TheorySourceFormatException("WM source must begin with its exact H1 title");
        }

        var structuralOrder = new List<string> { "metadata/preamble" };
        foreach (var heading in headings.Skip(1))
        {
            var locator = IdentifyHeading(heading.Text);
            if (locator is null
                || locator == "metadata/preamble"
                || locator.StartsWith("section/", StringComparison.Ordinal) && heading.Level is not (2 or 3)
                || locator == "section/7-appendix" && heading.Level != 3
                || locator != "section/7-appendix"
                    && locator.StartsWith("section/", StringComparison.Ordinal)
                    && heading.Level != 2
                || locator == "audit" && heading.Level != 2)
            {
                throw new TheorySourceFormatException($"unknown or misplaced WM heading: {heading.Text}");
            }

            structuralOrder.Add(locator);
        }

        var expectedStructure = new List<string> { "metadata/preamble" };
        for (var section = 0; section <= 11; section++)
        {
            expectedStructure.Add($"section/{section}");
            if (section == 7)
            {
                expectedStructure.Add("section/7-appendix");
            }
        }

        expectedStructure.Add("audit");
        if (!structuralOrder.SequenceEqual(expectedStructure, StringComparer.Ordinal))
        {
            throw new TheorySourceFormatException(
                "WM sections must be unique and ordered as 0..11 with §7-附 and audit in canonical positions");
        }

        var versionLeads = text.Split(['\r', '\n'], StringSplitOptions.RemoveEmptyEntries)
            .Where(static line => VersionLeadPattern.IsMatch(line))
            .ToArray();
        if (versionLeads.Any(static line => !VersionPattern.IsMatch(line)))
        {
            throw new TheorySourceFormatException("unknown WM version ledger line");
        }

        var versions = versionLeads
            .Select(static line => VersionPattern.Match(line).Groups["version"].Value)
            .ToArray();
        var expectedVersions = versions.Contains("v0.2", StringComparer.Ordinal)
            ? new[] { "v0", "v0.1", "v0.2" }
            : new[] { "v0", "v0.1" };
        if (!versions.SequenceEqual(expectedVersions, StringComparer.Ordinal))
        {
            throw new TheorySourceFormatException(
                "WM version ledger must contain v0 and v0.1, followed only by optional v0.2");
        }

        ValidateDiscipline(text, blocks, headings, versionLeads[^1]);

        var hasV02Audit = scaffold.Claims.Any(static atom => atom.AstPath == "audit/v0.2");
        if (hasV02Audit != versions.Contains("v0.2", StringComparer.Ordinal))
        {
            throw new TheorySourceFormatException("WM v0.2 version and audit atoms must be appended together");
        }

        var expectedClaims = new List<string> { "metadata/preamble" };
        expectedClaims.AddRange(expectedVersions.Select(static version => "version/" + version));
        expectedClaims.AddRange(expectedStructure.Skip(1));
        if (hasV02Audit)
        {
            expectedClaims.Add("audit/v0.2");
        }

        if (!scaffold.Claims.Select(static atom => atom.AstPath)
            .SequenceEqual(expectedClaims, StringComparer.Ordinal))
        {
            throw new TheorySourceFormatException("WM locator set does not match the canonical dialect");
        }

        var finalParagraph = blocks.OfType<MarkdownParagraph>().LastOrDefault()?.Text;
        if (finalParagraph is null
            || !(hasV02Audit
                ? V02AuditClosurePattern.IsMatch(finalParagraph)
                : CurrentTodoClosurePattern.IsMatch(finalParagraph)))
        {
            throw new TheorySourceFormatException("WM source has missing audit closure or trailing conversation residue");
        }
    }

    private static void ShiftV02AuditSeparator(byte[] raw, List<DigestionAtom> claims)
    {
        var newAuditIndex = claims.FindIndex(static atom => atom.AstPath == "audit/v0.2");
        if (newAuditIndex < 0)
        {
            return;
        }

        var oldAuditIndex = claims.FindIndex(static atom => atom.AstPath == "audit");
        var boundary = claims[newAuditIndex].StartByte;
        var shiftedBoundary = boundary >= 4
            && raw.AsSpan(boundary - 4, 4).SequenceEqual("\r\n\r\n"u8)
                ? boundary - 2
                : boundary >= 2 && raw[boundary - 1] == (byte)'\n' && raw[boundary - 2] == (byte)'\n'
                    ? boundary - 1
                    : boundary >= 2 && raw[boundary - 1] == (byte)'\r' && raw[boundary - 2] == (byte)'\r'
                        ? boundary - 1
                    : throw new TheorySourceFormatException(
                        "WM v0.2 audit block must be separated by exactly one blank line");
        claims[oldAuditIndex] = ReSpan(raw, claims[oldAuditIndex], claims[oldAuditIndex].StartByte, shiftedBoundary);
        claims[newAuditIndex] = ReSpan(raw, claims[newAuditIndex], shiftedBoundary, claims[newAuditIndex].EndByte);
    }

    private static void ExtendLastVersionLineEnding(byte[] raw, List<DigestionAtom> claims)
    {
        var index = claims.FindLastIndex(static atom =>
            atom.AstPath.StartsWith("version/", StringComparison.Ordinal));
        var atom = claims[index];
        var end = atom.EndByte;
        if (end < raw.Length && raw[end] == (byte)'\r')
        {
            end++;
        }

        if (end < raw.Length && raw[end] == (byte)'\n')
        {
            end++;
        }

        if (end == atom.EndByte)
        {
            throw new TheorySourceFormatException("WM version ledger lines must have line terminators");
        }

        claims[index] = ReSpan(raw, atom, atom.StartByte, end);
    }

    private static DigestionAtom ReSpan(byte[] raw, DigestionAtom atom, int start, int end) =>
        CreateAtom(raw, atom.AstPath, start, end, atom.Context);

    private static DigestionAtom CreateAtom(
        byte[] raw,
        string astPath,
        int start,
        int end,
        ImmutableArray<DigestionContext> context)
    {
        if (start < 0 || end <= start || end > raw.Length)
        {
            throw new TheorySourceFormatException($"invalid WM atom span for {astPath}");
        }

        var atomBytes = ImmutableArray.CreateRange(raw[start..end]);
        return new DigestionAtom(
            astPath,
            start,
            end,
            atomBytes,
            DigestionFingerprint.Compute(atomBytes.AsSpan()),
            context);
    }
}

internal static class MarkdownAstAtomizer
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static AtomizedTheoryDocument Atomize(
        ReadOnlySpan<byte> bytes,
        Func<string, string?> identify,
        Func<string, string?>? identifyFirstTableCell = null,
        Func<string, string?>? identifyHeading = null,
        Func<string, string?>? identifyFirstTableCellSource = null)
    {
        var raw = bytes.ToArray();
        var text = StrictUtf8.GetString(raw);
        var blocks = MarkdownBlockAst.Parse(text);
        var headings = new List<DigestionContext>();
        var candidates = new List<Candidate>();
        var headingStarts = new List<int>();
        foreach (var block in blocks)
        {
            if (block is MarkdownHeading heading)
            {
                while (headings.Count > 0 && headings[^1].Level >= heading.Level)
                {
                    headings.RemoveAt(headings.Count - 1);
                }

                var headingAstPath = identifyHeading?.Invoke(heading.Text);
                if (headingAstPath is not null)
                {
                    candidates.Add(new Candidate(
                        headingAstPath,
                        heading.Start,
                        text.Length,
                        headings.ToImmutableArray(),
                        Extend: true));
                }

                headings.Add(new DigestionContext(heading.Level, heading.Text));
                headingStarts.Add(heading.Start);
                continue;
            }

            if (block is MarkdownTableRow row)
            {
                var tableAstPath = identifyFirstTableCellSource is not null
                    ? TheorySourceFormatException.IdentifyAt(
                        identifyFirstTableCellSource, row.FirstCellSourceText, row.Start, text)
                    : identifyFirstTableCell is not null
                    ? TheorySourceFormatException.IdentifyAt(
                        identifyFirstTableCell, row.FirstCellText, row.Start, text)
                    : TheorySourceFormatException.IdentifyAt(identify, row.Text, row.Start, text);
                if (tableAstPath is not null)
                {
                    candidates.Add(new Candidate(
                        tableAstPath,
                        row.Start,
                        row.End,
                        headings.ToImmutableArray(),
                        Extend: false));
                }

                continue;
            }

            if (block is not MarkdownParagraph paragraph)
            {
                continue;
            }

            var lineClaims = SourceLines(paragraph.Text, paragraph.Start)
                .Select(line => (Line: line, AstPath: TheorySourceFormatException.IdentifyAt(
                    identify, line.Text, line.Start, text)))
                .Where(static item => item.AstPath is not null)
                .ToArray();
            if (lineClaims.Length > 1)
            {
                foreach (var lineClaim in lineClaims)
                {
                    candidates.Add(new Candidate(
                        lineClaim.AstPath!,
                        lineClaim.Line.Start,
                        lineClaim.Line.End,
                        headings.ToImmutableArray(),
                        Extend: false));
                }

                continue;
            }

            var astPath = TheorySourceFormatException.IdentifyAt(
                identify, paragraph.Text, paragraph.Start, text);
            if (astPath is null)
            {
                continue;
            }

            candidates.Add(new Candidate(
                astPath,
                paragraph.Start,
                text.Length,
                headings.ToImmutableArray(),
                Extend: true));
        }

        var boundaries = candidates.Select(static candidate => candidate.StartCharacter)
            .Concat(headingStarts)
            .Distinct()
            .Order()
            .ToArray();
        for (var index = 0; index < candidates.Count; index++)
        {
            var candidate = candidates[index];
            if (!candidate.Extend)
            {
                continue;
            }

            var nestedBoundary = boundaries.FirstOrDefault(start =>
                start > candidate.StartCharacter && start < candidate.EndCharacter);
            if (nestedBoundary > 0)
            {
                candidates[index] = candidate with { EndCharacter = nestedBoundary };
            }
        }

        var claims = ImmutableArray.CreateBuilder<DigestionAtom>(candidates.Count);
        var slices = ImmutableArray.CreateBuilder<DigestionSlice>(candidates.Count * 2 + 1);
        var locatorCounts = candidates
            .GroupBy(static candidate => candidate.AstPath, StringComparer.Ordinal)
            .ToDictionary(static group => group.Key, static group => group.Count(), StringComparer.Ordinal);
        var locatorOccurrences = new Dictionary<string, int>(StringComparer.Ordinal);
        var cursor = 0;
        foreach (var candidate in candidates.OrderBy(static item => item.StartCharacter))
        {
            locatorOccurrences.TryGetValue(candidate.AstPath, out var occurrence);
            occurrence++;
            locatorOccurrences[candidate.AstPath] = occurrence;
            var astPath = locatorCounts[candidate.AstPath] == 1
                ? candidate.AstPath
                : $"{candidate.AstPath}/occurrence/{occurrence}";
            var start = ByteOffset(text, candidate.StartCharacter);
            var end = ByteOffset(text, candidate.EndCharacter);
            if (start < cursor || end <= start || end > raw.Length)
            {
                throw new FormatException($"invalid Markdown AST span for {astPath}");
            }

            if (start > cursor)
            {
                slices.Add(new DigestionSlice(false, ImmutableArray.CreateRange(raw[cursor..start])));
            }

            var atomBytes = ImmutableArray.CreateRange(raw[start..end]);
            slices.Add(new DigestionSlice(true, atomBytes));
            claims.Add(new DigestionAtom(
                astPath,
                start,
                end,
                atomBytes,
                DigestionFingerprint.Compute(atomBytes.AsSpan()),
                candidate.Context));
            cursor = end;
        }

        if (cursor < raw.Length)
        {
            slices.Add(new DigestionSlice(false, ImmutableArray.CreateRange(raw[cursor..])));
        }

        return new AtomizedTheoryDocument(claims.MoveToImmutable(), slices.ToImmutable());
    }

    private static int ByteOffset(string text, int characterOffset) =>
        characterOffset == text.Length
            ? StrictUtf8.GetByteCount(text)
            : StrictUtf8.GetByteCount(text.AsSpan(0, characterOffset));

    private static IEnumerable<SourceLine> SourceLines(string paragraph, int sourceStart)
    {
        var offset = 0;
        while (offset < paragraph.Length)
        {
            var lineEnd = paragraph.IndexOfAny(['\r', '\n'], offset);
            if (lineEnd < 0) lineEnd = paragraph.Length;
            var next = lineEnd;
            while (next < paragraph.Length && paragraph[next] is '\r' or '\n') next++;
            yield return new SourceLine(
                paragraph[offset..lineEnd],
                sourceStart + offset,
                sourceStart + next);
            offset = next;
        }
    }

    private sealed record Candidate(
        string AstPath,
        int StartCharacter,
        int EndCharacter,
        ImmutableArray<DigestionContext> Context,
        bool Extend);

    private sealed record SourceLine(string Text, int Start, int End);
}
