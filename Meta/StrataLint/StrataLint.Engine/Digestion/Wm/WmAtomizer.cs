using System.Collections.Immutable;
using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class WmAtomizer
{
    private const string Title = "世界模型账本卷:公理纲要(BEDC-WM)";
    private const string AppendixHeading = "§7-附 尸检账(只增不删)";
    private const string AuditHeading = "校核记录(append-only,按版分块)";
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly Regex VersionPattern = new(
        "^-\\s+\\*\\*(?<version>v0(?:\\.(?<revision>[1-9][0-9]*))?)\\*\\*",
        RegexOptions.CultureInvariant);
    private static readonly Regex VersionLeadPattern = new(
        "^-\\s+\\*\\*v[^*]+\\*\\*",
        RegexOptions.CultureInvariant);
    private static readonly Regex AuditLeadPattern = new(
        "^\\*\\*v[^*\\r\\n]*校核\\*\\*",
        RegexOptions.CultureInvariant);
    private static readonly Regex AuditPattern = new(
        "^\\*\\*(?<version>v0(?:\\.(?<revision>[1-9][0-9]*))?) 校核\\*\\*",
        RegexOptions.CultureInvariant);
    private static readonly Regex AppendedAuditClosurePattern = new(
        "^\\*\\*v0\\.(?<revision>[1-9][0-9]*) 校核\\*\\*\\([^\\r\\n]+\\):[^\\r\\n]*旧块不改。\\z",
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
        ShiftAppendedAuditSeparators(raw, claims);
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
            ParseRevision(version, "WM version ledger");
            return "version/" + version.Groups["version"].Value;
        }

        if (VersionLeadPattern.IsMatch(paragraph))
        {
            throw new TheorySourceFormatException("unknown WM version ledger line");
        }

        var audit = AuditPattern.Match(paragraph);
        if (audit.Success)
        {
            var revision = ParseRevision(audit, "WM audit block");
            return revision >= 2 ? "audit/" + audit.Groups["version"].Value : null;
        }

        if (AuditLeadPattern.IsMatch(paragraph))
        {
            throw new TheorySourceFormatException("unknown WM audit block");
        }

        return null;
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

        var versionMatches = versionLeads.Select(static line => VersionPattern.Match(line)).ToArray();
        var revisions = versionMatches
            .Select(static match => ParseRevision(match, "WM version ledger"))
            .ToArray();
        if (revisions.Length < 2
            || revisions.Where((revision, index) => revision != index).Any())
        {
            throw new TheorySourceFormatException(
                "WM version ledger must be strictly continuous from v0 through v0.N");
        }

        var versions = versionMatches
            .Select(static match => match.Groups["version"].Value)
            .ToArray();

        ValidateDiscipline(text, blocks, headings, versionLeads[^1]);

        var auditBlocks = blocks.OfType<MarkdownParagraph>()
            .Select(static paragraph => (Paragraph: paragraph, Match: AuditPattern.Match(paragraph.Text)))
            .Where(static item => item.Match.Success)
            .Select(static item => new WmAuditBlock(
                item.Paragraph,
                ParseRevision(item.Match, "WM audit block")))
            .ToArray();
        var appendedAudits = auditBlocks.Where(static item => item.Revision >= 2).ToArray();
        var expectedAppendedCount = revisions.Length - 2;
        if (appendedAudits.Length != expectedAppendedCount
            || appendedAudits.Where((audit, index) => audit.Revision != index + 2).Any())
        {
            throw new TheorySourceFormatException(
                "WM appended audits must be exactly v0.2 through v0.N in ledger order");
        }

        var expectedClaims = new List<string> { "metadata/preamble" };
        expectedClaims.AddRange(versions.Select(static version => "version/" + version));
        expectedClaims.AddRange(expectedStructure.Skip(1));
        expectedClaims.AddRange(versions.Skip(2).Select(static version => "audit/" + version));

        if (!scaffold.Claims.Select(static atom => atom.AstPath)
            .SequenceEqual(expectedClaims, StringComparer.Ordinal))
        {
            throw new TheorySourceFormatException("WM locator set does not match the canonical dialect");
        }

        ValidateClosure(text, blocks, auditBlocks, appendedAudits);
    }

    private static void ShiftAppendedAuditSeparators(byte[] raw, List<DigestionAtom> claims)
    {
        var appendedAuditIndexes = claims
            .Select((atom, index) => (Atom: atom, Index: index))
            .Where(static item => IsAppendedAuditPath(item.Atom.AstPath))
            .Select(static item => item.Index)
            .ToArray();
        foreach (var newAuditIndex in appendedAuditIndexes)
        {
            var previousIndex = newAuditIndex - 1;
            var boundary = claims[newAuditIndex].StartByte;
            var lineEndingLength = LineEndingLengthBefore(raw, boundary);
            var priorBoundary = boundary - lineEndingLength;
            if (lineEndingLength == 0
                || LineEndingLengthBefore(raw, priorBoundary) != lineEndingLength
                || LineEndingLengthBefore(raw, priorBoundary - lineEndingLength) != 0)
            {
                throw new TheorySourceFormatException(
                    "WM appended audit blocks must be separated by exactly one blank line");
            }

            var shiftedBoundary = priorBoundary;
            claims[previousIndex] = ReSpan(
                raw,
                claims[previousIndex],
                claims[previousIndex].StartByte,
                shiftedBoundary);
            claims[newAuditIndex] = ReSpan(
                raw,
                claims[newAuditIndex],
                shiftedBoundary,
                claims[newAuditIndex].EndByte);
        }
    }

    private static int LineEndingLengthBefore(byte[] raw, int boundary)
    {
        if (boundary >= 2 && raw[boundary - 2] == (byte)'\r' && raw[boundary - 1] == (byte)'\n')
        {
            return 2;
        }

        return boundary >= 1 && raw[boundary - 1] is (byte)'\r' or (byte)'\n' ? 1 : 0;
    }

    private static bool IsAppendedAuditPath(string astPath) =>
        astPath.StartsWith("audit/v0.", StringComparison.Ordinal);

    private static int ParseRevision(Match match, string source)
    {
        var revision = match.Groups["revision"];
        if (!revision.Success)
        {
            return 0;
        }

        if (!int.TryParse(
                revision.ValueSpan,
                NumberStyles.None,
                CultureInfo.InvariantCulture,
                out var parsed))
        {
            throw new TheorySourceFormatException($"{source} revision is out of range");
        }

        return parsed;
    }

    private sealed record WmAuditBlock(MarkdownParagraph Paragraph, int Revision);

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
