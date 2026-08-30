using System.Collections.Immutable;
using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class WmAtomizer
{
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
    private static readonly Regex DisciplinePattern = new(
        "^> 一句话:[^\\r\\n]+(?:\\r\\n|\\r|\\n)> 纪律:[^\\r\\n]+\\z",
        RegexOptions.CultureInvariant);
    private static readonly Regex SectionHeadingPattern = new(
        "^(?<number>0|[1-9][0-9]*)\\.\\s+",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes, TheoryAtomizerRules rules) =>
        Atomize(bytes, rules, contentKinds: null);

    internal static ImmutableDictionary<string, string> ResolveContentKinds(
        ReadOnlyMemory<byte> bytes,
        TheoryAtomizerRules rules) =>
        AtomizerRegistry.CaptureContentKinds(kinds => Atomize(bytes.Span, rules, kinds));

    private static AtomizedTheoryDocument Atomize(
        ReadOnlySpan<byte> bytes,
        TheoryAtomizerRules rules,
        IDictionary<string, string>? contentKinds)
    {
        ArgumentNullException.ThrowIfNull(rules);
        Dictionary<string, string>? scaffoldKinds = contentKinds is null
            ? null
            : new Dictionary<string, string>(StringComparer.Ordinal);
        var scaffold = MarkdownAstAtomizer.Atomize(
            bytes,
            Identify,
            static () => GenreRegistryCheck.NoGenreRegistry,
            identifyHeading: heading => IdentifyHeading(heading, rules),
            extendLineClaims: false,
            contentKinds: scaffoldKinds);
        var raw = bytes.ToArray();
        var text = StrictUtf8.GetString(raw);
        ValidateStructure(text, scaffold, rules);

        var claims = scaffold.Claims.ToList();
        ExtendLastVersionLineEnding(raw, claims);
        ShiftAppendedAuditSeparators(raw, claims);
        var lastVersion = claims.Last(static atom => VersionPattern.IsMatch(AtomText(atom)));
        var sectionZero = claims.Single(static atom => IsSection(atom, "0"));
        claims.Add(CreateAtom(
            raw,
            lastVersion.EndByte,
            sectionZero.StartByte,
            [new DigestionContext(1, rules.WmHeadings["title"])]));
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

        if (contentKinds is not null && scaffoldKinds is not null)
        {
            foreach (var claim in claims)
            {
                var source = scaffold.Claims
                    .Select(atom => (Atom: atom, Overlap: Math.Min(atom.EndByte, claim.EndByte)
                        - Math.Max(atom.StartByte, claim.StartByte)))
                    .Where(static item => item.Overlap > 0)
                    .OrderByDescending(static item => item.Overlap)
                    .FirstOrDefault();
                var kind = source.Atom is not null
                    && scaffoldKinds.TryGetValue(source.Atom.Fingerprints.RawSha256, out var captured)
                        ? captured
                        : DisciplinePattern.IsMatch(AtomText(claim))
                            ? "metadata"
                            : null;
                if (kind is not null)
                {
                    AtomizerRegistry.RecordContentKind(contentKinds, claim, kind);
                }
            }
        }

        return new AtomizedTheoryDocument(
            claims.ToImmutableArray(),
            slices.MoveToImmutable(),
            GenreRegistryCheck.NoGenreRegistry);
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

    private static string? IdentifyHeading(string heading, TheoryAtomizerRules rules)
    {
        if (heading == rules.WmHeadings["title"])
        {
            return "metadata/preamble";
        }

        var section = SectionHeadingPattern.Match(heading);
        if (section.Success)
        {
            return "section/" + section.Groups["number"].Value;
        }

        if (heading == rules.WmHeadings["appendix"])
        {
            return "section/7-appendix";
        }

        return heading == rules.WmHeadings["audit"] ? "audit" : null;
    }

    private static void ValidateStructure(
        string text,
        AtomizedTheoryDocument scaffold,
        TheoryAtomizerRules rules)
    {
        var blocks = MarkdownBlockAst.Parse(text);
        var headings = blocks.OfType<MarkdownHeading>().ToArray();
        if (headings.Length == 0
            || headings[0].Start != 0
            || headings[0].Level != 1
            || headings[0].Text != rules.WmHeadings["title"])
        {
            throw new TheorySourceFormatException("WM source must begin with its exact H1 title");
        }

        var structuralOrder = new List<string> { "metadata/preamble" };
        foreach (var heading in headings.Skip(1))
        {
            var locator = IdentifyHeading(heading.Text, rules);
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
                "WM appended audits must cover every revision after v0.1 in ledger order");
        }

        var expectedClaimCount = versions.Length + expectedStructure.Count
            + versions.Skip(2).Count();
        if (scaffold.Claims.Length != expectedClaimCount)
        {
            throw new TheorySourceFormatException("WM atom set does not match the canonical dialect");
        }

        var firstAppendedVersion = versions.Length > 2
            ? versions[2]
            : $"v0.{revisions[^1] + 1}";
        ValidateClosure(text, blocks, auditBlocks, appendedAudits, firstAppendedVersion);
    }

    private static void ShiftAppendedAuditSeparators(byte[] raw, List<DigestionAtom> claims)
    {
        var appendedAuditIndexes = claims
            .Select((atom, index) => (Atom: atom, Index: index))
            .Where(static item => IsAppendedAudit(item.Atom))
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

    private static bool IsAppendedAudit(DigestionAtom atom)
    {
        var match = AuditPattern.Match(AtomText(atom));
        return match.Success && ParseRevision(match, "WM audit block") >= 2;
    }

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
            VersionPattern.IsMatch(AtomText(atom)));
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
        CreateAtom(raw, start, end, atom.Context);

    internal static DigestionAtom CreateAtom(
        byte[] raw,
        int start,
        int end,
        ImmutableArray<DigestionContext> context)
    {
        if (start < 0 || end <= start || end > raw.Length)
        {
            throw new TheorySourceFormatException($"invalid WM atom span at byte {start}");
        }

        var atomBytes = ImmutableArray.CreateRange(raw[start..end]);
        return new DigestionAtom(
            start,
            end,
            atomBytes,
            DigestionFingerprint.Compute(atomBytes.AsSpan()),
            context,
            DigestionAtomStatusMarker.Parse(atomBytes.AsSpan()));
    }

    private static string AtomText(DigestionAtom atom) =>
        StrictUtf8.GetString(atom.RawBytes.AsSpan());

    private static bool IsSection(DigestionAtom atom, string number)
    {
        var first = MarkdownBlockAst.Parse(AtomText(atom)).OfType<MarkdownHeading>().FirstOrDefault();
        var match = first is null ? null : SectionHeadingPattern.Match(first.Text);
        return match is { Success: true } && match.Groups["number"].Value == number;
    }
}
