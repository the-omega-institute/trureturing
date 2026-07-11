using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static class BackfillInventoryRule
{
    private const string BackfillPath = "Meta/BACKFILL.yaml";
    private const string InventoryVersion = "m0-protected-v1";

    private static readonly Regex HashPattern = new(
        "^[0-9a-f]{64}$",
        RegexOptions.CultureInvariant);

    private static readonly Regex CasePattern = new(
        "^D5-T[0-9]{4}$",
        RegexOptions.CultureInvariant);

    // Hashes and line anchors are the content-addressed baseline trust root. Candidate policy owns
    // path membership; keeping paths here would duplicate registry.governance_documents.
    private static readonly ImmutableArray<ProtectedSource> ProtectedSources =
    [
        new(
            "GICT-v3.6",
            "d61cda25af5f6bf17b065711ee762b63d6d196f94dd77e5ece962cf146bc163c",
            [
                new("GICT-heart-O5", 228, "ad0167e83242b219a2332786ea2896ffde279a535e0c491922398ff8f49ae970"),
                new("GICT-heart-O6", 228, "ad0167e83242b219a2332786ea2896ffde279a535e0c491922398ff8f49ae970"),
                new("constant-kappa", 266, "8bf05a9c8f1f0c4e89d6c2b07dd217b1e7ced40442df14ba85b1f983302cff53"),
                new("constant-C0", 267, "52a6bfce146c22055aed1985c2ed9d79935cf96558f84a7bbab6bd6c14302dde"),
                new("constant-cstar", 268, "1ef74dbf9311393d801a3875b0d03c46b47ffd72812d53dcef5113de8558aa11"),
                new("constant-hbar", 269, "b6068cd957ea5d82535af31287f6ee52ba2c8e232c7f18224db5e1c7504b604c"),
                new("constant-s1", 270, "d2b1a4f7727b5187be905416aafae8fa332ab7cb786da18f85c4a5ac0f7a8238"),
                new("constant-Ah", 271, "5536d0b171320ffe238f600a0402a5c29621c4f8a5db881fee4b44afd4889ccc"),
                new("constant-E", 272, "128bd1363ca1def11b0dff7f6986e8d0fa740c9e2d0cc30e629960ad8c19345d"),
                new("constant-Cphi", 273, "3b54cc6cd44ddecea50eb2d68e1037c1d1fc520176020dcacce91ae35134e551"),
                new("constant-T0", 274, "c8e0d2e19b6bf9158eb39544e3e5e38f24306e71744f22ff65f2c65fe6d30337"),
                new("constant-delta-mean", 275, "1af557f45a43b0badf08cd58f93d645311985374247be50c671b915f6efc1a18"),
                new("constant-T1", 276, "34c3b42a8445e88358c01c48967af6312889bfe46ce13844ddc6fdf3bce2759f"),
                new("constant-Bh", 277, "bb4524178917d778e7e46522f266ca7f514aaa57b74e10df1f9d305519190875"),
                new("constant-c1", 278, "ea5eaca443f31646487fd6ed18714cc33ae4789f08b476e76d441cf8c60b875f"),
                new("constant-c2", 279, "6abb48a72f98fd04d41b6a4ed36d8d7acf02f4ef7276bc5165cf269db1991214"),
            ]),
        new(
            "PZG-v170",
            "02f17b403914c50795a82e54658061920b5510cb83ee9ce9587134e500060279",
            [
                new("PZG-chapter-29-O5", 2784, "bf0a0ef5fe508a4b82f611d1f6431bacf25b039929015b061664c778c86fb29f"),
                new("PZG-chapter-29-O6", 2785, "84efc878d587793ec813af69649561317fad57fdc1b626eca8a0f2c87fe23147"),
            ]),
        new(
            "spec-v7.11-section-10",
            "b93e3c2be88160503ccef6425f101c9b3556d79aa6c1667397dc42733f01e302",
            [
                new("acceptance-sample-01", 249, "92c7f0274e16991a21f4c20affcfbb981de83f40f7bfffb31b24114b48129dd1"),
                new("acceptance-sample-02", 252, "218727c897b767e0cf6b913cbb630246ff3d85aa42174d9c294bac5bcc61e057"),
                new("acceptance-sample-03", 254, "62e6cd5c0e0446f3a8e010fb714cc05ee83c3d321a6ada19759a11e52f1af8fa"),
                new("acceptance-sample-04", 256, "e707d82098872abd634ced82ea8e4697c9b25e7eb2d258a8b523d6929cbc69e8"),
                new("acceptance-sample-05", 258, "aee4ab863825e4f334f4c4a9c2dbc195d5d2a58b63449718c58e252f459fc48e"),
                new("acceptance-sample-06", 264, "8a2f1e6e94f750168225d52fabf9ea5b78066bb35a8bd383e7bb69bc795531b5"),
                new("acceptance-sample-07", 266, "267a6d0c7a9f4c442b7eabfa62838d5aad81e3a9a0e8fe2384a440e9ba82cd6e"),
                new("acceptance-sample-08", 272, "a7a46b989275423f40f14f3564538041ffcf3d09ed99f806c1ba72f4ad74e02b"),
                new("acceptance-sample-09", 275, "096f06f4f94132b890bbd0cee9f5d80ad1d485e47b1256082419439128c7af56"),
                new("acceptance-sample-10", 277, "eb947bde0d0a21a29245ec1add69bbecefc609554072e8daf879ec0d57b01146"),
                new("acceptance-sample-11", 279, "acb16038a443ae373294184e4df3447a6c51ce9531493081da6d67e695e42bdb"),
                new("acceptance-sample-12", 282, "46f0b508128b0a3f99ab793eb0b8ea994a75bbe0ae6028dcabf1a6bf573b6dd1"),
            ]),
    ];

    private static readonly ImmutableArray<string> ProtectedCaseIds = Enumerable.Range(1, 17)
        .Select(static number => $"D5-T{number:0000}")
        .ToImmutableArray();

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
        if (!context.Current.TryGetFile(BackfillPath, out var file))
        {
            return [new RuleFinding(BackfillPath, "required governance document is missing")];
        }

        Dictionary<string, object?> root;
        try
        {
            root = (Dictionary<string, object?>)YamlSubsetParser.Parse(file.Text);
        }
        catch (FormatException exception)
        {
            return [new RuleFinding(BackfillPath, exception.Message)];
        }

        if (!root.TryGetValue("schema_version", out var schema)
            || schema is not int version
            || version != 2
            || !root.TryGetValue("inventory", out var inventory)
            || inventory is not string inventoryName
            || !string.Equals(inventoryName, InventoryVersion, StringComparison.Ordinal))
        {
            return [new RuleFinding(
                BackfillPath,
                $"BACKFILL must use schema_version 2 and inventory {InventoryVersion}")];
        }

        if (!root.TryGetValue("sources", out var rawSources) || rawSources is not List<object?> sources)
        {
            return [new RuleFinding(BackfillPath, "sources must be a list")];
        }

        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var byId = new Dictionary<string, Dictionary<string, object?>>(StringComparer.Ordinal);
        var seenPaths = new HashSet<string>(StringComparer.Ordinal);
        foreach (var rawSource in sources)
        {
            if (rawSource is not Dictionary<string, object?> source
                || !source.TryGetValue("id", out var rawId)
                || rawId is not string sourceId)
            {
                findings.Add(new RuleFinding(BackfillPath, "each source needs an id"));
                continue;
            }

            if (!byId.TryAdd(sourceId, source))
            {
                findings.Add(new RuleFinding(BackfillPath, $"duplicate source id: {sourceId}"));
            }

            if (source.TryGetValue("path", out var rawPath) && rawPath is string sourcePath
                && !seenPaths.Add(sourcePath))
            {
                findings.Add(new RuleFinding(BackfillPath, $"duplicate source path: {sourcePath}"));
            }
        }

        var missingSources = ProtectedSources
            .Where(source => !byId.ContainsKey(source.Id))
            .Select(static source => source.Id)
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (missingSources.Length > 0)
        {
            findings.Add(new RuleFinding(
                BackfillPath,
                "protected sources are missing: " + string.Join(", ", missingSources)));
            return findings.ToImmutable();
        }

        if (!root.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(
                ["schema_version", "inventory", "sources", "ticket_index"]))
        {
            findings.Add(new RuleFinding(BackfillPath, "BACKFILL top-level keys are not the protected schema"));
        }

        foreach (var protectedSource in ProtectedSources)
        {
            ValidateSource(
                context.Current,
                context.Policy,
                byId[protectedSource.Id],
                protectedSource,
                findings);
        }

        root.TryGetValue("ticket_index", out var ticketIndex);
        ValidateTicketIndex(context.Current, ticketIndex, findings);
        return findings.ToImmutable();
    }

    private static void ValidateSource(
        RepositorySnapshot snapshot,
        ValidatedPolicy policy,
        Dictionary<string, object?> source,
        ProtectedSource protectedSource,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (!source.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(
                ["id", "path", "source_sha256", "entries"]))
        {
            findings.Add(new RuleFinding(
                BackfillPath,
                $"source {protectedSource.Id} keys are not canonical"));
        }

        source.TryGetValue("path", out var rawPath);
        if (rawPath is not string sourcePath
            || !RepoPath.TryCreate(sourcePath, out var sourceRepoPath)
            || !policy.GovernanceDocuments.Contains(sourceRepoPath))
        {
            findings.Add(new RuleFinding(
                BackfillPath,
                $"protected source {protectedSource.Id} path changed"));
            return;
        }

        if (!snapshot.TryGetFile(sourcePath, out var sourceFile))
        {
            findings.Add(new RuleFinding(BackfillPath, $"source path is dangling: {sourcePath}"));
            return;
        }

        source.TryGetValue("source_sha256", out var declaredHash);
        var actualHash = Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(sourceFile.Text)));
        if (declaredHash is not string sourceHash
            || !string.Equals(sourceHash, protectedSource.Sha256, StringComparison.Ordinal)
            || !string.Equals(actualHash, protectedSource.Sha256, StringComparison.Ordinal))
        {
            findings.Add(new RuleFinding(
                BackfillPath,
                $"protected source digest mismatch: {protectedSource.Id}"));
        }

        source.TryGetValue("entries", out var rawEntries);
        var entries = rawEntries as List<object?>;
        if (entries is null || entries.Count == 0)
        {
            findings.Add(new RuleFinding(
                BackfillPath,
                $"source {sourcePath} has no entries"));
            entries = [];
        }

        var expected = protectedSource.Entries.ToDictionary(static entry => entry.Anchor, StringComparer.Ordinal);
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var lines = SplitLinesKeepingLf(sourceFile.Text);
        foreach (var rawEntry in entries)
        {
            if (rawEntry is not Dictionary<string, object?> entry)
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"source {sourcePath} has a non-mapping entry"));
                continue;
            }

            if (!entry.TryGetValue("anchor", out var rawAnchor) || rawAnchor is not string anchor)
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"source {sourcePath} entry needs an anchor"));
                continue;
            }

            if (!seen.Add(anchor))
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"duplicate source anchor: {sourcePath}#{anchor}"));
            }

            entry.TryGetValue("source_line", out var rawLine);
            entry.TryGetValue("line_sha256", out var rawLineHash);
            if (rawLine is not int sourceLine
                || sourceLine < 1
                || rawLineHash is not string lineHash
                || !HashPattern.IsMatch(lineHash))
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"source {sourcePath}#{anchor} has invalid line anchor"));
            }
            else if (sourceLine > lines.Length || !lines[sourceLine - 1].EndsWith('\n'))
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"source line is absent or lacks LF: {sourcePath}#{anchor}"));
            }
            else
            {
                var actualLineHash = Convert.ToHexStringLower(
                    SHA256.HashData(Encoding.UTF8.GetBytes(lines[sourceLine - 1])));
                expected.TryGetValue(anchor, out var protectedEntry);
                if (!string.Equals(actualLineHash, lineHash, StringComparison.Ordinal)
                    || protectedEntry is not null
                    && (sourceLine != protectedEntry.Line || !string.Equals(
                        lineHash,
                        protectedEntry.Sha256,
                        StringComparison.Ordinal)))
                {
                    findings.Add(new RuleFinding(
                        BackfillPath,
                        $"protected line anchor mismatch: {sourcePath}#{anchor}"));
                }
            }

            entry.TryGetValue("disposition", out var disposition);
            ValidateDisposition(snapshot, disposition, sourcePath, anchor, findings);
        }

        foreach (var anchor in expected.Keys.Where(anchor => !seen.Contains(anchor)).Order(StringComparer.Ordinal))
        {
            findings.Add(new RuleFinding(
                BackfillPath,
                $"protected source {protectedSource.Id} missing disposition: {anchor}"));
        }
    }

    private static void ValidateDisposition(
        RepositorySnapshot snapshot,
        object? disposition,
        string sourcePath,
        string anchor,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (disposition is not string gidText)
        {
            findings.Add(new RuleFinding(
                BackfillPath,
                $"source {sourcePath}#{anchor} needs a disposition"));
            return;
        }

        if (!Gid.TryParse(gidText, out var gid) || !snapshot.TryGetFile(gid.Path.Value, out _))
        {
            findings.Add(new RuleFinding(
                BackfillPath,
                $"dangling disposition {gidText}: canonical target is absent"));
        }
    }

    private static void ValidateTicketIndex(
        RepositorySnapshot snapshot,
        object? rawTicketIndex,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (rawTicketIndex is not List<object?> ticketIndex)
        {
            findings.Add(new RuleFinding(BackfillPath, "ticket_index must be a list"));
            return;
        }

        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var rawTicket in ticketIndex)
        {
            if (rawTicket is not Dictionary<string, object?> ticket
                || !ticket.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(["case_id", "gid"]))
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    "ticket_index entry must contain only case_id and gid"));
                continue;
            }

            ticket.TryGetValue("case_id", out var rawCaseId);
            ticket.TryGetValue("gid", out var rawGid);
            if (rawCaseId is not string caseId
                || !CasePattern.IsMatch(caseId)
                || rawGid is not string gidText)
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    "ticket_index entry has an invalid case_id or gid"));
                continue;
            }

            if (!seen.Add(caseId))
            {
                findings.Add(new RuleFinding(BackfillPath, $"duplicate ticket case: {caseId}"));
            }

            if (!Gid.TryParse(gidText, out var gid) || !snapshot.TryGetFile(gid.Path.Value, out _))
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"dangling ticket {caseId}: ticket target is absent"));
            }
        }

        var missing = ProtectedCaseIds.Where(caseId => !seen.Contains(caseId)).Order(StringComparer.Ordinal).ToArray();
        if (missing.Length > 0)
        {
            findings.Add(new RuleFinding(
                BackfillPath,
                "protected ticket cases are missing: " + string.Join(", ", missing)));
        }
    }

    private static ImmutableArray<string> SplitLinesKeepingLf(string text)
    {
        var lines = ImmutableArray.CreateBuilder<string>();
        var start = 0;
        for (var index = 0; index < text.Length; index++)
        {
            if (text[index] != '\n')
            {
                continue;
            }

            lines.Add(text[start..(index + 1)]);
            start = index + 1;
        }

        if (start < text.Length)
        {
            lines.Add(text[start..]);
        }

        return lines.ToImmutable();
    }

    private sealed record ProtectedEntry(string Anchor, int Line, string Sha256);

    private sealed record ProtectedSource(
        string Id,
        string Sha256,
        ImmutableArray<ProtectedEntry> Entries);
}
