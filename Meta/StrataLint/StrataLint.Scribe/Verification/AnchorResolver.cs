using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class AnchorResolver
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static AnchorResolution Resolve(Anchor anchor, string repositoryRoot)
    {
        ArgumentNullException.ThrowIfNull(anchor);
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);

        var matches = AnchorCatalogDefinitions.All
            .Where(item => string.Equals(
                item.Anchor.CanonicalString,
                anchor.CanonicalString,
                StringComparison.Ordinal))
            .ToArray();
        if (matches.Length == 0)
        {
            return new AnchorResolution.Unregistered(anchor);
        }

        if (matches.Length > 1)
        {
            return new AnchorResolution.Ambiguous(anchor, "canonical id maps to multiple definitions");
        }

        var definition = matches[0];
        return definition.Target is MathlibSymbolTarget mathlib
            ? ResolveMathlib(definition, mathlib, repositoryRoot)
            : ResolveLocal(definition, repositoryRoot);
    }

    private static AnchorResolution ResolveLocal(
        AnchorDefinition definition,
        string repositoryRoot)
    {
        if (definition.Anchor is GictAnchor gict
            && !string.Equals(
                definition.Target.Selector.HeadingPrefix,
                TheoryAnchorManifest.HeadingPrefix(gict),
                StringComparison.Ordinal))
        {
            return new AnchorResolution.InvalidTarget(
                definition.Anchor,
                "structural selector heading does not match the typed GICT division");
        }

        if (definition.Target is TheoryNodeTarget
            && !TheorySourceMatchesBackfill(
                definition.Target,
                repositoryRoot,
                out var bindingReason))
        {
            return new AnchorResolution.InvalidTarget(definition.Anchor, bindingReason);
        }

        var path = Path.Combine(repositoryRoot, definition.Target.SourcePath);
        if (!File.Exists(path))
        {
            return new AnchorResolution.InvalidTarget(
                definition.Anchor,
                "registered local source is missing: " + definition.Target.SourcePath);
        }

        byte[] bytes;
        string text;
        try
        {
            bytes = File.ReadAllBytes(path);
            text = StrictUtf8.GetString(bytes);
        }
        catch (Exception exception) when (exception is IOException or DecoderFallbackException)
        {
            return new AnchorResolution.InvalidTarget(
                definition.Anchor,
                "registered local source is unreadable strict UTF-8: " + exception.Message);
        }

        var actualHash = Convert.ToHexStringLower(SHA256.HashData(bytes));
        if (!string.Equals(
                actualHash,
                definition.Target.ExpectedSha256,
                StringComparison.Ordinal))
        {
            return new AnchorResolution.InvalidTarget(
                definition.Anchor,
                "registered local source SHA-256 does not match the frozen receipt");
        }

        var selector = definition.Target.Selector;
        var matches = CountSelectorMatches(text, selector);
        if (matches == 0)
        {
            return new AnchorResolution.InvalidTarget(
                definition.Anchor,
                "registered structural selector has no target");
        }

        if (matches > 1)
        {
            return new AnchorResolution.Ambiguous(
                definition.Anchor,
                "registered structural selector matches multiple targets");
        }

        var receipt = Receipt(definition.Target, actualHash);
        return definition.Status switch
        {
            AnchorRegistrationStatus.Resolved =>
                new AnchorResolution.Resolved(definition.Target, receipt),
            AnchorRegistrationStatus.RegisteredOpen =>
                new AnchorResolution.RegisteredOpen(
                    definition.Target,
                    definition.CaseId!,
                    definition.OpenReason!,
                    receipt),
            _ => throw new InvalidOperationException("Unknown anchor registration status."),
        };
    }

    private static AnchorResolution ResolveMathlib(
        AnchorDefinition definition,
        MathlibSymbolTarget target,
        string repositoryRoot)
    {
        var path = Path.Combine(repositoryRoot, target.SourcePath);
        if (!File.Exists(path))
        {
            return new AnchorResolution.InvalidTarget(
                definition.Anchor,
                "lake manifest is missing");
        }

        byte[] bytes;
        try
        {
            bytes = File.ReadAllBytes(path);
            using var document = JsonDocument.Parse(bytes);
            if (document.RootElement.ValueKind != JsonValueKind.Object
                || !document.RootElement.TryGetProperty("packages", out var packages)
                || packages.ValueKind != JsonValueKind.Array)
            {
                return new AnchorResolution.InvalidTarget(
                    definition.Anchor,
                    "lake manifest packages are malformed");
            }

            var revisions = packages.EnumerateArray()
                .Where(static package =>
                    package.ValueKind == JsonValueKind.Object
                    && package.TryGetProperty("name", out var name)
                    && name.ValueKind == JsonValueKind.String
                    && name.GetString() == "mathlib")
                .Select(static package =>
                    package.TryGetProperty("rev", out var revision)
                    && revision.ValueKind == JsonValueKind.String
                        ? revision.GetString()
                        : null)
                .ToArray();
            if (revisions.Length == 0)
            {
                return new AnchorResolution.InvalidTarget(
                    definition.Anchor,
                    "lake manifest has no mathlib package");
            }

            if (revisions.Length > 1)
            {
                return new AnchorResolution.Ambiguous(
                    definition.Anchor,
                    "lake manifest has multiple mathlib packages");
            }

            if (!string.Equals(revisions[0], target.SourceRevision, StringComparison.Ordinal))
            {
                return new AnchorResolution.InvalidTarget(
                    definition.Anchor,
                    "mathlib revision does not match the registered pin");
            }
        }
        catch (Exception exception) when (exception is IOException or JsonException)
        {
            return new AnchorResolution.InvalidTarget(
                definition.Anchor,
                "lake manifest is unreadable: " + exception.Message);
        }

        var receipt = Receipt(
            target,
            Convert.ToHexStringLower(SHA256.HashData(bytes)));
        return new AnchorResolution.RegisteredOpen(
            target,
            definition.CaseId!,
            definition.OpenReason!,
            receipt);
    }

    private static AnchorResolutionReceipt Receipt(AnchorTarget target, string sourceSha256) =>
        new(
            target.SourceId,
            target.SourcePath,
            target.SourceRevision,
            sourceSha256,
            target.Selector.CanonicalString);

    private static int CountSelectorMatches(string text, StructuralSelector selector)
    {
        var contextLevel = selector.HeadingPrefix is null
            ? 0
            : AtxHeadingLevel(selector.HeadingPrefix);
        var contextMatches = selector.HeadingPrefix is null;
        var matches = 0;
        foreach (var line in text.Split('\n'))
        {
            if (selector.HeadingPrefix is not null)
            {
                var headingLevel = AtxHeadingLevel(line);
                if (headingLevel is > 0 && headingLevel <= contextLevel)
                {
                    contextMatches = headingLevel == contextLevel
                        && line.StartsWith(selector.HeadingPrefix, StringComparison.Ordinal);
                }
            }

            if (contextMatches
                && line.StartsWith(selector.LinePrefix, StringComparison.Ordinal)
                && (selector.RequiredToken is null
                    || line.Contains(selector.RequiredToken, StringComparison.Ordinal)))
            {
                matches++;
            }
        }

        return matches;
    }

    private static int AtxHeadingLevel(string line)
    {
        var level = 0;
        while (level < line.Length && level < 6 && line[level] == '#')
        {
            level++;
        }

        return level > 0 && level < line.Length && line[level] == ' ' ? level : 0;
    }

    private static bool TheorySourceMatchesBackfill(
        AnchorTarget target,
        string repositoryRoot,
        out string reason)
    {
        var path = Path.Combine(repositoryRoot, "Meta", "BACKFILL.yaml");
        if (!File.Exists(path))
        {
            reason = "BACKFILL source registry is missing";
            return false;
        }

        try
        {
            var document = BackfillInventoryLoader.Load(File.ReadAllText(path, StrictUtf8));
            if (!document.Root.TryGetValue("sources", out var rawSources)
                || rawSources is not List<object?> sources)
            {
                reason = "BACKFILL sources are malformed";
                return false;
            }

            var paths = sources
                .OfType<Dictionary<string, object?>>()
                .Where(source => string.Equals(
                    source.GetValueOrDefault("id") as string,
                    target.SourceId,
                    StringComparison.Ordinal))
                .Select(static source => source.GetValueOrDefault("path") as string)
                .ToArray();
            if (paths.Length != 1
                || !string.Equals(paths[0], target.SourcePath, StringComparison.Ordinal))
            {
                reason = $"BACKFILL source {target.SourceId} does not bind {target.SourcePath}";
                return false;
            }

            reason = string.Empty;
            return true;
        }
        catch (Exception exception) when (exception is IOException or FormatException)
        {
            reason = "BACKFILL source registry is unreadable: " + exception.Message;
            return false;
        }
    }
}
