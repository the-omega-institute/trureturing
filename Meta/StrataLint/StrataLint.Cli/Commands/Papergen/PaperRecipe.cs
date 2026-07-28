using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record PaperRecipe(
    string Id,
    ImmutableArray<Gid> Declarations,
    ImmutableArray<Gid> Blueprint,
    ImmutableArray<Gid> Evidence,
    ImmutableArray<string> NarrativeOrder,
    string Venue);

internal abstract record PaperRecipeLoadOutcome
{
    internal sealed record Loaded(PaperRecipe Recipe, ImmutableArray<byte> Bytes) : PaperRecipeLoadOutcome;

    internal sealed record Invalid(string Message) : PaperRecipeLoadOutcome;
}

internal static class PaperRecipeLoader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    private static readonly string[] SchemaKeys =
        ["blueprint", "decls", "evidence", "id", "narrative_order", "venue"];

    internal static PaperRecipeLoadOutcome Load(ImmutableArray<byte> bytes, string fileName)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(fileName);
        if (bytes.IsDefault)
        {
            return Invalid("recipe bytes are unavailable");
        }

        if (bytes.AsSpan().StartsWith(Encoding.UTF8.Preamble))
        {
            return Invalid("recipe must not contain a UTF-8 BOM");
        }

        string text;
        try
        {
            text = StrictUtf8.GetString(bytes.AsSpan());
        }
        catch (DecoderFallbackException)
        {
            return Invalid("recipe must be strict UTF-8");
        }

        Dictionary<string, object?> mapping;
        try
        {
            var canonical = StructuredCanonicalWriter.WriteYaml(text);
            if (!canonical.AsSpan().SequenceEqual(bytes.AsSpan()))
            {
                return Invalid("recipe does not have canonical bytes");
            }

            mapping = (Dictionary<string, object?>)YamlSubsetParser.Parse(text);
        }
        catch (FormatException exception)
        {
            return Invalid($"recipe YAML is invalid: {exception.Message}");
        }

        if (!mapping.Keys.SequenceEqual(SchemaKeys, StringComparer.Ordinal))
        {
            return Invalid("recipe schema keys must be exactly blueprint, decls, evidence, id, narrative_order, venue");
        }

        if (mapping["id"] is not string id || id.Length == 0)
        {
            return Invalid("id must be non-empty");
        }

        var expectedId = Path.GetFileNameWithoutExtension(fileName);
        if (!string.Equals(Path.GetExtension(fileName), ".yaml", StringComparison.Ordinal)
            || !string.Equals(id, expectedId, StringComparison.Ordinal))
        {
            return Invalid($"recipe id {id} does not match filename {fileName}");
        }

        if (!Gid.TryParse($"D5/P/{id}", out var paperGid)
            || paperGid.ToTarget() is not Target.Paper { Frozen: false })
        {
            return Invalid("id must be a canonical A11 paper id");
        }

        var declarations = Gids(mapping["decls"], "decls", static target =>
            target is Target.Formal { Declaration: not null }, "formal declaration GID");
        if (declarations.Error is not null) return Invalid(declarations.Error);

        var blueprint = Gids(mapping["blueprint"], "blueprint", static target =>
            target is Target.Blueprint, "Blueprint GID");
        if (blueprint.Error is not null) return Invalid(blueprint.Error);

        var evidence = Gids(mapping["evidence"], "evidence", static target =>
            target is Target.Evidence, "Evidence GID");
        if (evidence.Error is not null) return Invalid(evidence.Error);

        var narrative = Strings(mapping["narrative_order"], "narrative_order", requireNonEmpty: true);
        if (narrative.Error is not null) return Invalid(narrative.Error);

        if (mapping["venue"] is not string venue || string.IsNullOrWhiteSpace(venue))
        {
            return Invalid("venue must be non-empty");
        }

        return new PaperRecipeLoadOutcome.Loaded(
            new PaperRecipe(
                id,
                declarations.Values,
                blueprint.Values,
                evidence.Values,
                narrative.Values,
                venue),
            bytes);
    }

    private static (ImmutableArray<Gid> Values, string? Error) Gids(
        object? raw,
        string key,
        Func<Target, bool> accepts,
        string expected)
    {
        var strings = Strings(raw, key, requireNonEmpty: false);
        if (strings.Error is not null) return ([], strings.Error);

        var gids = ImmutableArray.CreateBuilder<Gid>();
        foreach (var value in strings.Values)
        {
            if (!Gid.TryParse(value, out var gid) || !accepts(gid.ToTarget()))
            {
                return ([], $"{key} entry must be a canonical {expected}: {value}");
            }

            gids.Add(gid);
        }

        return (gids.ToImmutable(), null);
    }

    private static (ImmutableArray<string> Values, string? Error) Strings(
        object? raw,
        string key,
        bool requireNonEmpty)
    {
        if (raw is not List<object?> list)
        {
            return ([], $"{key} must be a sequence");
        }

        if (requireNonEmpty && list.Count == 0)
        {
            return ([], $"{key} must be a non-empty sequence");
        }

        var values = ImmutableArray.CreateBuilder<string>();
        foreach (var item in list)
        {
            if (item is not string value || string.IsNullOrWhiteSpace(value))
            {
                return ([], $"{key} entries must be non-empty strings");
            }

            values.Add(value);
        }

        return (values.ToImmutable(), null);
    }

    private static PaperRecipeLoadOutcome.Invalid Invalid(string message) => new(message);
}

internal abstract record PaperRecipeValidationOutcome
{
    internal sealed record Valid(PaperRecipe Recipe, string RecipeSha256) : PaperRecipeValidationOutcome;

    internal sealed record Invalid(string Message) : PaperRecipeValidationOutcome;
}

internal static class PaperRecipeValidator
{
    internal static PaperRecipeValidationOutcome Validate(string repositoryRoot, string id)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentException.ThrowIfNullOrWhiteSpace(id);
        if (!Gid.TryParse($"D5/P/{id}", out var paperGid)
            || paperGid.ToTarget() is not Target.Paper { Frozen: false })
        {
            return Invalid("paper id must be canonical A11");
        }

        var recipePath = Path.Combine(repositoryRoot, paperGid.Path.Value);
        if (!File.Exists(recipePath))
        {
            return Invalid($"recipe file is missing: {paperGid.Path.Value}");
        }

        var bytes = ImmutableArray.CreateRange(File.ReadAllBytes(recipePath));
        var loaded = PaperRecipeLoader.Load(bytes, Path.GetFileName(recipePath));
        if (loaded is PaperRecipeLoadOutcome.Invalid invalid)
        {
            return Invalid(invalid.Message);
        }

        var material = (PaperRecipeLoadOutcome.Loaded)loaded;
        foreach (var gid in material.Recipe.Declarations
            .Concat(material.Recipe.Blueprint)
            .Concat(material.Recipe.Evidence))
        {
            var targetPath = Path.Combine(repositoryRoot, gid.Path.Value);
            if (!File.Exists(targetPath))
            {
                return Invalid($"GID {gid.Value} target file is missing: {gid.Path.Value}");
            }

            if (gid.ToTarget() is Target.Formal { Declaration: { } declaration }
                && !LeanDeclarationScanner.Contains(
                    File.ReadAllText(targetPath, Encoding.UTF8),
                    gid.Path.Value[..^".lean".Length].Replace('/', '.'),
                    declaration))
            {
                return Invalid($"GID {gid.Value} Lean declaration is missing from {gid.Path.Value}");
            }
        }

        var hash = Convert.ToHexStringLower(SHA256.HashData(material.Bytes.AsSpan()));
        return new PaperRecipeValidationOutcome.Valid(material.Recipe, "sha256:" + hash);
    }

    private static PaperRecipeValidationOutcome.Invalid Invalid(string message) => new(message);
}

internal static class LeanDeclarationScanner
{
    private static readonly Regex NamespacePattern = new(
        "^namespace[ \\t]+(?<name>[A-Za-z_][A-Za-z0-9_.]*)[ \\t]*$",
        RegexOptions.CultureInvariant);

    private static readonly Regex ScopePattern = new(
        "^(?:section(?:[ \\t]+[A-Za-z_][A-Za-z0-9_]*)?|mutual)[ \\t]*$",
        RegexOptions.CultureInvariant);

    private static readonly Regex EndPattern = new(
        "^end(?:[ \\t]+[A-Za-z_][A-Za-z0-9_.]*)?[ \\t]*$",
        RegexOptions.CultureInvariant);

    internal static bool Contains(string source, string expectedNamespace, string declaration)
    {
        var visible = RemoveCommentsAndStrings(source);
        var declarationPattern = "^[ \\t]*(?:@\\[[^]\\r\\n]+\\][ \\t]*)*"
            + "(?:(?:noncomputable|unsafe|partial)[ \\t]+)*"
            + "(?:theorem|lemma|def|abbrev|opaque|axiom|instance|structure|class|inductive)[ \\t]+"
            + Regex.Escape(declaration)
            + "(?=[ \\t\\r\\n:({\\[])";
        var scopes = new List<string?>();
        foreach (var line in visible.Split('\n'))
        {
            var content = line.Trim();
            var namespaceMatch = NamespacePattern.Match(content);
            if (namespaceMatch.Success)
            {
                scopes.Add(namespaceMatch.Groups["name"].Value);
                continue;
            }

            if (ScopePattern.IsMatch(content))
            {
                scopes.Add(null);
                continue;
            }

            if (EndPattern.IsMatch(content))
            {
                if (scopes.Count > 0) scopes.RemoveAt(scopes.Count - 1);
                continue;
            }

            var currentNamespace = string.Join('.', scopes.OfType<string>());
            if (string.Equals(currentNamespace, expectedNamespace, StringComparison.Ordinal)
                && Regex.IsMatch(line, declarationPattern, RegexOptions.CultureInvariant))
            {
                return true;
            }
        }

        return false;
    }

    private static string RemoveCommentsAndStrings(string source)
    {
        var result = source.ToCharArray();
        var blockDepth = 0;
        var lineComment = false;
        var inString = false;
        var escaped = false;
        for (var index = 0; index < source.Length; index++)
        {
            var current = source[index];
            var next = index + 1 < source.Length ? source[index + 1] : '\0';
            if (lineComment)
            {
                if (current == '\n') lineComment = false;
                else result[index] = ' ';
                continue;
            }

            if (blockDepth > 0)
            {
                if (current == '/' && next == '-')
                {
                    result[index++] = ' ';
                    result[index] = ' ';
                    blockDepth++;
                }
                else if (current == '-' && next == '/')
                {
                    result[index++] = ' ';
                    result[index] = ' ';
                    blockDepth--;
                }
                else if (current != '\n')
                {
                    result[index] = ' ';
                }

                continue;
            }

            if (inString)
            {
                if (current != '\n') result[index] = ' ';
                if (current == '"' && !escaped) inString = false;
                escaped = current == '\\' && !escaped;
                if (current != '\\') escaped = false;
                continue;
            }

            if (current == '-' && next == '-')
            {
                result[index++] = ' ';
                result[index] = ' ';
                lineComment = true;
            }
            else if (current == '/' && next == '-')
            {
                result[index++] = ' ';
                result[index] = ' ';
                blockDepth = 1;
            }
            else if (current == '"')
            {
                result[index] = ' ';
                inString = true;
            }
        }

        return new string(result);
    }
}
