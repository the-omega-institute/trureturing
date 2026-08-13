using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class ValuesKernelBindingValidator
{
    internal const string RelativePath = "Golden/values-kernels.toml";

    private static readonly ImmutableHashSet<string> RequiredAxioms =
        ImmutableHashSet.Create(StringComparer.Ordinal, "Classical.choice", "Quot.sound", "propext");

    [GeneratedRegex("^[0-9a-f]{64}$", RegexOptions.CultureInvariant)]
    private static partial Regex Sha256Pattern();

    internal static ImmutableArray<RuleFinding> Validate(string text, LeanAxiomReport report)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        ImmutableArray<ValueBinding> bindings;
        try
        {
            bindings = Parse(text);
        }
        catch (FormatException exception)
        {
            findings.Add(new RuleFinding(RelativePath, exception.Message));
            return findings.ToImmutable();
        }

        foreach (var binding in bindings)
        {
            Validate(binding, report, findings);
        }

        return findings.ToImmutable();
    }

    internal static int CountBindings(string text) => Parse(text).Length;

    private static void Validate(
        ValueBinding binding,
        LeanAxiomReport report,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (!Gid.TryParse(binding.LeanGid, out var gid)
            || gid.ToTarget() is not Target.Formal { Declaration: { } declarationName })
        {
            findings.Add(Finding(binding, "is not a canonical Lean declaration GID"));
            return;
        }

        if (!report.Files.TryGetValue(gid.Path, out var module))
        {
            findings.Add(Finding(binding, $"GID matched 0 declarations; candidate report has no module {gid.Path.Value}"));
            return;
        }

        if (!string.IsNullOrEmpty(module.Error))
        {
            findings.Add(Finding(binding, $"candidate report failed for {gid.Path.Value}: {module.Error}"));
            return;
        }

        var suffix = "." + declarationName;
        var matches = module.Declarations
            .Where(candidate =>
                string.Equals(candidate.Name, declarationName, StringComparison.Ordinal)
                || candidate.Name.EndsWith(suffix, StringComparison.Ordinal))
            .ToImmutableArray();
        if (matches.Length != 1)
        {
            findings.Add(Finding(binding, $"GID matched {matches.Length} declarations in candidate report"));
            return;
        }

        var declaration = matches[0];
        if (!string.Equals(declaration.Kind, "def", StringComparison.Ordinal))
        {
            findings.Add(Finding(binding, $"expected kind=def, found {declaration.Kind}"));
        }

        var actualAxioms = declaration.Axioms.ToImmutableHashSet(StringComparer.Ordinal);
        if (!actualAxioms.SetEquals(RequiredAxioms))
        {
            findings.Add(Finding(
                binding,
                "axiom closure mismatch: expected [Classical.choice, Quot.sound, propext], found ["
                + string.Join(", ", actualAxioms.Order(StringComparer.Ordinal))
                + "]"));
        }

        var statement = CanonicalStatementWriter.DeclarationStatementIds(
            gid.Path,
            new LeanFileReport([], [declaration]));
        if (statement.Length != 1)
        {
            findings.Add(Finding(binding, "declaration is excluded from canonical statement encoding"));
            return;
        }

        var actualSha256 = statement[0].StatementId.Value["sha256:".Length..];
        if (!Sha256Pattern().IsMatch(binding.StatementSha256)
            || !CryptographicOperations.FixedTimeEquals(
                Convert.FromHexString(binding.StatementSha256),
                Convert.FromHexString(actualSha256)))
        {
            findings.Add(Finding(
                binding,
                $"statement SHA-256 mismatch: expected {binding.StatementSha256}, recomputed {actualSha256}"));
        }
    }

    private static RuleFinding Finding(ValueBinding binding, string reason) =>
        new(RelativePath, $"values constant {binding.Id} ({binding.LeanGid}): {reason}");

    private static ImmutableArray<ValueBinding> Parse(string text)
    {
        ArgumentNullException.ThrowIfNull(text);
        var bindings = ImmutableArray.CreateBuilder<ValueBinding>();
        Dictionary<string, string>? current = null;
        var sawSchema = false;
        foreach (var rawLine in text.Split('\n'))
        {
            var line = rawLine.Trim();
            if (line.Length == 0 || line.StartsWith('#'))
            {
                continue;
            }

            if (line == "schema_version = 1")
            {
                if (sawSchema || current is not null)
                {
                    throw new FormatException("values kernel binding schema_version is duplicated or misplaced");
                }

                sawSchema = true;
                continue;
            }

            if (line == "[[constants]]")
            {
                if (current is not null)
                {
                    bindings.Add(Binding(current, bindings.Count));
                }

                current = new Dictionary<string, string>(StringComparer.Ordinal);
                continue;
            }

            if (current is null)
            {
                throw new FormatException("values kernel binding data must be inside [[constants]]");
            }

            foreach (var key in new[] { "id", "lean_gid", "lean_statement_sha256" })
            {
                var prefix = key + " = ";
                if (!line.StartsWith(prefix, StringComparison.Ordinal))
                {
                    continue;
                }

                var value = line[prefix.Length..];
                if (value.Length < 2 || value[0] != '"' || value[^1] != '"'
                    || value[1..^1].Contains('"', StringComparison.Ordinal)
                    || !current.TryAdd(key, value[1..^1]))
                {
                    throw new FormatException($"values constant #{bindings.Count + 1} has malformed or duplicate {key}");
                }

                break;
            }
        }

        if (!sawSchema)
        {
            throw new FormatException("values kernel binding schema_version must be 1");
        }

        if (current is not null)
        {
            bindings.Add(Binding(current, bindings.Count));
        }

        if (bindings.Count == 0)
        {
            throw new FormatException("values kernel binding data contains no constants");
        }

        return bindings.ToImmutable();
    }

    private static ValueBinding Binding(IReadOnlyDictionary<string, string> fields, int index)
    {
        foreach (var key in new[] { "id", "lean_gid", "lean_statement_sha256" })
        {
            if (!fields.TryGetValue(key, out var value) || string.IsNullOrWhiteSpace(value))
            {
                throw new FormatException($"values constant #{index + 1} is missing {key}");
            }
        }

        return new ValueBinding(
            fields["id"],
            fields["lean_gid"],
            fields["lean_statement_sha256"]);
    }

    private sealed record ValueBinding(string Id, string LeanGid, string StatementSha256);
}
