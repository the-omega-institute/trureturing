using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text.RegularExpressions;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Engine;

internal static partial class ValuesKernelBindingValidator
{
    internal const string RelativePath = "Golden/values-kernels.toml";

    [GeneratedRegex("^[0-9a-f]{64}$", RegexOptions.CultureInvariant)]
    private static partial Regex Sha256Pattern();

    internal static ImmutableArray<RuleFinding> Validate(string text, LeanAxiomReport report)
        => Validate(text, report, changes: null);

    internal static ImmutableArray<RuleFinding> Validate(
        string text,
        LeanAxiomReport report,
        RawChangeSet? changes)
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

        var validateAll = changes is null || changes.Paths.Any(static path =>
            path.Value == RelativePath
            || FrozenLedgerDeltaPredicate.IsEnvironmentInput(path.Value)
            || FrozenLedgerDeltaPredicate.IsDeltaDefinitionInput(path.Value));
        foreach (var binding in bindings.Where(binding =>
                     validateAll || BindingInputChanged(binding, report, changes!)))
        {
            Validate(binding, report, findings);
        }

        return findings.ToImmutable();
    }

    internal static bool ReferencesChangedLeanInput(
        string text,
        LeanAxiomReport report,
        RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(report);
        ArgumentNullException.ThrowIfNull(changes);
        try
        {
            return Parse(text).Any(binding => BindingInputChanged(binding, report, changes));
        }
        catch (FormatException)
        {
            // An unchanged malformed binding belongs to the trusted base. A candidate edit to
            // this file is caught by the direct RelativePath branch before this method is called.
            return false;
        }
    }

    private static bool BindingInputChanged(
        ValueBinding binding,
        LeanAxiomReport report,
        RawChangeSet changes) =>
        Gid.TryParse(binding.LeanGid, out var gid)
        && LeanImportClosure.RepositoryPaths(report, gid.Path).Overlaps(changes.Paths);

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
        if (!actualAxioms.SetEquals(LeanAxiomFacts.StandardAxioms))
        {
            findings.Add(Finding(
                binding,
                "axiom closure mismatch: expected ["
                + string.Join(", ", LeanAxiomFacts.StandardAxioms.Order(StringComparer.Ordinal))
                + "], found ["
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
        TomlTable root;
        try
        {
            root = TomlSerializer.Deserialize<TomlTable>(text)
                ?? throw new FormatException("values kernel binding data is empty");
        }
        catch (TomlException exception)
        {
            throw new FormatException("values kernel binding data is malformed TOML", exception);
        }
        if (!root.TryGetValue("schema_version", out var version) || version is not long schema || schema != 1)
            throw new FormatException("values kernel binding schema_version must be 1");
        if (!root.TryGetValue("constants", out var rows) || rows is not TomlTableArray constants || constants.Count == 0)
            throw new FormatException("values kernel binding data contains no constants");
        var bindings = ImmutableArray.CreateBuilder<ValueBinding>();
        foreach (var row in constants)
        {
            string Field(string key) => row.TryGetValue(key, out var raw) && raw is string value
                && (key == "id" ? value.Length > 0 : !string.IsNullOrWhiteSpace(value))
                ? value : throw new FormatException($"values constant #{bindings.Count + 1} is missing {key}");
            var id = Field("id");
            _ = ValuesProjectionAddress.Encode(id);
            bindings.Add(new ValueBinding(id, Field("lean_gid"), Field("lean_statement_sha256")));
        }
        return bindings.ToImmutable();
    }

    private sealed record ValueBinding(string Id, string LeanGid, string StatementSha256);
}
