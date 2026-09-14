using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Serialization;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class StatementProjectionReconciliation
{
    private const string FixtureRoot = "Golden/Projection/";

    internal static bool IsAffectedBy(RepositorySnapshot snapshot, RawChangeSet? changes)
    {
        if (changes is null)
        {
            return true;
        }

        var implementation = RegisteredImplementationInputs(snapshot, changes);
        return changes.Paths.Any(path =>
            path.Value.StartsWith(FixtureRoot, StringComparison.Ordinal)
                && path.Value.EndsWith(".json", StringComparison.Ordinal)
            || implementation.Contains(path.Value));
    }

    public static void Verify(string repositoryRoot, DeclarationCatalog catalog)
    {
        ArgumentNullException.ThrowIfNull(catalog);
        var findings = Check(repositoryRoot, catalog);
        if (!findings.IsEmpty)
        {
            throw new InvalidDataException(
                "Pinned statement-v1 projection fixtures do not match the live canonical raw Lean report."
                + Environment.NewLine
                + string.Join(Environment.NewLine, findings));
        }
    }

    public static ImmutableArray<string> Check(string repositoryRoot, DeclarationCatalog catalog)
    {
        ArgumentNullException.ThrowIfNull(catalog);
        var expected = StatementProjectionFixtureLoader.LoadStatements(repositoryRoot).Values
            .SelectMany(static module => module);
        var findings = ImmutableArray.CreateBuilder<string>();

        foreach (var item in expected.OrderBy(static item => item.SourcePath.Value, StringComparer.Ordinal)
                     .ThenBy(static item => item.Name, StringComparer.Ordinal))
        {
            var live = catalog.DeclarationsFor(item.SourcePath, item.Name);
            var identity = $"{item.Name} ({item.SourcePath.Value})";
            if (live.IsEmpty)
            {
                findings.Add($"pinned statement projection is missing from live report: {identity}");
            }
            else if (live.Length != 1)
            {
                findings.Add(
                    $"pinned statement projection is ambiguous in live report: {identity} ({live.Length} declarations)");
            }
            else if (!StringComparer.Ordinal.Equals(item.Kind, live[0].Kind)
                     || !StringComparer.Ordinal.Equals(item.Type, live[0].LoadTypeRepresentation()))
            {
                findings.Add($"pinned statement projection differs from live report: {identity}");
            }
        }

        return findings.ToImmutable();
    }

    private const string ProducerRegistration = "Meta/ReportProducers/scribe-content.json";
    private sealed record ProducerScope(string Schema, string[] Scripts, string[] Projects, string[] Materials);
    private static readonly JsonSerializerOptions Options = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
        AllowDuplicateProperties = false,
        RespectRequiredConstructorParameters = true,
    };

    private static IReadOnlySet<string> RegisteredImplementationInputs(RepositorySnapshot snapshot, RawChangeSet changes)
    {
        if (!snapshot.TryGetFile(ProducerRegistration, out var file))
            throw new InvalidDataException($"missing producer registration: {ProducerRegistration}");
        try
        {
            var scope = JsonSerializer.Deserialize<ProducerScope>(file.Text, Options);
            if (scope is null || scope.Schema != "report-producer-scope-v1"
                || scope.Scripts is null || scope.Projects is null || scope.Materials is null)
                throw new InvalidDataException($"invalid producer registration: {ProducerRegistration}");
            var paths = scope.Scripts.Concat(scope.Projects).Concat(scope.Materials).ToArray();
            EngineeringProjectRegistry.ValidateInputPaths(paths, ProducerRegistration);
            if (scope.Projects.Any(path => !path.EndsWith(".csproj", StringComparison.Ordinal))
                || scope.Scripts.Any(path => Path.GetExtension(path) is not (".sh" or ".py" or ".lean")))
                throw new InvalidDataException($"invalid project or script registration: {ProducerRegistration}");
            foreach (var path in paths)
                if (!snapshot.TryGetFile(path, out _))
                    throw new InvalidDataException($"required producer registration input is absent: {ProducerRegistration}: {path}");
            var registry = EngineeringProjectRegistry.Read(snapshot);
            // Changed paths are included to consume declared globs for removed/renamed sources.
            var sources = registry.ProjectInputs(scope.Projects,
                snapshot.Files.Keys.Select(path => path.Value), changes.Paths.Select(path => path.Value));
            return paths.Concat(sources).Append(ProducerRegistration).Append(EngineeringProjectRegistry.ManifestPath)
                .ToHashSet(StringComparer.Ordinal);
        }
        catch (JsonException exception)
        {
            throw new InvalidDataException($"invalid producer registration: {ProducerRegistration}: {exception.Message}", exception);
        }
    }
}
