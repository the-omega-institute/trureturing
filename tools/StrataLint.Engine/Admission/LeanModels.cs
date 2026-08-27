using System.Collections.Immutable;
using Dunet;

namespace StrataLint.Engine;

public sealed record LeanDeclaration(
    string Name,
    string Kind,
    string TypeRepresentation,
    ImmutableArray<string> Axioms)
{
    private readonly string? precomputedStatementTypeAddress;
    private Lazy<string>? typeMaterial;

    internal LeanDeclaration(
        string name,
        string kind,
        string statementTypeAddress,
        string statementId,
        ImmutableArray<string> axioms,
        Func<string> loadTypeMaterial)
        : this(name, kind, string.Empty, axioms)
    {
        precomputedStatementTypeAddress = statementTypeAddress;
        PrecomputedStatementId = statementId;
        typeMaterial = new Lazy<string>(
            loadTypeMaterial ?? throw new ArgumentNullException(nameof(loadTypeMaterial)),
            LazyThreadSafetyMode.ExecutionAndPublication);
    }

    public string NameKey { get; init; } = Name;

    public bool IncludeInStatement { get; init; } = true;

    public string StatementTypeAddress =>
        TypeRepresentation.Length > 0
            ? CanonicalStatementWriter.StatementTypeAddress(TypeRepresentation)
            : precomputedStatementTypeAddress
                ?? CanonicalStatementWriter.StatementTypeAddress(TypeRepresentation);

    internal string? PrecomputedStatementId { get; init; }

    public (string Name, string Kind, string TypeRepresentation) Signature =>
        (Name, Kind, LoadTypeRepresentation());

    public string LoadTypeRepresentation()
    {
        if (TypeRepresentation.Length > 0)
        {
            return TypeRepresentation;
        }

        if (typeMaterial is null)
        {
            throw new InvalidDataException(
                $"Lean declaration {Name} has no statement material source.");
        }

        return typeMaterial.Value;
    }
}

public sealed record LeanFileReport(
    ImmutableArray<string> Imports,
    ImmutableArray<LeanDeclaration> Declarations,
    string? Error = null);

public sealed class LeanAxiomReport
{
    private LeanAxiomReport(ImmutableDictionary<RepoPath, LeanFileReport> files) => Files = files;

    public ImmutableDictionary<RepoPath, LeanFileReport> Files { get; }

    public static LeanAxiomReport Create(IReadOnlyDictionary<string, LeanFileReport> reports)
    {
        ArgumentNullException.ThrowIfNull(reports);
        var builder = ImmutableDictionary.CreateBuilder<RepoPath, LeanFileReport>();
        foreach (var (rawPath, report) in reports)
        {
            if (!RepoPath.TryCreate(rawPath, out var path) || !builder.TryAdd(path, report))
            {
                throw new ArgumentException($"Invalid or duplicate Lean report path: {rawPath}.", nameof(reports));
            }
        }

        return new LeanAxiomReport(builder.ToImmutable());
    }
}

public sealed class AcceptedLeanClosure
{
    private AcceptedLeanClosure(LeanAxiomReport report) => Report = report;

    internal LeanAxiomReport Report { get; }

    internal static AcceptedLeanClosure Create(LeanAxiomReport report) => new(report);

    // Header-only rules can run without a report; Lean-dependent rules must use Create.
    internal static AcceptedLeanClosure CreateWithoutReport() =>
        new(LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)));
}

[Union(EnableImplicitConversions = false)]
public partial record LeanValidationOutcome
{
    public partial record Accepted
    {
        internal Accepted(AcceptedLeanClosure capability) =>
            Capability = capability ?? throw new ArgumentNullException(nameof(capability));

        public AcceptedLeanClosure Capability { get; }
    }

    public partial record InfrastructureFailure(string Message);
}

public static class LeanClosureValidator
{
    public static LeanValidationOutcome Validate(RepositorySnapshot snapshot, LeanAxiomReport report)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(report);
        foreach (var (path, file) in snapshot.Files)
        {
            if (!IsManagedLean(path.Value))
            {
                continue;
            }

            if (!report.Files.TryGetValue(path, out var fileReport))
            {
                return new LeanValidationOutcome.InfrastructureFailure(
                    $"Lean environment report is missing for {path.Value}.");
            }

            if (file.RawBytes.IsDefault)
            {
                return new LeanValidationOutcome.InfrastructureFailure(
                    $"Lean source bytes are unavailable for {path.Value}.");
            }

            if (fileReport.Imports.Any(string.IsNullOrWhiteSpace)
                || fileReport.Declarations.Any(static declaration =>
                    string.IsNullOrWhiteSpace(declaration.Name)
                    || string.IsNullOrWhiteSpace(declaration.NameKey)
                    || string.IsNullOrWhiteSpace(declaration.Kind)
                    || !FrozenHashSyntax.IsSha256(declaration.StatementTypeAddress)
                    || declaration.PrecomputedStatementId is not null
                        && !FrozenHashSyntax.IsSha256(declaration.PrecomputedStatementId)
                    || declaration.Axioms.Any(string.IsNullOrWhiteSpace)))
            {
                return new LeanValidationOutcome.InfrastructureFailure(
                    $"Lean environment report is malformed for {path.Value}.");
            }

            // Axiom allowlisting is admission semantics and is stamped as SL-020 by RuleCatalog.
        }

        return new LeanValidationOutcome.Accepted(AcceptedLeanClosure.Create(report));
    }

    public static bool IsManagedLean(string path) =>
        string.Equals(path, "Trureturing.lean", StringComparison.Ordinal)
        || path.StartsWith("D5/", StringComparison.Ordinal) && path.EndsWith(".lean", StringComparison.Ordinal);
}
