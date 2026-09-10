using System.Reflection;
using StrataLint.Engine;
using StrataLint.Scribe;
using StrataLint.Scribe.Documents;

namespace StrataLint.Cli;

internal sealed class MaterializedRepositorySnapshot : IDisposable
{
    private MaterializedRepositorySnapshot(string root) => Root = root;

    internal string Root { get; }

    internal static MaterializedRepositorySnapshot Create(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-snapshot-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);
        try
        {
            foreach (var (path, file) in snapshot.Files
                .OrderBy(static item => item.Key.Value, StringComparer.Ordinal))
            {
                var destination = Path.Combine(
                    root,
                    path.Value.Replace('/', Path.DirectorySeparatorChar));
                Directory.CreateDirectory(Path.GetDirectoryName(destination)
                    ?? throw new InvalidOperationException("snapshot path has no parent directory"));
                File.WriteAllBytes(destination, file.RawBytes.AsSpan());
            }

            return new MaterializedRepositorySnapshot(root);
        }
        catch
        {
            Directory.Delete(root, recursive: true);
            throw;
        }
    }

    public void Dispose() => Directory.Delete(Root, recursive: true);
}

internal interface IScribeEmissionVerifier
{
    VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes = null,
        FrozenStateCatalog? frozenState = null,
        FrozenStatementIndex? frozenStatements = null);
}

internal sealed class ProductionScribeEmissionVerifier : IScribeEmissionVerifier
{
    private readonly Func<string, LeanAxiomReport, FrozenStateCatalog?, FrozenStatementIndex?, VerifiedScribeEmissions> verifyMaterialized;

    internal ProductionScribeEmissionVerifier()
        : this(typeof(DocumentAssembly).Assembly)
    {
    }

    internal ProductionScribeEmissionVerifier(Assembly documentsAssembly)
        : this((root, report, frozenState, frozenStatements) =>
            VerifyMaterialized(documentsAssembly, root, report, frozenState, frozenStatements))
    {
    }

    internal ProductionScribeEmissionVerifier(
        Func<string, LeanAxiomReport, FrozenStateCatalog?, FrozenStatementIndex?, VerifiedScribeEmissions> verifyMaterialized) =>
        this.verifyMaterialized = verifyMaterialized
            ?? throw new ArgumentNullException(nameof(verifyMaterialized));

    public VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes = null,
        FrozenStateCatalog? frozenState = null,
        FrozenStatementIndex? frozenStatements = null)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(report);
        using var materialized = MaterializedRepositorySnapshot.Create(snapshot);
        if (StatementProjectionReconciliation.IsAffectedBy(changes))
        {
            StatementProjectionReconciliation.Verify(
                materialized.Root,
                DeclarationCatalog.Create(report));
        }
        return verifyMaterialized(materialized.Root, report, frozenState, frozenStatements);
    }

    private static VerifiedScribeEmissions VerifyMaterialized(
        Assembly documentsAssembly,
        string repositoryRoot,
        LeanAxiomReport report,
        FrozenStateCatalog? frozenState,
        FrozenStatementIndex? frozenStatements)
    {
        var error = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        return ScribeEmitter.Verify(documentsAssembly, repositoryRoot, error, report,
                frozenState, frozenStatements)
            ?? throw new InvalidOperationException(
                "Scribe emission verification failed: " + error.ToString().Trim());
    }

}
