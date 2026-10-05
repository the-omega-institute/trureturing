using StrataLint.Engine;
using StrataLint.Scribe;

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
        IReadOnlyList<DocumentDefinition> definitions) =>
        throw new InvalidOperationException("Scribe verifier does not support supplied definitions.");

    VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes,
        FrozenStateCatalog? frozenState = null,
        FrozenStatementIndex? frozenStatements = null);
}

internal sealed class ProductionScribeEmissionVerifier : IScribeEmissionVerifier
{
    private readonly Func<string, IReadOnlyList<DocumentDefinition>>? definitions;
    private readonly Func<string, LeanAxiomReport, FrozenStateCatalog?, FrozenStatementIndex?, VerifiedScribeEmissions>? verifyMaterialized;

    internal ProductionScribeEmissionVerifier() { }

    internal ProductionScribeEmissionVerifier(Func<string, IReadOnlyList<DocumentDefinition>> definitions) =>
        this.definitions = definitions ?? throw new ArgumentNullException(nameof(definitions));

    internal ProductionScribeEmissionVerifier(
        Func<string, LeanAxiomReport, FrozenStateCatalog?, FrozenStatementIndex?, VerifiedScribeEmissions> verifyMaterialized) =>
        this.verifyMaterialized = verifyMaterialized ?? throw new ArgumentNullException(nameof(verifyMaterialized));

    public VerifiedScribeEmissions Verify(RepositorySnapshot snapshot, LeanAxiomReport report,
        IReadOnlyList<DocumentDefinition> definitions)
    {
        ArgumentNullException.ThrowIfNull(definitions);
        using var materialized = MaterializedRepositorySnapshot.Create(snapshot);
        return VerifyMaterialized(definitions, materialized.Root, report, null, null, scoped: false);
    }

    public VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes,
        FrozenStateCatalog? frozenState = null,
        FrozenStatementIndex? frozenStatements = null)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(report);
        if (changes is null)
            throw new InvalidOperationException("SCRIBE_SCOPE_REQUIRED: supply an explicit definition scope.");
        using var materialized = MaterializedRepositorySnapshot.Create(snapshot);
        if (StatementProjectionReconciliation.IsAffectedBy(snapshot, changes))
            StatementProjectionReconciliation.Verify(materialized.Root, DeclarationCatalog.Create(report));
        if (verifyMaterialized is not null)
            return verifyMaterialized(materialized.Root, report, frozenState, frozenStatements);
        var selection = ScribeDefinitionSelector.Select(materialized.Root, changes.Paths.Select(path => path.Value));
        if (!selection.IsSuccess)
            throw new InvalidOperationException("SCRIBE_SCOPE_INVALID: " + selection.Failure);
        IReadOnlyList<DocumentDefinition> selected;
        if (definitions is not null)
            selected = definitions(materialized.Root).Where(definition => selection.Paths.Contains(
                ScribeEmissionAttestation.DefinitionPath(definition.Document.Header.Gid.Value))).ToArray();
        else
        {
            var admission = ScribeSdkAdmission.Check(materialized.Root, selection.Paths);
            if (admission.ExitCode != 0)
            {
                var error = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
                admission.WriteFailure(error);
                throw new ScribeSdkAdmissionException(admission.ExitCode, error.ToString());
            }
            var results = ScribeScriptHost.ExecuteBatch(materialized.Root, selection.Paths);
            var failures = results.Where(result => !result.IsSuccess).ToArray();
            if (failures.Length != 0)
                throw new InvalidOperationException("Scribe emission verification failed: "
                    + string.Join("; ", failures.Select(result => result.Failure)));
            selected = results.Select(result => ScribeResourceCodec.Decode(
                ScribeResourceCodec.Encode(result.Definition!), result.Definition!.Document.Header.Gid.Value,
                result.RelativePath)).ToArray();
        }
        return VerifyMaterialized(selected, materialized.Root, report, frozenState, frozenStatements);
    }

    private static VerifiedScribeEmissions VerifyMaterialized(
        IReadOnlyList<DocumentDefinition> definitions, string root, LeanAxiomReport report,
        FrozenStateCatalog? frozenState, FrozenStatementIndex? frozenStatements, bool scoped = true)
    {
        if (definitions.Count == 0) return VerifiedScribeEmissions.Empty;
        var error = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        return ScribeEmitter.Verify(root, error, report, definitions, frozenState, frozenStatements, scoped)
            ?? throw new InvalidOperationException("Scribe emission verification failed: " + error.ToString().Trim());
    }
}
