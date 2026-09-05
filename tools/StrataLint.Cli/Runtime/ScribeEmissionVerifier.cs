using StrataLint.Engine;
using StrataLint.Scribe;
using StrataLint.Scribe.Documents;

namespace StrataLint.Cli;

internal interface IScribeEmissionVerifier
{
    VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes = null);
}

internal sealed class ProductionScribeEmissionVerifier : IScribeEmissionVerifier
{
    private readonly Func<string, LeanAxiomReport, VerifiedScribeEmissions> verifyMaterialized;

    internal ProductionScribeEmissionVerifier()
        : this(VerifyMaterialized)
    {
    }

    internal ProductionScribeEmissionVerifier(
        Func<string, LeanAxiomReport, VerifiedScribeEmissions> verifyMaterialized) =>
        this.verifyMaterialized = verifyMaterialized
            ?? throw new ArgumentNullException(nameof(verifyMaterialized));

    public VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes = null)
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
        return verifyMaterialized(materialized.Root, report);
    }

    private static VerifiedScribeEmissions VerifyMaterialized(
        string repositoryRoot,
        LeanAxiomReport report)
    {
        var error = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        return ScribeEmitter.Verify(DocumentAssembly.Value, repositoryRoot, error, report)
            ?? throw new InvalidOperationException(
                "Scribe emission verification failed: " + error.ToString().Trim());
    }

}
