using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.TestSupport;

internal sealed class FakeScribeEmissionVerifier(VerifiedScribeEmissions? verification)
    : IScribeEmissionVerifier
{
    internal int CallCount { get; private set; }

    internal List<RawChangeSet> Scopes { get; } = [];

    public VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        IReadOnlyList<StrataLint.Scribe.DocumentDefinition> definitions) =>
        Verify(snapshot, report, RawChangeSet.Create(definitions.Select(definition => definition.SourcePath)));

    public VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes,
        FrozenStateCatalog? frozenState = null,
        FrozenStatementIndex? frozenStatements = null)
    {
        if (changes is null) throw new InvalidOperationException("SCRIBE_SCOPE_REQUIRED");
        Scopes.Add(changes);
        CallCount++;
        return verification
            ?? throw new InvalidOperationException("Scribe emission verification failed: synthetic");
    }
}
