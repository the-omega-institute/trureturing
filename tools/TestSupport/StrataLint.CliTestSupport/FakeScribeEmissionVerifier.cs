using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.TestSupport;

internal sealed class FakeScribeEmissionVerifier(VerifiedScribeEmissions? verification)
    : IScribeEmissionVerifier
{
    internal int CallCount { get; private set; }

    public VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes = null,
        FrozenStateCatalog? frozenState = null,
        FrozenStatementIndex? frozenStatements = null)
    {
        CallCount++;
        return verification
            ?? throw new InvalidOperationException("Scribe emission verification failed: synthetic");
    }
}
