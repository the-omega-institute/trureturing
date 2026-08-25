using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record TruthContext(
    RepositorySnapshot Snapshot,
    AcceptedLeanClosure Lean,
    LeanAxiomReport Report);
