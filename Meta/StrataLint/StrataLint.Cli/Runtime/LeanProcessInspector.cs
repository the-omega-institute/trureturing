using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed class LeanProcessInspector(string repositoryRoot) : ILeanInspector
{
    private readonly CompiledLeanProcessInspector inspector = new(repositoryRoot);

    public LeanAxiomReport Inspect(RepositorySnapshot snapshot) => inspector.Inspect(snapshot);
}
