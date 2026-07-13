using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal interface IScribeEmissionVerifier
{
    VerifiedScribeEmissions Verify(LeanAxiomReport report);
}

internal sealed class ProductionScribeEmissionVerifier(string repositoryRoot)
    : IScribeEmissionVerifier
{
    private readonly string repositoryRoot = Path.GetFullPath(repositoryRoot);

    public VerifiedScribeEmissions Verify(LeanAxiomReport report)
    {
        ArgumentNullException.ThrowIfNull(report);
        var error = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        return ScribeEmitter.Verify(repositoryRoot, error, report)
            ?? throw new InvalidOperationException(
                "Scribe emission verification failed: " + error.ToString().Trim());
    }
}
