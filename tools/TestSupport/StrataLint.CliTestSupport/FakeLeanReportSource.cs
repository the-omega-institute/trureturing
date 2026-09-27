using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.TestSupport;

internal sealed class FakeLeanReportSource(LeanAxiomReport? report) : ILeanReportSource
{
    internal int CallCount { get; private set; }

    public LeanAxiomReport Load(RepositorySnapshot snapshot)
    {
        CallCount++;
        return report ?? throw new InvalidOperationException("Lean report source should not be called");
    }
}
