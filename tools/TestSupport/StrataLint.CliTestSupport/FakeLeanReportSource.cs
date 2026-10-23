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

    public LeanAxiomReport Load(LeanReportScope scope)
    {
        var current = Load(scope.SourceSnapshot);
        foreach (var path in scope.Paths)
            if (!current.Files.ContainsKey(path))
                throw new InvalidOperationException("Lean report is missing " + path.Value);
        return LeanAxiomReport.CreateScoped(current.Files.Where(item => scope.Paths.Contains(item.Key))
            .ToDictionary(static item => item.Key.Value, static item => item.Value));
    }
}
