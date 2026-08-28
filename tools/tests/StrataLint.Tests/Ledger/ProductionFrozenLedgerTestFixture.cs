using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private static void SetLedger(
        Dictionary<string, string> files,
        IEnumerable<RepositoryFile> events)
    {
        foreach (var path in files.Keys
            .Where(FrozenLedgerChangeClassifier.IsAcceptedEventPath)
            .ToArray())
        {
            files.Remove(path);
        }

        FrozenLedgerTestData.AddLedgerFiles(files, events);
    }
}
