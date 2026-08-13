using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private static void SetLedger(Dictionary<string, string> files, string ledger)
    {
        files.Remove(FrozenLedgerChangeClassifier.LedgerPath);
        foreach (var path in files.Keys
            .Where(FrozenLedgerChangeClassifier.IsAcceptedEventPath)
            .ToArray())
        {
            files.Remove(path);
        }

        FrozenLedgerTestData.AddLedgerFiles(
            files,
            ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(ledger)));
    }
}
