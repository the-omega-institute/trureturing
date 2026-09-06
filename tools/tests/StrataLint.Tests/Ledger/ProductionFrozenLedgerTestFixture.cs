using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private static void SetLedger(
        Dictionary<string, string> files,
        IEnumerable<RepositoryFile> events)
    {
        foreach (var path in files.Keys
            .Where(path => FrozenLedgerChangeClassifier.IsAcceptedEventPath(path)
                || FrozenStatePath.IsUnderRoot(path))
            .ToArray())
        {
            files.Remove(path);
        }

        var eventFiles = events.ToArray();
        FrozenLedgerTestData.AddLedgerFiles(files, eventFiles);
        var view = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            eventFiles.ToImmutableDictionary(static file => file.Path)));
        foreach (var (modulePath, active) in view.ActiveByPath)
        {
            files[FrozenStatePath.FromModulePath(modulePath).Value] =
                System.Text.Encoding.UTF8.GetString(
                    FrozenStateRecord.Encode(active.Material.StatementId).AsSpan());
        }
    }
}
