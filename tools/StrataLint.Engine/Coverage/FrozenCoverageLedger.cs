using System.Collections.Immutable;
using Dunet;

namespace StrataLint.Engine;

[Union(EnableImplicitConversions = false)]
public partial record FrozenCoverageLoadOutcome
{
    public partial record Loaded(ImmutableArray<RepoPath> ActiveFrozenPaths);

    public partial record Invalid(string Message);
}

public static class FrozenCoverageLedger
{
    public static FrozenCoverageLoadOutcome Load(ImmutableArray<DagLedgerFileEvent> events)
    {
        if (events.IsDefault)
        {
            throw new ArgumentException("Frozen event set is uninitialized.", nameof(events));
        }

        try
        {
            if (events.Any(static item => item.EventType != "Freeze"))
            {
                throw new FormatException("frozen ledger v5 contains a non-Freeze event");
            }

            var paths = events.Select(static item => item.DescriptorPath).ToImmutableArray();
            if (paths.Distinct().Count() != paths.Length)
            {
                throw new FormatException("frozen ledger v5 contains a duplicate descriptor_selector");
            }

            return new FrozenCoverageLoadOutcome.Loaded(
                paths.OrderBy(static path => path.Value, StringComparer.Ordinal).ToImmutableArray());
        }
        catch (FormatException exception)
        {
            return new FrozenCoverageLoadOutcome.Invalid(exception.Message);
        }
    }
}
