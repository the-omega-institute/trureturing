using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Cli;

internal static class FrozenLedgerHeadAssembler
{
    internal static ImmutableArray<byte> Assemble(FrozenLedgerBaseView ledger)
    {
        ArgumentNullException.ThrowIfNull(ledger);
        var element = JsonSerializer.SerializeToElement(new
        {
            head_hash = ledger.EventSetRoot(),
            sequence = ledger.EventCount,
        });
        return StructuredCanonicalWriter.WriteJson(element);
    }
}
