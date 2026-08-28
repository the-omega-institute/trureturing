using System.Collections.Immutable;
using System.Security.Cryptography;
using Trureturing.Truth;

namespace StrataLint.Engine;

public sealed class TrustedFrozenGitReferences
{
    private readonly ImmutableHashSet<string> inputKeys;

    private TrustedFrozenGitReferences(ImmutableHashSet<string> inputKeys)
    {
        this.inputKeys = inputKeys;
    }

    internal static TrustedFrozenGitReferences CreateForTrustedAdapter(
        IEnumerable<FrozenLedgerInput> inputs)
    {
        ArgumentNullException.ThrowIfNull(inputs);
        return new TrustedFrozenGitReferences(
            inputs.Select(Key).ToImmutableHashSet(StringComparer.Ordinal));
    }

    internal bool Covers(FrozenLedgerInput input) => inputKeys.Contains(Key(input));

    private static string Key(FrozenLedgerInput input) =>
        Convert.ToHexStringLower(SHA256.HashData(
            StructuredCanonicalWriter.WriteJson(
                FrozenLedgerCanonicalWriter.InputElement(input)).AsSpan()));

}
