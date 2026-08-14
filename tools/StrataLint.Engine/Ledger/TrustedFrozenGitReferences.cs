using System.Collections.Immutable;
using System.Security.Cryptography;

namespace StrataLint.Engine;

public sealed class TrustedFrozenGitReferences
{
    private readonly ImmutableHashSet<string> inputKeys;
    private readonly ImmutableHashSet<string> environmentKeys;

    private TrustedFrozenGitReferences(
        ImmutableHashSet<string> inputKeys,
        ImmutableHashSet<string> environmentKeys)
    {
        this.inputKeys = inputKeys;
        this.environmentKeys = environmentKeys;
    }

    internal static TrustedFrozenGitReferences CreateForTrustedAdapter(
        IEnumerable<FrozenLedgerInput> inputs,
        IEnumerable<FrozenEnvironmentReference>? environmentReferences = null)
    {
        ArgumentNullException.ThrowIfNull(inputs);
        return new TrustedFrozenGitReferences(
            inputs.Select(Key).ToImmutableHashSet(StringComparer.Ordinal),
            (environmentReferences ?? Array.Empty<FrozenEnvironmentReference>())
                .Select(EnvironmentKey)
                .ToImmutableHashSet(StringComparer.Ordinal));
    }

    internal bool Covers(FrozenLedgerInput input) => inputKeys.Contains(Key(input));

    internal bool Covers(FrozenEnvironmentReference reference) =>
        environmentKeys.Contains(EnvironmentKey(reference));

    private static string Key(FrozenLedgerInput input) =>
        Convert.ToHexStringLower(SHA256.HashData(
            StructuredCanonicalWriter.WriteJson(
                FrozenLedgerCanonicalWriter.InputElement(input)).AsSpan()));

    private static string EnvironmentKey(FrozenEnvironmentReference reference) =>
        Convert.ToHexStringLower(SHA256.HashData(
            StructuredCanonicalWriter.WriteJson(
                FrozenLedgerCanonicalWriter.EnvironmentReferenceElement(reference)).AsSpan()));
}
