using System.Text;
using StrataLint.Engine;

namespace StrataLint.TestSupport;

internal static class TheoryAtomizerAssertions
{
    internal static void AssertContentIdentity(DigestionAtom atom) => Assert.Equal(
        DigestionFingerprint.Compute(atom.RawBytes.AsSpan()).RawSha256,
        atom.Fingerprints.RawSha256);

    internal static DigestionAtom ClaimContaining(AtomizedTheoryDocument document, string text) =>
        Assert.Single(document.Claims, atom =>
            Encoding.UTF8.GetString(atom.RawBytes.AsSpan()).Contains(text, StringComparison.Ordinal));
}
