using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal static partial class DigestionLedgerAligner
{
    private static bool GenreRegistryChecksEqual(
        GenreRegistryCheck left,
        GenreRegistryCheck right) =>
        left.Kind == right.Kind
        && left.UnregisteredGenres.SequenceEqual(
            right.UnregisteredGenres,
            StringComparer.Ordinal);

    private static string GenreRegistryProjectionFinding(
        DigestionLedgerSource source,
        GenreRegistryCheck stored,
        GenreRegistryCheck recomputed) =>
        $"source {source.SourceId} genre registry projection differs: "
        + $"stored {RenderGenreRegistryCheck(stored)}; "
        + $"recomputed {RenderGenreRegistryCheck(recomputed)}";

    private static string RenderGenreRegistryCheck(GenreRegistryCheck check) =>
        GenreRegistryCheckNames.Render(check.Kind)
        + " ["
        + string.Join(", ", check.UnregisteredGenres)
        + "]";

    internal static bool IsAtomizerImplementationPath(string path, IReadOnlySet<string> registeredInputs) =>
        StrataLintEngineBuildInputs.Contains(path, registeredInputs);

    internal static string? AtomizerIntegrityFailure(
        AtomizedTheoryDocument document,
        ReadOnlySpan<byte> sourceBytes)
    {
        var sourceLength = sourceBytes.Length;
        if (document.Slices.Count(static slice => slice.IsClaim) != document.Claims.Length)
        {
            return "claim slice count does not match claim count";
        }

        if (!document.Reassemble().AsSpan().SequenceEqual(sourceBytes))
        {
            return "slices do not reassemble the source bytes";
        }

        var claimIndex = 0;
        var cursor = 0;
        foreach (var slice in document.Slices)
        {
            var end = cursor + slice.RawBytes.Length;
            if (slice.IsClaim)
            {
                var atom = document.Claims[claimIndex++];
                if (atom.StartByte != cursor || atom.EndByte != end)
                {
                    return $"claim at byte {atom.StartByte} boundaries do not match its source slice";
                }

                if (!atom.RawBytes.AsSpan().SequenceEqual(slice.RawBytes.AsSpan()))
                {
                    return $"claim at byte {atom.StartByte} raw bytes do not match its source span";
                }
            }

            cursor = end;
        }

        foreach (var atom in document.Claims)
        {
            if (atom.RawBytes.Length == 0
                || atom.StartByte < 0
                || atom.EndByte <= atom.StartByte
                || atom.EndByte > sourceLength
                || atom.EndByte - atom.StartByte != atom.RawBytes.Length)
            {
                return $"claim at byte {atom.StartByte} has invalid byte boundaries";
            }

            if (atom.Fingerprints != DigestionFingerprint.Compute(atom.RawBytes.AsSpan()))
            {
                return $"claim at byte {atom.StartByte} fingerprint does not match its raw bytes";
            }
        }

        var clausePlanFailure = ClausePlanIntegrityFailure(document);
        if (clausePlanFailure is not null)
        {
            return clausePlanFailure;
        }

        return null;
    }

}
