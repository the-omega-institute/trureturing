using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal static partial class DigestionLedgerAligner
{
    private static string? AdmissionGenreFinding(
        DigestionAlignmentMode mode,
        RepositorySnapshot candidateSnapshot,
        RepositorySnapshot? baselineSnapshot,
        DigestionLedgerSource candidateSource,
        DigestionLedgerSource? baselineSource,
        bool registeredAtomizer,
        TheoryAtomizerRules? atomizerRules,
        Func<string, TheoryAtomizer> atomizerResolver)
    {
        if (mode != DigestionAlignmentMode.Admission
            || candidateSource.Atomizer == AtomizerRegistry.NoAtomizerId
            || !registeredAtomizer
            || atomizerRules is null
            || AtomizerDecisionClosureEqualBaseline(
                candidateSnapshot,
                baselineSnapshot,
                candidateSource,
                baselineSource)
            || !candidateSnapshot.TryGetFile(candidateSource.SourcePath, out var sourceFile))
        {
            return null;
        }

        AtomizedTheoryDocument atomized;
        try
        {
            var atomize = atomizerResolver(candidateSource.Atomizer);
            atomized = atomize(sourceFile.RawBytes.AsSpan(), atomizerRules);
        }
        catch (Exception exception) when (
            exception is TheorySourceFormatException or DecoderFallbackException)
        {
            // The ordinary pass owns theory-source and UTF-8 decoding failures, so the probe
            // must not replace those outcomes with a genre finding.
            return null;
        }

        if (AtomizerIntegrityFailure(atomized, sourceFile.RawBytes.AsSpan()) is not null
            || !HasUniqueAstPaths(atomized.Claims)
            || atomized.Claims.Length == 0
            || atomized.GenreRegistryCheck.Kind != GenreRegistryCheckKind.Collected
            || atomized.UnregisteredGenres.IsEmpty)
        {
            return null;
        }

        return UnregisteredGenreFinding(candidateSource, atomized.UnregisteredGenres);
    }

    private static string UnregisteredGenreFinding(
        DigestionLedgerSource source,
        ImmutableArray<string> unregisteredGenres) =>
        $"source {source.SourceId} uses claim genres its dialect does not register: "
        + string.Join(", ", unregisteredGenres)
        + $". Register them in {TheoryAtomizerDataLoader.DataPath} or correct the volume.";

    private static bool AtomizerDecisionClosureEqualBaseline(
        RepositorySnapshot candidateSnapshot,
        RepositorySnapshot? baselineSnapshot,
        DigestionLedgerSource candidateSource,
        DigestionLedgerSource? baselineSource) =>
        baselineSnapshot is not null
        && baselineSource is not null
        && candidateSource.Atomizer == baselineSource.Atomizer
        && FileBytesEqual(
            candidateSnapshot,
            candidateSource.SourcePath,
            baselineSnapshot,
            baselineSource.SourcePath)
        && FileBytesEqual(
            candidateSnapshot,
            TheoryAtomizerDataLoader.DataPath,
            baselineSnapshot,
            TheoryAtomizerDataLoader.DataPath)
        // Atomizer implementations have no narrower stable content address. Whole-tree equality
        // proves their code closure is unchanged; any candidate change pays the cheap recheck.
        && RepositoryBytesEqual(candidateSnapshot, baselineSnapshot);

    private static bool RepositoryBytesEqual(
        RepositorySnapshot candidateSnapshot,
        RepositorySnapshot baselineSnapshot) =>
        candidateSnapshot.Files.Count == baselineSnapshot.Files.Count
        && candidateSnapshot.Files.All(candidate =>
            baselineSnapshot.Files.TryGetValue(candidate.Key, out var baseline)
            && candidate.Value.RawBytes.AsSpan().SequenceEqual(baseline.RawBytes.AsSpan()));

    private static bool FileBytesEqual(
        RepositorySnapshot candidateSnapshot,
        string candidatePath,
        RepositorySnapshot baselineSnapshot,
        string baselinePath) =>
        candidateSnapshot.TryGetFile(candidatePath, out var candidate)
        && baselineSnapshot.TryGetFile(baselinePath, out var baseline)
        && candidate.RawBytes.AsSpan().SequenceEqual(baseline.RawBytes.AsSpan());

    private static string CanonicalEntry(DigestionLedgerEntry entry) =>
        Convert.ToBase64String(BackfillInventoryWriter.WriteEntry(entry).AsSpan());

    private static string? AtomizerIntegrityFailure(
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
                    return $"claim {atom.AstPath} boundaries do not match its source slice";
                }

                if (!atom.RawBytes.AsSpan().SequenceEqual(slice.RawBytes.AsSpan()))
                {
                    return $"claim {atom.AstPath} raw bytes do not match its source span";
                }
            }

            cursor = end;
        }

        foreach (var atom in document.Claims)
        {
            if (string.IsNullOrWhiteSpace(atom.AstPath))
            {
                return "claim ast_path is empty";
            }

            if (atom.RawBytes.Length == 0
                || atom.StartByte < 0
                || atom.EndByte <= atom.StartByte
                || atom.EndByte > sourceLength
                || atom.EndByte - atom.StartByte != atom.RawBytes.Length)
            {
                return $"claim {atom.AstPath} has invalid byte boundaries";
            }

            if (atom.Fingerprints != DigestionFingerprint.Compute(atom.RawBytes.AsSpan()))
            {
                return $"claim {atom.AstPath} fingerprint does not match its raw bytes";
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
