using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal static partial class DigestionLedgerAligner
{
    private static readonly DigestionStatus StructuralIdentityStatus = new(
        DigestionMigrationState.Residual,
        DigestionTruthState.Open);

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
            || AtomizerDecisionClosureEqualBaseline(
                candidateSnapshot,
                baselineSnapshot,
                candidateSource,
                baselineSource))
        {
            return null;
        }

        if (candidateSource.Atomizer == AtomizerRegistry.NoAtomizerId)
        {
            return GenreRegistryChecksEqual(
                candidateSource.GenreRegistryCheck,
                GenreRegistryCheck.NoGenreRegistry)
                    ? null
                    : GenreRegistryProjectionFinding(
                        candidateSource,
                        candidateSource.GenreRegistryCheck,
                        GenreRegistryCheck.NoGenreRegistry);
        }

        if (!registeredAtomizer
            || atomizerRules is null
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
            || !HasUniqueAstPaths(atomized.Claims))
        {
            return null;
        }

        return GenreRegistryChecksEqual(
            candidateSource.GenreRegistryCheck,
            atomized.GenreRegistryCheck)
                ? null
                : GenreRegistryProjectionFinding(
                    candidateSource,
                    candidateSource.GenreRegistryCheck,
                    atomized.GenreRegistryCheck);
    }

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
        && AtomizerImplementationClosureEqualBaseline(candidateSnapshot, baselineSnapshot);

    private static bool AtomizerImplementationClosureEqualBaseline(
        RepositorySnapshot candidateSnapshot,
        RepositorySnapshot baselineSnapshot)
    {
        var paths = candidateSnapshot.Files.Keys
            .Concat(baselineSnapshot.Files.Keys)
            .Select(static path => path.Value)
            .Where(IsAtomizerImplementationPath)
            .Distinct(StringComparer.Ordinal);
        return paths.All(path => FileBytesEqual(
            candidateSnapshot,
            path,
            baselineSnapshot,
            path));
    }

    internal static bool IsAtomizerImplementationPath(string path) =>
        StrataLintEngineBuildInputs.Contains(path);

    private static bool FileBytesEqual(
        RepositorySnapshot candidateSnapshot,
        string candidatePath,
        RepositorySnapshot baselineSnapshot,
        string baselinePath) =>
        candidateSnapshot.TryGetFile(candidatePath, out var candidate)
        && baselineSnapshot.TryGetFile(baselinePath, out var baseline)
        && candidate.RawBytes.AsSpan().SequenceEqual(baseline.RawBytes.AsSpan());

    private static string CanonicalEntry(
        DigestionLedgerSource source,
        DigestionLedgerEntry entry)
    {
        var admissionEntry = entry with
        {
            // Once stale has been acknowledged, projected status is derived output. Including it
            // here makes alignment invalidate its own settled receipt on a status-directory move.
            ProjectedStatus = source.AcknowledgedStale.Contains(
                entry.AtomId,
                StringComparer.Ordinal)
                ? StructuralIdentityStatus
                : entry.ProjectedStatus,
            Receipts = entry.Receipts with
            {
                Coverage = [],
                Scribe = [],
                CoverDisposition = null,
            },
        };
        return Convert.ToBase64String(BackfillInventoryWriter.WriteEntry(admissionEntry).AsSpan());
    }

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

        var unregisteredGenreFailure = UnregisteredGenreIntegrityFailure(document);
        if (unregisteredGenreFailure is not null)
        {
            return unregisteredGenreFailure;
        }

        var clausePlanFailure = ClausePlanIntegrityFailure(document);
        if (clausePlanFailure is not null)
        {
            return clausePlanFailure;
        }

        return null;
    }

    private static string? UnregisteredGenreIntegrityFailure(AtomizedTheoryDocument document)
    {
        var claimTokens = ImmutableArray.CreateBuilder<string>();
        foreach (var claim in document.Claims.Where(static atom =>
                     atom.AstPath.StartsWith(UnregisteredGenreLocator.Prefix, StringComparison.Ordinal)))
        {
            if (!UnregisteredGenreLocator.TryGetToken(claim.AstPath, out var token))
            {
                return $"claim {claim.AstPath} uses a noncanonical reserved unregistered namespace path";
            }

            claimTokens.Add(token);
        }

        var expectedTokens = claimTokens
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var check = document.GenreRegistryCheck;
        if (check.Kind != GenreRegistryCheckKind.Collected && !expectedTokens.IsEmpty
            || check.Kind == GenreRegistryCheckKind.Collected
            && !check.UnregisteredGenres.SequenceEqual(expectedTokens, StringComparer.Ordinal))
        {
            return "reserved unregistered namespace differs from genre registry check: "
                + $"paths [{string.Join(", ", expectedTokens)}]; "
                + $"marker {RenderGenreRegistryCheck(check)}";
        }

        foreach (var atom in document.Claims
                     .Concat(document.ClausePlans.SelectMany(static plan => plan.Children))
                     .Where(static atom => atom.AstPath.StartsWith(
                         UnregisteredGenreLocator.Prefix,
                         StringComparison.Ordinal)))
        {
            if (!UnregisteredGenreLocator.TryGetToken(atom.AstPath, out var token))
            {
                return $"claim {atom.AstPath} uses a noncanonical reserved unregistered namespace path";
            }

            if (!expectedTokens.Contains(token, StringComparer.Ordinal))
            {
                return "reserved unregistered namespace differs from genre registry check: "
                    + $"claim {atom.AstPath} has no top-level open genre";
            }
        }

        return null;
    }
}
