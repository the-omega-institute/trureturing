using System;
using System.Collections.Generic;
using System.IO;
using System.Text;

namespace Trureturing.Truth;

/// <summary>
/// Fail-closed INTEGRITY verification of a truth-release bundle against an out-of-band expected digest.
/// This proves the bundle's bytes are internally consistent with the digest the caller already trusts;
/// it does NOT establish provenance (that the digest names a real protected-dev release) — that is done
/// independently by re-querying the commit's required checks and re-deriving the bundle.
/// <para>
/// The bytes that SHA256SUMS covers (the seven artifacts) are fully bound. The manifest's own bytes are
/// NOT bound (it cannot list its own SHA256SUMS digest and be inside SHA256SUMS), so a verified
/// <see cref="VerifiedTruthRelease"/> vouches only for the artifact set and the release digest — the
/// manifest's source / trust / producer / produced_at remain producer self-assertions to be checked
/// against the bound source-snapshot and GitHub during the independent provenance step.
/// </para>
/// </summary>
public static class TruthReleaseVerification
{
    private const string SumsFileName = "SHA256SUMS";
    private const string ManifestFileName = "release-manifest.v1.json";

    private static readonly UTF8Encoding StrictUtf8 = new(encoderShouldEmitUTF8Identifier: false, throwOnInvalidBytes: true);

    /// <summary>
    /// Verifies the bundle in <paramref name="bundleDirectory"/> against <paramref name="expectedReleaseDigest"/>
    /// (which must come from outside the bundle) and, only if every check passes, mints a
    /// <see cref="VerifiedTruthRelease"/>. Throws <see cref="FormatException"/> on any inconsistency.
    /// </summary>
    public static VerifiedTruthRelease Verify(string bundleDirectory, string expectedReleaseDigest)
    {
        ArgumentNullException.ThrowIfNull(bundleDirectory);
        ArgumentNullException.ThrowIfNull(expectedReleaseDigest);

        // 1. The RAW SHA256SUMS bytes bind the whole bundle; their digest must equal the out-of-band
        //    expectation. Hash the bytes directly — never a decoded-then-re-encoded string, which is
        //    lossy for malformed UTF-8 and would let distinct byte sequences collapse to one digest.
        var sumsBytes = ReadContainedBytes(bundleDirectory, SumsFileName);
        if (!string.Equals(Sha256Sums.ReleaseDigest(sumsBytes), expectedReleaseDigest, StringComparison.Ordinal))
        {
            throw new FormatException("bundle SHA256SUMS does not hash to the expected release digest.");
        }

        // 2. Parse SHA256SUMS in its exact canonical shape (strict UTF-8; "<64hex>  <name>", name-sorted,
        //    no blank lines, trailing newline).
        var sums = ParseSha256Sums(DecodeStrict(sumsBytes));

        // 3. The manifest's self-reported digest must also equal the out-of-band expectation.
        var manifest = TruthReleaseManifestReader.Read(DecodeStrict(ReadContainedBytes(bundleDirectory, ManifestFileName)));
        if (!string.Equals(manifest.Sha256SumsDigest, expectedReleaseDigest, StringComparison.Ordinal))
        {
            throw new FormatException("manifest sha256sums_digest does not match the expected release digest.");
        }

        // 4. SHA256SUMS must cover EXACTLY the manifest's artifact files — no fewer, no extra, no
        //    duplicates. (A mere count check lets seven manifest slots collapse onto one filename while
        //    six unrelated SHA256SUMS entries go unverified.)
        var artifacts = ListArtifacts(manifest.Artifacts);
        var files = new List<string>(artifacts.Count);
        foreach (var artifact in artifacts)
        {
            RequireSafeBundleName(artifact.File);
            files.Add(artifact.File);
        }

        var fileSet = new HashSet<string>(files, StringComparer.Ordinal);
        if (fileSet.Count != files.Count)
        {
            throw new FormatException("manifest lists the same artifact filename more than once.");
        }

        if (!fileSet.SetEquals(sums.Keys))
        {
            throw new FormatException("SHA256SUMS does not cover exactly the manifest's artifact files.");
        }

        // 5. Every artifact's bytes must hash to the value both SHA256SUMS and the manifest record.
        foreach (var artifact in artifacts)
        {
            var manifestHex = StripDigestPrefix(artifact.Sha256);
            if (!string.Equals(sums[artifact.File], manifestHex, StringComparison.Ordinal))
            {
                throw new FormatException($"artifact '{artifact.File}' hash disagrees between SHA256SUMS and the manifest.");
            }

            var actualHex = Sha256Sums.HashHex(ReadContainedBytes(bundleDirectory, artifact.File));
            if (!string.Equals(actualHex, manifestHex, StringComparison.Ordinal))
            {
                throw new FormatException($"artifact '{artifact.File}' content does not match its recorded sha256.");
            }
        }

        return VerifiedTruthRelease.Create(manifest, expectedReleaseDigest);
    }

    private static IReadOnlyList<TruthReleaseArtifact> ListArtifacts(TruthReleaseArtifacts artifacts) =>
        new[]
        {
            artifacts.SourceSnapshot,
            artifacts.TruthGraph,
            artifacts.RawLeanReport,
            artifacts.Declarations,
            artifacts.BlueprintIndex,
            artifacts.FrozenLedgerHead,
            artifacts.ResidualFrontier,
        };

    private static Dictionary<string, string> ParseSha256Sums(string text)
    {
        if (text.Length == 0 || text[^1] != '\n')
        {
            throw new FormatException("SHA256SUMS must be non-empty and end with a newline.");
        }

        var map = new Dictionary<string, string>(StringComparer.Ordinal);
        string? previousName = null;
        foreach (var line in text[..^1].Split('\n'))
        {
            // Exact shape: "<64 lowercase hex>  <name>" — 64 hex, exactly two spaces, then a non-space name.
            if (line.Length < 67 || line[64] != ' ' || line[65] != ' ' || line[66] == ' ')
            {
                throw new FormatException("SHA256SUMS has a malformed line.");
            }

            var hex = line[..64];
            if (!IsLowercaseHex(hex))
            {
                throw new FormatException("SHA256SUMS has a malformed digest.");
            }

            var name = line[66..];
            if (previousName != null && string.CompareOrdinal(previousName, name) >= 0)
            {
                throw new FormatException("SHA256SUMS names are not in strict ascending order.");
            }

            previousName = name;
            map[name] = hex;
        }

        return map;
    }

    private static void RequireSafeBundleName(string name)
    {
        var safe = !string.IsNullOrEmpty(name)
            && name != "."
            && name != ".."
            && name.IndexOf('/') < 0
            && name.IndexOf('\\') < 0
            && !Path.IsPathRooted(name)
            && string.Equals(name, Path.GetFileName(name), StringComparison.Ordinal);
        if (!safe)
        {
            throw new FormatException($"artifact filename '{name}' is not a plain bundle-relative name.");
        }
    }

    private static byte[] ReadContainedBytes(string bundleDirectory, string name)
    {
        var info = new FileInfo(Path.Combine(bundleDirectory, name));
        if (!info.Exists)
        {
            throw new FormatException($"bundle is missing '{name}'.");
        }

        // A release bundle must contain real files. Refuse a symlink so a matching external file cannot
        // stand in for bundle contents (lexical path checks alone do not stop File.ReadAllBytes following it).
        if (info.LinkTarget != null)
        {
            throw new FormatException($"bundle entry '{name}' is a symbolic link; a release bundle must contain real files.");
        }

        return File.ReadAllBytes(info.FullName);
    }

    private static string DecodeStrict(byte[] bytes)
    {
        try
        {
            return StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("bundle text is not valid UTF-8.", exception);
        }
    }

    private static string StripDigestPrefix(string digest)
    {
        const string prefix = "sha256:";
        return digest.StartsWith(prefix, StringComparison.Ordinal)
            ? digest[prefix.Length..]
            : throw new FormatException("artifact sha256 is not a 'sha256:<hex>' digest.");
    }

    private static bool IsLowercaseHex(ReadOnlySpan<char> value)
    {
        foreach (var character in value)
        {
            var isHex = character is (>= '0' and <= '9') or (>= 'a' and <= 'f');
            if (!isHex)
            {
                return false;
            }
        }

        return true;
    }
}
