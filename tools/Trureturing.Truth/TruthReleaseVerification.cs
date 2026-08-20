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
/// </summary>
public static class TruthReleaseVerification
{
    private const string SumsFileName = "SHA256SUMS";
    private const string ManifestFileName = "release-manifest.v1.json";

    /// <summary>
    /// Verifies the bundle in <paramref name="bundleDirectory"/> against <paramref name="expectedReleaseDigest"/>
    /// (which must come from outside the bundle) and, only if every check passes, mints a
    /// <see cref="VerifiedTruthRelease"/>. Throws <see cref="FormatException"/> on any inconsistency.
    /// </summary>
    public static VerifiedTruthRelease Verify(string bundleDirectory, string expectedReleaseDigest)
    {
        ArgumentNullException.ThrowIfNull(bundleDirectory);
        ArgumentNullException.ThrowIfNull(expectedReleaseDigest);

        // 1. SHA256SUMS bytes bind the whole bundle; their digest must equal the out-of-band expectation.
        var sumsText = ReadBundleText(bundleDirectory, SumsFileName);
        if (!string.Equals(Sha256Sums.ReleaseDigest(sumsText), expectedReleaseDigest, StringComparison.Ordinal))
        {
            throw new FormatException("bundle SHA256SUMS does not hash to the expected release digest.");
        }

        // 2. Parse SHA256SUMS into name -> hex.
        var sums = ParseSha256Sums(sumsText);

        // 3. The manifest's self-reported digest must also equal the out-of-band expectation.
        var manifest = TruthReleaseManifestReader.Read(ReadBundleText(bundleDirectory, ManifestFileName));
        if (!string.Equals(manifest.Sha256SumsDigest, expectedReleaseDigest, StringComparison.Ordinal))
        {
            throw new FormatException("manifest sha256sums_digest does not match the expected release digest.");
        }

        // 4. SHA256SUMS must cover exactly the manifest's artifacts, and every artifact's bytes must hash
        //    to the value both the manifest and SHA256SUMS record.
        var artifacts = ListArtifacts(manifest.Artifacts);
        if (sums.Count != artifacts.Count)
        {
            throw new FormatException("SHA256SUMS does not cover exactly the manifest's artifacts.");
        }

        foreach (var artifact in artifacts)
        {
            RequireSafeBundleName(artifact.File);

            if (!sums.TryGetValue(artifact.File, out var sumsHex))
            {
                throw new FormatException($"artifact '{artifact.File}' is absent from SHA256SUMS.");
            }

            var manifestHex = StripDigestPrefix(artifact.Sha256);
            if (!string.Equals(sumsHex, manifestHex, StringComparison.Ordinal))
            {
                throw new FormatException($"artifact '{artifact.File}' hash disagrees between SHA256SUMS and the manifest.");
            }

            var actualHex = Sha256Sums.HashHex(ReadBundleBytes(bundleDirectory, artifact.File));
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
        var map = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var rawLine in text.Split('\n'))
        {
            if (rawLine.Length == 0)
            {
                continue;
            }

            // Exact shape: "<64 lowercase hex>  <name>" (two spaces).
            if (rawLine.Length < 67 || rawLine[64] != ' ' || rawLine[65] != ' ')
            {
                throw new FormatException("SHA256SUMS has a malformed line.");
            }

            var hex = rawLine[..64];
            if (!IsLowercaseHex(hex))
            {
                throw new FormatException("SHA256SUMS has a malformed digest.");
            }

            var name = rawLine[66..];
            if (!map.TryAdd(name, hex))
            {
                throw new FormatException($"SHA256SUMS lists '{name}' more than once.");
            }
        }

        return map;
    }

    private static void RequireSafeBundleName(string name)
    {
        var safe = !string.IsNullOrEmpty(name)
            && name != "."
            && name != ".."
            && !Path.IsPathRooted(name)
            && string.Equals(name, Path.GetFileName(name), StringComparison.Ordinal);
        if (!safe)
        {
            throw new FormatException($"artifact filename '{name}' is not a plain bundle-relative name.");
        }
    }

    private static string ReadBundleText(string bundleDirectory, string name) =>
        Encoding.UTF8.GetString(ReadBundleBytes(bundleDirectory, name));

    private static byte[] ReadBundleBytes(string bundleDirectory, string name)
    {
        var path = Path.Combine(bundleDirectory, name);
        if (!File.Exists(path))
        {
            throw new FormatException($"bundle is missing '{name}'.");
        }

        return File.ReadAllBytes(path);
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
