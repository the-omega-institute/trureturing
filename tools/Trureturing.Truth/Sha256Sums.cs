using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using System.Text;

namespace Trureturing.Truth;

/// <summary>
/// The canonical SHA256SUMS text format and the release digest that names a truth-release bundle.
/// SHA256SUMS binds the bundle's bytes together (integrity); it does NOT authenticate provenance —
/// a consumer establishes provenance independently (re-query the commit's required checks and
/// re-derive the bundle). This writer only fixes the byte-exact, two-machine-reproducible shape.
/// </summary>
public static class Sha256Sums
{
    /// <summary>Lowercase-hex SHA-256 of <paramref name="content"/>.</summary>
    public static string HashHex(ReadOnlySpan<byte> content)
    {
        Span<byte> hash = stackalloc byte[32];
        SHA256.HashData(content, hash);
        return Convert.ToHexStringLower(hash);
    }

    /// <summary>
    /// Canonical SHA256SUMS text over <paramref name="hexByName"/>: one line "&lt;hex&gt;  &lt;name&gt;"
    /// (two spaces) per entry, entries sorted by name (Ordinal), lines joined by "\n" with a trailing "\n".
    /// </summary>
    public static string Format(IReadOnlyDictionary<string, string> hexByName)
    {
        ArgumentNullException.ThrowIfNull(hexByName);
        var builder = new StringBuilder();
        foreach (var name in hexByName.Keys.OrderBy(static key => key, StringComparer.Ordinal))
        {
            builder.Append(hexByName[name]).Append("  ").Append(name).Append('\n');
        }

        return builder.ToString();
    }

    /// <summary>
    /// The release digest naming the bundle: "sha256:" + <see cref="HashHex"/> of the exact
    /// <paramref name="sha256sumsBytes"/>. A verifier MUST use this byte overload over the raw SHA256SUMS
    /// file bytes — decoding to a string and re-encoding is lossy for malformed UTF-8, so distinct byte
    /// sequences that decode to the same replacement characters would otherwise collapse to one digest.
    /// </summary>
    public static string ReleaseDigest(ReadOnlySpan<byte> sha256sumsBytes) =>
        "sha256:" + HashHex(sha256sumsBytes);

    /// <summary>
    /// Convenience overload for already-decoded, well-formed text (e.g. text a producer just built).
    /// For verifying bytes read off disk, use the <see cref="ReleaseDigest(System.ReadOnlySpan{byte})"/>
    /// overload instead — this one round-trips through UTF-8 and is not byte-faithful for malformed input.
    /// </summary>
    public static string ReleaseDigest(string sha256sumsText)
    {
        ArgumentNullException.ThrowIfNull(sha256sumsText);
        return ReleaseDigest(Encoding.UTF8.GetBytes(sha256sumsText));
    }
}
