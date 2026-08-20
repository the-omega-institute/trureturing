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
    /// The release digest naming the bundle: "sha256:" + <see cref="HashHex"/> of the UTF-8 bytes of
    /// <paramref name="sha256sumsText"/>.
    /// </summary>
    public static string ReleaseDigest(string sha256sumsText)
    {
        ArgumentNullException.ThrowIfNull(sha256sumsText);
        return "sha256:" + HashHex(Encoding.UTF8.GetBytes(sha256sumsText));
    }
}
