using System.Text;

namespace StrataLint.Engine;

/// Reversible addresses for values mutation keys, independent of catalog membership.
public static class ValuesProjectionAddress
{
    public const string DirectoryPath = "Evidence/D5/values";
    public const string FileSuffix = ".value.json";
    // k + 2 * 120 ASCII hex digits + .value.json = 252 bytes, below NAME_MAX=255.
    // The caller must also supply a repository root within the host's full-path limit.
    public const int MaximumKeyUtf8Bytes = 120;
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static string Encode(string id)
    {
        ArgumentNullException.ThrowIfNull(id);
        byte[] bytes;
        try { bytes = StrictUtf8.GetBytes(id); }
        catch (EncoderFallbackException exception)
        {
            throw new FormatException("Values key must contain valid Unicode scalar values.", exception);
        }
        if (bytes.Length is 0 or > MaximumKeyUtf8Bytes)
            throw new FormatException($"Values key must contain 1..{MaximumKeyUtf8Bytes} UTF-8 bytes.");
        return "k" + Convert.ToHexStringLower(bytes);
    }

    public static string Decode(string encoded)
    {
        if (encoded.Length < 3 || encoded.Length > 1 + 2 * MaximumKeyUtf8Bytes
            || encoded[0] != 'k' || encoded.Length % 2 != 1
            || encoded.AsSpan(1).ContainsAnyExcept("0123456789abcdef"))
            throw new FormatException("Values key encoding must be k followed by lowercase UTF-8 hex.");
        string id;
        try { id = StrictUtf8.GetString(Convert.FromHexString(encoded[1..])); }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("Values key encoding is not strict UTF-8.", exception);
        }
        if (!string.Equals(Encode(id), encoded, StringComparison.Ordinal))
            throw new FormatException("Values key encoding did not round-trip.");
        return id;
    }

    public static string PathFor(string id) => $"{DirectoryPath}/{Encode(id)}{FileSuffix}";
    public static string GidFor(string id) => $"D5/E/values/{Encode(id)}.value--json";

    public static bool TryIdFromPath(string path, out string id)
    {
        id = string.Empty;
        if (!path.StartsWith(DirectoryPath + "/", StringComparison.Ordinal)
            || !path.EndsWith(FileSuffix, StringComparison.Ordinal)) return false;
        try
        {
            id = Decode(path[(DirectoryPath.Length + 1)..^FileSuffix.Length]);
            return string.Equals(PathFor(id), path, StringComparison.Ordinal);
        }
        catch (FormatException) { return false; }
    }
}
