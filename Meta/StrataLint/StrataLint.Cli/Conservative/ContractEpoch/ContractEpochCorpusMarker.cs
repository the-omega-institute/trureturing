using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class ContractEpochCorpusMarker
{
    private const string Prefix = "CONTRACT-CORPUS-V1/";
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static bool IsMarker(string value) => value.StartsWith(Prefix, StringComparison.Ordinal);

    internal static string Write(ConservativeContractCaseResult result)
    {
        ArgumentNullException.ThrowIfNull(result);
        RequireResult(result);
        var bytes = StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
        {
            case_id = result.CaseId,
            finding_codes = result.FindingCodes,
            schema = "stratalint-contract-corpus-result-v1",
        }));
        var root = Convert.ToHexStringLower(SHA256.HashData(bytes.AsSpan()));
        return Prefix + root + "/" + Base64UrlEncode(bytes.AsSpan());
    }

    internal static ConservativeContractCaseResult Read(string marker)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(marker);
        if (!IsMarker(marker)) throw new FormatException("contract corpus marker prefix is invalid");
        var payload = marker[Prefix.Length..];
        var separator = payload.IndexOf('/');
        if (separator != 64
            || payload[..separator].Any(static character =>
                character is not (>= '0' and <= '9') and not (>= 'a' and <= 'f')))
        {
            throw new FormatException("contract corpus marker root is invalid");
        }

        var bytes = Base64UrlDecode(payload[(separator + 1)..]);
        var actual = Convert.ToHexStringLower(SHA256.HashData(bytes));
        if (!string.Equals(actual, payload[..separator], StringComparison.Ordinal))
        {
            throw new FormatException("contract corpus marker root does not match its bytes");
        }

        string text;
        try
        {
            text = StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("contract corpus marker must be strict UTF-8", exception);
        }

        ImmutableArray<byte> canonical;
        try
        {
            canonical = StructuredCanonicalWriter.WriteJson(text);
        }
        catch (JsonException exception)
        {
            throw new FormatException("contract corpus marker is not valid JSON", exception);
        }

        if (!canonical.AsSpan().SequenceEqual(bytes))
        {
            throw new FormatException("contract corpus marker bytes are not canonical JSON");
        }

        try
        {
            using var document = JsonDocument.Parse(bytes);
            var root = document.RootElement;
            var properties = root.EnumerateObject().Select(static item => item.Name).ToArray();
            if (!properties.SequenceEqual(
                ["case_id", "finding_codes", "schema"],
                StringComparer.Ordinal)
                || !string.Equals(
                    root.GetProperty("schema").GetString(),
                    "stratalint-contract-corpus-result-v1",
                    StringComparison.Ordinal))
            {
                throw new FormatException("contract corpus marker schema is invalid");
            }

            var result = new ConservativeContractCaseResult(
                root.GetProperty("case_id").GetString()
                    ?? throw new FormatException("contract corpus case id is missing"),
                root.GetProperty("finding_codes").EnumerateArray()
                    .Select(item => item.GetString()
                        ?? throw new FormatException("contract corpus finding code is not a string"))
                    .ToImmutableArray());
            RequireResult(result);
            return result;
        }
        catch (InvalidOperationException exception)
        {
            throw new FormatException("contract corpus marker schema is invalid", exception);
        }
    }

    private static void RequireResult(ConservativeContractCaseResult result)
    {
        if (!result.CaseId.StartsWith("contract:", StringComparison.Ordinal)
            || string.IsNullOrWhiteSpace(result.CaseId["contract:".Length..]))
        {
            throw new FormatException("contract corpus case id is invalid");
        }

        string? previous = null;
        foreach (var code in result.FindingCodes)
        {
            if (string.IsNullOrWhiteSpace(code)
                || previous is not null && string.CompareOrdinal(previous, code) >= 0)
            {
                throw new FormatException("contract corpus finding codes must be sorted and unique");
            }

            previous = code;
        }
    }

    private static string Base64UrlEncode(ReadOnlySpan<byte> bytes) =>
        Convert.ToBase64String(bytes).TrimEnd('=').Replace('+', '-').Replace('/', '_');

    private static byte[] Base64UrlDecode(string value)
    {
        if (value.Length == 0 || value.Any(static character =>
            !char.IsAsciiLetterOrDigit(character) && character is not '-' and not '_'))
        {
            throw new FormatException("contract corpus marker payload is not base64url");
        }

        var padded = value.Replace('-', '+').Replace('_', '/');
        padded += (padded.Length % 4) switch
        {
            0 => string.Empty,
            2 => "==",
            3 => "=",
            _ => throw new FormatException("contract corpus marker payload length is invalid"),
        };
        try
        {
            return Convert.FromBase64String(padded);
        }
        catch (FormatException exception)
        {
            throw new FormatException("contract corpus marker payload is not base64url", exception);
        }
    }
}
