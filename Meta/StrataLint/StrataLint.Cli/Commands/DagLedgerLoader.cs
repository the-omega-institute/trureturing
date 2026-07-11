using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

public abstract record DagLedgerLoadOutcome
{
    private DagLedgerLoadOutcome() { }

    public sealed record Loaded(FrozenLedgerSyntax Syntax) : DagLedgerLoadOutcome;

    public sealed record Invalid(string Message) : DagLedgerLoadOutcome;
}

public static class DagLedgerLoader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static DagLedgerLoadOutcome Load(ReadOnlySpan<byte> bytes)
    {
        try
        {
            _ = StrictUtf8.GetString(bytes);
            var raw = ImmutableArray.CreateRange(bytes.ToArray());
            var lines = ImmutableArray.CreateBuilder<FrozenLedgerLineSyntax>();
            var start = 0;
            for (var index = 0; index < bytes.Length; index++)
            {
                if (bytes[index] != (byte)'\n')
                {
                    continue;
                }

                var lineBytes = bytes[start..(index + 1)].ToArray();
                if (lineBytes.Length == 1 || lineBytes.AsSpan().Contains((byte)'\r'))
                {
                    throw new FormatException("Frozen ledger contains a blank or CR-terminated line.");
                }

                using var document = JsonDocument.Parse(lineBytes.AsMemory(0, lineBytes.Length - 1));
                if (document.RootElement.ValueKind != JsonValueKind.Object)
                {
                    throw new FormatException("Frozen ledger line must be a JSON object.");
                }

                lines.Add(new FrozenLedgerLineSyntax(
                    ImmutableArray.CreateRange(lineBytes),
                    document.RootElement.Clone()));
                start = index + 1;
            }

            if (start != bytes.Length)
            {
                var lineBytes = bytes[start..].ToArray();
                using var document = JsonDocument.Parse(lineBytes);
                if (document.RootElement.ValueKind != JsonValueKind.Object)
                {
                    throw new FormatException("Frozen ledger line must be a JSON object.");
                }

                lines.Add(new FrozenLedgerLineSyntax(
                    ImmutableArray.CreateRange(lineBytes),
                    document.RootElement.Clone()));
            }

            return new DagLedgerLoadOutcome.Loaded(new FrozenLedgerSyntax(raw, lines.ToImmutable()));
        }
        catch (Exception exception) when (exception is DecoderFallbackException or JsonException or FormatException)
        {
            return new DagLedgerLoadOutcome.Invalid(exception.Message);
        }
    }
}
