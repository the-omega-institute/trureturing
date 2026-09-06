using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class AtomContextCommand
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static CommandResult Run(IRepositoryGateway repository, IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            if (arguments.Count != 2 || arguments[0] != "--atom-id"
                || !DigestionFingerprint.IsCanonicalSha256("sha256:" + arguments[1]))
                throw new DigestionAtomContextException(DigestionAtomContextError.ARGUMENTS_INVALID,
                    "USAGE: StrataLint atom-context --atom-id ATOM_ID");
            var snapshot = Decode(repository.ReadCurrent());
            var context = DigestionAtomContextProjection.Resolve(snapshot, BackfillInventoryLoader.Load(snapshot), arguments[1]);
            return new CommandResult(true, Render(context), string.Empty);
        }
        catch (DigestionAtomContextException error)
        {
            return Invalid(error.Code, error.Message);
        }
        catch (Exception error) when (error is FormatException or InvalidOperationException or IOException or ArgumentException)
        {
            return Invalid(DigestionAtomContextError.OCCURRENCE_MISSING, error.Message);
        }
    }

    private static CommandResult Invalid(DigestionAtomContextError code, string detail) =>
        new(false, string.Empty, $"ATOM_CONTEXT_INVALID {code} {detail}\n");

    private static string Render(DigestionAtomContext context)
    {
        var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        writer.WriteLine($"ATOM_CONTEXT atom_id={context.Target.AtomId} source_id={context.SourceId} "
            + $"source_path={context.SourcePath} atomizer={context.Atomizer} index={context.Index}/{context.Count}");
        WriteNeighbor(writer, "PREVIOUS", context.Previous, context.PreviousBoundaryReason);
        WriteNeighbor(writer, "CURRENT", context.Current, null);
        WriteNeighbor(writer, "NEXT", context.Next, context.NextBoundaryReason);
        if (context.Previous is { } previous) WriteText(writer, "PREVIOUS", previous.RawBytes);
        WriteText(writer, "CURRENT", context.Current.RawBytes);
        if (context.Next is { } next) WriteText(writer, "NEXT", next.RawBytes);
        return writer.ToString();
    }

    private static void WriteNeighbor(StringWriter writer, string label,
        (string AtomId, string? LedgerState, ImmutableArray<byte> RawBytes)? neighbor, string? boundary)
    {
        writer.WriteLine(neighbor is { } value
            ? $"{label} atom_id={value.AtomId} state={value.LedgerState ?? "unregistered"}"
            : $"{label} none reason={boundary}");
    }

    private static void WriteText(StringWriter writer, string label, ImmutableArray<byte> bytes)
    {
        var text = StrictUtf8.GetString(bytes.AsSpan());
        writer.WriteLine($"BEGIN_{label}_TEXT");
        writer.Write(text);
        if (!text.EndsWith('\n')) writer.WriteLine();
        writer.WriteLine($"END_{label}_TEXT");
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure error => throw new InvalidOperationException(error.Message),
    };
}
