using System.Collections.Immutable;
using System.Text;
using System.Text.Json;

namespace StrataLint.Engine;

public sealed record DagLedgerFileEvent(
    RepoPath SourcePath,
    string Identity,
    string EventHash,
    string EventType,
    JsonElement Payload,
    int SchemaVersion,
    FrozenLedgerLineSyntax Syntax,
    FrozenLedgerInput? Input);

public abstract record DagLedgerFilesLoadOutcome
{
    private DagLedgerFilesLoadOutcome() { }

    public sealed record Loaded(ImmutableArray<DagLedgerFileEvent> Events) : DagLedgerFilesLoadOutcome;

    public sealed record Invalid(string Message) : DagLedgerFilesLoadOutcome;
}

public static class FrozenAcceptedEventLoader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static DagLedgerFilesLoadOutcome LoadFiles(IEnumerable<RepositoryFile> files)
        => LoadFiles(files, validateRecordedHash: true);

    internal static DagLedgerFilesLoadOutcome LoadTrustedFiles(IEnumerable<RepositoryFile> files)
        => LoadFiles(files, validateRecordedHash: false);

    private static DagLedgerFilesLoadOutcome LoadFiles(
        IEnumerable<RepositoryFile> files,
        bool validateRecordedHash)
    {
        ArgumentNullException.ThrowIfNull(files);
        try
        {
            var events = ImmutableArray.CreateBuilder<DagLedgerFileEvent>();
            var identities = new HashSet<string>(StringComparer.Ordinal);
            var hashes = new HashSet<string>(StringComparer.Ordinal);
            foreach (var file in files.OrderBy(static file => file.Path.Value, StringComparer.Ordinal))
            {
                var bytes = file.RawBytes.AsSpan();
                _ = StrictUtf8.GetString(bytes);
                if (bytes.Length < 2
                    || bytes[^1] != (byte)'\n'
                    || bytes[..^1].Contains((byte)'\n')
                    || bytes.Contains((byte)'\r'))
                {
                    throw new FormatException(
                        "Content-addressed frozen event file must contain exactly one LF-terminated JSON object.");
                }

                using var document = JsonDocument.Parse(bytes[..^1].ToArray());
                var valid = validateRecordedHash
                    ? FrozenLedgerCanonicalWriter.ValidateDagEvent(
                        document.RootElement,
                        out var identity,
                        out var eventHash,
                        out var validationMessage)
                    : FrozenLedgerCanonicalWriter.ReadTrustedDagEvent(
                        document.RootElement,
                        out identity,
                        out eventHash,
                        out validationMessage);
                if (!valid)
                {
                    throw new FormatException(validationMessage);
                }

                if (!hashes.Add(eventHash))
                {
                    throw new FormatException("Content-addressed frozen event event_hash is duplicated.");
                }

                if (!identities.Add(identity))
                {
                    throw new FormatException("Content-addressed frozen event identity is duplicated.");
                }

                var fileName = file.Path.Value[(file.Path.Value.LastIndexOf('/') + 1)..];
                if (!string.Equals(
                    fileName,
                    FrozenLedgerChangeClassifier.AcceptedFileName(identity),
                    StringComparison.Ordinal))
                {
                    throw new FormatException(
                        "Content-addressed frozen event file name does not match event identity.");
                }

                var value = document.RootElement.Clone();
                var eventType = value.GetProperty("event_type").GetString()!;
                var payload = value.GetProperty("payload").Clone();
                var schemaVersion = value.GetProperty("schema_version").GetInt32();
                var input = FrozenLedger.ParseAcceptedEventInput(
                    eventType,
                    payload,
                    schemaVersion);

                events.Add(new DagLedgerFileEvent(
                    file.Path,
                    identity,
                    eventHash,
                    eventType,
                    payload,
                    schemaVersion,
                    new FrozenLedgerLineSyntax(ImmutableArray.CreateRange(bytes.ToArray()), value),
                    input));
            }

            return new DagLedgerFilesLoadOutcome.Loaded(events.ToImmutable());
        }
        catch (Exception exception) when (
            exception is DecoderFallbackException or JsonException or FormatException)
        {
            return new DagLedgerFilesLoadOutcome.Invalid(exception.Message);
        }
    }
}
