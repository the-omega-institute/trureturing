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
    RepoPath DescriptorPath,
    FrozenNodeId FrozenNodeId);

public abstract record DagLedgerFilesLoadOutcome
{
    private DagLedgerFilesLoadOutcome() { }

    public sealed record Loaded(ImmutableArray<DagLedgerFileEvent> Events) : DagLedgerFilesLoadOutcome;

    public sealed record Invalid(string Message) : DagLedgerFilesLoadOutcome;
}

public static class FrozenAcceptedEventLoader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    private enum ValidationMode
    {
        Candidate,
        Trusted,
    }

    public static DagLedgerFilesLoadOutcome LoadFiles(IEnumerable<RepositoryFile> files)
        => LoadFiles(files, ValidationMode.Candidate);

    internal static DagLedgerFilesLoadOutcome LoadTrustedFiles(IEnumerable<RepositoryFile> files)
        => LoadFiles(files, ValidationMode.Trusted);

    private static DagLedgerFilesLoadOutcome LoadFiles(
        IEnumerable<RepositoryFile> files,
        ValidationMode validationMode)
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
                JsonElement value;
                string identity;
                string eventHash;
                if (validationMode is ValidationMode.Candidate)
                {
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
                    if (!FrozenLedgerCanonicalWriter.ValidateDagEvent(
                        document.RootElement,
                        out identity,
                        out eventHash,
                        out var validationMessage))
                    {
                        throw new FormatException(validationMessage);
                    }

                    value = document.RootElement.Clone();
                }
                else
                {
                    var trusted = FrozenLedgerBaseViewReader.ReadEvent(file);
                    identity = trusted.Identity;
                    eventHash = trusted.EventHash;
                    value = trusted.Root;
                }

                if (validationMode is ValidationMode.Candidate && !hashes.Add(eventHash))
                {
                    throw new FormatException("Content-addressed frozen event event_hash is duplicated.");
                }

                if (validationMode is ValidationMode.Candidate && !identities.Add(identity))
                {
                    throw new FormatException("Content-addressed frozen event identity is duplicated.");
                }

                var fileName = file.Path.Value[(file.Path.Value.LastIndexOf('/') + 1)..];
                if (validationMode is ValidationMode.Candidate
                    && !string.Equals(
                        fileName,
                        FrozenLedgerChangeClassifier.AcceptedFileName(identity),
                        StringComparison.Ordinal))
                {
                    throw new FormatException(
                        "Content-addressed frozen event file name does not match event identity.");
                }

                var eventType = value.GetProperty("event_type").GetString()!;
                var payload = value.GetProperty("payload").Clone();
                var schemaVersion = value.GetProperty("schema_version").GetInt32();
                var descriptorPath = FrozenLedger.ParseAcceptedEventDescriptorPath(eventType, payload);
                var statement = StatementId.Create(
                    FrozenLedgerAttestationChain.RequiredString(payload, "statement_id"));
                var prerequisites = FrozenLedgerAttestationChain.RequiredStringArray(
                        payload,
                        "prerequisite_frozen_node_ids")
                    .Select(FrozenNodeId.Create)
                    .ToImmutableArray();

                events.Add(new DagLedgerFileEvent(
                    file.Path,
                    identity,
                    eventHash,
                    eventType,
                    payload,
                    schemaVersion,
                    descriptorPath,
                    FrozenContentAddress.ComputeFrozenNodeId(
                        descriptorPath,
                        statement,
                        prerequisites)));
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
