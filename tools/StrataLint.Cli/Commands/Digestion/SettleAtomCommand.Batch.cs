using System.Text;
using StrataLint.Engine;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Cli;

internal static partial class SettleAtomCommand
{
    // Strict UTF-8/LF TOML: the sole root key is [[requests]]. Each table has
    // exactly the single-settle keys. Validate the envelope before any writes;
    // validate and commit records in input order, retaining the successful prefix.
    internal static CommandResult RunBatch(string root, IRepositoryGateway repository, IReadOnlyList<string> arguments,
        ILeanReportSource? reportSource = null)
    {
        string? file = null;
        TomlTableArray requests;
        try
        {
            const string usage = "USAGE: StrataLint settle-batch --requests FILE";
            for (var index = 0; index < arguments.Count; index += 2)
            {
                if (index + 1 >= arguments.Count) throw new FormatException(usage);
                switch (arguments[index])
                {
                    case "--requests" when file is null: file = arguments[index + 1]; break;
                    default: throw new FormatException(usage);
                }
            }
            if (file is null)
                throw new FormatException(usage);
            var table = TomlSerializer.Deserialize<TomlTable>(DecodeRequest(ReadRequest(root, file)));
            if (table is null || table.Count != 1 || !table.TryGetValue("requests", out var value)
                || value is not TomlTableArray { Count: > 0 } items)
                throw new FormatException("expected only a nonempty [[requests]] array");
            requests = items;
        }
        catch (Exception error) when (error is not OutOfMemoryException)
        {
            return new(false, string.Empty, $"SETTLE_BATCH_INPUT_INVALID {error.Message}\n", 2);
        }

        var output = new StringBuilder();
        Session? session = null;
        for (var index = 0; index < requests.Count; index++)
        {
            var table = requests[index];
            var atomId = table.TryGetValue("atom_id", out var value) && value is string id
                && DigestionNonpropositional.IsAtomId(id.Trim()) ? id.Trim() : "invalid";
            CommandResult result;
            try
            {
                var request = LoadRequest([.. StrictUtf8.GetBytes(TomlSerializer.Serialize(table))]);
                session ??= new Session(repository);
                // Reuse the complete single writer, including request validation,
                // adjacency, round-trip validation and atomic commit. The session
                // keeps the scoped ledger and source context across records.
                result = RunCore(
                    root,
                    repository,
                    [],
                    BackfillInventoryWriter.WriteAtom,
                    ReadRequest,
                    static (directory, current, updates) =>
                        IngestCommand.ApplyLedgerUpdatesAtomically(directory, current, updates),
                    reportSource,
                    session,
                    request);
            }
            catch (SettleAtomException error)
            {
                result = new CommandResult(false, string.Empty,
                    $"SETTLE_INVALID {error.Code} {error.Message}\n");
            }
            catch (Exception error) when (error is not OutOfMemoryException)
            {
                result = new CommandResult(false, string.Empty,
                    $"SETTLE_INVALID INFRASTRUCTURE {error.Message}\n");
            }
            output.Append(result.Output);
            if (!result.Success)
            {
                return new(false, output.ToString(),
                    $"SETTLE_BATCH_STOP record={index + 1} atom_id={atomId} settled={index} requested={requests.Count}\n" + result.Error,
                    result.ExitCode);
            }
        }
        output.Append($"SETTLE_BATCH settled={requests.Count} requested={requests.Count}\n");
        return new(true, output.ToString(), string.Empty);
    }
}
