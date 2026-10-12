using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;
using Trureturing.Truth;

namespace StrataLint.Cli;

internal static class TruthReleaseCommand
{
    internal static ExplicitCommandResult Run(IRepositoryGateway repository,
        IScribeEmissionVerifier? scribeEmissionVerifier, IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(arguments);
        if (!TryParseArguments(arguments, out _, out var missingScribePack))
            return missingScribePack ? MissingScribePackUsage() : Usage();
        return new(2, string.Empty, "TRUTH_RELEASE_EVENT_FIELDS_UNAVAILABLE "
            + "frozen-ledger-head and source-snapshot frozen_ledger_sequence have no state-table source; issuance is unavailable\n");
    }

    internal static bool IsReleaseInput(string path) =>
        !path.StartsWith("Meta/Digestion/", StringComparison.Ordinal)
        && !path.StartsWith("docs/", StringComparison.Ordinal)
        && !path.StartsWith("Blueprint/", StringComparison.Ordinal);

    private static bool TryParseArguments(
        IReadOnlyList<string> arguments,
        out TruthReleaseArguments options,
        out bool missingScribePack)
    {
        options = default;
        missingScribePack = false;
        if (arguments.Count % 2 != 0)
        {
            return false;
        }

        string? outDirectory = null;
        string? candidateLeanReport = null;
        string? producerPackageCommit = null;
        string? producedAt = null;
        string? scribePackPath = null;
        string? scribePackDigest = null;
        bool? commitOnProtectedDev = null;
        var requiredChecks = ImmutableArray.CreateBuilder<TruthReleaseRequiredCheck>();
        for (var index = 0; index < arguments.Count; index += 2)
        {
            var value = arguments[index + 1];
            if (string.IsNullOrWhiteSpace(value))
            {
                return false;
            }

            switch (arguments[index])
            {
                case "--out" when outDirectory is null:
                    outDirectory = value;
                    break;
                case "--candidate-lean-report" when candidateLeanReport is null:
                    candidateLeanReport = value;
                    break;
                case "--producer-package-commit" when producerPackageCommit is null:
                    producerPackageCommit = value;
                    break;
                case "--produced-at" when producedAt is null:
                    producedAt = value;
                    break;
                case "--scribe-pack" when scribePackPath is null:
                    scribePackPath = value;
                    break;
                case "--scribe-pack-digest" when scribePackDigest is null:
                    scribePackDigest = value;
                    break;
                case "--commit-on-protected-dev" when commitOnProtectedDev is null
                    && bool.TryParse(value, out var parsedCommitOnProtectedDev):
                    commitOnProtectedDev = parsedCommitOnProtectedDev;
                    break;
                case "--required-check" when TryParseRequiredCheck(value, out var requiredCheck):
                    requiredChecks.Add(requiredCheck);
                    break;
                default:
                    return false;
            }
        }

        if (outDirectory is null
            || candidateLeanReport is null
            || producerPackageCommit is null
            || producedAt is null
            || commitOnProtectedDev is null
            || requiredChecks.Count == 0)
        {
            return false;
        }

        if (scribePackPath is null || scribePackDigest is null)
        {
            missingScribePack = true;
            return false;
        }

        if (!ScribePackInput.IsDigest(scribePackDigest))
        {
            return false;
        }

        options = new TruthReleaseArguments(
            outDirectory,
            candidateLeanReport,
            producerPackageCommit,
            producedAt,
            new TruthReleaseTrust(
                commitOnProtectedDev.Value,
                requiredChecks.ToImmutable(),
                BlessedBy: null),
            scribePackPath,
            scribePackDigest);
        return true;
    }

    private static bool TryParseRequiredCheck(
        string value,
        out TruthReleaseRequiredCheck requiredCheck)
    {
        requiredCheck = null!;
        var separator = value.IndexOf('=', StringComparison.Ordinal);
        if (separator <= 0 || separator == value.Length - 1)
        {
            return false;
        }

        requiredCheck = new TruthReleaseRequiredCheck(
            value[..separator],
            value[(separator + 1)..]);
        return true;
    }

    private static ExplicitCommandResult Usage() => new(
        1,
        string.Empty,
        "USAGE: StrataLint truth-release --out DIR --candidate-lean-report FILE "
            + "--producer-package-commit COMMIT --produced-at TIMESTAMP "
            + "--commit-on-protected-dev true|false "
            + "--required-check NAME=CONCLUSION (required: "
            + "every required check supplied by the caller" + ") "
            + "--scribe-pack FILE --scribe-pack-digest HEX64\n");

    private static ExplicitCommandResult MissingScribePackUsage() => new(
        2,
        string.Empty,
        "TRUTH_RELEASE_INVALID required Scribe resource pack: "
            + "--scribe-pack FILE --scribe-pack-digest HEX64\n");

    private readonly record struct TruthReleaseArguments(
        string OutDirectory,
        string CandidateLeanReport,
        string ProducerPackageCommit,
        string ProducedAt,
        TruthReleaseTrust Trust,
        string ScribePackPath,
        string ScribePackDigest);
}
