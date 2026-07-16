using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal enum MachineCustodianKind
{
    Loader,
    C0Anchor,
    RuleId,
}

internal sealed record MachineCustodian
{
    internal MachineCustodian(MachineCustodianKind kind, string reference)
    {
        Kind = kind;
        Reference = kind switch
        {
            MachineCustodianKind.Loader => ContractEpochSyntax.ExactPath(reference),
            MachineCustodianKind.C0Anchor => ContractEpochSyntax.C0Anchor(reference),
            MachineCustodianKind.RuleId => ContractEpochSyntax.RuleId(reference),
            _ => throw new ArgumentOutOfRangeException(nameof(kind)),
        };
    }

    internal MachineCustodianKind Kind { get; }

    internal string Reference { get; }
}

internal abstract record TransitionPlan
{
    private TransitionPlan() { }

    internal sealed record CustodyTransferV1 : TransitionPlan
    {
        internal CustodyTransferV1(
            IEnumerable<string> exactPaths,
            MachineCustodian newCustodian,
            string receipt)
        {
            ExactPaths = ContractEpochSyntax.ExactPaths(exactPaths, allowEmpty: false);
            NewCustodian = newCustodian ?? throw new ArgumentNullException(nameof(newCustodian));
            Receipt = ContractEpochSyntax.ContentRef(receipt);
        }

        internal ImmutableArray<string> ExactPaths { get; }

        internal MachineCustodian NewCustodian { get; }

        internal string Receipt { get; }
    }

    internal sealed record AuthorityDischargeV1 : TransitionPlan
    {
        internal AuthorityDischargeV1(
            IEnumerable<string> exactPaths,
            string? ruleObligation,
            string unreachabilityProofRef)
        {
            ExactPaths = ContractEpochSyntax.ExactPaths(exactPaths, allowEmpty: true);
            RuleObligation = ruleObligation is null
                ? null
                : ContractEpochSyntax.RuleId(ruleObligation);
            if (ExactPaths.IsEmpty == (RuleObligation is null))
            {
                throw new ArgumentException(
                    "authority discharge must select exactly one of exact paths or rule obligation");
            }

            UnreachabilityProofRef = ContractEpochSyntax.ContentRef(unreachabilityProofRef);
        }

        internal ImmutableArray<string> ExactPaths { get; }

        internal string? RuleObligation { get; }

        internal string UnreachabilityProofRef { get; }
    }
}

internal static class ContractEpochSyntax
{
    internal static ImmutableArray<string> ExactPaths(
        IEnumerable<string> rawPaths,
        bool allowEmpty)
    {
        ArgumentNullException.ThrowIfNull(rawPaths);
        var exact = new HashSet<string>(StringComparer.Ordinal);
        var folded = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        var builder = ImmutableArray.CreateBuilder<string>();
        foreach (var raw in rawPaths)
        {
            var path = ExactPath(raw);
            if (!exact.Add(path) || !folded.Add(path))
            {
                throw new ArgumentException($"duplicate or case-colliding exact path: {path}");
            }

            builder.Add(path);
        }

        if (!allowEmpty && builder.Count == 0)
        {
            throw new ArgumentException("transition plan exact paths must not be empty");
        }

        return builder.Order(StringComparer.Ordinal).ToImmutableArray();
    }

    internal static string ExactPath(string raw)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(raw);
        if (!RepoPath.TryCreate(raw, out var path)
            || raw.EndsWith("/", StringComparison.Ordinal)
            || raw.IndexOfAny(['*', '?', '[', ']', '{', '}']) >= 0)
        {
            throw new ArgumentException($"transition plan value is not an exact path: {raw}");
        }

        return path.Value;
    }

    internal static string RuleId(string value)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(value);
        if (value.Length != 6
            || !value.StartsWith("SL-", StringComparison.Ordinal)
            || value.AsSpan(3).IndexOfAnyExceptInRange('0', '9') >= 0)
        {
            throw new ArgumentException($"transition plan rule obligation is invalid: {value}");
        }

        return value;
    }

    internal static string ContentRef(string value)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(value);
        if (value.Length != 71
            || !value.StartsWith("sha256:", StringComparison.Ordinal)
            || value.AsSpan(7).IndexOfAnyExcept("0123456789abcdef") >= 0)
        {
            throw new ArgumentException($"transition evidence reference is invalid: {value}");
        }

        return value;
    }

    internal static string PolicyRoot(string value) => ContentRef(value);

    internal static string TreeOid(string value)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(value);
        if (value.Length != 49
            || !value.StartsWith("git-sha1:", StringComparison.Ordinal)
            || value.AsSpan(9).IndexOfAnyExcept("0123456789abcdef") >= 0)
        {
            throw new ArgumentException($"transition baseline tree oid is invalid: {value}");
        }

        return value;
    }

    internal static string PlanId(string value)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(value);
        if (value.Length is < 3 or > 64
            || value[0] is not (>= 'A' and <= 'Z')
            || value.Any(static character =>
                character is not (>= 'A' and <= 'Z')
                    and not (>= '0' and <= '9')
                    and not '-'))
        {
            throw new ArgumentException($"transition plan id is invalid: {value}");
        }

        return value;
    }

    internal static string C0Anchor(string value)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(value);
        if (!value.StartsWith("c0/", StringComparison.Ordinal)
            || value.Length == "c0/".Length
            || value.Any(char.IsControl)
            || !string.Equals(value, value.Trim(), StringComparison.Ordinal))
        {
            throw new ArgumentException($"transition C0 anchor is invalid: {value}");
        }

        return value;
    }
}
