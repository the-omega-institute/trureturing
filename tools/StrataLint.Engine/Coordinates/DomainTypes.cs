using System.Diagnostics.CodeAnalysis;
using System.Globalization;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

public enum Plane
{
    Formal,
    Blueprint,
    Evidence,
    Chronicle,
    Library,
    Papers,
}

public enum Stratum
{
    S0,
    S1,
    S2,
    S3,
    S4,
}

public enum Generality
{
    General,
    Instance,
    Extremal,
}

public enum DisplaySeverity
{
    Info,
    Warning,
    Error,
}

public enum AdmissionEffect
{
    Observe,
    Block,
    HumanGate,
}

public enum RuleLifecycle
{
    Active,
    Deferred,
}

public sealed record RepoPath
{
    private RepoPath(string value) => Value = value;

    public string Value { get; }

    public static bool TryCreate(string? value, [NotNullWhen(true)] out RepoPath? path)
    {
        if (!string.IsNullOrEmpty(value)
            && !value.StartsWith("/", StringComparison.Ordinal)
            && value.IndexOf('\\') < 0
            && value.IndexOf('\0') < 0
            && value.Split('/').All(static segment => segment.Length > 0 && segment is not "." and not ".."))
        {
            path = new RepoPath(value);
            return true;
        }

        path = null;
        return false;
    }

    public override string ToString() => Value;

    internal static RepoPath CreateKnown(string value) =>
        TryCreate(value, out var path)
            ? path
            : throw new ArgumentException("Invalid repository path.", nameof(value));
}

public sealed record RuleId
{
    private RuleId(string value) => Value = value;

    public string Value { get; }

    public static bool TryCreate(string? value, [NotNullWhen(true)] out RuleId? ruleId)
    {
        if (value is { Length: 6 }
            && value.StartsWith("SL-", StringComparison.Ordinal)
            && int.TryParse(
                value.AsSpan(3),
                NumberStyles.None,
                CultureInfo.InvariantCulture,
                out var number)
            && (number is >= 0 and <= 23 || number is 25 or 26 or 28 or 29 or 30 or 31))
        {
            ruleId = new RuleId(value);
            return true;
        }

        ruleId = null;
        return false;
    }

    public static RuleId CreateKnown(int number)
    {
        var value = $"SL-{number:000}";
        return TryCreate(value, out var ruleId)
            ? ruleId
            : throw new ArgumentOutOfRangeException(nameof(number));
    }

    public override string ToString() => Value;
}

public sealed record CaseId
{
    private CaseId(string value) => Value = value;

    public string Value { get; }

    public static bool TryCreate(string? value, [NotNullWhen(true)] out CaseId? caseId)
    {
        if (value is { Length: 8 }
            && value.StartsWith("D5-T", StringComparison.Ordinal)
            && value.AsSpan(4).IndexOfAnyExceptInRange('0', '9') < 0)
        {
            caseId = new CaseId(value);
            return true;
        }

        caseId = null;
        return false;
    }

    public static CaseId CreateKnown(string value) =>
        TryCreate(value, out var caseId)
            ? caseId
            : throw new ArgumentException("Invalid case id.", nameof(value));

    public override string ToString() => Value;
}

public sealed record DomainId
{
    private DomainId(string value) => Value = value;

    public string Value { get; }

    public static bool TryCreate(string? value, [NotNullWhen(true)] out DomainId? domainId)
    {
        if (value is not null
            && Regex.IsMatch(value, "^[A-Z][A-Za-z0-9]*$", RegexOptions.CultureInvariant))
        {
            domainId = new DomainId(value);
            return true;
        }

        domainId = null;
        return false;
    }

    public override string ToString() => Value;
}

public sealed record ArtifactKindId
{
    private ArtifactKindId(string value) => Value = value;

    public string Value { get; }

    public static bool TryCreate(string? value, [NotNullWhen(true)] out ArtifactKindId? artifactKindId)
    {
        if (value is not null
            && Regex.IsMatch(value, "^[a-z][a-z0-9-]*$", RegexOptions.CultureInvariant))
        {
            artifactKindId = new ArtifactKindId(value);
            return true;
        }

        artifactKindId = null;
        return false;
    }

    public override string ToString() => Value;
}
