using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum UtilityKind
{
    None,
    BoundedEnumeration,
    Checker,
    NumericReduction,
    CertifiedInstance,
}

internal enum UtilityBasisKind
{
    None,
    Consumer,
    Refutes,
    Terminal,
}

internal enum UtilityTargetKind
{
    Gid,
    Atom,
    Task,
}

internal enum UtilityParseFailure
{
    None,
    Missing,
    Syntax,
    InstanceMissing,
    PremisesMissing,
}

internal sealed record UtilityTarget(UtilityTargetKind Kind, string Value, Gid? Gid);

internal sealed record UtilityDeclaration(
    UtilityKind Kind,
    UtilityBasisKind BasisKind,
    UtilityTarget? BasisTarget,
    Gid? Instance,
    ImmutableArray<Gid> Premises,
    Gid? Result);

internal static class UtilitySyntax
{
    internal static bool TryParse(
        string? text,
        out UtilityDeclaration? utility,
        out UtilityParseFailure failure)
    {
        utility = null;
        failure = UtilityParseFailure.Syntax;
        if (text is null || string.Equals(text, "EDIT-ME", StringComparison.Ordinal))
        {
            failure = UtilityParseFailure.Missing;
            return false;
        }

        if (string.Equals(text, "none", StringComparison.Ordinal))
        {
            utility = new UtilityDeclaration(
                UtilityKind.None,
                UtilityBasisKind.None,
                null,
                null,
                [],
                null);
            failure = UtilityParseFailure.None;
            return true;
        }

        var encodedFields = text.Split("; ", StringSplitOptions.None);
        var fields = new List<(string Key, string Value)>();
        var keys = new HashSet<string>(StringComparer.Ordinal);
        foreach (var encodedField in encodedFields)
        {
            var separator = encodedField.IndexOf('=');
            if (separator <= 0
                || separator == encodedField.Length - 1
                || !keys.Add(encodedField[..separator]))
            {
                return false;
            }

            fields.Add((encodedField[..separator], encodedField[(separator + 1)..]));
        }

        if (fields.Count is < 2 or > 5
            || fields[0].Key != "kind"
            || fields[1].Key != "basis")
        {
            return false;
        }

        var optionalKeys = fields.Skip(2).Select(static field => field.Key).ToArray();
        var canonicalOptionalKeys = new[] { "instance", "premises", "result" }
            .Where(optionalKeys.Contains)
            .ToArray();
        if (!optionalKeys.SequenceEqual(canonicalOptionalKeys, StringComparer.Ordinal))
        {
            return false;
        }

        var kind = fields[0].Value switch
        {
            "bounded-enumeration" => UtilityKind.BoundedEnumeration,
            "checker" => UtilityKind.Checker,
            "numeric-reduction" => UtilityKind.NumericReduction,
            "certified-instance" => UtilityKind.CertifiedInstance,
            _ => (UtilityKind?)null,
        };
        if (kind is null || !TryParseBasis(fields[1].Value, out var basisKind, out var basisTarget))
        {
            return false;
        }

        Gid? instance = null;
        var premises = ImmutableArray<Gid>.Empty;
        Gid? result = null;
        foreach (var field in fields.Skip(2))
        {
            if (field.Key == "instance")
            {
                if (!TryParseDeclarationGid(field.Value, out instance)) return false;
            }
            else if (field.Key == "premises")
            {
                var parsed = ImmutableArray.CreateBuilder<Gid>();
                foreach (var item in field.Value.Split(',', StringSplitOptions.None))
                {
                    if (!TryParseDeclarationGid(item, out var premise)) return false;
                    parsed.Add(premise);
                }

                premises = parsed.ToImmutable();
            }
            else if (field.Key == "result")
            {
                if (!TryParseDeclarationGid(field.Value, out result)) return false;
            }
        }

        if (kind is UtilityKind.Checker && instance is null)
        {
            failure = UtilityParseFailure.InstanceMissing;
            return false;
        }

        if (kind is UtilityKind.NumericReduction && premises.IsEmpty)
        {
            failure = UtilityParseFailure.PremisesMissing;
            return false;
        }

        if (kind is UtilityKind.NumericReduction
            && basisKind is not (UtilityBasisKind.Consumer or UtilityBasisKind.Refutes))
        {
            return false;
        }

        utility = new UtilityDeclaration(
            kind.Value,
            basisKind,
            basisTarget,
            instance,
            premises,
            result);
        failure = UtilityParseFailure.None;
        return true;
    }

    private static bool TryParseBasis(
        string text,
        out UtilityBasisKind kind,
        out UtilityTarget? target)
    {
        kind = UtilityBasisKind.None;
        target = null;
        if (text.StartsWith("consumer=", StringComparison.Ordinal)
            && TryParseDeclarationGid(text["consumer=".Length..], out var consumer))
        {
            kind = UtilityBasisKind.Consumer;
            target = new UtilityTarget(UtilityTargetKind.Gid, consumer.Value, consumer);
            return true;
        }

        if (text.StartsWith("refutes=", StringComparison.Ordinal)
            && TryParseTarget(text["refutes=".Length..], out target))
        {
            kind = UtilityBasisKind.Refutes;
            return true;
        }

        if (text.StartsWith("terminal=", StringComparison.Ordinal)
            && TryParseTarget(text["terminal=".Length..], out target))
        {
            kind = UtilityBasisKind.Terminal;
            return true;
        }

        return false;
    }

    private static bool TryParseTarget(string text, out UtilityTarget? target)
    {
        target = null;
        if (text.StartsWith("atom:", StringComparison.Ordinal)
            && IsAtomId(text["atom:".Length..]))
        {
            target = new UtilityTarget(UtilityTargetKind.Atom, text["atom:".Length..], null);
            return true;
        }

        if (text.StartsWith("task:", StringComparison.Ordinal)
            && IsTaskCode(text["task:".Length..]))
        {
            target = new UtilityTarget(UtilityTargetKind.Task, text["task:".Length..], null);
            return true;
        }

        if (text.StartsWith("gid:", StringComparison.Ordinal)
            && TryParseDeclarationGid(text["gid:".Length..], out var gid))
        {
            target = new UtilityTarget(UtilityTargetKind.Gid, gid.Value, gid);
            return true;
        }

        return false;
    }

    private static bool IsAtomId(string value) =>
        value.Length == 64
        && value.All(static character =>
            character is >= '0' and <= '9' or >= 'a' and <= 'f');

    private static bool IsTaskCode(string value) =>
        value.Length == 8
        && value.StartsWith("D5-T", StringComparison.Ordinal)
        && value[4..].All(char.IsAsciiDigit);

    private static bool TryParseDeclarationGid(string text, out Gid gid)
    {
        if (Gid.TryParse(text, out var parsed)
            && parsed.ToTarget() is Target.Formal { Declaration: not null })
        {
            gid = parsed;
            return true;
        }

        gid = null!;
        return false;
    }
}
