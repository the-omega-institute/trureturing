using System.Collections.Immutable;

namespace StrataLint.Engine;

// SL-028. Two drivers once proved the same proposition under different names
// (ChannelMonotone against DpiDefect) and one formalization round was spent twice.
// The prior-art search that would have caught it is a prose duty no machine reads,
// so this reports the collision the elaborated statement already makes visible.
//
// Advisory, never blocking: restating a frozen result in a fresh namespace is
// lawful, and the 2026-08-18 census over the dev report put the honest human
// collisions at three to five against 4713 authored theorems. Refusing them would
// cost far more than the duplicate work it would prevent.
internal static class DuplicateStatementAdvisory
{
    internal const string Code = "duplicate-statement";

    private const string EquationLemma = "eq_def";
    private const string AutoInstancePrefix = "inst";
    private const string EquationIndexPrefix = "eq_";
    private const string MatchAuxiliaryPrefix = "match_";
    private const string CongruenceLemma = "congr_simp";

    internal static bool IsAffectedBy(RuleEvaluationContext context) =>
        ChangedLeanModules(context).Count > 0;

    // Admission carries exactly one elaborated report, the candidate's, so there is
    // no baseline elaboration to diff declarations against. The delta this rule can
    // decide is therefore the changed Lean module, not the changed declaration: a
    // collision class is reported only when this candidate touched the source of at
    // least one of its members. A pair that predates the candidate on both sides
    // stays silent, which is what keeps the repository's existing collisions from
    // landing on every unrelated PR.
    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
        ArgumentNullException.ThrowIfNull(context);
        var changed = ChangedLeanModules(context);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var classes = context.Lean.Report.Files
            .SelectMany(static entry => entry.Value.Declarations
                .Where(IsAuthoredTheorem)
                .Select(declaration => new AuthoredStatement(
                    entry.Key,
                    declaration.NameKey,
                    declaration.Name,
                    CanonicalStatementWriter.StatementTypeAddress(declaration))))
            .GroupBy(static statement => statement.Address, StringComparer.Ordinal)
            .OrderBy(static group => group.Key, StringComparer.Ordinal);
        foreach (var group in classes)
        {
            var members = group
                .DistinctBy(static statement => (statement.Path.Value, statement.NameKey))
                .OrderBy(static statement => statement.Path.Value, StringComparer.Ordinal)
                .ThenBy(static statement => statement.Name, StringComparer.Ordinal)
                .ToArray();
            if (members.Length < 2)
            {
                continue;
            }

            var anchor = Array.FindIndex(members, statement => changed.Contains(statement.Path));
            if (anchor < 0)
            {
                continue;
            }

            findings.Add(new RuleFinding(
                members[anchor].Path.Value,
                $"{Code}: {members[anchor].Name} repeats the elaborated statement of "
                    + string.Join(
                        ", ",
                        members
                            .Where((_, index) => index != anchor)
                            .Select(static statement => $"{statement.Path.Value}:{statement.Name}")),
                AdmissionEffect.Observe));
        }

        return findings.ToImmutable();
    }

    private static HashSet<RepoPath> ChangedLeanModules(RuleEvaluationContext context) =>
        context.RuleImplementationChanged
            ? context.Lean.Report.Files.Keys.ToHashSet()
            : context.Changes.Paths
                .Where(path => LeanClosureValidator.IsManagedLean(path.Value)
                    && context.Current.TryGetFile(path.Value, out _))
                .ToHashSet();

    // A module report carries every constant the module declares, and the census
    // found the colliding ones to be overwhelmingly machine-made: automatic
    // instances can reach here recorded as theorems (see IsAutoInstance), and the
    // equation compiler emits the rest. Nobody duplicated proof work writing those.
    private static bool IsAuthoredTheorem(LeanDeclaration declaration) =>
        declaration.IncludeInStatement
        && string.Equals(declaration.Kind, "theorem", StringComparison.Ordinal)
        && !declaration.Name.Split('.').Any(IsGeneratedComponent);

    // Closed marker vocabulary, one clause per generator the census named. Each
    // clause is exact rather than a prefix sweep because the two failure directions
    // are not symmetric: a clause that is too narrow adds noise to an advisory that
    // blocks nothing, while one that is too wide silently drops the collisions this
    // rule exists to report. So eq_zero and match_cons must survive it, and eq_1,
    // eq_def and match_1 must not.
    private static bool IsGeneratedComponent(string component) =>
        component.StartsWith('_')
        || string.Equals(component, EquationLemma, StringComparison.Ordinal)
        || IsIndexed(component, EquationIndexPrefix)
        || IsIndexed(component, MatchAuxiliaryPrefix)
        || string.Equals(component, CongruenceLemma, StringComparison.Ordinal)
        || IsAutoInstance(component);

    // The 2026-08-18 census falsified the assumption that automatic instances are
    // defs: the inspector records Prop-valued instances (instIsTransNatLeHAddOfNat_d5
    // twelve times over) as theorems, so kind alone cannot exclude them. Lean's
    // instance namer emits inst followed by an uppercase type head; a human name
    // like instability_bound continues past inst in lowercase and must survive.
    private static bool IsAutoInstance(string component) =>
        component.Length > AutoInstancePrefix.Length
        && component.StartsWith(AutoInstancePrefix, StringComparison.Ordinal)
        && char.IsAsciiLetterUpper(component[AutoInstancePrefix.Length]);

    private static bool IsIndexed(string component, string prefix)
    {
        if (component.Length <= prefix.Length
            || !component.StartsWith(prefix, StringComparison.Ordinal))
        {
            return false;
        }

        for (var index = prefix.Length; index < component.Length; index++)
        {
            if (!char.IsAsciiDigit(component[index]))
            {
                return false;
            }
        }

        return true;
    }

    private sealed record AuthoredStatement(
        RepoPath Path,
        string NameKey,
        string Name,
        string Address);
}
