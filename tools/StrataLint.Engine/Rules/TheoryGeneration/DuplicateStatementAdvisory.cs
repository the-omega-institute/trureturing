using System.Collections.Immutable;

namespace StrataLint.Engine;

// SL-028. Exact declaration reuse advisory.
//
// The original incident was two drivers proving one proposition under different
// names. The same failure mode also applies to authored value-bearing declarations:
// a second public def or opaque can reproduce an elaborated type-and-value body
// under a fresh name while every proof remains valid. The canonical Lean report
// already exposes both shapes through one declaration material address, so this
// rule consumes that existing identity instead of introducing another fingerprint.
//
// The comparison remains deliberately exact. Theorems compare their elaborated
// type because proof bodies are absent from statement-v1; defs and opaques compare
// universe parameters, type, and value because statement-v1 carries the value for
// those kinds. Definitional equality, algebraic rewrites, symmetry, index shifts,
// and representation bridges remain outside this rule and require separate Lean
// evidence before any reuse conclusion is drawn.
//
// Advisory, never blocking: exact restatements and exact definition aliases can be
// lawful public interfaces. The finding exists to make that choice visible before
// a second owner is accepted, not to decide the owner automatically.
internal static class DuplicateStatementAdvisory
{
    internal const string StatementCode = "duplicate-statement";
    internal const string DefinitionCode = "duplicate-definition";

    private const string TheoremKind = "theorem";
    private const string DefinitionKind = "def";
    private const string OpaqueKind = "opaque";
    private const string EquationLemma = "eq_def";
    private const string AutoInstancePrefix = "inst";
    private const string EquationIndexPrefix = "eq_";
    private const string MatchAuxiliaryPrefix = "match_";
    private const string CongruenceLemma = "congr_simp";
    private const string CasesOn = "casesOn";
    private const string RecOn = "recOn";

    internal static bool IsAffectedBy(RuleEvaluationContext context) =>
        ChangedLeanModules(context).Count > 0;

    // Admission carries exactly one elaborated report, the candidate's, so there is
    // no baseline elaboration to diff declarations against. The delta this rule can
    // decide is therefore the changed Lean module, not the changed declaration: a
    // collision class is reported only when this candidate touched the source of at
    // least one of its members. A pair that predates the candidate on both sides
    // stays silent, which keeps existing collisions off unrelated pull requests.
    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
        ArgumentNullException.ThrowIfNull(context);
        var changed = ChangedLeanModules(context);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var classes = context.Lean.Report.Files
            .SelectMany(static entry => entry.Value.Declarations
                .Where(IsAuthoredDeclaration)
                .Select(declaration => new AuthoredDeclaration(
                    entry.Key,
                    declaration.NameKey,
                    declaration.Name,
                    declaration.Kind,
                    CanonicalStatementWriter.StatementTypeAddress(declaration))))
            .GroupBy(static declaration =>
                new CollisionKey(declaration.Kind, declaration.Address))
            .OrderBy(static group => group.Key.Kind, StringComparer.Ordinal)
            .ThenBy(static group => group.Key.Address, StringComparer.Ordinal);
        foreach (var group in classes)
        {
            var members = group
                .DistinctBy(static declaration =>
                    (declaration.Path.Value, declaration.NameKey))
                .OrderBy(static declaration => declaration.Path.Value, StringComparer.Ordinal)
                .ThenBy(static declaration => declaration.Name, StringComparer.Ordinal)
                .ToArray();
            if (members.Length < 2)
            {
                continue;
            }

            var anchor = Array.FindIndex(
                members,
                declaration => changed.Contains(declaration.Path));
            if (anchor < 0)
            {
                continue;
            }

            var selected = members[anchor];
            findings.Add(new RuleFinding(
                selected.Path.Value,
                $"{CodeFor(selected.Kind)}: {selected.Name} repeats the "
                    + $"{MaterialDescription(selected.Kind)} of "
                    + string.Join(
                        ", ",
                        members
                            .Where((_, index) => index != anchor)
                            .Select(static declaration =>
                                $"{declaration.Path.Value}:{declaration.Name}")),
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

    // A module report carries every constant the module declares. The generated-name
    // vocabulary filters equation-compiler artifacts, recursor façades, and automatic
    // instances for all supported kinds. The kind gate then limits this rule to
    // authored theorems and value-bearing declarations whose exact material is
    // meaningful for reuse review.
    private static bool IsAuthoredDeclaration(LeanDeclaration declaration) =>
        declaration.IncludeInStatement
        && IsSupportedKind(declaration.Kind)
        && !declaration.Name.Split('.').Any(IsGeneratedComponent);

    private static bool IsSupportedKind(string kind) =>
        string.Equals(kind, TheoremKind, StringComparison.Ordinal)
        || string.Equals(kind, DefinitionKind, StringComparison.Ordinal)
        || string.Equals(kind, OpaqueKind, StringComparison.Ordinal);

    private static string CodeFor(string kind) =>
        string.Equals(kind, TheoremKind, StringComparison.Ordinal)
            ? StatementCode
            : DefinitionCode;

    private static string MaterialDescription(string kind) =>
        string.Equals(kind, TheoremKind, StringComparison.Ordinal)
            ? "elaborated statement"
            : $"elaborated {kind} type-and-value material";

    // Closed marker vocabulary, one clause per generator shape established by the
    // repository census. Each clause is exact rather than a broad prefix sweep because
    // the two failure directions are not symmetric: a clause that is too narrow adds
    // noise to an advisory that blocks nothing, while one that is too wide silently
    // drops the collisions this rule exists to report. Thus eq_zero, match_cons,
    // casesOnPurpose and recOnPurpose survive; eq_1, match_1_4, casesOn and recOn do not.
    private static bool IsGeneratedComponent(string component) =>
        component.StartsWith('_')
        || string.Equals(component, EquationLemma, StringComparison.Ordinal)
        || IsNumberedCompilerAuxiliary(component, EquationIndexPrefix)
        || IsNumberedCompilerAuxiliary(component, MatchAuxiliaryPrefix)
        || string.Equals(component, CongruenceLemma, StringComparison.Ordinal)
        || string.Equals(component, CasesOn, StringComparison.Ordinal)
        || string.Equals(component, RecOn, StringComparison.Ordinal)
        || IsAutoInstance(component);

    // Lean may append more than one numeric coordinate to a generated equation or
    // match declaration, for example match_1_1 and match_1_8. Every segment after the
    // prefix must be a nonempty ASCII-decimal number. Near shapes such as match_cons,
    // match_1_tail and eq_zero remain authored.
    private static bool IsNumberedCompilerAuxiliary(string component, string prefix)
    {
        if (component.Length <= prefix.Length
            || !component.StartsWith(prefix, StringComparison.Ordinal))
        {
            return false;
        }

        var hasDigitInSegment = false;
        for (var index = prefix.Length; index < component.Length; index++)
        {
            var current = component[index];
            if (char.IsAsciiDigit(current))
            {
                hasDigitInSegment = true;
                continue;
            }

            if (current == '_' && hasDigitInSegment)
            {
                hasDigitInSegment = false;
                continue;
            }

            return false;
        }

        return hasDigitInSegment;
    }

    // The 2026-08-18 census falsified the assumption that automatic instances are
    // defs: the inspector records Prop-valued instances (instIsTransNatLeHAddOfNat_d5
    // twelve times over) as theorems, so kind alone cannot exclude them. Lean's
    // instance namer emits inst followed by an uppercase type head; a human name
    // like instability_bound continues past inst in lowercase and must survive.
    private static bool IsAutoInstance(string component) =>
        component.Length > AutoInstancePrefix.Length
        && component.StartsWith(AutoInstancePrefix, StringComparison.Ordinal)
        && char.IsAsciiLetterUpper(component[AutoInstancePrefix.Length]);

    private sealed record CollisionKey(string Kind, string Address);

    private sealed record AuthoredDeclaration(
        RepoPath Path,
        string NameKey,
        string Name,
        string Kind,
        string Address);
}
