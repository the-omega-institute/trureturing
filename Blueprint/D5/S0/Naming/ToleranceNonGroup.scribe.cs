using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class ToleranceNonGroupDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-base semantic tolerance contains the identity but need not be closed under composition.",
        H("Fixed-Base Tolerance Is Not a Group"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partial-monoid-action"),
                DeclarationHandle.Create("D5/S0/Naming/ToleranceNonGroup.PartialAction"),
                H("Partial monoid action"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A partial action assigns each monoid element and sentence an optional moved sentence. "
                    + "The identity is defined everywhere, and multiplication is exactly sequential optional "
                    + "composition through Option.bind."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-base-semantic-tolerance-set"),
                DeclarationHandle.Create("D5/S0/Naming/ToleranceNonGroup.toleranceSet"),
                H("Fixed-base semantic tolerance set"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("T"), Underscore, Grp(Varepsilon), Open, F.Id("s"), Close, Sp, Eq, Sp,
                    OpenBrace, F.Id("p"), Sp, Mid, Sp, Exists, Sp, F.Id("sPrime"), Comma, Sp,
                    Operatorname, Grp(F.Id("act")), Open, F.Id("p"), Comma, F.Id("s"), Close,
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("some")), Open, F.Id("sPrime"), Close,
                    Sp, Land, Sp,
                    F.Id("d"), Open, SigmaLower, Open, F.Id("sPrime"), Close, Comma, Sp,
                    SigmaLower, Open, F.Id("s"), Close, Close, Sp, Leq, Sp, Varepsilon,
                    CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A transformation is tolerated at a fixed base sentence s exactly when its partial action "
                    + "is defined there and the semantic displacement from s is at most epsilon."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-base-tolerance-contains-identity-but-is-not-composition-closed"),
                DeclarationHandle.Create("D5/S0/Naming/ToleranceNonGroup.tolerance_non_group"),
                H("Fixed-base tolerance contains the identity but is not composition-closed"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Sp, Leq, Sp, Varepsilon, Sp, Rightarrow, Sp,
                    D(1), Sp, InMacro, Sp, F.Id("T"), Underscore, Grp(Varepsilon), Open, F.Id("s"), Close,
                    RowBreak,
                    Land, Sp, Exists, Sp, Pi, Underscore, Grp(D(1)), InMacro, Sp,
                    Operatorname, Grp(F.Id("Perm")), Open,
                    Operatorname, Grp(F.Id("Fin")), Open, D(3), Close, Close, Comma, Sp,
                    Pi, Underscore, Grp(D(2)), InMacro, Sp,
                    Operatorname, Grp(F.Id("Perm")), Open,
                    Operatorname, Grp(F.Id("Fin")), Open, D(3), Close, Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("IsCompositionCounterexample")), Open,
                    Operatorname, Grp(F.Id("permutationAction")), Open,
                    Operatorname, Grp(F.Id("Fin")), Open, D(3), Close, Close, Comma, Sp,
                    Operatorname, Grp(F.Id("sentenceMeaning")), Comma, Sp, D(0), Comma, Sp,
                    Operatorname, Grp(F.Id("abc")), Comma, Sp,
                    Pi, Underscore, Grp(D(1)), Comma, Sp, Pi, Underscore, Grp(D(2)), Close,
                    RowBreak,
                    Land, Sp, Forall, Sp, Pi, Underscore, Grp(D(1)), InMacro, Sp, F.Id("P"), Comma, Sp,
                    Pi, Underscore, Grp(D(2)), InMacro, Sp, F.Id("P"), Comma, Sp,
                    F.Id("s"), Underscore, Grp(D(1)), InMacro, Sp, F.Id("S"), Comma, Sp,
                    F.Id("s"), Underscore, Grp(D(2)), InMacro, Sp, F.Id("S"), Comma, Sp,
                    OpenBracket,
                    Pi, Underscore, Grp(D(1)), InMacro, Sp,
                    F.Id("T"), Underscore, Grp(Varepsilon), Open, F.Id("s"), Close,
                    Sp, Land, Sp,
                    Pi, Underscore, Grp(D(2)), InMacro, Sp,
                    F.Id("T"), Underscore, Grp(Varepsilon), Open, F.Id("s"), Close,
                    RowBreak,
                    Land, Sp, Operatorname, Grp(F.Id("act")), Open,
                    Pi, Underscore, Grp(D(1)), Comma, Sp, F.Id("s"), Close,
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("some")), Open,
                    F.Id("s"), Underscore, Grp(D(1)), Close,
                    RowBreak,
                    Land, Sp, Operatorname, Grp(F.Id("act")), Open,
                    Pi, Underscore, Grp(D(2)), Comma, Sp,
                    F.Id("s"), Underscore, Grp(D(1)), Close,
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("some")), Open,
                    F.Id("s"), Underscore, Grp(D(2)), Close,
                    CloseBracket, Sp, Rightarrow, Sp, OpenBracket,
                    Operatorname, Grp(F.Id("act")), Open,
                    Pi, Underscore, Grp(D(2)), Star, Pi, Underscore, Grp(D(1)), Comma, Sp,
                    F.Id("s"), Close, Sp, Eq, Sp, Operatorname, Grp(F.Id("some")), Open,
                    F.Id("s"), Underscore, Grp(D(2)), Close,
                    RowBreak,
                    Land, Sp,
                    F.Id("d"), Open,
                    SigmaLower, Open, F.Id("s"), Underscore, Grp(D(2)), Close, Comma, Sp,
                    SigmaLower, Open, F.Id("s"), Close, Close,
                    Sp, Leq, Sp,
                    F.Id("d"), Open,
                    SigmaLower, Open, F.Id("s"), Underscore, Grp(D(2)), Close, Comma, Sp,
                    SigmaLower, Open, F.Id("s"), Underscore, Grp(D(1)), Close, Close,
                    Sp, Plus, Sp, Varepsilon,
                    RowBreak,
                    Land, Sp, Exists, Sp,
                    F.Id("baseMoved"), Comma, Sp,
                    Operatorname, Grp(F.Id("act")), Open,
                    Pi, Underscore, Grp(D(2)), Comma, Sp, F.Id("s"), Close,
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("some")), Open,
                    F.Id("baseMoved"), Close,
                    Sp, Land, Sp,
                    F.Id("d"), Open,
                    SigmaLower, Open, F.Id("baseMoved"), Close,
                    Comma, Sp, SigmaLower, Open, F.Id("s"), Close, Close,
                    Sp, Leq, Sp, Varepsilon, CloseBracket))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Clause (i): for every partial monoid action, meaning map, base sentence, and "
                        + "nonnegative epsilon, the everywhere-defined identity belongs to the fixed-base "
                        + "tolerance set.")),
                    Paragraph(Text(
                        "Clause (ii): the total permutation action on three positions supplies a concrete "
                        + "special case. Swapping positions 2 and 3 sends ABC to ACB, swapping positions 1 "
                        + "and 2 sends ABC to BAC, and applying the second swap after the first sends ACB to "
                        + "CAB. The meanings of ABC, ACB, and BAC are zero, while CAB has meaning one. At "
                        + "epsilon zero both nontrivial swaps are tolerated at ABC, but their composite is not, "
                        + "so the nonempty tolerance set is not closed under composition.")),
                    Paragraph(Text(
                        "Clause (iii): whenever the first action, the intermediate second action, and the "
                        + "composite are defined, the metric triangle inequality bounds the composite "
                        + "displacement by d(sigma(s2), sigma(s1)) + epsilon. Membership of the second "
                        + "transformation in the tolerance set controls only its separate action at the "
                        + "original sentence s; it gives no prior bound on its displacement at the moved "
                        + "sentence s1. The Lean conclusion retains both facts explicitly.")),
                    Paragraph(Text(
                        "Repository and pinned-mathlib searches found no matching partial-action tolerance "
                        + "theorem. Loogle returned zero declarations named PartialAction. GitHub code search "
                        + "required authentication, LeanSearch GET probes were unavailable, and grep.app was "
                        + "rate-limited. The proof reuses mathlib's metric triangle inequality; the explicit "
                        + "finite permutation witness is checked directly."))),
                DescribeRole.Theorem)),
        []));
}
