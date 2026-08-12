using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class TerminalGradeDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A stabilized guarded ledger partitions its semantic statements into migrated, wall, and resident parts.",
        H("Terminal Grade Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("terminal-grade-three-way-decomposition"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/TerminalGradeDecomposition.terminal_grade_three_way_decomposition"),
                H("Terminal grades give a three-way disjoint decomposition"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("RepairClause")), Open, F.Id("history"), Close, Comma, Sp,
                    F.Id("W"), Sp, Subseteq, Sp, F.Id("Sem"), Comma, RowBreak,
                    Forall, Sp, F.Id("t"), Comma, Sp, F.Id("g"), InMacro, Sp, F.Id("T"), Comma, Sp,
                    SigmaLower, Underscore, Grp(F.Id("t")), Open, F.Id("g"), Close,
                    InMacro, Sp, F.Id("Gplus"), Comma, RowBreak,
                    Forall, Sp, F.Id("t"), Comma, Sp, F.Id("w"), InMacro, Sp, F.Id("W"), Comma, Sp,
                    Open, SigmaLower, Underscore, Grp(F.Id("t")), Open, F.Id("w"), Close,
                    InMacro, Sp, F.Id("Gplus"), Sp, Land, Sp,
                    Forall, Sp, F.Id("g"), InMacro, Sp, F.Id("T"), Comma, Sp,
                    SigmaLower, Underscore, Grp(F.Id("t")), Open, F.Id("g"), Close,
                    InMacro, Sp, F.Id("Gplus"), Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("forbidden")), Open, F.Id("t"), Comma, F.Id("w"), Close,
                    Comma, RowBreak,
                    Forall, Sp, F.Id("t"), Comma, Sp, F.Id("w"), InMacro, Sp, F.Id("W"), Comma, Sp,
                    Neg, Operatorname, Grp(F.Id("forbidden")), Open,
                    F.Id("t"), Comma, F.Id("w"), Close, RowBreak,
                    Rightarrow, Sp, Exists, Bang, Sp,
                    SigmaLower, Underscore, Grp(Infty), Colon, Sp,
                    F.Id("Statement"), Sp, To, Sp, F.Id("Grade"), Comma, Sp,
                    Open, Forall, Sp, F.Id("s"), Comma, Sp, Exists, Sp, F.Id("N"), Sp,
                    Geq, Sp,
                    Operatorname, Grp(F.Id("enrolledAt")), Open, F.Id("s"), Close, Comma, Sp,
                    Forall, Sp, F.Id("t"), Sp, Geq, Sp, F.Id("N"), Comma, Sp,
                    SigmaLower, Underscore, Grp(F.Id("t")), Open, F.Id("s"), Close,
                    Sp, Eq, Sp, SigmaLower, Underscore, Grp(Infty), Open, F.Id("s"), Close,
                    Close, Sp, Land, RowBreak,
                    F.Id("M"), Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("intersection")), Open,
                    F.Id("Sem"), Comma,
                    Operatorname, Grp(F.Id("preimage")), Open,
                    SigmaLower, Underscore, Grp(Infty), Comma, F.Id("Gplus"), Close, Close,
                    Comma, Sp,
                    F.Id("R"), Sp, Eq, Sp, F.Id("Sem"), Sp, Setminus, Sp,
                    Open, F.Id("M"), Sp, Operatorname, Grp(F.Id("union")), Sp, F.Id("W"), Close,
                    Comma, RowBreak,
                    F.Id("Sem"), Sp, Eq, Sp, F.Id("M"), Sp,
                    Operatorname, Grp(F.Id("union")), Sp, F.Id("W"), Sp,
                    Operatorname, Grp(F.Id("union")), Sp, F.Id("R"), Sp, Land, RowBreak,
                    Operatorname, Grp(F.Id("Disjoint")), Open, F.Id("M"), Comma, F.Id("W"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Disjoint")), Open, F.Id("M"), Comma, F.Id("R"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Disjoint")), Open, F.Id("W"), Comma, F.Id("R"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a countable statement ledger take values in a finite partially ordered grade "
                        + "space, and assume each statement changes grade only finitely often after enrollment. "
                        + "The pointwise ledger-limit theorem supplies a unique terminal grading and a "
                        + "stabilization cutoff for every statement.")),
                    Paragraph(Text(
                        "Let Sem be the semantic domain, W a wall contained in Sem, T its gatekeepers, and "
                        + "Gplus the positive grades. Assume every gatekeeper remains positive, joint positivity "
                        + "of a wall statement and all gatekeepers is forbidden, and forbidden wall "
                        + "configurations never occur. The guarded-wall theorem makes every wall statement "
                        + "non-positive at every time. Evaluating at its terminal cutoff therefore keeps W "
                        + "disjoint from the terminal-positive migrated part M.")),
                    Paragraph(Text(
                        "Define M as the semantic statements whose terminal grade lies in Gplus, and define R "
                        + "as Sem with M and W removed. Elementary set extensionality gives Sem = M union W "
                        + "union R. Guarded-wall non-positivity proves M and W are disjoint, while the defining "
                        + "set difference proves that R is disjoint from each. The Boolean witness in the Lean "
                        + "module checks that all assumptions can hold simultaneously."))),
                DescribeRole.Theorem)),
        []));
}
