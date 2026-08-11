using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class LedgerLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/History/LedgerLimit",
            "A finitely revised ledger has a unique pointwise terminal grading."),
        H("The Pointwise Ledger Limit"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("finite-revisions-determine-a-unique-terminal-grading"),
                H("Finite revisions determine a unique terminal grading"),
                LeanTheorem(
                    "D5/S0/History/LedgerLimit.ledger_limit_exists_unique"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("FiniteRevisions")), Open, SigmaLower, Close,
                    Sp, Rightarrow, Sp,
                    Exists, Bang, Sp, SigmaLower, Underscore, Grp(Infty), Comma, Sp,
                    Forall, Sp, F.Id("s"), Comma, Sp, Exists, Sp, F.Id("N"),
                    Sp, Geq, Sp, F.Id("e"), Open, F.Id("s"), Close, Comma, Sp,
                    Forall, Sp, F.Id("t"), Sp, Geq, Sp, F.Id("N"), Comma, Sp,
                    SigmaLower, Underscore, Grp(F.Id("t")), Open, F.Id("s"), Close,
                    Sp, Eq, Sp,
                    SigmaLower, Underscore, Grp(Infty), Open, F.Id("s"), Close, Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "A ledger history contains every eventually enrolled statement, its "
                        + "enrollment time, and its grade at every natural-number clock tick. "
                        + "The statements visible by time t are exactly those whose enrollment "
                        + "time is at most t, so the visible statement sets are append-only by "
                        + "construction. A revision time for a statement is a tick at or after "
                        + "enrollment where the next grade differs from the current grade.")),
                    Paragraph(Text(
                        "Assume each statement has only finitely many revision times. The "
                        + "complement of that finite set is eventually universal on the natural "
                        + "clock, so there is a cutoff after which no adjacent pair of grades "
                        + "differs. Induction from the cutoff makes the entire tail constant. "
                        + "Two proposed terminal grades agree by evaluating both constant tails "
                        + "at the maximum of their cutoffs. Pointwise choice therefore produces "
                        + "one terminal grading on all statements, and pointwise uniqueness plus "
                        + "function extensionality proves that this grading is unique.")),
                    Paragraph(Text(
                        "The primary declaration retains the source model's countable statement "
                        + "space and finite partially ordered grade space. The stabilization "
                        + "lemma is proved at the stronger type-generic scope because neither "
                        + "finiteness nor the order is needed once finite revision times are "
                        + "assumed. The word limit means eventual equality in this discrete "
                        + "grading model; no convergence claim for an arbitrary topology is made. "
                        + "The construction and proof are elementary and assembled in this "
                        + "repository, so the theorem is recorded as repository-derived.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("permanent-alternation-has-no-terminal-grade"),
                H("Permanent alternation has no terminal grade"),
                LeanTheorem(
                    "D5/S0/History/LedgerLimit.alternating_grade_has_no_terminal_value"),
                Disp(Seq(
                    Neg, Exists, Sp, F.Id("g"), Comma, F.Id("N"), Comma, Sp,
                    Forall, Sp, F.Id("t"), Sp, Geq, Sp, F.Id("N"), Comma, Sp,
                    Operatorname, Grp(F.Id("alternate")), Open, F.Id("t"), Close,
                    Sp, Eq, Sp, F.Id("g"), Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The two-grade counterexample starts at false and negates its grade at "
                        + "every successor tick. Any claimed terminal cutoff would force the "
                        + "grades at that cutoff and its successor to equal the same terminal "
                        + "value, while the defining recursion proves those adjacent grades are "
                        + "unequal. The same argument, composed with the stabilization theorem, "
                        + "proves that the counterexample has infinitely many revision times. "
                        + "This discharges the source theorem's necessity clause rather than "
                        + "silently treating finite revision as cosmetic.")))
            ))));
}
