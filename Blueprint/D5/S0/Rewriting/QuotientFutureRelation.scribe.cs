using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class QuotientFutureRelationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "A preserved equivalence is recovered from all future quotient observations.",
            H("Quotient Future Relation"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("future-quotient-observations-recover-the-relation"),
                    DeclarationHandle.Create(
                        "D5/S0/Rewriting/QuotientFutureRelation."
                        + "quotient_future_relation_iff"),
                    H("Future quotient observations recover the relation"),
                    StatementSource.FromAuthor(FutureRelationFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let R be an equivalence relation preserved by a self-map tau. "
                            + "Two points have equal quotient classes after every finite number "
                            + "of steps exactly when they were R-related initially. The reverse "
                            + "direction uses preservation repeatedly; the forward direction is "
                            + "already forced by the zeroth observation.")),
                        Paragraph(Text(
                            "The pinned library search found Quotient.eq' as the exact "
                            + "characterization of equality between quotient classes. Searches "
                            + "for the complete all-future statement and for an arbitrary "
                            + "relation-preservation iterate theorem found no exact declaration. "
                            + "The proof applies the quotient characterization and performs only "
                            + "the remaining one-step induction locally.")),
                        Paragraph(Text(
                            "The statement is general in the carrier and does not require its "
                            + "finiteness. It asserts only recovery of the chosen preserved "
                            + "equivalence from quotient observations; no classification or "
                            + "existence claim is included."))),
                    DescribeRole.Theorem))));

    private static Formula Related(Formula x, Formula y) =>
        Seq(F.Id("R"), Open, x, Comma, Sp, y, Close);

    private static Formula Iterate(Formula x) =>
        Seq(F.Id("tau"), Caret, Grp(F.Id("k")), Open, x, Close);

    private static Formula QuotientClass(Formula x) =>
        Seq(OpenBracket, x, CloseBracket, Underscore, Grp(F.Id("R")));

    private static Formula FutureRelationFormula()
    {
        Formula y = F.Id("y");
        Formula yPrime = Seq(F.Id("y"), Apos);
        Formula tauY = Seq(F.Id("tau"), Open, y, Close);
        Formula tauYPrime = Seq(F.Id("tau"), Open, yPrime, Close);
        return Disp(Seq(
            Forall, Sp, F.Id("Y"), Comma, Sp,
            F.Id("tau"), Colon, Sp, F.Id("Y"), Sp, To, Sp, F.Id("Y"), Comma, Esc,
            F.Id("R"), Colon, Sp, Operatorname, Grp(F.Id("Setoid")),
            Open, F.Id("Y"), Close, Comma, Esc,
            Open, Forall, Sp, y, Comma, Sp, yPrime, Comma, Esc,
            Related(y, yPrime), Sp, Rightarrow, Sp,
            Related(tauY, tauYPrime), Close, Sp, Rightarrow, Sp,
            Forall, Sp, y, Comma, Sp, yPrime, Comma, Esc,
            Open, Open, Forall, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")),
            Comma, Esc, QuotientClass(Iterate(y)), Sp, Eq, Sp,
            QuotientClass(Iterate(yPrime)), Close, Sp, Iff, Sp,
            Related(y, yPrime), Close, Dot));
    }
}
