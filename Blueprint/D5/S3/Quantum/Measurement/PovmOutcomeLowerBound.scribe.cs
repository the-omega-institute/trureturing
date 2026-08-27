using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class PovmOutcomeLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized finite effect family needs at least d squared outcomes for completeness.",
        H("POVM Outcome Lower Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("povm-outcome-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/PovmOutcomeLowerBound."
                        + "povm_outcome_lower_bound"),
                H("An informationally complete POVM has at least d squared outcomes"),
                StatementSource.FromAuthor(OutcomeBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The effects are a finite family on the canonical real Hermitian "
                            + "carrier whose sum is the identity. The displayed centered "
                            + "family is constructed by the repository's canonical trace-"
                            + "removal map.")),
                    Paragraph(Text(
                        "Normalization gives a nonzero all-ones coefficient relation among "
                            + "the centered effects. Their real span therefore has dimension "
                            + "at most one less than the number of outcomes.")),
                    Paragraph(Text(
                        "When that span is the whole real trace-zero Hermitian carrier, its "
                            + "dimension is d squared minus one, so the outcome count is at "
                            + "least d squared."))),
                DescribeRole.Theorem))));

    private static Formula Indexed(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula OutcomeBoundFormula()
    {
        Formula d = F.Id("d"), m = F.Id("m"), effects = F.Id("E");
        Formula index = F.Id("a"), centered = F.Id("C");
        Formula naturals = Seq(Operatorname, Grp(F.Id("Nat")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula indexType = Call("Fin", m);
        Formula hermitian = Call("HermitianSpace", d);
        Formula traceZero = Call("traceZeroHermitian", d);
        Formula effect = Indexed(effects, index);
        Formula centeredEffect = Indexed(centered, index);
        Formula normalized = Seq(
            Sum, Underscore, Grp(index, Sp, InMacro, Sp, indexType), Sp,
            effect, Sp, Eq, Sp, Call("identityHermitian", d));
        Formula centeredDefinition = Seq(
            centeredEffect, Sp, Colon, Eq, Sp,
            Call("centeredHermitianMap", d, effect));
        Formula centeredSet = Seq(
            OpenBrace, centeredEffect, Colon, Sp,
            index, Sp, InMacro, Sp, indexType, CloseBrace);
        Formula centeredSpan = Call("span", reals, centeredSet);
        Formula centeredSum = Seq(
            Sum, Underscore, Grp(index, Sp, InMacro, Sp, indexType), Sp,
            centeredEffect, Sp, Eq, Sp, D(0));
        Formula spanBound = Seq(
            Call("finrank", reals, centeredSpan), Sp, Leq, Sp,
            m, Sp, Minus, Sp, D(1));
        Formula completeBound = Seq(
            centeredSpan, Sp, Eq, Sp, traceZero, Sp, Rightarrow, Sp,
            new Formula.Power(d, D(2)), Sp, Leq, Sp, m);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, d, Comma, Sp, m, Colon, Sp, naturals, Comma, Sp,
            Call("NeZero", d), Comma, RowBreak, Grp(),
            effects, Colon, Sp, indexType, Sp, To, Sp, hermitian, Comma,
            RowBreak, Grp(), normalized, Sp, Rightarrow, RowBreak, Grp(),
            centeredDefinition, Comma, RowBreak, Grp(),
            centeredSum, Sp, Land, RowBreak, Grp(),
            spanBound, Sp, Land, RowBreak, Grp(),
            Open, completeBound, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
