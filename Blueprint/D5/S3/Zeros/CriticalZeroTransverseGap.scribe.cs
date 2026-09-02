using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class CriticalZeroTransverseGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A critical-line zero has a transverse gap whose order is twice its multiplicity.",
        H("Critical-Zero Transverse Gap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("critical-zero-transverse-gap"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/CriticalZeroTransverseGap.critical_zero_transverse_gap"),
                H("The transverse gap at a critical zero"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let t0 be a zero of the canonical critical-line completed-xi reading "
                            + "with positive multiplicity r: all derivatives below r vanish and "
                            + "the derivative of order r is nonzero. Every normal jet below r "
                            + "then vanishes, while the depth-r jet is the strictly positive "
                            + "square of the leading Taylor coefficient.")),
                    Paragraph(Text(
                        "The two final public conjuncts concern the actual norm-squared normal "
                            + "intensity. Its leading transverse term has degree 2r with remainder "
                            + "of order 2r+2; at a simple zero this becomes the squared first "
                            + "derivative times the displacement squared, with quartic remainder.")),
                    Paragraph(Text(
                        "The proof imports the canonical normal-jet convolution formula. It also "
                            + "uses conjugate reflection to prove evenness of the actual intensity "
                            + "and applies the pinned Taylor remainder theorem to that smooth "
                            + "function."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Zeros/NormalJetFormula")),
        ]));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula r = F.Id("r");
        Formula t0 = new Formula.Subscript(F.Id("t"), D(0));
        Formula j = F.Id("j");
        Formula m = F.Id("m");
        Formula delta = F.Id("delta");
        Formula criticalXi = F.Id("criticalXi");
        Formula derivativeAtJ = Call("iteratedDeriv", j, criticalXi, t0);
        Formula derivativeAtR = Call("iteratedDeriv", r, criticalXi, t0);
        Formula derivativeAtOne = Call("iteratedDeriv", D(1), criticalXi, t0);
        Formula factorialR = Call("factorial", r);
        Formula leadingCoefficient = Power(
            new Formula.Fraction(derivativeAtR, factorialR), D(2));
        Formula twiceR = Seq(D(2), r);
        Formula leadingTerm = Seq(
            leadingCoefficient, Sp, Cdot, Sp, Power(delta, twiceR));
        Formula generalResidual = Seq(
            Call("normalIntensity", delta, t0), Sp, Minus, Sp, leadingTerm);
        Formula generalScale = Power(delta, Seq(twiceR, Sp, Plus, Sp, D(2)));
        Formula simpleLeadingTerm = Seq(
            Power(derivativeAtOne, D(2)), Sp, Cdot, Sp, Power(delta, D(2)));
        Formula simpleResidual = Seq(
            Call("normalIntensity", delta, t0), Sp, Minus, Sp, simpleLeadingTerm);
        Formula simpleScale = Power(delta, D(4));

        Formula premises = Seq(
            D(0), Sp, Lt, Sp, r, Sp, Land,
            Open, Forall, Sp, j, Colon, Sp, Naturals(), Comma, Sp,
            j, Sp, Lt, Sp, r, Sp, Rightarrow, Sp,
            derivativeAtJ, Sp, Eq, Sp, D(0), Close, Sp, Land,
            derivativeAtR, Sp, Neq, Sp, D(0));

        Formula conclusions = Seq(
            Begin, Grp(F.Id("gathered")),
            Open, Forall, Sp, m, Colon, Sp, Naturals(), Comma, Sp,
            m, Sp, Lt, Sp, r, Sp, Rightarrow, Sp,
            Call("normalJet", t0, m), Sp, Eq, Sp, D(0), Close, Sp, Land,
            RowBreak, Grp(),
            Call("normalJet", t0, r), Sp, Eq, Sp, leadingCoefficient, Sp, Land,
            RowBreak, Grp(),
            D(0), Sp, Lt, Sp, Call("normalJet", t0, r), Sp, Land,
            RowBreak, Grp(),
            Call("IsBigOAtZero",
                Lambda(delta, generalResidual),
                Lambda(delta, generalScale)), Sp, Land,
            RowBreak, Grp(),
            Open, r, Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp,
            Call("IsBigOAtZero",
                Lambda(delta, simpleResidual),
                Lambda(delta, simpleScale)), Close,
            End, Grp(F.Id("gathered")));

        return Disp(Seq(
            Forall, Sp, r, Colon, Sp, Naturals(), Comma, Sp,
            t0, Colon, Sp, Reals(), Comma,
            RowBreak, Grp(),
            premises, Sp, Rightarrow, Sp,
            conclusions, Dot));
    }
}
