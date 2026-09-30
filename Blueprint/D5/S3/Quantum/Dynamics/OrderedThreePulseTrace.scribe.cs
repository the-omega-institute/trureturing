using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class OrderedThreePulseTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/OrderedThreePulseTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered three-pulse trace deviation has a dimension-free Frobenius bound.",
        H("Ordered Three-Pulse Trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordered-three-pulse-definition"),
                DeclarationHandle.Create(Prefix + "pulse0"),
                H("The matrix pulse integral"),
                StatementSource.FromAuthor(PulseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite index type, complex square matrix X and real s, "
                        + "the pulse is the interval integral of exp(i r s X) X over 0 <= r <= 1. "
                        + "The matrix product keeps X on the right."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ordered-three-pulse-real-trace-bound"),
                DeclarationHandle.Create(Prefix + "ordered_three_pulse_real_trace_bound"),
                H("Ordered three-pulse real trace bound"),
                StatementSource.FromAuthor(BoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The index type is any finite type, including the empty type. A, B and C "
                            + "are real symmetric square matrices with their actual Frobenius norms "
                            + "at most L, where L is nonnegative; t is positive. No pairwise "
                            + "commutation is assumed.")),
                    Paragraph(Text(
                        "The same theorem proves D_X(0) = X and, for every nonzero real s, "
                            + "D_X(s) = (exp(i s X) - I)/(i s), even for arbitrary complex X. "
                            + "In the trace bound each real matrix is entrywise complexified; "
                            + "the three pulse factors remain in A, B, C order.")),
                    Paragraph(Text(
                        "The proof uses the existing GNS Frobenius norm-square trace identity, "
                            + "unitary matrix exponentials, two derivatives of the ordered product, "
                            + "and the nine-term second-derivative estimate. The latter is at most "
                            + "5 L^5/2; the zero derivative of the real trace at zero gives the "
                            + "5 L^5 t^2/4 remainder. The quotient identity follows from the "
                            + "interval fundamental theorem of calculus."))),
                DescribeRole.Theorem))));

    private static Formula Pulse(Formula x, Formula s) =>
        Seq(F.Id("D"), Underscore, Grp(x), Open, s, Close);

    private static Formula PulseFormula()
    {
        Formula x = F.Id("X"), s = F.Id("s"), r = F.Id("r");
        return Disp(Seq(
            Pulse(x, s), Sp, Eq, Sp, Int, Underscore, Grp(D(0)), Caret, Grp(D(1)),
            Exp, Grp(F.Id("i"), Sp, r, Sp, s, Sp, x), Sp, x, Sp, F.Id("dr")));
    }

    private static Formula BoundFormula()
    {
        Formula index = F.Id("I");
        Formula a = F.Id("A"), b = F.Id("B"), c = F.Id("C");
        Formula x = F.Id("X"), s = F.Id("s"), t = F.Id("t"), l = F.Id("L");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula realMatrix = Seq(F.Id("Mat"), Underscore, Grp(index), Open, real, Close);
        Formula complexMatrix = Seq(F.Id("Mat"), Underscore, Grp(index), Open, complex, Close);
        Formula aComplex = Seq(a, Underscore, Grp(complex));
        Formula bComplex = Seq(b, Underscore, Grp(complex));
        Formula cComplex = Seq(c, Underscore, Grp(complex));
        Formula normA = Seq(Vert, Sp, a, Sp, Vert, Underscore, Grp(F.Id("F")));
        Formula normB = Seq(Vert, Sp, b, Sp, Vert, Underscore, Grp(F.Id("F")));
        Formula normC = Seq(Vert, Sp, c, Sp, Vert, Underscore, Grp(F.Id("F")));
        Formula traceComplex = Seq(Operatorname, Grp(F.Id("Tr")), Underscore, Grp(complex));
        Formula traceReal = Seq(Operatorname, Grp(F.Id("Tr")), Underscore, Grp(real));
        Formula quotient = Seq(
            Frac, Grp(Exp, Grp(F.Id("i"), Sp, s, Sp, x), Sp, Minus, Sp, F.Id("I")),
            Grp(F.Id("i"), Sp, s));
        Formula ordered = Seq(
            Pulse(aComplex, t), Sp, Pulse(bComplex, t), Sp, Pulse(cComplex, t));
        Formula bound = Seq(
            Bar, Re, Sp, traceComplex, Open, ordered, Close, Sp, Minus, Sp,
            traceReal, Open, a, Sp, b, Sp, c, Close, Bar, Sp, Leq, Sp,
            Frac, Grp(D(5)), Grp(D(4)), Sp, l, Caret, Grp(D(5)), Sp,
            t, Caret, Grp(D(2)));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Open, index, Colon, Sp, F.Id("Type"), Close, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, index, Close,
            CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, index, Close,
            CloseBracket, Comma, RowBreak,
            Forall, Sp, a, Comma, Sp, b, Comma, Sp, c, Colon, Sp, realMatrix,
            Comma, Sp, Forall, Sp, l, Comma, Sp, t, Colon, Sp, real, Comma, RowBreak,
            a, Caret, Grp(F.Id("T")), Sp, Eq, Sp, a, Sp, Land, Sp,
            b, Caret, Grp(F.Id("T")), Sp, Eq, Sp, b, Sp, Land, Sp,
            c, Caret, Grp(F.Id("T")), Sp, Eq, Sp, c, Sp, Land, RowBreak,
            D(0), Sp, Leq, Sp, l, Sp, Land, Sp,
            normA, Sp, Leq, Sp, l, Sp, Land, Sp,
            normB, Sp, Leq, Sp, l, Sp, Land, Sp,
            normC, Sp, Leq, Sp, l, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, t, Sp, Rightarrow, RowBreak, Grp(),
            OpenBracket, Open, Forall, Sp, x, Colon, Sp, complexMatrix, Comma, Sp,
            Pulse(x, D(0)), Sp, Eq, Sp, x, Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, x, Colon, Sp, complexMatrix, Comma, Sp,
            Forall, Sp, s, Colon, Sp, real, Comma, Sp,
            s, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Pulse(x, s), Sp, Eq, Sp, quotient, Close,
            Sp, Land, RowBreak,
            bound, CloseBracket, End, Grp(F.Id("gathered"))));
    }
}
