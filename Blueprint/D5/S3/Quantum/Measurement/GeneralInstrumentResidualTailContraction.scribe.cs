using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class GeneralInstrumentResidualTailContractionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/GeneralInstrumentResidualTailContraction.residual_tail_contraction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The residual above the maximal fixed survival effect contracts geometrically, has a summable tail, "
            + "and determines a unique dominated solution of the residual Poisson equation.",
        H("Residual Tail Contraction for General Instruments"),
        Blocks(Describe.Lean(
            DescribeId.Create("general-instrument-residual-tail-contraction"),
            DeclarationHandle.Create(Declaration),
            H("Geometric contraction and the residual Poisson solution"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let A be the dual no-click map, let S_n be its n-fold action on the identity, and let F be "
                        + "the limiting survival effect. Write R = I - F and R_n = S_n - F. The residuals are "
                        + "positive, decrease in the Loewner order, and equal A^n(R).")),
                Paragraph(Text(
                    "When R is nonzero, finite-dimensional spectral comparison gives a block length M for which "
                        + "R_M is at most one strict scalar multiple of R. Positivity and monotonicity propagate "
                        + "this estimate to every residual, so the residual series is summable and its block tails "
                        + "obey a geometric bound.")),
                Paragraph(Text(
                    "The sum T of the residuals is positive, is bounded by the corresponding geometric majorant, "
                        + "and satisfies T - A(T) = R. Iterating the same equation shows that any positive solution "
                        + "dominated by a scalar multiple of R has a remainder tending to zero, and therefore equals T."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), alpha = F.Alpha, iota = F.Iota;
        Formula a = F.Id("a"), i = F.Id("i"), n = F.Id("n"), k = F.Id("k");
        Formula m = F.Id("M"), q = F.Id("q"), x = F.Id("X"), c = F.Id("c");
        Formula eff = F.Id("F"), identity = F.Id("I"), t = F.Id("T");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula finD = Call("Fin", d);
        Formula matrix = Call("Matrix", finD, finD, complex);
        Formula qa = Sub(F.Id("Q"), a), li = Sub(F.Id("L"), i);
        Formula residual = Seq(identity, Sp, Minus, Sp, eff);
        Formula rn = Residual(n, eff);

        Formula complete = Seq(
            Sum, Underscore, Grp(a, Sp, InMacro, Sp, alpha), Sp,
            Adjoint(qa), Sp, qa, Sp, Plus, Sp,
            Sum, Underscore, Grp(i, Sp, InMacro, Sp, iota), Sp,
            Adjoint(li), Sp, li, Sp, Eq, Sp, identity);
        Formula limit = Seq(
            Lim, Underscore, Grp(n, Sp, To, Sp, Infty), Sp,
            Sub(F.Id("S"), n), Sp, Eq, Sp, eff);
        Formula residualIdentity = Seq(
            Forall, Sp, n, Sp, InMacro, Sp, nat, Comma, Sp,
            rn, Sp, Eq, Sp, Iterate(n, residual), Sp, Land, Sp,
            D(0), Sp, Leq, Sp, rn, Sp, Leq, Sp, residual);
        Formula contract = Seq(
            Residual(m, eff), Sp, Leq, Sp, Scalar(q, residual));
        Formula decay = Seq(
            Forall, Sp, n, Sp, InMacro, Sp, nat, Comma, Sp,
            Residual(n, eff), Sp, Leq, Sp,
            Scalar(Power(q, Floor(Frac(n, m))), residual));
        Formula summable = Call("Summable", Seq(n, Sp, Mapsto, Sp, Residual(n, eff)));
        Formula tDefinition = Seq(
            t, Sp, Eq, Sp, Sum, Underscore, Grp(n, Eq, D(0)), Caret, Grp(Infty), Sp,
            Residual(n, eff));
        Formula tUpper = Seq(
            t, Sp, Leq, Sp, Scalar(Frac(m, Grp(D(1), Sp, Minus, Sp, q)), residual));
        Formula poisson = Seq(
            t, Sp, Minus, Sp, ApplyA(t), Sp, Eq, Sp, residual);
        Formula partial = Seq(
            Sum, Underscore, Grp(n, Sp, Lt, Sp, Seq(k, Sp, m)), Sp, Residual(n, eff));
        Formula tail = Seq(t, Sp, Minus, Sp, partial);
        Formula tailBound = Seq(
            Forall, Sp, k, Sp, InMacro, Sp, nat, Comma, Sp,
            D(0), Sp, Leq, Sp, tail, Sp, Land, Sp,
            tail, Sp, Leq, Sp,
            Scalar(Frac(Seq(m, Sp, Power(q, k)), Grp(D(1), Sp, Minus, Sp, q)), residual));
        Formula uniqueness = Seq(
            Forall, Sp, Typed(x, matrix), Comma, Sp, Typed(c, real), Comma, Sp,
            x, Sp, Minus, Sp, ApplyA(x), Sp, Eq, Sp, residual, Sp, Rightarrow, Sp,
            D(0), Sp, Leq, Sp, x, Sp, Rightarrow, Sp,
            x, Sp, Leq, Sp, Scalar(c, residual), Sp, Rightarrow, Sp,
            x, Sp, Eq, Sp, t);

        return Disp(Seq(
            Forall, Sp, Typed(d, nat), Comma, Sp,
            Typed(alpha, type), Comma, Sp, Typed(iota, type), Comma, Sp,
            OpenBracket, Call("Fintype", alpha), CloseBracket, Comma, Sp,
            OpenBracket, Call("Fintype", iota), CloseBracket, Comma, RowBreak, Grp(),
            Typed(F.Id("Q"), Arrow(alpha, matrix)), Comma, Sp,
            Typed(F.Id("L"), Arrow(iota, matrix)), Comma, Sp, Typed(eff, matrix), Comma, RowBreak, Grp(),
            complete, Sp, Rightarrow, Sp, limit, Sp, Rightarrow, RowBreak, Grp(),
            residualIdentity, Sp, Land, RowBreak, Grp(),
            residual, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Exists, Sp, m, Sp, InMacro, Sp, nat, Comma, Sp,
            D(1), Sp, Leq, Sp, m, Sp, Land, Sp,
            Exists, Sp, q, Sp, InMacro, Sp, real, Comma, Sp,
            D(0), Sp, Lt, Sp, q, Sp, Lt, Sp, D(1), Sp, Land, RowBreak, Grp(),
            contract, Sp, Land, Sp, decay, Sp, Land, Sp, summable, Sp, Land, RowBreak, Grp(),
            tDefinition, Comma, Sp, D(0), Sp, Leq, Sp, t, Sp, Land, Sp,
            tUpper, Sp, Land, Sp, poisson, Sp, Land, RowBreak, Grp(),
            tailBound, Sp, Land, Sp, uniqueness, Dot));
    }

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(Grp(source), Sp, To, Sp, target);

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Adjoint(Formula value) => Seq(value, Caret, Grp(Star));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Floor(Formula value) => Seq(Lfloor, value, Rfloor);

    private static Formula Frac(Formula numerator, Formula denominator) =>
        Seq(F.Frac, Grp(numerator), Grp(denominator));

    private static Formula Scalar(Formula scalar, Formula value) =>
        Seq(scalar, Sp, Grp(value));

    private static Formula Residual(Formula index, Formula eff) =>
        Seq(Sub(F.Id("S"), index), Sp, Minus, Sp, eff);

    private static Formula ApplyA(Formula value) =>
        Seq(Mathcal, Grp(F.Id("A")), Open, value, Close);

    private static Formula Iterate(Formula index, Formula value) =>
        Seq(Grp(Mathcal, Grp(F.Id("A"))), Caret, Grp(index), Open, value, Close);
}
