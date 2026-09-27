using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Curvature;

internal sealed class CardinalSplineRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Curvature/CardinalSplineRecurrence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One normalized finite positive-part spline representation satisfies knot-safe "
            + "differentiation, the unit-window recurrence, and the centered reflected recurrence.",
        H("Normalized Cardinal-Spline Recurrences"),
        Blocks(
            Paragraph(Text(
                "All objects in this document use the same finite positive-part sum T. "
                    + "There is no second recursive spline definition: D and C are exponent "
                    + "specializations of T, while s and Q package the shifted comparison used "
                    + "by the strict-curvature induction.")),
            Node("normalized-positive-part-spline", "The normalized finite positive-part spline", "T",
                TFormula(),
                "For natural m and q and real x, T(m,q,x) is the alternating binomial sum "
                    + "over k=0,...,m of max(x-k,0)^q, divided by q!. The normalization is "
                    + "part of the definition and is retained by every later identity.",
                DescribeRole.Definition),
            Node("first-spline-derivative", "The first-derivative specialization", "D",
                DFormula(),
                "D_m is T at exponent m-2. It is represented directly by the same finite sum; "
                    + "the definition does not invoke the noncomputable deriv operator.",
                DescribeRole.Definition),
            Node("second-spline-derivative", "The curvature specialization", "C",
                CFormula(),
                "C_m is T at exponent m-3. The knot-safe derivative theorem identifies it as "
                    + "the derivative of D_m in the orders used later.",
                DescribeRole.Definition),
            Node("off-center-point", "The shifted center", "s",
                SFormula(),
                "The point s_m=m/2-2/3 is the left endpoint of the closed core. Its half-unit "
                    + "increment under m -> m+1 aligns the box recurrence with the reflected "
                    + "difference.",
                DescribeRole.Definition),
            Node("reflected-derivative-difference", "The global reflected difference", "Q",
                QFormula(),
                "Q_m(u) compares D_m at equal offsets on the two sides of s_m. It is defined "
                    + "for every real u; the strict-curvature proof maintains nonnegativity for "
                    + "all u>=0, including offsets beyond the spline support.",
                DescribeRole.Definition),
            Node("knot-safe-derivative", "Knot-safe differentiation", "T_hasDerivAt",
                DerivativeFormula(),
                "For q>=1, T(m,q+1) has derivative T(m,q) at every real x, including integral "
                    + "knots where a positive-part summand changes branch. The only locally "
                    + "ported fact is the derivative of max(x-c,0)^(r+2). It is attributed to "
                    + "Zhi Kai Pong's Physlib source at commit "
                    + "50ac243729e00925f91224e3916cce74bb971edf under Apache 2.0; the port "
                    + "changes namespace, imports, and pinned-toolchain adaptation only. It is "
                    + "to be retired when the repository's pinned Mathlib supplies an equivalent "
                    + "declaration. The full applicable license is retained at "
                    + "docs/reports/inoutbalance/physlib-LICENSE.txt.",
                DescribeRole.Theorem),
            Node("unit-window-recurrence", "The unit-window recurrence", "D_succ_eq_integral",
                DRecurrenceFormula(),
                "For m>=3, raising the spline order averages D_m over [x-1,x]. The proof applies "
                    + "Mathlib's Pascal summation identity Finset.sum_choose_succ_mul directly, "
                    + "identifies the finite-difference antiderivative, and invokes the interval "
                    + "fundamental theorem of calculus. No standalone Pascal wrapper is added.",
                DescribeRole.Theorem),
            Node("centered-reflected-recurrence", "The centered reflected recurrence", "Q_succ_eq_integral",
                QRecurrenceFormula(),
                "Substituting the unit-window recurrence at the two reflected points, using "
                    + "s_(m+1)=s_m+1/2, and changing variables gives the exact centered moving "
                    + "window. This identity is global in u and therefore carries support-tail "
                    + "information into the induction rather than asserting only a local core fact.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula M => F.Id("m");
    private static Formula QIndex => F.Id("q");
    private static Formula X => F.Id("x");
    private static Formula U => F.Id("u");
    private static Formula K => F.Id("k");

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Paren(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Subscript(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula TAt(Formula m, Formula q, Formula x) => Call("T", m, q, x);
    private static Formula DAt(Formula m, Formula x) => Call("D", m, x);
    private static Formula CAt(Formula m, Formula x) => Call("C", m, x);
    private static Formula SAt(Formula m) => Call("s", m);
    private static Formula QAt(Formula m, Formula u) => Call("Q", m, u);

    private static Formula TFormula()
    {
        Formula summand = Seq(
            Pow(Paren(Seq(Minus, D(1))), K), Sp, Times, Sp,
            Call("binom", M, K), Sp, Times, Sp,
            Pow(Call("max", Seq(X, Sp, Minus, Sp, K), D(0)), QIndex));
        Formula sum = Seq(
            Subscript(Sum, Seq(D(0), Sp, Leq, Sp, K, Sp, Leq, Sp, M)),
            Sp, summand);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, M, Comma, Sp, QIndex, Sp, InMacro, Sp, Naturals,
                Comma, Sp, X, Sp, InMacro, Sp, Reals, Comma),
            EqualTo(TAt(M, QIndex, X),
                new Formula.Fraction(sum, Seq(QIndex, Bang))),
        ]));
    }

    private static Formula DFormula() => Disp(EqualTo(
        DAt(M, X), TAt(M, Seq(M, Sp, Minus, Sp, D(2)), X)));

    private static Formula CFormula() => Disp(EqualTo(
        CAt(M, X), TAt(M, Seq(M, Sp, Minus, Sp, D(3)), X)));

    private static Formula SFormula() => Disp(EqualTo(
        SAt(M), Seq(new Formula.Fraction(M, D(2)), Sp, Minus, Sp,
            new Formula.Fraction(D(2), D(3)))));

    private static Formula QFormula() => Disp(EqualTo(
        QAt(M, U), Seq(
            DAt(M, Seq(SAt(M), Sp, Minus, Sp, U)), Sp, Minus, Sp,
            DAt(M, Seq(SAt(M), Sp, Plus, Sp, U)))));

    private static Formula DerivativeFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, M, Comma, Sp, QIndex, Sp, InMacro, Sp, Naturals,
            Comma, Sp, X, Sp, InMacro, Sp, Reals, Comma),
        Seq(AtMost(D(1), QIndex), Sp, Implies, Sp,
            Call("HasDerivAt",
                Seq(F.Id("y"), Sp, Mapsto, Sp,
                    TAt(M, Seq(QIndex, Sp, Plus, Sp, D(1)), F.Id("y"))),
                TAt(M, QIndex, X), X), Dot),
    ]));

    private static Formula DRecurrenceFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, M, Sp, InMacro, Sp, Naturals, Comma, Sp,
            AtMost(D(3), M), Comma, Sp, X, Sp, InMacro, Sp, Reals, Comma),
        EqualTo(DAt(Seq(M, Sp, Plus, Sp, D(1)), X),
            Call("integral", Seq(X, Sp, Minus, Sp, D(1)), X, F.Id("t"),
                DAt(M, F.Id("t")))),
    ]));

    private static Formula QRecurrenceFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, M, Sp, InMacro, Sp, Naturals, Comma, Sp,
            AtMost(D(3), M), Comma, Sp, U, Sp, InMacro, Sp, Reals, Comma),
        EqualTo(QAt(Seq(M, Sp, Plus, Sp, D(1)), U),
            Call("integral",
                Seq(U, Sp, Minus, Sp, new Formula.Fraction(D(1), D(2))),
                Seq(U, Sp, Plus, Sp, new Formula.Fraction(D(1), D(2))),
                F.Id("t"), QAt(M, F.Id("t")))),
    ]));
}
