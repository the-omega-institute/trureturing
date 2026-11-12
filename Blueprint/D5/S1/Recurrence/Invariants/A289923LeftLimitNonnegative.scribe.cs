using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class A289923LeftLimitNonnegativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/kimberling2017a289923");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficientwise left limit defining OEIS A289923 exists uniquely and is nonnegative at every index.",
        H("A289923: coefficientwise left limit and nonnegativity"),
        Blocks(
            Paragraph(Text("Clark Kimberling's OEIS A289923 defines the limiting sequence "
                + "from the left at the rational parameter 19/21 and conjectures that all "
                + "terms are nonnegative. Every index below ranges over the natural numbers, "
                + "including zero. The parameter is real; coefficients and sequence values "
                + "are integers. Each coefficient may have its own positive neighborhood. "
                + "No single fixed approximation to the parameter is used.")),
            Node("parameterDenominator", "The real-parameter denominator", DenominatorFormula(),
                "The coefficient at index k is the signed floor from the source definition. "
                + "For parameters strictly between zero and one, its constant coefficient is one.",
                DescribeRole.Definition),
            Node("parameterInverse", "The normalized formal inverse", InverseFormula(),
                "The unit inverse is invOfUnit with the unit one. On the stated parameter "
                + "domain, its product with the denominator is one.", DescribeRole.Definition),
            Node("IsLeftLimit", "The coefficientwise left-limit property", LimitFormula(),
                "At each index n there is a positive delta such that every real parameter "
                + "in the specified left interval, also strictly between zero and one, "
                + "has the same inverse coefficient. Delta may depend on n.", DescribeRole.Definition),
            Paragraph(Text("For indices at most n, delta equal to the reciprocal of "
                + "21 times n+1 stabilizes every floor coefficient. The existing "
                + "AbsoluteReciprocalGeometricParity.agree_inv theorem transports this "
                + "finite coefficient agreement through the normalized inverse. Two "
                + "candidate limit sequences agree by choosing a parameter in the "
                + "intersection of their two positive left neighborhoods.")),
            Paragraph(Text("Write D for the series with coefficient (-1) to the k times "
                + "the natural quotient (19(k+1)+20)/21. The quotient shifts by 19 after "
                + "21 steps. Consequently the coefficients of D times (1+X) squared "
                + "change sign after 21 steps beyond the initial two coefficients. "
                + "This proves the full series identity D P = Q, where "
                + "P=(1+X)^2(1+X^21) and Q=1-X^10-X^11-X^20. "
                + "Multiplying by the unit inverse gives Q F=P. Its coefficient recurrence "
                + "expresses each coefficient of F as the nonnegative coefficient of P "
                + "plus coefficients at the strictly smaller indices n-10, n-11 and "
                + "n-20 when those indices exist. Strong induction proves nonnegativity. "
                + "The finite initial coefficient cases certify a symbolic identity with "
                + "an all-degree shift proof; they do not replace the universal theorem. "
                + "Colin Barker's rational generating function is a known source formula, "
                + "and is not assumed as the connection to the limiting sequence.")),
            Node("result", "The complete left-limit theorem", ResultFormula(),
                "There is a limit sequence, every other sequence satisfying the same "
                + "left-limit property equals it, and every one of its terms is nonnegative.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("a289923-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Int() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LtN(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula LeN(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Conj(params Formula[] clauses) =>
        Seq([.. clauses.SelectMany((clause, index) => index == 0
            ? new Formula[] { Open, clause, Close }
            : new Formula[] { Sp, Land, Sp, Open, clause, Close })]);
    private static Formula For(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Ex(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Open, a, Close, Sp, Implies, Sp, Open, b, Close);
    private static Formula SequenceType() => Seq(Nat(), Sp, To, Sp, Int());
    private static Formula Value(Formula a, Formula n) => new Formula.Apply(a, [n]);
    private static Formula Ratio() => new Formula.Fraction(D(1, 9), D(2, 1));

    private static Formula DenominatorFormula()
    {
        var r = F.Id("r"); var k = F.Id("k");
        return Disp(For(r, Real(), For(k, Nat(),
            Eqn(Call("coeff", k, Call("parameterDenominator", r)),
                Mul(new Formula.Power(Seq(Open, D(0), Minus, D(1), Close), k),
                    Call("floor", Add(D(1), Mul(Add(k, D(1)), r))))))));
    }

    private static Formula InverseFormula() => Disp(For(F.Id("r"), Real(),
        Eqn(Call("parameterInverse", F.Id("r")),
            Call("invOfUnit", Call("parameterDenominator", F.Id("r")), D(1)))));

    private static Formula LimitBody(Formula a)
    {
        var n = F.Id("n"); var r = F.Id("r"); var delta = F.Id("delta");
        return For(n, Nat(), Ex(delta, Real(), Conj(LtN(D(0), delta),
            For(r, Real(), Imp(Conj(LtN(D(0), r), LtN(r, D(1)),
                LtN(new Formula.Binary(Ratio(), FormulaBinaryOperator.Subtract, delta), r), LtN(r, Ratio())),
                Eqn(Call("coeff", n, Call("parameterInverse", r)), Value(a, n)))))));
    }

    private static Formula LimitFormula() => Disp(For(F.Id("a"), SequenceType(),
        Seq(Call("IsLeftLimit", F.Id("a")), Sp, Iff, Sp, LimitBody(F.Id("a")))));

    private static Formula ResultFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var n = F.Id("n");
        return Disp(Ex(a, SequenceType(), Conj(Call("IsLeftLimit", a),
            For(b, SequenceType(), Imp(Call("IsLeftLimit", b), Eqn(b, a))),
            For(n, Nat(), LeN(D(0), Value(a, n))))));
    }
}
