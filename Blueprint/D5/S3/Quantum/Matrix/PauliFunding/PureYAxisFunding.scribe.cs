using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.PauliFunding;

internal sealed class PureYAxisFundingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/PauliFunding/PureYAxisFunding.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive-order funding coefficient is nonnegative for an actual pure-Y Pauli source, with exact strict and degenerate cases.",
        H("All-order funding for a pure-Y source"), Blocks(
            Paragraph(Text("Let C=(0,y,0) with y squared equal to one and let D=(X,Y,Z) be any real unit Bloch vector. These are the Bloch coordinates of complex pure qubit sources; the imaginary Pauli coordinate is retained. The section-20 parameters reduce to kappa=0, lambda=0 and mu=-yY. Thus the actual control blocks are H plus or minus=(I+aZ plus or minus mu sqrt(1-a squared) X)/4. In the notation below t=mu sqrt(1-a squared). Their real entries are embedded into complex matrices before taking shifted inverses and the positive square root. The function complexMoment is the real part of the trace of the j-th power of sqrt(P minus) P plus sqrt(P minus).")),
            Item("matrix-coefficient", "The matrix integral coefficient", "resolventCoefficient",
                CoefficientStatement(),
                "For every real a,t and natural j, resolventCoefficient is defined using Lebesgue integration on s>0. In the physical domain the shifted inverses exist, the filters are positive semidefinite, and the integrability asserted below makes this the finite section-20 resolvent integral.", true),
            Item("funding-coefficient", "The actual local funding coefficient", "fundingCoefficient",
                FundingStatement(),
                "The displayed zeroArgumentSeries is the private Lean series expanded exactly: n and j are natural, n-j is truncated natural subtraction, and the binomial coefficient and denominator are cast to real numbers. Real division is total, with division by zero equal to zero; in particular zeroArgumentSeries(0)=0. For j at least one its value is 1/[2j(2j-1)]. For a pure-Y first factor, z=x=0 and y squared equals one. The scalar terms are L=(1-a^(2j))zeroArgumentSeries(j) and m=zeroArgumentSeries(j). The definition retains this series at every natural order.", true),
            Item("all-orders", "Nonnegativity, strictness and every equality case", "pure_y_axis_funding",
                TheoremStatement(),
                "For every a in [0,1], y squared equal to one, real unit partner (X,Y,Z), and natural j at least one, the actual complex matrix moment is integrable and fundingCoefficient is nonnegative. It is strictly positive exactly when a<1 and abs(Y)<1, and is zero exactly when a=1 or abs(Y)=1. The quantifier includes every finite positive order, a=0, singular unshifted blocks, and both partner-axis endpoints. Applying the same result after exchanging the two source labels gives the corresponding local coefficients for a pure-Y second factor.", false,
                "The parity-conjugate resolvent identities give the exact even power sum of two real quadratic roots. Evaluating their characteristic polynomial at a/(1+2s) gives the pointwise lower comparison, strict when the block determinant is positive. Evaluation at 1/(1+2s) bounds both root magnitudes and dominates the full trace by 2/(1+2s)^(2j). The existing shifted inverse-power integral proves integrability and gives the reference integral 1/[2(2j-1)]. Strict positivity of the difference on s>0 gives a strictly positive integral. When the determinant vanishes, the moment equals the reference pointwise and direct integration gives d=0. For the actual source the determinant numerator is (1-a squared)(1-Y squared), so these are exactly the stated strict and equality alternatives.")
            , Paragraph(Text("This comparison concerns the complete pure-Y family of local funding coefficients. It asserts no coefficient sign for a general first source, no full funding inequality, and no sign for the original pure-product deficit.")))));

    private static DocumentBlock Item(string id, string title, string name, Formula statement,
        string prose, bool definition, string? proof = null) => Describe.Lean(
            DescribeId.Create("pauli-pure-y-funding-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            proof is null ? Blocks(Paragraph(Text(prose))) :
                Blocks(Paragraph(Text(prose)), Paragraph(Text(proof))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula V(string x) => F.Id(x);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula ImpliesF(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Integral(Formula body) => Seq(Int, Underscore,
        Grp(Lt(D(0), V("s"))), Sp, body, Sp, Mathrm, Grp(V("d")), Sp, V("s"));
    private static Formula Integrable(Formula a, Formula t, Formula j) => Call("IntegrableOn",
        Seq(LambdaLower, Sp, V("s"), Colon, Real, Mapsto, Call("complexMoment", a, t, j, V("s"))),
        Call("Ioi", D(0)));

    private static Formula CoefficientStatement()
    {
        Formula a = V("a"), t = V("t"), j = V("j");
        return All("a", Real, All("t", Real, All("j", Nat,
            Eq(Call("resolventCoefficient", a, t, j), Mul(Div(D(1), j), Integral(Call("complexMoment", a, t, j, V("s"))))))));
    }

    private static Formula ZeroArgumentSeriesExpansion()
    {
        Formula n = V("n"), j = V("j");
        Formula term = Div(Mul(Call("choose", n, j), Pow(D(0), Mul(D(2), Sub(n, j)))),
            Mul(Mul(D(2), n), Sub(Mul(D(2), n), D(1))));
        Formula cases = Seq(Begin, Grp(V("cases")), term, Amp, Le(j, n), RowBreak,
            D(0), Amp, Lt(n, j), End, Grp(V("cases")));
        Formula series = Seq(new Formula.Power(Sum, new Formula.LatexSymbol(FormulaLatexSymbol.Apostrophe)),
            Underscore, Grp(n, Colon, Nat), Sp, cases);
        return All("j", Nat, Eq(Call("zeroArgumentSeries", j), series));
    }

    private static Formula FundingStatement()
    {
        Formula a = V("a"), t = V("t"), j = V("j");
        Formula series = Call("zeroArgumentSeries", j);
        return new Formula.Aligned([
            ZeroArgumentSeriesExpansion(),
            Eq(Call("zeroArgumentSeries", D(0)), D(0)),
            All("a", Real, All("t", Real, All("j", Nat,
                Eq(Call("fundingCoefficient", a, t, j), Sub(Add(Call("resolventCoefficient", a, t, j),
                    Mul(Sub(D(1), Pow(a, Mul(D(2), j))), series)), series)))))
        ]);
    }

    private static Formula TheoremStatement()
    {
        Formula a = V("a"), y = V("y"), x = V("X"), z = V("Z"), yy = V("Y"), j = V("j");
        Formula t = Mul(Mul(Sub(D(0), y), yy), Call("sqrt", Sub(D(1), Pow(a, D(2)))));
        Formula d = Call("fundingCoefficient", a, t, j);
        Formula assumptions = And(And(Le(D(0), a), Le(a, D(1))),
            And(Eq(Pow(y, D(2)), D(1)),
                And(Eq(Add(Add(Pow(x, D(2)), Pow(yy, D(2))), Pow(z, D(2))), D(1)), Le(D(1), j))));
        Formula conclusion = And(Integrable(a, t, j), And(Le(D(0), d),
            And(Iff(Lt(D(0), d), And(Lt(a, D(1)), Lt(Call("abs", yy), D(1)))),
                Iff(Eq(d, D(0)), Or(Eq(a, D(1)), Eq(Call("abs", yy), D(1)))))));
        return All("a", Real, All("y", Real, All("X", Real, All("Y", Real,
            All("Z", Real, All("j", Nat, ImpliesF(assumptions, conclusion)))))));
    }
}
