using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class WeightedTailInverseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive logarithmic weighted-tail inversion for arbitrary real L1 kernels",
        H("A positive inverse with only an L1 premise"),
        Blocks(
            Paragraph(Text("Use the existing tail(k,x)=integral_(x,infinity) k(t) dt and "
                + "weightedTail(k,x)=integral_(x,infinity) k(t)*r(t) dt, where "
                + "r(t)=(1+log(t))/log(t)^2. Set a(t)=log(t)^2/(1+log(t)) and "
                + "v(t)=log(t)*(log(t)+2)/(t*(1+log(t))^2). On t>1, v=a' is "
                + "nonnegative and r*a=1. Neither v nor its half-line integral is "
                + "assumed integrable. All integrals use Lebesgue volume.")),
            Describe.Lean(DescribeId.Create("weighted-tail-inverse-reciprocal"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/WeightedTailInverse.a"),
                H("The reciprocal logarithmic weight"),
                StatementSource.FromAuthor(Disp(All("t", Real, EqClaim(Call("a", F.Id("t")),
                    new Formula.Fraction(new Formula.Power(Call("log", F.Id("t")), D(2)),
                        Add(D(1), Call("log", F.Id("t")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The definition is totalized on Real; positivity and the "
                    + "reciprocal identity are used only at t>1."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weighted-tail-inverse-density"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/WeightedTailInverse.v"),
                H("The positive derivative density"),
                StatementSource.FromAuthor(Disp(All("t", Real, EqClaim(Call("v", F.Id("t")),
                    new Formula.Fraction(Multiply(Call("log", F.Id("t")),
                        Add(Call("log", F.Id("t")), D(2))),
                        Multiply(F.Id("t"), new Formula.Power(Add(D(1),
                            Call("log", F.Id("t"))), D(2)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This derivative density is nonnegative on t>1; only finite "
                    + "interval integrability is used before triangular absolute Fubini."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weighted-tail-positive-inverse"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/WeightedTailInverse.inverse"),
                H("Absolute Fubini proves the positive inverse"),
                StatementSource.FromAuthor(InverseClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each endpoint u>x, truncate v to (x,u). Its mass is "
                    + "a(u)-a(x), and 0<=r(u)*(a(u)-a(x))<=1. Hence the norm integral "
                    + "of the triangular kernel is bounded by |k(u)|. Absolute Fubini "
                    + "pays both the exchanged integral and integrability of v*weightedTail. "
                    + "No boundary limit, extra moment, or sign premise on k is used."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-tail-inverse-lower-bound"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/WeightedTailInverse.tail_lower_bound"),
                H("A closed-tail weighted lower bound controls the unweighted tail"),
                StatementSource.FromAuthor(LowerClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For x>=exp(1) and A>=0, assume the weighted bound at "
                    + "every t>=x, including x. The endpoint contribution is at least "
                    + "-A/sqrt(x). Since v(t)/(sqrt(t)*log(t))<=t^(-3/2), the integral "
                    + "contribution is at least -2*A/sqrt(x). The inverse gives the "
                    + "stated -3*A/sqrt(x) lower bound. The kernel remains arbitrary real L1."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula EqClaim(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Integral(Formula integrand) => Seq(Int,
        Underscore, Grp(Lt(F.Id("x"), F.Id("t"))), integrand, Thin, F.Id("dt"));
    private static Formula ProductTail => Multiply(Call("v", F.Id("t")),
        Call("weightedTail", F.Id("k"), F.Id("t")));
    private static Formula KernelType => new Formula.TypeArrow(Real, Real);
    private static Formula L1 => Call("IntegrableOn", F.Id("k"), Call("Ioi", F.Id("x")));
    private static Formula InverseClaim()
    {
        var x = F.Id("x");
        var integrable = Seq(Operatorname, Grp(F.Id("IntegrableOn")), Open,
            F.Id("t"), Mapsto, ProductTail, Comma, Call("Ioi", x), Close);
        var identity = EqClaim(Call("tail", F.Id("k"), x),
            Add(Multiply(Call("a", x), Call("weightedTail", F.Id("k"), x)),
                Integral(ProductTail)));
        return Disp(All("k", KernelType, All("x", Real,
            Imp(Le(D(2), x), Imp(L1, And(integrable, identity))))));
    }
    private static Formula LowerClaim()
    {
        var x = F.Id("x");
        var t = F.Id("t");
        var a = F.Id("A");
        var bound = Le(new Formula.Fraction(new Formula.Negate(a),
            Multiply(Call("sqrt", t), Call("log", t))), Call("weightedTail", F.Id("k"), t));
        var closed = All("t", Real, Imp(Le(x, t), bound));
        var conclusion = Le(new Formula.Fraction(new Formula.Negate(Multiply(D(3), a)),
            Call("sqrt", x)), Call("tail", F.Id("k"), x));
        return Disp(All("k", KernelType, All("x", Real, All("A", Real,
            Imp(Le(Call("exp", D(1)), x), Imp(Le(D(0), a), Imp(L1, Imp(closed, conclusion))))))));
    }
}
