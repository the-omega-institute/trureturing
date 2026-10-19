using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.QuadraticLoad;

internal sealed class StarExtremaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/QuadraticLoad/StarExtrema.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The star has explicit optimal quadratic shares and an explicit maximizing probability vector. "
        + "Its value also bounds every finite graph from below through its maximum degree.",
        H("Sharp quadratic loads on stars"),
        Blocks(
            Paragraph(Text(
                "For an integer m at least one, let H(m) be the simple star on Option(Fin(m)), "
                + "with centre none and leaves some(i). Write s for the positive square root of m "
                + "and t for 1/(1+s). The allocation a(m)(b,c) is t when b is the centre and "
                + "1-t otherwise. These formulas also bound the irrelevant nonedge coordinates. "
                + "The probability vector mu(m) assigns t to the centre and 1/(s(1+s)) to every leaf. "
                + "The function Phi(m) sums p(b)p(c)/(p(b)+p(c)) once over each unordered edge. "
                + "Real division assigns zero when both coordinates vanish. The simplex contains "
                + "every nonnegative vector of total mass one, including vectors with zero coordinates.")),
            Paragraph(Math(Eq(Call("q", F.Id("m")), Value(F.Id("m"))))),
            Describe.Lean(DescribeId.Create("maximum-degree-lower-bound"),
                DeclarationHandle.Create(Prefix + "maximum_degree_lower_bound"),
                H("Every graph contains the maximum-degree obstruction"),
                StatementSource.FromAuthor(LowerFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take an actual minimum allocation and a vertex b of maximum degree D. "
                    + "Set s equal to the square root of D and t equal to 1/(1+s). "
                    + "For each neighbour c, the complementary shares x and 1-x satisfy "
                    + "s*x*x+(1-x)*(1-x) at least s*t: their difference is (1+s)(x-t)^2. "
                    + "Summing gives D*s*t at most s times the load at b plus the sum of "
                    + "the loads at its neighbours. The latter is at most (s+D) times kappa. "
                    + "Cancellation gives D/(1+s)^2 at most kappa. Additional edges among "
                    + "the neighbours only add nonnegative squares to their loads; neither "
                    + "connectivity nor regularity is required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("star-extrema"),
                DeclarationHandle.Create(Prefix + "star_extrema"),
                H("Both attained extrema on every star"),
                StatementSource.FromAuthor(StarFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The centre load is m*t*t, and each leaf load is (1-t)^2=m*t*t. "
                    + "This allocation gives the upper bound, while the maximum-degree estimate "
                    + "gives the reverse bound. The displayed measure has mass one and gives t*t "
                    + "on every edge. For any nonnegative competing masses x and y, "
                    + "xy/(x+y) is at most x*t*t+y*(1-t)^2. When x+y is positive, clearing "
                    + "the denominator leaves the square (x*t-y*(1-t))^2; at x=y=0 both sides "
                    + "vanish. Summing over the m edges bounds every competing probability "
                    + "vector by q(m). Thus both extrema are attained on their full carriers. "
                    + "For m=1 the value is one quarter; for m=2 it is 2(3-2*sqrt(2)). "
                    + "These conclusions alone do not establish growth or legal-word bounds."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Value(Formula m) => new Formula.Fraction(m,
        new Formula.Power(Add(D(1), Call("sqrt", m)), D(2)));

    private static Formula LowerFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), degree = Call("maxDegree", g);
        return Disp(All("V", Call("Type"), Instance(Call("Fintype", v),
            Instance(Call("Nonempty", v), All("G", Call("SimpleGraph", v),
                Instance(Call("DecidableRel", Call("Adj", g)),
                    Imp(Le(D(1), degree), Le(Value(degree), Call("kappa", g)))))))));
    }

    private static Formula StarFormula()
    {
        Formula m = F.Id("m"), g = Call("H", m), a = Call("a", m), mu = Call("mu", m);
        Formula p = F.Id("p"), b = F.Id("b"), v = Call("Option", Call("Fin", m));
        Formula q = Call("q", m), kappa = Call("kappa", g);
        Formula simplex = Call("stdSimplex", Call("Real"), v);
        Formula In(Formula x) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, simplex);
        Formula Phi(Formula x) => Call("Phi", m, x);
        Formula twoValue = Mul(D(2), Sub(D(3), Mul(D(2), Call("sqrt", D(2)))));
        Formula body = And(Call("Feasible", g, a),
            And(All("b", v, Eq(Call("load", g, a, b), q)),
                And(Eq(kappa, q), And(In(mu), And(Eq(Phi(mu), q),
                    And(All("p", new Formula.TypeArrow(v, Call("Real")),
                            Imp(In(p), Le(Phi(p), q))),
                        And(Imp(Eq(m, D(1)), Eq(kappa, new Formula.Fraction(D(1), D(4)))),
                            Imp(Eq(m, D(2)), Eq(kappa, twoValue)))))))));
        return Disp(All("m", Call("Nat"), Imp(Le(D(1), m), body)));
    }
}
