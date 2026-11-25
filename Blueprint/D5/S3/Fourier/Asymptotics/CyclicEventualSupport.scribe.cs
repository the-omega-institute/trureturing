using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicEventualSupportDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicEventualSupport";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive budget, the two-cosine squared-mass minimizer eventually has a closed front window and all nearest antipodal sites as its positive support.",
        H("Exact eventual support of the cyclic minimizer"),
        Blocks(
            Describe.Lean(DescribeId.Create("cyclic-eventual-exact-support"),
                DeclarationHandle.Create(Owner + ".cyclic_eventual_exact_support"),
                H("Eventual support for both parities and all activation levels"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a positive budget λ, set m = λ/(8π²), and take the integer-lattice activation data at m. " +
                        "The lattice weight at j is (t−j²)₊/Z. For all sufficiently large positive moduli q, " +
                        "the unique cyclic minimizer has both cosine moments equal to 1−λ/q². The positive sites " +
                        "of every minimizer are exactly those with centered j² ≤ t and those attaining " +
                        "the smallest sampled first cosine. The cutoff applies to even and odd moduli.")),
                    Paragraph(Text(
                        "Take h = 2π/q and d = 0 or 1/2 on even or odd moduli respectively. " +
                        "Use rows (1, 1−c, (1−c²)/h²) on the front window and the one or two closest " +
                        "antipodal sites. The Gram matrix has an invertible limit because its rows at the " +
                        "center, a front neighbor, and a closest antipode span three dimensions. Its solve " +
                        "matches (1, 2mh², m), with limiting coefficients (t/Z, −(t−d²)/(2Z), −1/Z).")),
                    Paragraph(Text(
                        "The total antipodal weight divided by h² tends to μ = 3m/4. Positive limiting front weights " +
                        "stay positive. At t = N², the front variation has mass −μ and squared-index moment " +
                        "m₄/3 − d²μ, where m₄ is the fourth moment of the lattice law. Adding μ times the lattice law " +
                        "gives zero mass, positive squared-index moment, and quadratic leading coefficient 1/(3Z) " +
                        "in the squared index. The weighted pair identity gives a strictly positive value at N². " +
                        "The lattice law vanishes there, so this is also the sign of the original variation.")),
                    Paragraph(Text(
                        "The two first excluded cosine levels are −cos((d+1)h) and cos((N+1)h), with N the front radius. " +
                        "Their polynomial readings have strictly negative limits. Every excluded cosine lies between them, " +
                        "so convexity gives the strict sign throughout the complement. Exact moments and the squared-distance " +
                        "identity certify the positive part as the unique minimizer."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var lambda = F.LambdaLower;
        var m = F.Id("m");
        var n = F.Id("n");
        var t = F.Id("t");
        var Z = F.Id("Z");
        var w = F.Id("w");
        var q = F.Id("q");
        var Q = F.Id("Q");
        var a = Subtract(F.D(1), new Formula.Fraction(lambda, Sq(q)));
        var v = F.Id("v");
        var i = F.Id("i");
        var j = F.Id("j");
        var residues = Call("ZMod", q);
        var weights = Call("Feasible", q, a);
        var minimum = Call("IsMinOn", F.Id("E"), weights, v);
        var antipode = Bind(FormulaQuantifier.ForAll, "j", residues,
            Le(Call("c", i), Call("c", j)));
        var support = Logic(Lt(F.D(0), Call("v", i)), FormulaLogicOperator.Iff,
            Logic(Le(Sq(Call("Centered", i)), t), FormulaLogicOperator.Or, antipode));
        var u = F.Id("u");
        var distinct = new Formula.Relation(u, FormulaRelationOperator.NotEqual, v);
        var strict = Bind(FormulaQuantifier.ForAll, "u", weights,
            Logic(distinct, FormulaLogicOperator.Implies, Lt(Call("E", v), Call("E", u))));
        var exists = Bind(FormulaQuantifier.Exists, "v", weights, And(minimum,
            And(Eq(Call("M", F.D(1), v), a), And(Eq(Call("M", F.D(2), v), a), strict))));
        var every = Bind(FormulaQuantifier.ForAll, "v", weights,
            Logic(minimum, FormulaLogicOperator.Implies,
                Bind(FormulaQuantifier.ForAll, "i", residues, support)));
        var eventual = Bind(FormulaQuantifier.Exists, "Q", F.Id("Nat"),
            Bind(FormulaQuantifier.ForAll, "q", F.Id("Nat"),
                Logic(And(Lt(F.D(0), q), Le(Q, q)), FormulaLogicOperator.Implies,
                    And(exists, every))));
        var budgets = And(Le(new Formula.Fraction(Subtract(Sq(n), F.D(1)), F.D(5)), m),
            Lt(m, new Formula.Fraction(Multiply(n, Add(n, F.D(2))), F.D(5))));
        var activation = And(Lt(F.D(0), n), And(budgets, Call("Activation", m, n, t, Z, w)));
        var data = Bind(FormulaQuantifier.Exists, "n", F.Id("Nat"),
            Bind(FormulaQuantifier.Exists, "t", F.Id("Real"),
                Bind(FormulaQuantifier.Exists, "Z", F.Id("Real"),
                    Bind(FormulaQuantifier.Exists, "w", Call("LatticeWeights"),
                        And(activation, eventual)))));
        return F.Disp(F.Seq(F.Forall, F.Sp, lambda, F.Comma, F.Sp, Lt(F.D(0), lambda), F.Comma, F.Sp,
            Eq(m, new Formula.Fraction(lambda, Multiply(F.D(8), Sq(F.Pi)))),
            F.Comma, F.Sp, data));
    }

    private static Formula Bind(FormulaQuantifier kind, string name, Formula domain, Formula body) =>
        new Formula.BindMany(kind, [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);

    private static Formula Sq(Formula a) => new Formula.Power(a, F.D(2));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(a, op, b);
}
