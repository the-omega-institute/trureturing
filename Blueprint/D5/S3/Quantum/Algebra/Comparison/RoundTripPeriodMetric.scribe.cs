using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Comparison;

internal sealed class RoundTripPeriodMetricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Round-Trip Classification from Ray Continuity.",
        H("Round-Trip Classification from Ray Continuity"),
        Blocks(Describe.Lean(
            DescribeId.Create("comparison-classification-of-continuous-rays"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/Comparison/RoundTripPeriodMetric.comparison_classification_of_continuous_rays"),
            H("Round-Trip Classification from Ray Continuity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let A be a complete finite-dimensional real normed associative unital algebra. Let L be a real Lie subalgebra of A for the commutator, and let G be a subgroup of its units. The data ContinuousData(L,G) comprise the function phi on G, membership of exp(X) in G for each X in L, and preservation of L under conjugation by G. The function takes values in [0,1], equals 1 precisely at the identity, satisfies the duplication law phi(g*g)=(2*phi(g)-1)^2, and is invariant under conjugation. For each X, the real function t ↦ phi(exp(tX)) is continuous.")),
                Paragraph(Text("Every nonzero direction has a positive return time. Its return times are the integer multiples of the least positive return time T. The comparison is the square of the cosine at angular frequency pi/T on this ray, and the symmetric bilinear form h satisfies h(X,X)=2*pi^2/T^2.")),
                Paragraph(Text("In the complexified left regular representation, a generator with periodic exponential has an eigenbasis with integral frequencies after rescaling by a return time. The negative trace of its square is positive in each nonzero direction. After dividing the generator by the square root of this trace form, the characteristic determinant has countable range. It is constant on the connected punctured space in dimension at least two. The one-dimensional case follows from scaling a generator. The common return lattice of normalized directions then determines the scalar multiple of the trace form that gives h.")),
                Paragraph(Text("The resulting cosine formula and the bound of the bilinear form by the inherited algebra norm squared give the quadratic expansion at zero. Consequently h is positive definite and infinitesimally invariant. Commuting pairs are dependent, the dimension is zero, one or three, and the dimension-three space has an h-orthonormal basis with one positive cyclic bracket constant."))),

            DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(string n, Formula ty, Formula p) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(n), ty)], p);
    private static Formula Ex(string n, Formula ty, Formula p) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new Formula.BoundVariable(FormulaIdentifier.Create(n), ty)], p);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eqn(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Sp, Cdot, Sp, b, Close);
    private static Formula Sq(Formula a) => new Formula.Power(a, D(2));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Seq(Operatorname, Grp(F.Id("if")), Sp, Seq(Open, condition, Close), Sp,
            Operatorname, Grp(F.Id("then")), Sp, yes, Sp,
            Operatorname, Grp(F.Id("else")), Sp, no);

    private static Formula Context(Formula body)
    {
        Formula a = F.Id("A"), l = F.Id("L"), g = F.Id("G");
        Formula data = Call("ContinuousData", l, g);
        Formula result = All("D", data, body);
        return All("A", F.Id("Type"), Seq(
            OpenBracket, Call("NormedRing", a), CloseBracket, Sp,
            OpenBracket, Call("NormedAlgebra", Real, a), CloseBracket, Sp,
            OpenBracket, Call("CompleteSpace", a), CloseBracket, Sp,
            OpenBracket, Call("FiniteDimensional", Real, a), CloseBracket, Sp,
            All("L", Call("LieSubalgebra", Real, a),
                All("G", Call("Subgroup", Call("Units", a)), result))));
    }

    private static Formula TheoremFormula()
    {
        Formula l = F.Id("L"), d = F.Id("D");
        Formula h = F.Id("h"), p = Call("phi", d);
        Formula x = F.Id("X"), y = F.Id("Y"), c = F.Id("C"), t = F.Id("t");
        Formula q = At(h, x, x);
        Formula r = Call("sqrt", new Formula.Fraction(q, D(2)));
        Formula e = At(Call("exp", d), Mul(t, x));
        Formula nonnegative = All("X", l, Rel(q, FormulaRelationOperator.GreaterThanOrEqual, D(0)));
        Formula definite = All("X", l, Imp(Eqn(q, D(0)), Eqn(x, D(0))));
        Formula cosine = All("t", Real, All("X", l, Eqn(At(p, e), Sq(Call("cos", Mul(t, r))))));
        Formula periods = All("t", Real, All("X", l, new Formula.Logic(Eqn(e, D(1)), FormulaLogicOperator.Iff,
            Ex("n", Seq(Mathbb, Grp(F.Id("Z"))), Eqn(Mul(t, r), Mul(Pi, F.Id("n")))))));
        Formula period = F.Id("T"), k = F.Id("k");
        Formula exactReturnLattice = All("t", Real, new Formula.Logic(Eqn(e, D(1)),
            FormulaLogicOperator.Iff, Ex("k", Seq(Mathbb, Grp(F.Id("Z"))), Eqn(t, Mul(period, k)))));
        Formula metricFromPeriods = All("X", l, Imp(Rel(x, FormulaRelationOperator.NotEqual, D(0)),
            Ex("T", Real, And(Rel(period, FormulaRelationOperator.GreaterThan, D(0)),
                And(exactReturnLattice, Eqn(q, new Formula.Fraction(Mul(D(2), Sq(Pi)), Sq(period))))))));
        Formula invariant = All("C", l, All("X", l, All("Y", l,
            Eqn(Seq(At(h, Call("bracket", c, x), y), Plus, At(h, x, Call("bracket", c, y))), D(0)))));
        Formula dependent = All("X", l, All("Y", l, Imp(Eqn(Call("bracket", x, y), D(0)),
            new Formula.Logic(Eqn(x, D(0)), FormulaLogicOperator.Or, Ex("c", Real, Eqn(y, Mul(F.Id("c"), x)))))));
        Formula dim = Call("finrank", Real, l);
        Formula dimensions = new Formula.Logic(Eqn(dim, D(0)), FormulaLogicOperator.Or,
            new Formula.Logic(Eqn(dim, D(1)), FormulaLogicOperator.Or, Eqn(dim, D(3))));
        Formula b = F.Id("b"), mu = F.Id("mu"), i = F.Id("i"), j = F.Id("j");
        Formula orthogonal = All("i", Call("Fin", D(3)), All("j", Call("Fin", D(3)),
            Eqn(At(h, At(b, i), At(b, j)), IfThenElse(Eqn(i, j), D(1), D(0)))));
        Formula brackets = And(Eqn(Call("bracket", At(b, D(0)), At(b, D(1))), Mul(mu, At(b, D(2)))),
            And(Eqn(Call("bracket", At(b, D(1)), At(b, D(2))), Mul(mu, At(b, D(0)))),
                Eqn(Call("bracket", At(b, D(2)), At(b, D(0))), Mul(mu, At(b, D(1))))));
        Formula frame = Imp(Eqn(dim, D(3)), Ex("b", Call("Basis", Call("Fin", D(3)), Real, l),
            Ex("mu", Real, And(Rel(mu, FormulaRelationOperator.GreaterThan, D(0)), And(orthogonal, brackets)))));
        Formula geometry = And(dependent, And(invariant, And(dimensions, frame)));
        Formula returns = And(metricFromPeriods, And(periods, geometry));
        Formula classification = And(nonnegative, And(definite, And(cosine, returns)));
        Formula conclusion = Ex("h", Call("BilinForm", Real, l),
            And(Call("IsSymm", h), classification));
        return Disp(Context(conclusion));
    }
}
