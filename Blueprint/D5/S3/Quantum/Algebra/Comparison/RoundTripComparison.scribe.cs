using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Comparison;

internal sealed class RoundTripComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Metric and Periods from Round-Trip Comparison.",
        H("Metric and Periods from Round-Trip Comparison"),
        Blocks(Describe.Lean(
            DescribeId.Create("metric-consequences"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/Comparison/RoundTripComparison.metric_consequences"),
            H("Metric and Periods from Round-Trip Comparison"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let A be a complete finite-dimensional real normed associative unital algebra, L a real subspace closed under the commutator, and G a subgroup of its units. Assume exp(X) belongs to G for X in L and conjugation by G preserves L. The function phi on G takes values in [0,1], equals 1 precisely at the identity, satisfies phi(g*g)=(2*phi(g)-1)^2, and is invariant under conjugation.")),
                Paragraph(Text("The data also contain a symmetric real bilinear form h on L. As X tends to zero in the inherited norm, phi(exp(X))-(1-h(X,X)/2) is little-o of the squared norm. The neighborhood includes zero; faithfulness already fixes phi(exp(0))=1, so this does not strengthen the punctured germ together with that prescribed value.")),
                Paragraph(Text("In the displayed formula, Data(L,G) is the Lean comparison structure containing exactly these closure assumptions, the function phi, its symmetric form h, and the five comparison properties stated above. The notation h(D), phi(D), and exp(D) denotes respectively the form D.h, the function D.phi, and the exponential D.exp with values in G. The norm in the quadratic-germ condition is the inherited algebra norm.")),
                Paragraph(Text("Then h(X,X) is nonnegative, and vanishes only when X=0. For every real t and X in L, phi(exp(tX))=cos(t*sqrt(h(X,X)/2))^2. The exponential exp(tX) is the identity if and only if t*sqrt(h(X,X)/2)=pi*n for some integer n. This period equivalence includes X=0.")),
                Paragraph(Text("For all C,X,Y in L the form obeys h([C,X],Y)+h(X,[C,Y])=0. Thus the quadratic coefficient is an invariant positive definite form.")),
                Paragraph(Text("On each ray, boundedness forces the quadratic coefficient to be nonnegative. Applying the bounded duplication uniqueness theorem to 2*phi-1 gives the cosine formula. If the coefficient vanishes, faithfulness makes the entire exponential ray constant; its derivative at zero forces X=0. Conjugation invariance of the quadratic germ supplies the infinitesimal identity.")),
                Paragraph(Text("These are conditional statements about the given algebra, subgroup and function. They impose no group topology beyond the ambient algebra used in the germ, and do not identify a physical comparison function or classify global groups."))),
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

    private static Formula Context(Formula body)
    {
        Formula a = F.Id("A"), l = F.Id("L"), g = F.Id("G");
        Formula data = Call("Data", l, g);
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
        Formula h = Call("h", d), p = Call("phi", d);
        Formula x = F.Id("X"), y = F.Id("Y"), c = F.Id("C"), t = F.Id("t");
        Formula q = At(h, x, x);
        Formula r = Call("sqrt", new Formula.Fraction(q, D(2)));
        Formula e = At(Call("exp", d), Mul(t, x));
        Formula positive = All("X", l, And(Rel(q, FormulaRelationOperator.GreaterThanOrEqual, D(0)), Imp(Eqn(q, D(0)), Eqn(x, D(0)))));
        Formula cosine = All("t", Real, All("X", l, Eqn(At(p, e), Sq(Call("cos", Mul(t, r))))));
        Formula periods = All("t", Real, All("X", l, new Formula.Logic(Eqn(e, D(1)), FormulaLogicOperator.Iff,
            Ex("n", Seq(Mathbb, Grp(F.Id("Z"))), Eqn(Mul(t, r), Mul(Pi, F.Id("n")))))));
        Formula invariant = All("C", l, All("X", l, All("Y", l,
            Eqn(Seq(At(h, Call("bracket", c, x), y), Plus, At(h, x, Call("bracket", c, y))), D(0)))));
        Formula conclusion = And(positive, And(cosine, And(periods, invariant)));
        return Disp(Context(conclusion));
    }
}
