using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class QuadraticGermInvarianceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/QuadraticForms/QuadraticGermInvariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A scalar function's quadratic expansion determines the bilinear form preserved by its linear symmetries.",
        H("Symmetries of a Quadratic Germ"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-germ-on-ray"),
                DeclarationHandle.Create(Owner + "quadratic_germ_on_ray"),
                H("The coefficient on a ray"),
                StatementSource.FromAuthor(RayFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let E be a real normed vector space, B a real bilinear form, and f a real-valued function. The quadratic-germ hypothesis means that f(X) minus 1 plus B(X,X)/2 is little-o of the square of the original norm in the full neighborhood filter at zero, including the value at zero. For every fixed X, restriction to t times X has remainder little-o of t squared and quadratic term minus B(X,X)t squared/2. This includes X=0 and requires neither symmetry of B nor finite dimension.")),
                    Paragraph(Text("The restriction follows by composing the original remainder with the continuous ray and using the exact identity that the squared norm of t times X equals t squared times the squared norm of X."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bilinear-germ-symmetry"),
                DeclarationHandle.Create(Owner + "bilinear_invariant_of_quadratic_germ"),
                H("A linear symmetry preserves the quadratic form"),
                StatementSource.FromAuthor(InvarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume additionally that B is symmetric. Every real linear map T satisfying f(TX)=f(X) for all X preserves B on every pair: B(TX,TY)=B(X,Y). T need not be invertible, and no continuity assumption on f away from the quadratic germ is imposed.")),
                    Paragraph(Text("The expansions on the rays through X and TX are expansions of the same scalar function, so their quadratic coefficients agree. A nonzero constant multiple of t squared cannot be little-o of t squared on the punctured neighborhood of zero. The polarization identity then recovers every mixed value of B from diagonal values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("infinitesimal-conjugation-invariance"),
                DeclarationHandle.Create(Owner + "ad_invariant_of_exp_conjugation"),
                H("Exponential conjugation has skew infinitesimal action"),
                StatementSource.FromAuthor(AdjointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let A be a complete finite-dimensional real normed unital associative algebra and L a real Lie subalgebra for the commutator bracket. Let f on L have quadratic germ B, where B is symmetric. For every C and X in L and real t, assume that q(C,t,X)=exp(tC)X exp(-tC) belongs to L and f(q(C,t,X))=f(X). Then B([C,X],Y)+B(X,[C,Y])=0 for every C,X,Y in L.")),
                    Paragraph(Text("Each q(C,t,.) is a linear symmetry, hence preserves B by the preceding result. Its derivative at zero is the original commutator [C,X]; the calculation takes place in A and passes to the inherited topology on L. Finite dimension makes B continuous, so differentiating the invariant bilinear value gives the stated identity. No derivative of f beyond its prescribed quadratic expansion is used.")),
                    Paragraph(Text("These are consequences of quadratic expansion uniqueness, polarization and differentiation of the algebra exponential. They assert no classification of Lie algebras or groups, no positivity of B, and no empirical interpretation of the scalar function."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula ImpliesF(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
    private static Formula AndF(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Half(Formula value) => new Formula.Fraction(value, D(2));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);
    private static Formula LambdaF(string name, Formula type, Formula body) =>
        Seq(Open, F.Id(name), Colon, Sp, type, Sp, Mapsto, Sp, body, Close);
    private static Formula Bracket(Formula left, Formula right) =>
        Seq(OpenBracket, left, Comma, right, CloseBracket);

    private static Formula Germ(Formula space, Formula f, Formula b)
    {
        Formula x = F.Id("Z");
        return Call("IsLittleO", Call("nhds", D(0)),
            LambdaF("Z", space, Subtract(Apply(f, x), Subtract(D(1), Half(Apply(b, x, x))))),
            LambdaF("Z", space, Square(new Formula.Norm(x))));
    }

    private static Formula Symmetric(Formula space, Formula b) =>
        All("U", space, All("V", space,
            Equal(Apply(b, F.Id("U"), F.Id("V")), Apply(b, F.Id("V"), F.Id("U")))));

    private static Formula NormedSpaceBinders(Formula space, Formula body) =>
        All("E", F.Id("Type"),
            All("nE", Call("NormedAddCommGroup", space),
                All("sE", Call("NormedSpace", Real, space), body)));

    private static Formula RayFormula()
    {
        Formula e = F.Id("E"), b = F.Id("B"), f = F.Id("f"), x = F.Id("X");
        Formula t = F.Id("t");
        Formula conclusion = Call("IsLittleO", Call("nhds", D(0)),
            LambdaF("t", Real, Subtract(Apply(f, Call("smul", t, x)),
                Subtract(D(1), Half(Multiply(Apply(b, x, x), Square(t)))))),
            LambdaF("t", Real, Square(t)));
        return Disp(NormedSpaceBinders(e,
            All("f", Arrow(e, Real), All("B", Call("BilinForm", Real, e),
                ImpliesF(Germ(e, f, b), All("X", e, conclusion))))));
    }

    private static Formula InvarianceFormula()
    {
        Formula e = F.Id("E"), b = F.Id("B"), f = F.Id("f"), t = F.Id("T");
        Formula x = F.Id("X"), y = F.Id("Y");
        Formula invariance = All("X", e, Equal(Apply(f, Apply(t, x)), Apply(f, x)));
        Formula conclusion = All("X", e, All("Y", e,
            Equal(Apply(b, Apply(t, x), Apply(t, y)), Apply(b, x, y))));
        return Disp(NormedSpaceBinders(e,
            All("f", Arrow(e, Real), All("B", Call("BilinForm", Real, e),
                ImpliesF(Symmetric(e, b), ImpliesF(Germ(e, f, b),
                    All("T", Call("LinearMap", Real, e, e),
                        ImpliesF(invariance, conclusion))))))));
    }

    private static Formula AdjointFormula()
    {
        Formula a = F.Id("A"), l = F.Id("L"), f = F.Id("f"), b = F.Id("B");
        Formula c = F.Id("C"), t = F.Id("t"), x = F.Id("X"), y = F.Id("Y");
        Formula tc = Call("smul", t, c);
        Formula q = Multiply(Multiply(Call("exp", tc), x),
            Call("exp", new Formula.Negate(tc)));
        Formula conjugation = All("C", l, All("t", Real, All("X", l,
            AndF(new Formula.Relation(q, FormulaRelationOperator.MemberOf, l),
                Equal(Apply(f, q), Apply(f, x))))));
        Formula conclusion = All("C", l, All("X", l, All("Y", l,
            Equal(Add(Apply(b, Bracket(c, x), y), Apply(b, x, Bracket(c, y))), D(0)))));
        Formula body = All("L", Call("LieSubalgebra", Real, a),
            All("f", Arrow(l, Real), All("B", Call("BilinForm", Real, l),
                ImpliesF(Symmetric(l, b), ImpliesF(Germ(l, f, b),
                    ImpliesF(conjugation, conclusion))))));
        return Disp(All("A", F.Id("Type"),
            All("nA", Call("NormedRing", a),
                All("aA", Call("NormedAlgebra", Real, a),
                    All("cA", Call("CompleteSpace", a),
                        All("dA", Call("FiniteDimensional", Real, a), body))))));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
