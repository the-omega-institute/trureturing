using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryGram;

internal sealed class StationaryOccupationRankNullityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula a = Id("a"), B = Id("B"), u = Id("u"), i = Id("i"), r = Id("r"), c = Id("c");
        Formula box = Call("TailBox", a);
        Formula vectors = Arrow(box, C);
        Formula matrices = Call("Matrix", box, box, C);
        Formula kernel = Call("ker", Call("mulVecLin", B));
        Formula polynomial = Call("polynomialMap", a, u);
        Formula recurrence = Recurrence(a, B);
        Formula quadratic = Context(All("B", matrices, Imp(recurrence,
            All("u", vectors, Imp(Eq(At(u, D(0)), D(0)),
                Eq(Quadratic(B, u), SumAt("i", Id("sigma"),
                    Quadratic(B, Call("lowering", a, i, u)))))))));
        Formula closure = Context(All("B", matrices,
            Imp(And(Call("PosSemidef", B), recurrence), All("u", vectors,
                Imp(And(Mem(u, kernel), Eq(At(u, D(0)), D(0))),
                    All("i", Id("sigma"), Mem(Call("lowering", a, i, u), kernel)))))));
        Formula singleton = Context(All("r", box, All("c", C,
            Eq(Call("polynomialMap", a, Call("PiSingle", r, c)),
                Call("monomial", Call("exponent", a, r),
                    Div(c, Call("factorialProduct", a, r)))))));
        Formula injective = Context(Call("Injective", Call("polynomialMap", a)));
        Formula derivative = Context(All("i", Id("sigma"), All("u", vectors,
            Eq(Call("pderiv", i, polynomial),
                Call("polynomialMap", a, Call("lowering", a, i, u))))));
        Formula constant = Context(All("u", vectors,
            Eq(Call("constantCoeff", polynomial), At(u, D(0)))));
        Formula rank = Context(All("B", matrices,
            Imp(And(Call("PosSemidef", B), And(Eq(At(B, D(0), D(0)), D(1)), recurrence)),
                Le(Sub(ProdAt("i", Id("sigma"), Add(At(a, i), D(1))),
                    Call("FinsetSup", Call("univ", Id("sigma")), a)), Call("rank", B)))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "PSD occupation recurrence gives a rank bound through factorial polynomial coordinates.",
            H("Stationary Occupation Rank Nullity"), Blocks(
                Paragraph(Text(
                    "Let sigma be a finite type and let a assign a natural number to each coordinate. " +
                    "TailBox(a) is the product of the intervals Fin(a(i)+1), including their zero endpoints. " +
                    "The map lower decreases coordinate i by one using natural subtraction. The linear " +
                    "operator lowering sends a coordinate vector at r to the vector at lower(a,i,r) " +
                    "when r(i) is positive, and to zero otherwise. All matrices and vectors below are complex.")),
                Theorem("recurrence-quadratic-identity", "recurrence_quadratic_identity", quadratic,
                    "For a vector whose zero coordinate vanishes, the nonzero-index recurrence " +
                    "gives the sum of the lowered quadratic forms. The star is complex conjugation; " +
                    "dotProduct and mulVec give the sesquilinear expression."),
                Theorem("lowering-mem-kernel", "lowering_mem_kernel", closure,
                    "Positive semidefiniteness makes every term in that sum nonnegative. " +
                    "If the original vector lies in the kernel, their sum is zero, so each lowered " +
                    "quadratic form vanishes and each lowered vector lies in the same kernel."),
                Paragraph(Text(
                    "The exponent of r is the finitely supported function with value r(i). " +
                    "The factorialProduct is the product of the factorials of these values. It never " +
                    "vanishes. Scaling the monomial basis by its inverse defines a linear equivalence " +
                    "coordinateEquiv onto the polynomials supported in the rectangle; polynomialMap " +
                    "is its inclusion into the full multivariate polynomial ring.")),
                Theorem("polynomial-map-single", "polynomialMap_single", singleton,
                    "A single coefficient c at r becomes the monomial with coefficient " +
                    "c divided by the product of coordinate factorials."),
                Theorem("polynomial-map-injective", "polynomialMap_injective", injective,
                    "The scaled monomial coordinates are unique, so this polynomial map is injective."),
                Theorem("pderiv-polynomial-map", "pderiv_polynomialMap", derivative,
                    "The factorial scaling cancels the exponent introduced by differentiation. " +
                    "Consequently lowering and partial differentiation intertwine on every vector."),
                Theorem("constant-coeff-polynomial-map", "constantCoeff_polynomialMap", constant,
                    "The constant coefficient is exactly the zero coordinate of the coefficient vector."),
                Theorem("stationary-gram-rank-lower-bound", "stationary_gram_rank_lower_bound", rank,
                    "Map the matrix kernel into the rectangular polynomial subspace. The unit " +
                    "zero entry excludes nonzero constants, and the lowering identity gives conditional " +
                    "derivative closure. The rectangular polynomial dimension bound then bounds nullity " +
                    "by the finite supremum of a. Rank-nullity and the product cardinality give the " +
                    "displayed inequality, including the all-zero box and an empty coordinate type."))));
    }

    private static Formula Recurrence(Formula a, Formula B)
    {
        Formula r = Id("r"), s = Id("s"), i = Id("i");
        Formula box = Call("TailBox", a);
        return All("r", box, All("s", box,
            Imp(And(Ne(r, D(0)), Ne(s, D(0))), Eq(At(B, r, s),
                SumAt("i", Id("sigma"), Call("ite",
                    And(Lt(D(0), Call("val", At(r, i))), Lt(D(0), Call("val", At(s, i)))),
                    At(B, Call("lower", a, i, r), Call("lower", a, i, s)), D(0)))))));
    }

    private static Formula Context(Formula body) => All("sigma", Id("Type"),
        Imp(Call("Fintype", Id("sigma")), All("a", Arrow(Id("sigma"), N), body)));
    private static DocumentBlock Theorem(string id, string name, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(
            "D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity." + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))));
    private static Formula Id(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula C => Seq(Mathbb, Grp(Id("C")));
    private static Formula Call(string name, params Formula[] args) => At(Id(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Arrow(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Mem(Formula x, Formula y) => Seq(x, Sp, InMacro, Sp, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Quadratic(Formula B, Formula u) => Call("dotProduct", Call("star", u), Call("mulVec", B, u));
    private static Formula SumAt(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, domain)), Grp(body));
    private static Formula ProdAt(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(Id(name), Colon, domain)), Grp(body));
}
