using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class BlochBallKleinModelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/BlochBallKleinModel.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The open Bloch ball with the Klein distance is isometric to hyperbolic three-space, and the filters of invertible two-by-two complex matrices act on it by isometries, transitively already through positive definite matrices of determinant one.",
        H("The Klein model on the open Bloch ball"),
        Blocks(
            Node("klein-cosh", "kleinCosh", "The Klein distance function",
                StatementSource.FromAuthor(KleinCoshFormula()), AssessedProvenance.FromRepo(),
                "For vectors r and s of the Euclidean space R^3, kleinCosh(r, s) = (1 - <r, s>) / sqrt((1 - |r|^2) (1 - |s|^2)). On the open unit ball this is the hyperbolic cosine of the hyperbolic distance in the Beltrami-Klein model. The formula has this meaning only for |r| < 1 and |s| < 1. Elsewhere it is still defined: the product (1 - |r|^2) (1 - |s|^2) is zero when a point lies on the unit sphere, negative when one point lies inside the unit sphere and the other outside, and positive when both lie outside. In the first two cases the square root is 0 (by convention for a negative argument) and division by 0 gives 0, so kleinCosh is 0; in the last case the quotient is a real number without hyperbolic meaning.",
                DescribeRole.Definition),
            Node("filter", "filter", "The filter of a matrix on Bloch vectors",
                StatementSource.FromAuthor(FilterFormula()), AssessedProvenance.FromRepo(),
                "For a two-by-two complex matrix g and a vector r of R^3, let rho(r) = blochMatrix(1, r) = (1 + r_x X + r_y Y + r_z Z) / 2 be the Hermitian matrix of trace one with Bloch vector r, where X, Y, Z are the Pauli matrices. The filter sends r to the Bloch vector of the normalized matrix g rho(r) g^H / Re tr(g rho(r) g^H): with M = g rho(r) g^H, filter(g, r) is the scalar (Re tr M)^(-1) times bloch(M), the vector of Pauli coefficients of M. In the display g^H is written conjTranspose(g) and the scalar action is written as a product. On density matrices this is the map rho -> g rho g^H / tr(g rho g^H).",
                DescribeRole.Definition),
            Node("hyperbolic", "bloch_ball_hyperbolic", "The open Bloch ball is hyperbolic three-space",
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(Source),
                "The statement has four clauses. (1) There is a bijection Phi from the open ball {v in R^3 | |v| < 1} onto HyperbolicThreeSpace, the upper half-space model of hyperbolic three-space with its hyperbolic metric, such that cosh(dist(Phi(r), Phi(s))) = kleinCosh(r, s) for all r and s in the open ball. (2) The filter of the identity matrix is the identity: filter(1, r) = r for every r. (3) For every complex matrix g with det(g) nonzero: for every r with |r| < 1 the filtered vector filter(g, r) again has norm less than 1; for every r with |r| <= 1, that is on the closed ball, filter(h, filter(g, r)) = filter(h g, r) for every matrix h; and filter(g, .) preserves kleinCosh on the open ball, so it acts as an isometry of the Klein distance. (4) For every r with |r| < 1 there is a positive definite matrix g of determinant 1 with filter(g, 0) = r.",
                DescribeRole.Theorem,
                "Clause (1) uses the Klein chart r -> (r, 1) / sqrt(1 - |r|^2), a bijection of the open ball onto the future sheet of the unit hyperboloid of the Lorentz form with space-positive and time-negative signature; the Lorentz product of the images of r and s is -(1 - <r, s>) / sqrt((1 - |r|^2) (1 - |s|^2)), and the identity a * b = -cosh(d(a, b)) for points of the future sheet, together with the identification of that sheet with the upper half-space, gives the formula; the inverse map takes the spatial part of a hyperboloid point divided by its time part. Clause (3): for two-by-two matrices, the polarized determinant tr(X adj(Y)) satisfies tr(g X g^H adj(g Y g^H)) = |det g|^2 tr(X adj(Y)), and 1 - <r, s> = 2 tr(rho(r) adj(rho(s))); the positive normalizing factors and |det g|^2 cancel in kleinCosh, which is homogeneous of degree zero. Positive definiteness of rho(r) for |r| < 1 is preserved by g rho(r) g^H when det(g) is nonzero, and det rho(r) = (1 - |r|^2) / 4 is then positive, so the filtered vector stays in the open ball. For the composition law on the closed ball, rho(r) is positive semidefinite and of trace one when |r| <= 1, so g rho(r) g^H is positive semidefinite and nonzero for invertible g, and its trace is a positive real number; the scalar factor (Re tr M)^(-1) is therefore nonzero and cancels in the normalization. Clause (4): g is a positive multiple of a square root of rho(r), normalized to determinant one.",
                "The hypothesis det(g) nonzero is needed; this example is not formalized: for the singular matrix g = diag(1, 0) the matrix g rho(r) g^H is a multiple of diag(1, 0) for every r, so every point of the open ball is sent to the north pole (0, 0, 1), which has norm 1. The Klein and hyperboloid models of hyperbolic space and the action of SL(2, C) on Hermitian matrices by X -> g X g^H, which is the spinor map onto the identity component of the Lorentz group, are classical; the statement here takes all invertible complex matrices, the scalar factor cancelling in the normalization. The four clauses state neither that filters give every orientation-preserving isometry nor how two filters compose into a boost followed by a rotation."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, AssessedProvenance provenance,
        string prose, DescribeRole role, params string[] more) =>
        Describe.Lean(DescribeId.Create("bloch-ball-klein-model-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks([Paragraph(Text(prose)), .. more.Select(paragraph => Paragraph(Text(paragraph)))]), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Less(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThan, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(n => new Formula.BoundVariable(FormulaIdentifier.Create(n), domain))], body);

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Space => Call("EuclideanSpace", Reals, Call("Fin", D(3)));
    private static Formula Matrices => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Complex);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Inner(Formula x, Formula y) => Seq(Langle, Sp, x, Comma, Sp, y, Sp, Rangle);
    private static Formula InBall(Formula x) => Less(Norm(x), D(1));
    private static Formula Klein(Formula x, Formula y) => Call("kleinCosh", x, y);
    private static Formula Filter(Formula g, Formula x) => Call("filter", g, x);

    private static Formula KleinCoshFormula()
    {
        Formula r = F.Id("r"), s = F.Id("s");
        Formula denominator = Seq(Sqrt, Grp(Mul(
            Sub(D(1), new Formula.Power(Norm(r), D(2))),
            Sub(D(1), new Formula.Power(Norm(s), D(2))))));
        return Disp(ForAllMany(Space,
            Equal(Klein(r, s), new Formula.Fraction(Sub(D(1), Inner(r, s)), denominator)), "r", "s"));
    }

    private static Formula FilterFormula()
    {
        Formula g = F.Id("g"), r = F.Id("r");
        Formula m = Mul(Mul(g, Call("blochMatrix", D(1), r)), Call("conjTranspose", g));
        return Disp(ForAll("g", Matrices, ForAll("r", Space,
            Equal(Filter(g, r),
                Mul(new Formula.Power(Call("re", Call("trace", m)), new Formula.Negate(D(1))),
                    Call("bloch", m))))));
    }

    private static Formula TheoremFormula()
    {
        Formula r = F.Id("r"), s = F.Id("s"), g = F.Id("g"), h = F.Id("h"), phi = F.Id("Phi");
        Formula v = F.Id("v");
        Formula ball = Seq(OpenBrace, v, Sp, InMacro, Sp, Space, Sp, Mid, Sp, InBall(v), CloseBrace);
        Formula first = Exists("Phi", Call("Equiv", ball, Seq(Operatorname, Grp(F.Id("HyperbolicThreeSpace")))),
            ForAllMany(ball,
                Equal(Call("cosh", Call("dist", new Formula.Apply(phi, [r]), new Formula.Apply(phi, [s]))),
                    Klein(r, s)), "r", "s"));
        Formula second = ForAll("r", Space, Equal(Filter(D(1), r), r));
        Formula maps = ForAll("r", Space, Implies(InBall(r), InBall(Filter(g, r))));
        Formula compose = ForAll("r", Space,
            Implies(Rel(Norm(r), FormulaRelationOperator.LessThanOrEqual, D(1)),
                ForAll("h", Matrices, Equal(Filter(h, Filter(g, r)), Filter(Mul(h, g), r)))));
        Formula isometry = ForAllMany(Space, Implies(InBall(r), Implies(InBall(s),
            Equal(Klein(Filter(g, r), Filter(g, s)), Klein(r, s)))), "r", "s");
        Formula third = ForAll("g", Matrices,
            Implies(Rel(Call("det", g), FormulaRelationOperator.NotEqual, D(0)), And(maps, And(compose, isometry))));
        Formula fourth = ForAll("r", Space, Implies(InBall(r),
            Exists("g", Matrices, And(Call("PosDef", g),
                And(Equal(Call("det", g), D(1)), Equal(Filter(g, D(0)), r))))));
        return Disp(And(first, And(second, And(third, fourth))));
    }
}
