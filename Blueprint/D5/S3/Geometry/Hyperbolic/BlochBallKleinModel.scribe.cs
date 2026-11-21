using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperbolic;

internal sealed class BlochBallKleinModelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperbolic/BlochBallKleinModel.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The open Bloch ball with the Klein distance is isometric to hyperbolic three-space; the filters of invertible two-by-two complex matrices map the closed ball, the open ball and the unit sphere into themselves and preserve the Klein distance, filters compose as the matrices multiply wherever the normaliser is nonzero, and every point of the open ball is the image of the centre under the filter of a positive definite matrix of determinant one, so the action is transitive.",
        H("The Klein model on the open Bloch ball"),
        Blocks(
            Node("klein-cosh", "kleinCosh", "The Klein distance function",
                StatementSource.FromAuthor(KleinCoshFormula()), AssessedProvenance.FromRepo(),
                "For vectors r and s of the Euclidean space R^3, kleinCosh(r, s) = (1 - <r, s>) / sqrt((1 - |r|^2) (1 - |s|^2)). On the open unit ball this is the hyperbolic cosine of the hyperbolic distance in the Beltrami-Klein model. The formula has this meaning only for |r| < 1 and |s| < 1. Elsewhere it is still defined: the product (1 - |r|^2) (1 - |s|^2) is zero when a point lies on the unit sphere, negative when one point lies inside the unit sphere and the other outside, and positive when both lie outside. In the first two cases the square root is 0 (by convention for a negative argument) and division by 0 gives 0, so kleinCosh is 0; in the last case the quotient is a real number, but it is not the hyperbolic cosine of a distance between points of the ball.",
                DescribeRole.Definition),
            Node("bloch-filter", "blochFilter", "The filter of a matrix on Bloch vectors",
                StatementSource.FromAuthor(FilterFormula()), AssessedProvenance.FromRepo(),
                "For a two-by-two complex matrix g and a vector r of R^3, let rho(r) = blochMatrix(1, r) = (1 + r_x X + r_y Y + r_z Z) / 2 be the Hermitian matrix of trace one with Bloch vector r, where X, Y, Z are the Pauli matrices. The filter sends r to the Bloch vector of the normalized matrix g rho(r) g^H / Re tr(g rho(r) g^H): with M = g rho(r) g^H, blochFilter(g, r) is the scalar (Re tr M)^(-1) times bloch(M), the Bloch vector of M, whose entries for Hermitian M are tr(M X), tr(M Y) and tr(M Z). In the display g^H is written conjTranspose(g) and the scalar action is written as a product. On density matrices this is the map rho -> g rho g^H / tr(g rho g^H). When Re tr M = 0, the inverse is 0 by convention and blochFilter(g, r) = 0.",
                DescribeRole.Definition),
            Node("hyperbolic", "bloch_ball_hyperbolic", "The open Bloch ball is hyperbolic three-space",
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(Source),
                "The statement has five clauses. (1) There is a bijection Phi from the open ball {v in R^3 | |v| < 1} onto HyperbolicThreeSpace, the upper half-space model of hyperbolic three-space with its hyperbolic metric, such that cosh(dist(Phi(r), Phi(s))) = kleinCosh(r, s) for all r and s in the open ball. (2) The filter of the identity matrix is the identity: blochFilter(1, r) = r for every r. (3) For all complex matrices g and h and every vector r such that the normaliser Re tr(g rho(r) g^H) is nonzero, blochFilter(h, blochFilter(g, r)) = blochFilter(h g, r). (4) For every complex matrix g with det(g) nonzero: for every r with |r| <= 1, that is on the closed ball, the normaliser Re tr(g rho(r) g^H) is positive, |blochFilter(g, r)| <= 1, and |blochFilter(g, r)| < 1 holds exactly when |r| < 1; and blochFilter(g, .) preserves kleinCosh(r, s) whenever the normalisers of g at r and at s have a positive product, in particular on the open ball, so it acts as an isometry of the Klein distance; and kleinCosh(blochFilter(g, r), blochFilter(g, s)) = -kleinCosh(r, s) whenever the normalisers of g at r and at s have a negative product. (5) For every r with |r| < 1 there is a positive definite matrix g of determinant 1 with blochFilter(g, 0) = r. By (4) the normaliser of an invertible g is positive on the closed ball, so by (2), (3) and (4) the filters of invertible matrices act on the open ball; by (5) every point of the open ball is the image of the centre under the filter of a positive definite matrix of determinant one, so the action is transitive.",
                DescribeRole.Theorem,
                "Clause (1) uses the Klein chart r -> (r, 1) / sqrt(1 - |r|^2), a bijection of the open ball onto the future sheet of the unit hyperboloid of the Lorentz form with space-positive and time-negative signature; the Lorentz product of the images of r and s is -(1 - <r, s>) / sqrt((1 - |r|^2) (1 - |s|^2)), and the identity a * b = -cosh(d(a, b)) for points of the future sheet, together with the identification of that sheet with the upper half-space, gives the formula; the inverse map takes the spatial part of a hyperboloid point divided by its time part. Clause (3): rho(r) is Hermitian, hence so is g rho(r) g^H, and when its trace t(r) = Re tr(g rho(r) g^H) is nonzero the Bloch matrix rho(blochFilter(g, r)) equals t(r)^(-1) g rho(r) g^H; the filter of h then normalizes a nonzero real multiple of (h g) rho(r) (h g)^H, and the normalization removes the multiple. Clause (4): for two-by-two matrices, the polarized determinant tr(X adj(Y)) satisfies tr(g X g^H adj(g Y g^H)) = |det g|^2 tr(X adj(Y)), and 1 - <r, s> = 2 tr(rho(r) adj(rho(s))); hence 1 - <blochFilter(g, r), blochFilter(g, s)> = |det g|^2 (1 - <r, s>) / (t(r) t(s)) whenever t(r) and t(s) are nonzero. For invertible g and |r| <= 1, rho(r) is positive semidefinite of trace one, so g rho(r) g^H is positive semidefinite and nonzero, and t(r) is a positive real number. With s = r the identity reads 1 - |blochFilter(g, r)|^2 = |det g|^2 (1 - |r|^2) / t(r)^2, which gives both parts of the closed-ball statement; in terms of matrices, rho(blochFilter(g, r)) is the positive multiple t(r)^(-1) g rho(r) g^H of g rho(r) g^H, and its determinant (1 - |blochFilter(g, r)|^2) / 4 equals |det g|^2 (1 - |r|^2) / (4 t(r)^2). In kleinCosh the factor |det g|^2 / (t(r) t(s)) multiplies the numerator and, when t(r) t(s) is positive, also comes out of the square root in the denominator, so it cancels; when t(r) t(s) is negative the square root gives the absolute value of the factor, which is its negative, so kleinCosh changes sign. Clause (5): g is a positive multiple of a square root of rho(r), normalized to determinant one.",
                "Each hypothesis has a reason. The composition law needs only a nonzero normaliser of the first filter; for invertible g this holds on the whole closed ball, where clause (4) states that the trace t(r) is positive. Without it the law can fail: for g = h = diag(2, 1) and r = (0, 0, -5/3) the normaliser of g at r is 0, and the third coordinate of blochFilter(g, blochFilter(g, r)) is 3/5 while that of blochFilter(g g, r) is 5/3. For invertible g, kleinCosh is preserved when the two normalisers have the same sign, that is, have a positive product, and it is reversed in sign when they have opposite signs, that is, have a negative product. The same-sign case covers the whole closed ball, and also pairs outside it, for example g = diag(2, 1), r = (2, 0, 0) and s = (0, 2, 0), where both normalisers are 5/2 and kleinCosh(r, s) = 1/3. The opposite-sign case occurs as well: for g = diag(2, 1) the normaliser at r = (2, 0, 0) is 5/2 and the normaliser at s = (0, 0, -2) is -1/2, kleinCosh(r, s) = 1/3, and the opposite-sign part of clause (4) gives kleinCosh(blochFilter(g, r), blochFilter(g, s)) = -1/3; this pair is an instance of the stated part, not a separate theorem. When one normaliser vanishes the identity can fail: for g = diag(2, 1), r = (0, 0, -5/3) and s = 0 the normaliser of g at r is 0, so blochFilter(g, r) = 0, while blochFilter(g, 0) = (0, 0, 3/5); then kleinCosh(blochFilter(g, r), blochFilter(g, s)) = 5/4, whereas kleinCosh(r, s) = 0. The composition example, the same-sign pair outside the closed ball and this example with a vanishing normaliser are not stated as theorems here. Invertibility of g is needed for the closed-ball clause: for the singular matrix g = diag(1, 0) the matrix g rho(r) g^H is a multiple of diag(1, 0) for every r, so every point of the open ball is sent to the north pole (0, 0, 1), which has norm 1; this example is not stated as a theorem here either. The last clause is about the open ball: by clause (4) the filter of an invertible matrix, in particular of a positive definite one, sends the centre into the open ball.",
                "The Klein and hyperboloid models of hyperbolic space and the action of SL(2, C) on Hermitian matrices by X -> g X g^H, which is the spinor map onto the identity component of the Lorentz group, are classical; the statement here takes all invertible complex matrices, the scalar factor cancelling in the normalization. The clauses state neither that filters give every orientation-preserving isometry nor how two filters compose into a boost followed by a rotation."))));

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
    private static Formula AtMostOne(Formula x) => Rel(x, FormulaRelationOperator.LessThanOrEqual, D(1));
    private static Formula Klein(Formula x, Formula y) => Call("kleinCosh", x, y);
    private static Formula Filter(Formula g, Formula x) => Call("blochFilter", g, x);
    private static Formula Normaliser(Formula g, Formula x) => Call("re", Call("trace",
        Mul(Mul(g, Call("blochMatrix", D(1), x)), Call("conjTranspose", g))));

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
        Formula normaliser = Normaliser(g, r);
        Formula third = ForAllMany(Matrices, ForAll("r", Space,
            Implies(Rel(normaliser, FormulaRelationOperator.NotEqual, D(0)),
                Equal(Filter(h, Filter(g, r)), Filter(Mul(h, g), r)))), "g", "h");
        Formula closed = ForAll("r", Space,
            Implies(AtMostOne(Norm(r)),
                And(Less(D(0), normaliser),
                    And(AtMostOne(Norm(Filter(g, r))),
                        Logic(InBall(Filter(g, r)), FormulaLogicOperator.Iff, InBall(r))))));
        Formula isometry = ForAllMany(Space,
            Implies(Less(D(0), Mul(Normaliser(g, r), Normaliser(g, s))),
                Equal(Klein(Filter(g, r), Filter(g, s)), Klein(r, s))), "r", "s");
        Formula reversal = ForAllMany(Space,
            Implies(Less(Mul(Normaliser(g, r), Normaliser(g, s)), D(0)),
                Equal(Klein(Filter(g, r), Filter(g, s)), new Formula.Negate(Klein(r, s)))), "r", "s");
        Formula fourth = ForAll("g", Matrices,
            Implies(Rel(Call("det", g), FormulaRelationOperator.NotEqual, D(0)),
                And(closed, And(isometry, reversal))));
        Formula fifth = ForAll("r", Space, Implies(InBall(r),
            Exists("g", Matrices, And(Call("PosDef", g),
                And(Equal(Call("det", g), D(1)), Equal(Filter(g, D(0)), r))))));
        return Disp(And(first, And(second, And(third, And(fourth, fifth)))));
    }
}
