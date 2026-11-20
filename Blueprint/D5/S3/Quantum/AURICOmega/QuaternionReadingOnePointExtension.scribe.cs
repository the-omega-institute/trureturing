using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class QuaternionReadingOnePointExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/HilbertOperators/aronszajn1950theory");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adding one point with self-reading d to the unit quaternions keeps the Gram forms of the reading kappa x y = (1 + <x, y>) / 2 nonnegative exactly when the new readings are (a + <b, x>) / sqrt 2 with a^2 + |b|^2 <= d, and it suffices to test six points; feature rank five forces a^2 + |b|^2 = 1; and the extensions that reach the value one, or, when nonnegative of feature rank five, the value zero, are exactly the readings of points already present.",
        H("One-point extensions of the unit-quaternion reading"),
        Blocks(
            Node("feature-rank", "HasOnePointFeatureRank", "One-point extensions of feature rank r",
                StatementSource.FromAuthor(DefinitionFormula()), AssessedProvenance.FromRepo(),
                "A function f on the unit quaternions is read as the readings of one new point against the points of the unit quaternion comparison model. "
                    + "The extension has feature rank r when there is a map v from the unit quaternions with one extra point none into Euclidean r-space such that the inner products of the images of old points are the model readings, the inner product of the image of an old point x with the image of the new point is f(x), and the new point is sent to a unit vector. "
                    + "The unit norm says that the new point reads one against itself. In the Lean statement the map is called phi.",
                DescribeRole.Definition),
            Node("nonneg", "forall_nonneg_iff_norm_le", "Nonnegative affine readings",
                StatementSource.FromAuthor(NonnegFormula()), AssessedProvenance.FromRepo(),
                "For a real number a and a quaternion b, the affine readings (a + <b, x>) / sqrt 2 are nonnegative at every unit quaternion x exactly when |b| <= a. "
                    + "By the Cauchy-Schwarz inequality <b, x> >= -|b| for a unit quaternion x, and the value -|b| is attained at x = -b / |b| (at any unit quaternion when b = 0), so the minimum of the readings is (a - |b|) / sqrt 2.",
                DescribeRole.Lemma),
            Node("one-point-extension", "tfae_onePointExtension", "Positive semidefinite one-point extensions are affine",
                StatementSource.FromAuthor(ExtensionFormula()), AssessedProvenance.FromRepo(Source),
                "Extending the reading of the unit quaternions by one new point with readings f(x) against the old points and self-reading d gives, for weights c on finitely many old points x and the weight t on the new point, the Gram form d * t^2 + 2 * t * sum c(i) * f(x(i)) + sum sum c(i) * c(j) * kappa(x(i), x(j)). "
                    + "Three conditions are equivalent. The first says that all these forms are nonnegative, for every finite family of old points. The second says the same only for families of exactly six old points, which may repeat. The third says that f(x) = (a + <b, x>) / sqrt 2 for a real number a and a quaternion b with a^2 + |b|^2 <= d. "
                    + "The first condition contains the second. "
                    + "The Gram form of the old points alone is half of the squared total weight plus half of the squared norm of the weighted sum of the points, since kappa(x, y) = (1 + <x, y>) / 2. "
                    + "If f is affine with the stated bound, the extended form is half of (s + sqrt 2 * t * a)^2 + |q + sqrt 2 * t * b|^2 plus t^2 * (d - a^2 - |b|^2), where s is the total weight and q the weighted sum, and so it is nonnegative for every finite family; this gives the first condition from the third. "
                    + "From the second: every unit quaternion y is a combination of the five points 1, -1, i, j and k with total weight one and weighted sum y. The six-point family of y with weight -1 and of these five points with those weights has total weight zero and weighted sum zero, so its Gram form vanishes; a form that is nonnegative for every t and has no quadratic part in the old weights must then have zero linear part, so f(y) is the same combination of f(1), f(-1), f(i), f(j) and f(k), which makes f affine in the coordinates of y. "
                    + "The six-point family of the five points with total weight -sqrt 2 * a and weighted sum -sqrt 2 * b, padded by the point 1 with weight zero, together with t = 1, has Gram form d - a^2 - |b|^2, which gives the bound. "
                    + "So nonnegativity needs to be tested on families of six points only; whether fewer points suffice is not decided here. "
                    + "No sign condition on d is assumed; for negative d the first and third conditions fail. "
                    + "In the language of reproducing kernels, the equivalence of the first and third conditions is the finite-dimensional case of the classical description of the functions of the reproducing kernel Hilbert space of a positive semidefinite kernel and their norms, applied to the quaternion reading, whose space consists of the affine functions a + <b, x>.",
                DescribeRole.Theorem),
            Node("rank-five", "hasOnePointFeatureRank_five_iff", "One-point extensions of feature rank five",
                StatementSource.FromAuthor(RankFiveFormula()), AssessedProvenance.FromRepo(),
                "A function f on the unit quaternions is a one-point extension of feature rank five exactly when f(x) = (a + <b, x>) / sqrt 2 with a^2 + |b|^2 = 1. No sign condition on the readings is involved. "
                    + "A realization in Euclidean five-space has nonnegative extended Gram forms with self-reading one, so the previous theorem with d = 1 makes f affine with a^2 + |b|^2 <= 1. "
                    + "The reading of the unit quaternions itself has feature rank at least five, so the images of the old points span Euclidean five-space and the unit vector of the new point is a combination of them. Applying the Gram identity of the previous theorem to that combination and the Cauchy-Schwarz inequality for <b, q> gives a^2 + |b|^2 >= 1. "
                    + "Conversely, the vector (a, b) of Euclidean five-space is a unit vector when a^2 + |b|^2 = 1, and its inner product with the feature (1, x) / sqrt 2 of x is (a + <b, x>) / sqrt 2. "
                    + "Together with the nonnegativity criterion, the nonnegative extensions of feature rank five are those with |b| <= a and a^2 + |b|^2 = 1.",
                DescribeRole.Theorem),
            Node("value-one", "exists_eq_one_iff_exists_eq_kappa", "Extensions that reach one are old points",
                StatementSource.FromAuthor(OneFormula()), AssessedProvenance.FromRepo(),
                "Let f have nonnegative extended Gram forms with self-reading one. Then f takes the value one at some unit quaternion exactly when f is the reading kappa(x, x0) of some unit quaternion x0. No rank or sign condition is needed. "
                    + "By the extension theorem f(x) = (a + <b, x>) / sqrt 2 with a^2 + |b|^2 <= 1. A value one at x1 forces sqrt 2 <= a + |b|, while (a + |b|)^2 <= 2 * (a^2 + |b|^2) <= 2, so a = |b| = 1 / sqrt 2 and <b, x1> = |b|; the equality case of the Cauchy-Schwarz inequality gives b = x1 / sqrt 2, and f is the reading of x1. "
                    + "Conversely, the reading of x0 is one at x0. "
                    + "The positivity hypothesis is needed: the constant one takes the value one but is not the reading of any point, since the reading of x0 vanishes at -x0. In the display the points x1 and x0 of the Lean statement are written u and w.",
                DescribeRole.Theorem),
            Node("value-zero", "exists_eq_zero_iff_exists_eq_kappa", "Nonnegative rank-five extensions that reach zero are old points",
                StatementSource.FromAuthor(ZeroFormula()), AssessedProvenance.FromRepo(),
                "Let f be a nonnegative one-point extension of feature rank five. Then f takes the value zero at some unit quaternion exactly when f is the reading kappa(x, x0) of some unit quaternion x0. "
                    + "By the rank-five classification f(x) = (a + <b, x>) / sqrt 2 with a^2 + |b|^2 = 1, and by the nonnegativity criterion |b| <= a. A zero at x1 forces <b, x1> = -a <= -|b|, so a = |b| = 1 / sqrt 2 and <b, -x1> = |b|; the equality case of the Cauchy-Schwarz inequality gives b = -x1 / sqrt 2, and f is the reading of -x1. "
                    + "Conversely, the reading of x0 is zero at -x0. "
                    + "Both hypotheses are needed. The readings <1, x> / sqrt 2 (a = 0, b = 1) have feature rank five and vanish at i, but take the negative value -1 / sqrt 2 at -1, so they are not the readings of a point. The readings (1 / 2 + <b, x>) / sqrt 2 with b = 1 / 2 are nonnegative, have nonnegative extended Gram forms with self-reading one and vanish at -1, but never reach the value one, so they are not the readings of a point, and by this theorem they do not have feature rank five. "
                    + "Taken with the rank-five classification, the unit quaternions cannot be enlarged by a point whose readings reach zero without raising the feature rank above five or taking negative values, and not by a point whose readings reach one at all. In the display the points x1 and x0 of the Lean statement are written u and w.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("quaternion-reading-one-point-extension-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula AtMost(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sq(Formula x) => new Formula.Power(x, D(2));
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula SumOver(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Sp, InMacro, Sp, domain)), Sp, Parenthesized(body));

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Quaternions => Seq(Mathbb, Grp(F.Id("H")), OpenBracket, Reals, CloseBracket);
    private static Formula Units => Call("unitary", Quaternions);
    private static Formula Model => Seq(Operatorname, Grp(F.Id("quaternionModel")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Inner(Formula x, Formula y) =>
        new Formula.Subscript(Seq(Langle, Sp, x, Comma, Sp, y, Sp, Rangle), Reals);
    private static Formula Kappa(Formula x, Formula y) => Call("kappa", Model, x, y);
    private static Formula SqrtTwo => Seq(Sqrt, Grp(D(2)));
    private static Formula Affine(Formula x) => new Formula.Fraction(Add(F.Id("a"), Inner(F.Id("b"), x)), SqrtTwo);
    private static Formula Reading(Formula x) => At(F.Id("f"), x);
    private static Formula OverReading(Formula body) => ForAll("f", new Formula.TypeArrow(Units, Reals), body);

    /// <summary>f(x) = (a + &lt;b, x&gt;) / sqrt 2 for every unit quaternion x.</summary>
    private static Formula AffineReading() => ForAll("x", Units, Equal(Reading(F.Id("x")), Affine(F.Id("x"))));

    private static Formula DefinitionFormula()
    {
        Formula v = F.Id("v"), x = F.Id("x"), y = F.Id("y");
        Formula none = Seq(Operatorname, Grp(F.Id("none")));
        Formula domain = new Formula.TypeArrow(Call("Option", Units), Call("EuclideanSpace", Reals, Fin(F.Id("r"))));
        Formula old = ForAllMany(Units,
            Equal(Kappa(x, y), Inner(At(v, Call("some", x)), At(v, Call("some", y)))), "x", "y");
        Formula readings = ForAll("x", Units, Equal(Reading(x), Inner(At(v, Call("some", x)), At(v, none))));
        Formula unit = Equal(Norm(At(v, none)), D(1));
        return Disp(OverReading(ForAll("r", Naturals,
            Iff(Call("HasOnePointFeatureRank", F.Id("f"), F.Id("r")),
                Exists("v", domain, And(old, And(readings, unit)))))));
    }

    private static Formula Form(Formula d, Formula n, Formula x, Formula c, Formula t)
    {
        Formula i = F.Id("i"), j = F.Id("j");
        Formula linear = SumOver("i", Fin(n), Mul(At(c, i), Reading(At(x, i))));
        Formula quadratic = SumOver("i", Fin(n), SumOver("j", Fin(n),
            Mul(Mul(At(c, i), At(c, j)), Kappa(At(x, i), At(x, j)))));
        Formula square = d is null ? Sq(t) : Mul(d, Sq(t));
        return AtMost(D(0), Add(Add(square, Mul(Mul(D(2), t), linear)), quadratic));
    }

    /// <summary>Nonnegativity of the extended Gram forms over all finite families.</summary>
    private static Formula AllFamilies(Formula? d)
    {
        Formula n = F.Id("n"), x = F.Id("x"), c = F.Id("c"), t = F.Id("t");
        return ForAll("n", Naturals, ForAll("x", new Formula.TypeArrow(Fin(n), Units),
            ForAll("c", new Formula.TypeArrow(Fin(n), Reals), ForAll("t", Reals, Form(d, n, x, c, t)))));
    }

    private static Formula NonnegFormula() =>
        Disp(ForAll("a", Reals, ForAll("b", Quaternions,
            Iff(ForAll("x", Units, AtMost(D(0), Affine(F.Id("x")))), AtMost(Norm(F.Id("b")), F.Id("a"))))));

    private static Formula ExtensionFormula()
    {
        Formula d = F.Id("d"), x = F.Id("x"), c = F.Id("c"), t = F.Id("t");
        Formula six = ForAll("x", new Formula.TypeArrow(Fin(D(6)), Units),
            ForAll("c", new Formula.TypeArrow(Fin(D(6)), Reals), ForAll("t", Reals, Form(d, D(6), x, c, t))));
        Formula affine = Exists("a", Reals, Exists("b", Quaternions,
            And(AtMost(Add(Sq(F.Id("a")), Sq(Norm(F.Id("b")))), d), AffineReading())));
        Formula tfae = Seq(Operatorname, Grp(F.Id("List"), Dot, F.Id("TFAE")), Open, OpenBracket,
            Parenthesized(AllFamilies(d)), Comma, Sp, Parenthesized(six), Comma, Sp, Parenthesized(affine),
            CloseBracket, Close);
        return Disp(OverReading(ForAll("d", Reals, tfae)));
    }

    private static Formula RankFiveFormula()
    {
        Formula right = Exists("a", Reals, Exists("b", Quaternions,
            And(Equal(Add(Sq(F.Id("a")), Sq(Norm(F.Id("b")))), D(1)), AffineReading())));
        return Disp(OverReading(Iff(Call("HasOnePointFeatureRank", F.Id("f"), D(5)), right)));
    }

    private static Formula OldPoint()
    {
        Formula x = F.Id("x");
        return Exists("w", Units, ForAll("x", Units, Equal(Reading(x), Kappa(x, F.Id("w")))));
    }

    private static Formula OneFormula() =>
        Disp(OverReading(Implies(AllFamilies(null),
            Iff(Exists("u", Units, Equal(Reading(F.Id("u")), D(1))), OldPoint()))));

    private static Formula ZeroFormula() =>
        Disp(OverReading(Implies(Call("HasOnePointFeatureRank", F.Id("f"), D(5)),
            Implies(ForAll("x", Units, AtMost(D(0), Reading(F.Id("x")))),
                Iff(Exists("u", Units, Equal(Reading(F.Id("u")), D(0))), OldPoint())))));
}
