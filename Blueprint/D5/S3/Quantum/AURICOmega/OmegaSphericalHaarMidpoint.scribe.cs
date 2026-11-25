using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaSphericalHaarMidpointDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint";

    public DocumentDefinition Create()
    {
        Formula m = F.Id("m"), n = F.Id("n"), r = F.Id("r");
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula generator = F.Id("A"), initial = F.Id("x"), weight = F.Id("alpha");
        Formula z = D(0), one = D(1), two = D(2);
        Formula naturals = NumberSet("N");
        Formula integerQuaternions = new Formula.Power(NumberSet("Z"), D(4));
        Formula rationalQuaternions = new Formula.Power(NumberSet("Q"), D(4));
        Formula ratios = Call("IntRatio");
        Formula em = Call("character", m), en = Call("character", n);
        Formula er = Call("character", r);
        Formula nonzero = And(Ne(a, z), And(Ne(b, z), Ne(c, z)));
        Formula ab = Call("spread", a, b), bc = Call("spread", b, c), ca = Call("spread", c, a);
        Formula edges = And(Ne(ab, z), And(Ne(bc, z), Ne(ca, z)));
        Formula atA = Fraction(Call("vertexSpread", a, b, c), bc);
        Formula atB = Fraction(Call("vertexSpread", b, c, a), ca);
        Formula atC = Fraction(Call("vertexSpread", c, a, b), ab);
        Formula right = Eq(Mul(Call("dot", a, a), Call("dot", b, c)),
            Mul(Call("dot", a, b), Call("dot", a, c)));
        Formula pureUnit = And(Eq(Call("scalarPart", generator), z), Equiv(NormSq(initial), one));
        Formula sampled = Call("alphaSample", weight, generator, initial);
        Formula midpoint = Call("midpointStep", generator, initial);
        Formula liftedInitial = Call("numerator", initial);
        Formula liftedMidpoint = Call("numerator", midpoint);
        Formula liftedFull = Call("triad", liftedMidpoint, liftedInitial, liftedMidpoint);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact rational character identities, squared spherical triangle laws, and midpoint quaternion evolution.",
            H("Haar characters, spherical laws, and midpoint drift"),
            Blocks(
                Law("even-character-product", "evenChar_product_sum", "Even-character product expansion",
                    All(Call("Coefficientwise", Call("polyMul", em, en), Call("characterSum", m, n)),
                        ("m", naturals), ("n", naturals)),
                    "The character polynomials start with 1 and 4κ − 1, then follow the recurrence with multiplier 4κ − 2. The character sum runs from |m − n| through m + n, inclusive. Coefficientwise comparison assigns zero to omitted entries. Induction applies the character recurrence to a whole interval and cancels the overlapping terms."),
                Law("even-character-expectation", "haar_evenChar_expectation", "Haar expectation in every degree",
                    All(Equiv(Call("Haar", er), Call("delta", r, z)), ("r", naturals)),
                    "The shifted factorial moment recurrence determines the expectation for every character. The value is one at degree zero and zero at every positive degree."),
                Law("all-degree-orthonormality", "all_degree_peter_weyl_orthonormal", "Even-character Haar orthonormality",
                    All(Equiv(Call("HaarInner", em, en), Call("delta", m, n)), ("m", naturals), ("n", naturals)),
                    "Apply the factorial moment functional to the product expansion. The degree-zero character occurs exactly when the two indices coincide."),
                Law("spherical-sine-law", "rational_spherical_sine_law", "Squared spherical sine law",
                    All(If(And(nonzero, edges), And(Equiv(atA, atB), Equiv(atB, atC))),
                        ("a", integerQuaternions), ("b", integerQuaternions), ("c", integerQuaternions)),
                    "The edge spread is one minus projective fidelity. The vertex spread is the normalized Gram determinant divided by the product of the incident spreads. Dividing each vertex spread by the opposite spread gives the same ratio by cyclic invariance of the determinant."),
                Law("spherical-pythagorean-law", "rational_spherical_pythagorean", "Squared spherical Pythagorean law",
                    All(If(And(nonzero, right), Equiv(Call("kappa", b, c),
                        Mul(Call("kappa", a, b), Call("kappa", c, a)))),
                        ("a", integerQuaternions), ("b", integerQuaternions), ("c", integerQuaternions)),
                    "Square the right-angle dot identity and clear the nonzero norms. With nonzero incident spreads the right-angle identity is also equivalent to vertex spread one."),
                Law("alpha-sampling-drift", "alpha_sampling_norm_drift", "Exact norm drift at any rational sampling weight",
                    All(If(And(Call("Finite", weight), pureUnit),
                        Equiv(Sub(NormSq(sampled), one), Mul(Sub(one, Mul(two, weight)), NormSq(Sub(sampled, initial))))),
                        ("alpha", ratios), ("A", rationalQuaternions), ("x", rationalQuaternions)),
                    "The sample solves the implicit quaternion step by the conjugate and squared norm of the left factor. A pure generator acts by a skew-adjoint left multiplication, so the displacement is orthogonal to the weighted sample. Expanding that orthogonality gives the drift identity."),
                Law("midpoint-unit-norm", "midpoint_unit_norm", "The Cayley midpoint stays on the unit sphere",
                    All(If(pureUnit, Equiv(NormSq(midpoint), one)), ("A", rationalQuaternions), ("x", rationalQuaternions)),
                    "The drift multiplier vanishes when the sampling weight is one half."),
                Law("midpoint-fidelity", "midpoint_half_step_fidelity", "The two midpoint legs have equal fidelity",
                    All(If(pureUnit, Equiv(Call("kappa", liftedInitial, liftedMidpoint),
                        Call("kappa", liftedMidpoint, liftedFull))),
                        ("A", rationalQuaternions), ("x", rationalQuaternions)),
                    "Right multiplication of both nonzero numerator quaternions by the initial conjugate times the midpoint maps the first leg to the second up to a nonzero scaling. Projective fidelity is invariant under that common multiplication and scaling."))));
    }

    private static Formula NumberSet(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula NormSq(Formula value) => Call("normSq", value);
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula All(Formula body, params (string Name, Formula Type)[] variables) =>
        Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(FormulaIdentifier.Create(v.Name), v.Type))], body));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Equiv(Formula a, Formula b) => Call("Equivalent", a, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula If(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static DocumentBlock.Describe Law(string id, string selector, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Module}.{selector}"), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
