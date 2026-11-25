using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaComposeAndWitnessesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses";

    public DocumentDefinition Create()
    {
        Formula n = F.Id("N"), k = F.Id("k"), f = F.Id("f"), g = F.Id("g");
        Formula a = F.Id("A"), b = F.Id("B"), s = F.Id("gSpin");
        Formula nat = F.Id("OmegaNat"), jet = F.Id("JetSeq"), mat = F.Id("MatTwo");
        Formula angle = Call("scale", D(2), F.Id("Atan"));
        Formula cos = Call("compose", F.Id("Cos"), angle);
        Formula sin = Call("compose", F.Id("Sin"), angle);
        Formula rule = F.Id("pOmega"), start = D(1, 3, 1, 0, 7, 2), end = D(2, 2), count = D(1, 5);
        Formula ph = F.Id("pHalf"), qh = F.Id("qHalf"), o = F.Id("o");

        Formula identity = F.Id("identity");
        Formula Beat(byte i) => Call("pow", s, D(i));
        Formula Signed(byte i, Formula point) => Call("SignedEq", Beat(i), point);
        Formula Fidelity(byte i, byte value) => Equiv(Call("kappaSpin", identity, Beat(i)), D(value));
        Formula orbit = And(Signed(1, s),
            And(Signed(2, F.Id("second")),
                And(Signed(3, F.Id("antipode")),
                    And(Signed(4, F.Id("fourth")),
                        And(Signed(5, F.Id("fifth")),
                            And(Signed(6, identity), And(Fidelity(3, 0), Fidelity(6, 1))))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Formal power-series substitution and exact algebraic, geometric and arithmetic identities.",
            H("Formal composition, Cayley trigonometry and concrete witnesses"),
            Blocks(
                Law("deriv_compose_equivAt", "Formal chain rule",
                    Disp(All(If(And(And(Call("Finite", f), Call("Finite", g)), Equiv(Call("g", D(0)), D(0))),
                        Call("EquivalentAt", n, Call("deriv", Call("compose", f, g)),
                            Mul(Call("compose", Call("deriv", f), g), Call("deriv", g)))),
                        ("N", nat), ("f", jet), ("g", jet))),
                    "Every coefficient is a finite rational. With zero inner constant coefficient, powers of the inner stream vanish below their exponent. Leibniz's rule differentiates each finite substitution and the discarded terms contribute zero through the stated degree."),
                Law("cos_two_atan_eq_cayley", "Cosine of twice the formal arctangent",
                    Disp(All(Call("EquivalentAt", n, cos, F.Id("CayleyCos")), ("N", nat))),
                    "The formal chain rule and the arctangent equation give the cosine equation of the coupled Cayley system. The constant coefficient is one."),
                Law("sin_two_atan_eq_cayley", "Sine of twice the formal arctangent",
                    Disp(All(Call("EquivalentAt", n, sin, F.Id("CayleySin")), ("N", nat))),
                    "Multiplying the differentiated sine composition by one plus the square of the indeterminate gives twice the cosine composition. The zero sine constant and the unit cosine constant determine both streams at each truncation."),
                Law("mat2_det_mul", "Multiplicativity of the integer determinant",
                    Disp(All(Equal(Call("det", Mul(a, b)), Mul(Call("det", a), Call("det", b))),
                        ("A", mat), ("B", mat))),
                    "The identity holds for all two by two integer matrices, including singular matrices."),
                Law("phalf_qhalf_noncommutative", "Noncommuting ternion rays",
                    Disp(Seq(Neg, Sp, Call("RayEquiv", Call("triad", ph, o, qh), Call("triad", qh, o, ph)))),
                    "The middle point is the identity quaternion. The two products have the same nonzero real coordinate and opposite last coordinates, so they cannot represent the same ray."),
                Law("g120_spin_six_beat_orbit", "The signed six-beat orbit",
                    Disp(orbit),
                    "The generator has homogeneous coordinates (1, 1, 1, 1) with denominator two. The second, fourth and fifth beats have numerators (-1, 1, 1, 1), (-1, -1, -1, -1) and (1, -1, -1, -1), each with denominator two. Beat three is the radius-one antipode and beat six is the radius-one identity. The corresponding accumulated rotation angles are 360 and 720 degrees."),
                Law("orthogonal_triad_excess_quarter", "Quarter Gram determinant",
                    Disp(Equiv(Call("detGram", o, ph, qh), new Formula.Fraction(D(1), D(4)))),
                    "The three vectors are the identity coordinate vector and the sums of that vector with the first and second imaginary coordinate vectors. Their normalized Gram determinant is one quarter."),
                Law("p_omega_halts_at_22", "Exact first halt of the four-rule FRACTRAN program",
                    Disp(And(Call("Follows", rule, F.Id("trace"), start),
                        And(Equal(Call("run", rule, count, start), end),
                            And(Call("Halts", rule, end),
                                All(If(Rel(k, FormulaRelationOperator.LessThan, count),
                                    Seq(Neg, Sp, Call("Halts", rule, Call("run", rule, k, start)))),
                                    ("k", nat)))))),
                    "The rules in priority order are 11/49, 7/25, 5/9 and 3/4. After 131072 the states are 98304, 73728, 40960, 30720, 23040, 12800, 3584, 2688, 2016, 1120, 840, 630, 350, 98 and 22. Every listed transition fires the first enabled rule. All four guards fail at 22."))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(Formula body, params (string Name, Formula Domain)[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(variable => new Formula.BoundVariable(
                FormulaIdentifier.Create(variable.Name), variable.Domain))], body);

    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Equiv(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equivalent, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula If(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static DocumentBlock.Describe Law(string selector, string title, Formula statement, string note) =>
        Describe.Lean(DescribeId.Create(selector.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create($"{Module}.{selector}"),
            H(title), StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(note))), DescribeRole.Theorem);
}
