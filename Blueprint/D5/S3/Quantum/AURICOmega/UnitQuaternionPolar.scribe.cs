using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class UnitQuaternionPolarDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/UnitQuaternionPolar.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every unit quaternion is cos t + sin t * n with t = arccos of its real part and n a unit imaginary quaternion, and powers of such quaternions obey de Moivre's formula.",
        H("Polar form of unit quaternions and de Moivre's formula"),
        Blocks(
            Node("polar", "exists_eq_cos_arccos_add_sin_smul", "Polar form of a unit quaternion",
                StatementSource.FromAuthor(PolarFormula()), DescribeRole.Theorem,
                "Let q be a quaternion of norm one and put t = arccos (re q). "
                    + "Since the squared norm of q is the sum of the squares of its four coordinates, the imaginary part of q has squared norm 1 - (re q)^2, so |re q| <= 1. "
                    + "Hence cos t = re q, and sin t = sqrt (1 - (re q)^2) is the norm of the imaginary part of q. "
                    + "If the imaginary part of q is nonzero, n is the imaginary part divided by its norm; it has real part zero and norm one, and q = re q + im q = cos t + sin t * n. "
                    + "If the imaginary part of q is zero, then sin t = 0 and q = cos t, and any unit imaginary quaternion, for instance the quaternion unit i, serves as n."),
            Node("de-moivre", "cos_add_sin_smul_pow", "De Moivre's formula for a unit imaginary quaternion",
                StatementSource.FromAuthor(DeMoivreFormula()), DescribeRole.Lemma,
                "Let n be a quaternion with real part zero and norm one. "
                    + "A quaternion with real part zero squares to minus its squared norm, so n * n = -1. "
                    + "Hence there is a homomorphism of real algebras from the complex numbers to the quaternions that sends the imaginary unit i to n; it sends x + y i to x + y * n for real x and y. "
                    + "For every real angle t it sends exp (t i) = cos t + (sin t) i to cos t + sin t * n. "
                    + "For every natural number k, exp ((k * t) i) = exp (t i)^k, and the homomorphism preserves powers, "
                    + "so (cos t + sin t * n)^k is the image of exp ((k * t) i), which is cos (k * t) + sin (k * t) * n."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("unit-quaternion-polar-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Quaternions => Seq(Mathbb, Grp(F.Id("H")), OpenBracket, Reals, CloseBracket);

    /// <summary>The quaternion cos(t) + sin(t) n for a real angle t and a quaternion n.</summary>
    private static Formula CosAddSin(Formula angle, Formula axis) =>
        Add(Call("cos", angle), Mul(Call("sin", angle), axis));

    private static Formula PolarFormula()
    {
        Formula q = F.Id("q"), n = F.Id("n");
        Formula angle = Call("arccos", Call("re", q));
        return Disp(ForAll("q", Quaternions, Implies(Equal(new Formula.Norm(q), D(1)),
            Exists("n", Quaternions, And(Equal(Call("re", n), D(0)),
                And(Equal(new Formula.Norm(n), D(1)), Equal(q, CosAddSin(angle, n))))))));
    }

    private static Formula DeMoivreFormula()
    {
        Formula n = F.Id("n"), t = F.Id("t"), k = F.Id("k");
        Formula power = new Formula.Power(CosAddSin(t, n), k);
        return Disp(ForAll("n", Quaternions, Implies(Equal(Call("re", n), D(0)),
            Implies(Equal(new Formula.Norm(n), D(1)),
                ForAll("t", Reals, ForAll("k", Naturals,
                    Equal(power, CosAddSin(Mul(k, t), n))))))));
    }
}
