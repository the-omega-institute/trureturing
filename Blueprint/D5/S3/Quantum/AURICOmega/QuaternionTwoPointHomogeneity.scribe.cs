using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class QuaternionTwoPointHomogeneityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/QuaternionTwoPointHomogeneity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Left-right translations by unit quaternions preserve the reading of the quaternion comparison model and act transitively on pairs with equal reading.",
        H("Two-point homogeneity of the quaternion comparison model"),
        Blocks(
            Node("kappa-mul-mul", "kappa_mul_mul", "The reading is invariant under left-right translation",
                StatementSource.FromAuthor(KappaMulMulFormula()), DescribeRole.Lemma,
                "In the quaternion comparison model the transfer is tri a b c = a * b^-1 * c, so with the unit quaternion 1 as middle argument the products p * x and x * q are the transfers tri p 1 x and tri x 1 q. "
                    + "The reading is invariant under a transfer on the left and under a transfer on the right, so it is unchanged when both arguments are first multiplied by p on the left and then by q on the right. "
                    + "Equivalently, z -> p * z * q is a linear isometry of the quaternions, and the reading (1 + <x, y>) / 2 depends only on the real inner product."),
            Node("exists-unitary-mul-eq", "exists_unitary_mul_eq_mul", "Unit quaternions with equal real part are conjugate",
                StatementSource.FromAuthor(ConjugateFormula()), DescribeRole.Lemma,
                "The second unit quaternion, written a' in the source, is written b in the formula. "
                    + "Two unit quaternions a and b have the same norm one, so when they also have the same real part their imaginary parts have the same length. "
                    + "A nonzero quaternion w with w * a = b * w then exists: with imaginary parts u of a and v of b, the quaternion |u|^2 - v * u works unless v = -u, and otherwise any nonzero imaginary quaternion orthogonal to u works. "
                    + "Dividing w by its norm gives a unit quaternion c with c * a = b * c."),
            Node("exists-mul-mul-eq", "exists_mul_mul_eq_of_kappa_eq", "Pairs with equal reading are related by a left-right translation",
                StatementSource.FromAuthor(TwoPointFormula()), DescribeRole.Theorem,
                "The second pair is written u and v in the formula. "
                    + "By the invariance above with p = x^-1 and q = 1, the reading of x and y equals the reading of 1 and x^-1 * y, which is (1 + re (x^-1 * y)) / 2. "
                    + "Equal readings therefore give the unit quaternions a = x^-1 * y and a' = u^-1 * v the same real part; they also have the same norm one. "
                    + "By the conjugacy of unit quaternions with equal real part, there is a unit quaternion c with c * a = a' * c. "
                    + "The translation with p = u * c * x^-1 and q = c^-1 then sends x to u, and it sends y to u * c * a * c^-1 = u * a' = v."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("quaternion-two-point-homogeneity-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);
    private static Formula ExistsMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Quaternions => Seq(Mathbb, Grp(F.Id("H")), OpenBracket, Reals, CloseBracket);
    private static Formula Units => Call("unitary", Quaternions);
    private static Formula Model => Seq(Operatorname, Grp(F.Id("quaternionModel")));
    private static Formula Kappa(Formula x, Formula y) => Call("kappa", Model, x, y);
    private static Formula Translate(Formula z) => Mul(Mul(F.Id("p"), z), F.Id("q"));

    private static Formula KappaMulMulFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y");
        return Disp(ForAllMany(Units,
            Equal(Kappa(Translate(x), Translate(y)), Kappa(x, y)), "p", "q", "x", "y"));
    }

    private static Formula ConjugateFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        return Disp(ForAllMany(Units,
            Logic(Equal(Call("re", a), Call("re", b)), FormulaLogicOperator.Implies,
                ExistsMany(Units, Equal(Mul(c, a), Mul(b, c)), "c")),
            "a", "b"));
    }

    private static Formula TwoPointFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), u = F.Id("u"), v = F.Id("v");
        return Disp(ForAllMany(Units,
            Logic(Equal(Kappa(x, y), Kappa(u, v)), FormulaLogicOperator.Implies,
                ExistsMany(Units,
                    Logic(Equal(Translate(x), u), FormulaLogicOperator.And, Equal(Translate(y), v)),
                    "p", "q")),
            "x", "y", "u", "v"));
    }
}
