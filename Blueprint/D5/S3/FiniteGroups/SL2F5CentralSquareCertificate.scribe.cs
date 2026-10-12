using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class SL2F5CentralSquareCertificateDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/FiniteGroups/SL2F5CentralSquareCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite SL2 over F5 has only the two square roots of identity, with the explicit transport matrices.",
        H("The finite SL2(F5) central-square certificate"),
        Blocks(
            Paragraph(Text(
                "Work over the five-element field ZMod(5) and write M(a,b,c,d) for the "
                    + "two-by-two matrix with those four entries. The first clause enumerates "
                    + "all determinant-one matrices and checks the square-root alternatives "
                    + "I and -I. The remaining clauses check the explicit matrices used in "
                    + "the low and high return words.")),
            Paragraph(Text(
                "This is a finite certificate for the central-involution obstruction in the "
                    + "SL2(F5) example. It does not formalize the general face-transport theorem, "
                    + "the projective quotient PSL2(F5), or the geometric realization of the "
                    + "resulting twelve-degree and nine-degree edges.")),
            Theorem("sl2f5_central_square_certificate", "sl2f5-central-square-certificate",
                "Finite central-square and return-word certificate", CertificateFormula(),
                "The universal clause is a bounded kernel computation over all four entries in "
                    + "ZMod(5). The explicit determinant, inverse, matrix, and power identities "
                    + "are checked in the same computation."))));

    private static DocumentBlock Theorem(string declaration, string id, string title,
        Formula formula, string prose) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Root + declaration), H(title),
        StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula baseValue, int exponent) =>
        F.Seq(baseValue, Caret, Grp(Number(exponent)));

    private static Formula Number(int value) =>
        D(value.ToString(System.Globalization.CultureInfo.InvariantCulture)
            .Select(character => (byte)(character - '0')).ToArray());

    private static Formula ZMod5() => Call("ZMod", Number(5));
    private static Formula Matrix(Formula a, Formula b, Formula c, Formula d) =>
        Call("M", a, b, c, d);

    private static Formula CertificateFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), d = F.Id("d");
        Formula m = Matrix(a, b, c, d);
        Formula one = Number(1);
        Formula identity = F.Id("I");
        Formula negativeIdentity = F.Seq(Minus, Sp, identity);
        Formula rootClause = Implies(
            Eq(Subtract(Multiply(a, d), Multiply(b, c)), one),
            Implies(Eq(Multiply(m, m), identity),
                Or(Eq(m, identity), Eq(m, negativeIdentity))));
        Formula universal = All("a", ZMod5(),
            All("b", ZMod5(), All("c", ZMod5(), All("d", ZMod5(), rootClause))));
        Formula ellMatrix = Matrix(Number(0), Number(1), Number(4), Number(0));
        Formula hMatrix = Matrix(Number(3), Number(3), Number(4), Number(1));
        Formula explicitFormula = And(
            Ne(negativeIdentity, identity),
            Eq(Call("det", F.Id("u")), one),
            Eq(Call("det", F.Id("v")), one),
            Eq(Call("det", F.Id("vInverse")), one),
            Eq(Multiply(F.Id("vInverse"), F.Id("v")), identity),
            Eq(Multiply(F.Id("v"), F.Id("vInverse")), identity),
            Eq(F.Id("ell"), ellMatrix),
            Eq(F.Id("h"), hMatrix),
            Eq(Power(F.Id("ell"), 2), negativeIdentity),
            Eq(Power(F.Id("h"), 3), identity),
            Eq(Power(F.Id("u"), 3), negativeIdentity),
            Eq(Power(F.Id("v"), 5), identity));
        return And(universal, explicitFormula);
    }
}
