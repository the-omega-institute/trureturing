using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class OriginalCosineDeterminantInterfaceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original six-cosh cosine numerator and determinant identity for one target edge.",
        H("Original cosine determinant interface"),
        Blocks(
            Paragraph(Text(
                "For ordered local edge cosh coordinates (r,a,b,o,c,d), gram is the "
                + "signed four-by-four Gram matrix. D1 and D2 are the two target-edge "
                + "quadratic factors, and N is the original cosine numerator.")),
            Node("original-cosine-interface", "Original cosine determinant interface",
                "original_cosine_interface", StatementInterface(),
                "The theorem packages the positive target-edge factors, the exact "
                + "determinant identity, and the resulting strict sign criterion in "
                + "one algebraic interface."))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(F.Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);

    private static Formula StatementInterface()
    {
        var args = Vars();
        var hypotheses = new Formula[]
        {
            Lt(F.D(1), args[0]), Lt(F.D(1), args[1]), Lt(F.D(1), args[2]),
            Lt(F.D(1), args[3]), Lt(F.D(1), args[4]), Lt(F.D(1), args[5])
        };
        var positive = And(Lt(F.D(0), Call("D1", args[0], args[1], args[5])),
            Lt(F.D(0), Call("D2", args[0], args[2], args[4])));
        var identity = Eq(
            Sub(Mul(Call("D1", args[0], args[1], args[5]),
                Call("D2", args[0], args[2], args[4])),
                Pow(Call("N", args), (byte)2)),
            Mul(Neg(Sub(Pow(args[0], (byte)2), F.D(1))),
                Call("det", Call("gram", args))));
        var criterion = Iff(Lt(Call("det", Call("gram", args)), F.D(0)),
                Lt(F.D(0), Sub(Mul(Call("D1", args[0], args[1], args[5]),
                    Call("D2", args[0], args[2], args[4])), Pow(Call("N", args), (byte)2))));
        return Implies(And(hypotheses), And(positive, identity, criterion));
    }

    private static Formula[] Vars() => new[]
    {
        F.Id("r"), F.Id("a"), F.Id("b"), F.Id("o"), F.Id("c"), F.Id("d")
    };

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Iff(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(params Formula[] xs) =>
        xs.Aggregate((x, y) => new Formula.Logic(x, FormulaLogicOperator.And, y));
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Pow(Formula x, byte n) =>
        new Formula.Power(x, F.D(n));
    private static Formula Neg(Formula x) =>
        new Formula.Negate(x);
}
