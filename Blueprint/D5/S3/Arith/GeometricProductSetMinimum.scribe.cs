using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GeometricProductSetMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GeometricProductSetMinimum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite set of positive real numbers with the least possible number of products "
            + "is a geometric progression.",
        H("Minimum Product Sets of Positive Reals"),
        Blocks(
            Node("positive-product-lower-bound", "The ordered-product lower bound",
                "product_card_lower_bound", LowerBoundFormula(),
                "Let A be a nonempty finite set of positive real numbers, of size m. "
                    + "Then AA has at least 2m-1 elements. In increasing coordinates "
                    + "x_0<...<x_(m-1), the products along an increasing grid path from "
                    + "(0,0) to (m-1,m-1) are strictly increasing. Such a path has "
                    + "2m-1 vertices."),
            Node("minimal-product-geometric", "Equality forces constant consecutive ratios",
                "eq_geometric_of_product_card", GeometricFormula(),
                "Suppose A contains at least two positive real numbers and AA has "
                    + "at most 2|A|-1 elements. The lower bound gives equality. Every increasing product-grid path therefore "
                    + "enumerates AA in increasing order. Compare the path that first follows "
                    + "row zero with the path that changes from row zero to row one at "
                    + "column j-1. Their entries at position j agree, giving "
                    + "x_0 x_j=x_1 x_(j-1). Thus x_j=x_0(x_1/x_0)^j for every index j, "
                    + "and x_1/x_0>1.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Less(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula AtMost(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Card(Formula x) => Call("card", x);
    private static Formula Product(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Minimum(Formula a) =>
        new Formula.Binary(Product(D(2), Card(a)), FormulaBinaryOperator.Subtract, D(1));
    private static Formula Positive(Formula a) =>
        All("a", Real(), Imp(Call("Member", F.Id("a"), a), Less(D(0), F.Id("a"))));

    private static Formula LowerBoundFormula()
    {
        var a = F.Id("A");
        return Disp(All("A", Call("Finset", Real()),
            Imp(Positive(a), Imp(Call("Nonempty", a),
                AtMost(Minimum(a), Card(Product(a, a)))))));
    }

    private static Formula GeometricFormula()
    {
        var a = F.Id("A"); var b = F.Id("b"); var r = F.Id("r"); var i = F.Id("i");
        var sequence = new Formula.SetBuilder(Product(b, new Formula.Power(r, i)),
            i, Call("range", Card(a)));
        return Disp(All("A", Call("Finset", Real()),
            Imp(Positive(a), Imp(AtMost(D(2), Card(a)),
                Imp(AtMost(Card(Product(a, a)), Minimum(a)),
                    Exists("b", Real(), Exists("r", Real(),
                        And(Less(D(0), b), And(Less(D(1), r),
                            Eq(a, sequence))))))))));
    }
}
