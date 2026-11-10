using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ActualHeightFourteenSectorDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var n = DefinitionDsl.Id("N");
        var c = DefinitionDsl.Id("c");
        var p = DefinitionDsl.Id("p");
        var u = DefinitionDsl.Id("u");
        var real = Seq(Mathbb, Grp(FormulaDsl.Id("R")));
        var fin = Call("Fin", n);
        var nonnegative = All("j", fin,
            Le(new Formula.Number(0), Call("c", DefinitionDsl.Id("j"))));
        var conclusion = Call("StrictAntiOn",
            Seq(Open, Open, u, Colon, real, Close, Sp, Mapsto, Sp, Call("weight", c, u, p), Close),
            Call("Ioi", Call("threshold", n)));
        return All("N", Seq(Mathbb, Grp(FormulaDsl.Id("N"))),
            All("c", new Formula.TypeArrow(fin, real), All("p", real,
                Then(new Formula.Relation(new Formula.Number(0), FormulaRelationOperator.LessThan, n),
                    Then(nonnegative, Then(Le(new Formula.Number(0), p),
                        Then(Le(p, new Formula.Fraction(new Formula.Number(1), new Formula.Number(4))),
                            conclusion)))))));
    }

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Then(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic finite reciprocal-product sector calculus",
        H("Generic Finite Reciprocal-Product Sector Calculus"),
        Blocks(Describe.Lean(
            DescribeId.Create("actualheightfourteensector"),
            DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualHeightFourteenSector.strictAntiOn_weight_u"),
            H("Strict decrease in the height parameter"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every positive finite index size, every nonnegative shift family, and every " +
                "p in the closed interval [0,1/4], the real part of the reciprocal product is " +
                "strictly decreasing in u above the explicit threshold 4*(N+1)^2/pi^2. " +
                "The proof supplies the reusable polar-angle positivity, u- and p-derivative " +
                "signs, the endpoint continuity argument, and the signed-imaginary-part reduction. " +
                "No six-pole constants or zeta data occur in this generic source."))),
            DescribeRole.Theorem))));
}
