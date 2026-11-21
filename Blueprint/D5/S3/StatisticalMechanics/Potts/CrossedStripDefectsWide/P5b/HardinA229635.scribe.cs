using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b;

internal sealed class HardinA229635Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.";
    private const string Note = "D5/L/SpinModels/hardin2013a229635";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An order-27 recurrence for the literal width-six array count.", H("Hardin A229635"),
        Blocks(
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"), H("The order-27 recurrence"),
                StatementSource.FromAuthor(Disp(All("n", Call("Nat"), ImpliesFormula(AtMost(D(3, 1), V("n")), Equal(AsInt(Call("HardinA229637RowColumn.T", V("n"), D(6))), Sub(Add(Sub(Sub(Add(Add(Sub(Add(Add(Sub(Sub(Add(Sub(Sub(Add(Add(Sub(Sub(Add(Sub(Sub(Add(Add(Sub(Add(Sub(Mul(D(5, 4), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(1)), D(6)))), Mul(D(1, 1, 4, 0), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(2)), D(6))))), Mul(D(1, 1, 6, 3, 7), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(3)), D(6))))), Mul(D(5, 4, 2, 5, 2), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(4)), D(6))))), Mul(D(3, 3, 1, 9, 2), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(5)), D(6))))), Mul(D(6, 5, 8, 7, 5, 6), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(6)), D(6))))), Mul(D(1, 9, 2, 1, 2, 1, 2), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(7)), D(6))))), Mul(D(1, 5, 6, 6, 5, 1, 6), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(8)), D(6))))), Mul(D(1, 2, 8, 5, 0, 3, 7, 4), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(9)), D(6))))), Mul(D(7, 1, 0, 8, 6, 4, 4), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(1, 0)), D(6))))), Mul(D(3, 5, 0, 1, 8, 2, 3, 2), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(1, 1)), D(6))))), Mul(D(4, 3, 5, 0, 6, 0, 4, 6), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(1, 2)), D(6))))), Mul(D(3, 8, 5, 0, 0, 4, 4, 0), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(1, 3)), D(6))))), Mul(D(8, 5, 6, 8, 7, 8, 1, 2), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(1, 4)), D(6))))), Mul(D(2, 0, 0, 7, 9, 6), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(1, 5)), D(6))))), Mul(D(7, 5, 2, 4, 1, 3, 0, 8), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(1, 6)), D(6))))), Mul(D(3, 1, 6, 8, 5, 5, 9, 2), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(1, 7)), D(6))))), Mul(D(2, 5, 7, 6, 9, 2, 0, 0), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(1, 8)), D(6))))), Mul(D(2, 0, 8, 7, 8, 0, 6, 8), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(1, 9)), D(6))))), Mul(D(2, 1, 3, 3, 4, 8), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(2, 0)), D(6))))), Mul(D(3, 6, 5, 5, 7, 7, 0), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(2, 1)), D(6))))), Mul(D(6, 0, 8, 9, 1, 6), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(2, 2)), D(6))))), Mul(D(2, 3, 0, 9, 0, 4), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(2, 3)), D(6))))), Mul(D(6, 1, 7, 6, 1), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(2, 4)), D(6))))), Mul(D(2, 7, 9, 0), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(2, 5)), D(6))))), Mul(D(1, 8, 0, 0), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(2, 6)), D(6))))), Mul(D(1, 2, 5), AsInt(Call("HardinA229637RowColumn.T", Sub(V("n"), D(2, 7)), D(6)))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The literal count uses maps from the six-column rectangle to three available colours. Each in-range horizontal, diagonal or antidiagonal bond contributes one defect when its colours agree. The filter requires exactly two defects. The first occurrence of each used colour follows row-major order, including colourings that use only two colours."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229635"), ResolutionKind.Proved)))));

    private static Formula V(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Word(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] arguments)
        {
            Formula symbol = Seq(name.Split('.').SelectMany((part, index) =>
                index == 0 ? new[] { Word(part) } : new[] { Dot, Word(part) }).ToArray());
            return arguments.Length == 0 ? symbol : App(symbol, arguments);
        }
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula AtMost(Formula left, Formula right) => Seq(left, Sp, Le, Sp, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula ImpliesFormula(Formula left, Formula right) => Seq(Paren(left), Sp, Implies, Sp, Paren(right));
    private static Formula AsInt(Formula value) => Paren(Seq(value, Colon, Sp, Int));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Paren(body));
}
