using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b;

internal sealed class HardinA229635ResidualDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual.";
    private const string Note = "D5/L/SpinModels/hardin2013a229635";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A scalar readout and Cayley–Hamilton close the signed residual.", H("Symbolic recurrence closure"),
        Blocks(
            Describe.Lean(DescribeId.Create("coefficients"),
                DeclarationHandle.Create(Prefix + "coefficients"), H("The signed lag vector"),
                StatementSource.FromAuthor(Disp(Equal(Call("coefficients"), Vector(D(5, 4), Seq(Minus, D(1, 1, 4, 0)), D(1, 1, 6, 3, 7), Seq(Minus, D(5, 4, 2, 5, 2)), D(3, 3, 1, 9, 2), D(6, 5, 8, 7, 5, 6), Seq(Minus, D(1, 9, 2, 1, 2, 1, 2)), Seq(Minus, D(1, 5, 6, 6, 5, 1, 6)), D(1, 2, 8, 5, 0, 3, 7, 4), Seq(Minus, D(7, 1, 0, 8, 6, 4, 4)), Seq(Minus, D(3, 5, 0, 1, 8, 2, 3, 2)), D(4, 3, 5, 0, 6, 0, 4, 6), D(3, 8, 5, 0, 0, 4, 4, 0), Seq(Minus, D(8, 5, 6, 8, 7, 8, 1, 2)), Seq(Minus, D(2, 0, 0, 7, 9, 6)), D(7, 5, 2, 4, 1, 3, 0, 8), Seq(Minus, D(3, 1, 6, 8, 5, 5, 9, 2)), Seq(Minus, D(2, 5, 7, 6, 9, 2, 0, 0)), D(2, 0, 8, 7, 8, 0, 6, 8), D(2, 1, 3, 3, 4, 8), Seq(Minus, D(3, 6, 5, 5, 7, 7, 0)), D(6, 0, 8, 9, 1, 6), D(2, 3, 0, 9, 0, 4), Seq(Minus, D(6, 1, 7, 6, 1)), Seq(Minus, D(2, 7, 9, 0)), D(1, 8, 0, 0), Seq(Minus, D(1, 2, 5)))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Index zero multiplies the count at lag one. Index twenty-six multiplies the count at lag twenty-seven."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("scalar"),
                DeclarationHandle.Create(Prefix + "scalar"), H("Scalar matrix readout"),
                StatementSource.FromAuthor(Disp(All("D", Call("Nat"), All("M", Call("Matrix", Call("Fin", V("D")), Call("Fin", V("D")), Call("Int")), All("v", Arrow(Call("Fin", V("D")), Call("Int")), All("e", Arrow(Call("Fin", V("D")), Call("Int")), All("k", Call("Nat"), Equal(Call("scalar", V("M"), V("v"), V("e"), V("k")), Call("dotProduct", V("v"), Call("Matrix.mulVec", Power(V("M"), V("k")), V("e"))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The row and column vectors use the same dimension as the integer transition matrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("residual"),
                DeclarationHandle.Create(Prefix + "residual"), H("Signed scalar residual"),
                StatementSource.FromAuthor(Disp(All("D", Call("Nat"), All("M", Call("Matrix", Call("Fin", V("D")), Call("Fin", V("D")), Call("Int")), All("v", Arrow(Call("Fin", V("D")), Call("Int")), All("e", Arrow(Call("Fin", V("D")), Call("Int")), All("t", Call("Nat"), Equal(Call("residual", V("M"), V("v"), V("e"), V("t")), Sub(Call("scalar", V("M"), V("v"), V("e"), Add(D(3, 0), V("t"))), SumOver("j", Call("Fin", D(2, 7)), Mul(Call("coefficients", V("j")), Call("scalar", V("M"), V("v"), V("e"), Add(Sub(D(2, 9), Call("Fin.val", V("j"))), V("t")))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The exponent is one less than the strip length. The scalar residual at offset zero corresponds to length thirty-one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("residual-vector"),
                DeclarationHandle.Create(Prefix + "residualVector"), H("Signed row-vector residual"),
                StatementSource.FromAuthor(Disp(All("D", Call("Nat"), All("M", Call("Matrix", Call("Fin", V("D")), Call("Fin", V("D")), Call("Int")), All("v", Arrow(Call("Fin", V("D")), Call("Int")), Equal(Call("residualVector", V("M"), V("v")), Sub(Call("forward", V("M"), V("v"), D(3, 0)), SumOver("j", Call("Fin", D(2, 7)), Scale(Call("coefficients", V("j")), Call("forward", V("M"), V("v"), Sub(D(2, 9), Call("Fin.val", V("j"))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The row-vector residual uses the initial vector and the transfer powers before applying the terminal readout."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("residual-as-power"),
                DeclarationHandle.Create(Prefix + "residual_as_power"), H("Transport of the residual"),
                StatementSource.FromAuthor(Disp(All("D", Call("Nat"), All("M", Call("Matrix", Call("Fin", V("D")), Call("Fin", V("D")), Call("Int")), All("v", Arrow(Call("Fin", V("D")), Call("Int")), All("e", Arrow(Call("Fin", V("D")), Call("Int")), All("t", Call("Nat"), Equal(Call("residual", V("M"), V("v"), V("e"), V("t")), Call("dotProduct", Call("residualVector", V("M"), V("v")), Call("Matrix.mulVec", Power(V("M"), V("t")), V("e"))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each lagged term has the same additional power. Distributivity moves that power after the signed sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("residual-zero"),
                DeclarationHandle.Create(Prefix + "residual_zero"), H("Closure by the characteristic polynomial"),
                StatementSource.FromAuthor(Disp(All("D", Call("Nat"), All("M", Call("Matrix", Call("Fin", V("D")), Call("Fin", V("D")), Call("Int")), All("v", Arrow(Call("Fin", V("D")), Call("Int")), All("e", Arrow(Call("Fin", V("D")), Call("Int")), ImpliesFormula(All("t", Call("Nat"), ImpliesFormula(Less(V("t"), V("D")), Equal(Call("residual", V("M"), V("v"), V("e"), V("t")), D(0)))), All("t", Call("Nat"), Equal(Call("residual", V("M"), V("v"), V("e"), V("t")), D(0)))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Cayley–Hamilton gives a monic relation of degree equal to the matrix dimension. Applying the scalar readout yields a recurrence for the residual. A zero prefix of that dimension forces every residual to vanish."))), DescribeRole.Theorem))));

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
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula ImpliesFormula(Formula left, Formula right) => Seq(Paren(left), Sp, Implies, Sp, Paren(right));
    private static Formula Arrow(Formula left, Formula right) => Seq(Paren(left), Sp, To, Sp, Paren(right));
    private static Formula Power(Formula value, Formula exponent) => Seq(Paren(value), Caret, Grp(exponent));
    private static Formula Scale(Formula value, Formula vector) => Seq(Paren(value), Sp, Cdot, Sp, Paren(vector));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Paren(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
            Seq(Sum, Underscore, Grp(V(name), Colon, Sp, type), Sp, Paren(body));
    private static Formula Vector(params Formula[] items) => Seq(
            new Formula[] { Bang, OpenBracket }.Concat(items.SelectMany((item, index) =>
                index == 0 ? new[] { item } : new[] { Comma, Sp, item }))
                .Append(CloseBracket).ToArray());
}
