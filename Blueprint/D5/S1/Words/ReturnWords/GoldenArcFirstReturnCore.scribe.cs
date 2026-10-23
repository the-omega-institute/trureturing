using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.ReturnWords;

internal sealed class GoldenArcFirstReturnCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fractional phases add their forward displacement when the sum stays below one.",
        H("Forward displacement without wrapping"),
        Blocks(Describe.Lean(
            DescribeId.Create("fract-add-displacement-of-no-wrap"),
            DeclarationHandle.Create("D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.fract_add_displacement_of_no_wrap"),
            H("Fractional addition without wrapping"),
            StatementSource.FromAuthor(NoWrapFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For real alpha and x and a natural k, if x is nonnegative and x plus forwardDisplacement alpha k is less than one, the fractional part of x plus k times alpha equals that sum."))),
            DescribeRole.Theorem)), []));

    private static Formula NoWrapFormula()
    {
        var alpha = F.Id("alpha");
        var x = F.Id("x");
        var k = F.Id("k");
        var real = new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
        var nat = new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
        var displacement = Call("forwardDisplacement", alpha, k);
        var sum = new Formula.Binary(x, FormulaBinaryOperator.Add, displacement);
        var cast = Parenthesized(Seq(Dotted("Nat", "cast", k), Sp, Colon, Sp, real));
        var product = new Formula.Binary(cast, FormulaBinaryOperator.Multiply, alpha);
        var argument = new Formula.Binary(x, FormulaBinaryOperator.Add, product);
        var conclusion = new Formula.Relation(Dotted("Int", "fract", argument),
            FormulaRelationOperator.Equal, sum);
        var nonnegative = new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, x);
        var nowrap = new Formula.Relation(sum, FormulaRelationOperator.LessThan, D(1));
        return Disp(Bind("alpha", real, Bind("x", real, Bind("k", nat,
            Seq(Parenthesized(nonnegative), Sp, Rightarrow, Sp,
                Parenthesized(nowrap), Sp, Rightarrow, Sp, conclusion)))));
    }

    private static Formula Dotted(string owner, string name, Formula argument) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner)), Dot,
            Operatorname, Grp(F.Id(name))), [argument]);

    private static Formula Bind(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
