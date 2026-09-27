using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class IntegerIndexBinomialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binomial coefficient whose lower index is an integer is read as zero when that index is negative and as the ordinary binomial coefficient otherwise.",
        H("The binomial coefficient with an integer lower index"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integer-index-binomial"),
                DeclarationHandle.Create("D5/S0/Conventions/IntegerIndexBinomial.binom"),
                H("The binomial coefficient C(m, j) for an integer j"),
                StatementSource.FromAuthor(BinomFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural number m and an integer j, binom(m, j) is zero when j is negative and the binomial coefficient C(m, j) otherwise, so it also vanishes when j exceeds m. Sums of binomial coefficients over integer ranges use it to drop the terms with a negative lower index."))),
                DescribeRole.Definition)),
        []));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula BinomFormula()
    {
        Formula m = F.Id("m"), j = F.Id("j");
        Formula value = Seq(Operatorname, Grp(F.Id("if")), Sp, Less(j, D(0)), Sp,
            Operatorname, Grp(F.Id("then")), Sp, D(0), Sp,
            Operatorname, Grp(F.Id("else")), Sp, Call("choose", m, Call("toNat", j)));
        return Disp(Equal(Call("binom", m, j), value));
    }
}
