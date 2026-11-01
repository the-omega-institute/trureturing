using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class BallotCoefficientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ballot coefficients are differences of adjacent binomial coefficients.",
        H("Ballot coefficients"),
        Blocks(Describe.Lean(
            DescribeId.Create("ballot-coefficient"),
            DeclarationHandle.Create("D5/S0/Conventions/BallotCoefficient.ballotE"),
            H("The integer ballot coefficient"),
            StatementSource.FromAuthor(Definition()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The upper binomial index uses natural subtraction; the lower indices "
                + "use integer subtraction. IntegerIndexBinomial.binom is zero at a "
                + "negative lower index. Thus ballotE(r,1)=1, including r=0. "
                + "The Shankar closed form uses ballotE(r,b), and the degree-j "
                + "coefficient of the terminating Luschny array uses ballotE(k,j+1)."))),
            DescribeRole.Definition))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Definition()
    {
        Formula r = F.Id("r"), b = F.Id("b");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula upper = Sub(new Formula.Binary(r, FormulaBinaryOperator.Add, b), D(1));
        Formula cast = Seq(Open, b, Colon, Sp, integer, Close);
        return Disp(Seq(
            Forall, Sp, r, Colon, Sp, natural, Comma, Sp,
            Forall, Sp, b, Colon, Sp, natural, Comma, Sp,
            Call("ballotE", r, b), Sp, Eq, Sp,
            Sub(Call("binom", upper, Sub(cast, D(1))),
                Call("binom", upper, Sub(cast, D(2))))));
    }
}
