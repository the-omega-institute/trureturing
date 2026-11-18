using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.FactorWidth;

internal sealed class FiveCyclePosteriorFactorWidthDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/FactorWidth/FiveCyclePosteriorFactorWidth";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational five-cycle posterior moment belongs to the complex width-three cone and lies outside the width-two cone.",
        H("Factor width of the five-cycle posterior moment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("five-cycle-moment"),
                DeclarationHandle.Create(Owner + ".moment"),
                H("The cycle moment at the uniform prior"),
                StatementSource.FromAuthor(MomentDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The identity matrix has entries delta(i,j). The adjacency matrix W has entry one if "
                    + "i and j differ by one modulo five and entry zero otherwise."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("five-cycle-factor-width"),
                DeclarationHandle.Create(Owner + ".cycle_moment_width_exactly_three"),
                H("Exact complex factor width"),
                StatementSource.FromAuthor(WidthStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take the five cyclic shifts of (1,2,1,0,0) and (2,2,0,-1,0). Scale these "
                        + "columns by the square roots of 12/1100 and 3/1100. Add the five coordinate "
                        + "columns scaled by the square root of 1/1100. The two shifted families cancel "
                        + "on every nonedge and add up to 3/55 on every edge. The coordinate columns "
                        + "complete the diagonal to 5/55.")),
                    Paragraph(Text(
                        "Every complex outer product of a vector with at most two nonzero entries has "
                        + "a sum of diagonal entries at least twice the sum of real edge entries. A "
                        + "single vector with both ends of one edge in its support gives the squared "
                        + "norm of their difference after subtraction. The displayed cycle moment "
                        + "violates the resulting inequality by 5/55."))),
                DescribeRole.Theorem))));

    private static Formula MomentDefinition()
    {
        var i = F.Id("i");
        var j = F.Id("j");
        var indices = Seq(i, Comma, Sp, j);
        var range = Seq(Operatorname, Grp(F.Id("Fin")), Open, D(5), Close);
        var delta = Seq(F.Id("I"), Open, indices, Close);
        var edge = Seq(F.Id("W"), Open, indices, Close);
        var numerator = new Formula.Binary(
            new Formula.Binary(D(5), FormulaBinaryOperator.Multiply, delta),
            FormulaBinaryOperator.Add,
            new Formula.Binary(D(3), FormulaBinaryOperator.Multiply, edge));
        var value = new Formula.Fraction(numerator, D(5, 5));
        return Disp(Seq(Forall, Sp, Open, i, Colon, Sp, range, Close, Comma, Sp,
            Forall, Sp, Open, j, Colon, Sp, range, Close, Comma, Sp,
            F.Id("M"), Open, indices, Close, Sp, Eq, Sp, value));
    }

    private static Formula WidthStatement()
    {
        var complexMoment = Seq(Operatorname, Grp(F.Id("complex")), Open, F.Id("M"), Close);
        Formula HasWidth(byte width) => Seq(Operatorname, Grp(F.Id("IsKIncoherentSum")),
            Open, D(width), Comma, Sp, complexMoment, Close);
        return Disp(Seq(HasWidth(3), Sp, Land, Sp, Neg, Sp, HasWidth(2)));
    }
}
