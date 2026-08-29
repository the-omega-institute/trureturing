using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencySelf;

internal sealed class AgencyResidualWitnessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencySelf/AgencyResidualWitness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A hidden strategy difference is a concrete witness of agency residual.",
        H("Agency Residual Witness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-hidden-strategy-difference-is-residual"),
                DeclarationHandle.Create(Prefix + "hidden_strategy_difference_is_residual"),
                H("A hidden strategy difference is residual"),
                StatementSource.FromAuthor(ResidualStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume two histories have the same current-memory value but different "
                            + "strategy-profile values.")),
                    Paragraph(Text(
                        "These two displayed facts are exactly the defining components of an "
                            + "agency-residual witness for that pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-residual-pair-is-separated-by-the-paired-readout"),
                DeclarationHandle.Create(Prefix + "residual_separated_by_pair"),
                H("A residual pair is separated by the paired readout"),
                StatementSource.FromAuthor(SeparationStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the displayed pair lies in the agency residual.")),
                    Paragraph(Text(
                        "Equality of the paired memory-profile values would imply equality of "
                            + "their profile components, contradicting the residual witness."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula PrefixFormula(Formula antecedent, Formula conclusion) =>
        Disp(Seq(
            Forall, Sp, F.Id("current"), Colon, Sp,
            Arrow(F.Id("H"), F.Id("M")), Comma, Sp,
            F.Id("profile"), Colon, Sp, Arrow(F.Id("H"), F.Id("P")), Comma, Sp,
            F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp, F.Id("H"), Comma,
            RowBreak, Grp(),
            antecedent, Sp, Rightarrow, Sp, conclusion, Dot));

    private static Formula ResidualStatement()
    {
        Formula antecedent = Seq(
            Call("current", F.Id("x")), Sp, Eq, Sp, Call("current", F.Id("y")),
            Sp, Land, Sp,
            Call("profile", F.Id("x")), Sp, Neq, Sp, Call("profile", F.Id("y")));
        Formula residual = Call("AgencyResidual", F.Id("current"),
            F.Id("profile"), F.Id("x"), F.Id("y"));
        return PrefixFormula(Seq(Open, antecedent, Close), residual);
    }

    private static Formula SeparationStatement()
    {
        Formula residual = Call("AgencyResidual", F.Id("current"),
            F.Id("profile"), F.Id("x"), F.Id("y"));
        Formula leftPair = Call("pair", Call("current", F.Id("x")),
            Call("profile", F.Id("x")));
        Formula rightPair = Call("pair", Call("current", F.Id("y")),
            Call("profile", F.Id("y")));
        return PrefixFormula(residual, Seq(leftPair, Sp, Neq, Sp, rightPair));
    }
}
