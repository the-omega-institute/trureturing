using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics;

internal sealed class FirstBreakRationalCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/CompletionDynamics/FirstBreakRationalCounterexample.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A first nonzero observation admits both rational and irrational first coordinates.",
        H("First-Break Rational Counterexample"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("has-first-break"),
                DeclarationHandle.Create(Prefix + "HasFirstBreak"),
                H("First break"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A trajectory has a first break when coordinate zero vanishes and "
                        + "coordinate one does not."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("first-break-does-not-force-irrationality"),
                DeclarationHandle.Create(Prefix + "first_break_does_not_force_irrationality"),
                H("A first break does not force irrationality"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There are two explicit real trajectories with a first break: one "
                            + "has rational first coordinate one, while the other has irrational "
                            + "first coordinate square root of two.")),
                    Paragraph(Text(
                        "The paired witnesses show that the first-break condition alone does not "
                            + "select either arithmetic type."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula() => Disp(Seq(
        Exists, Sp,
        F.Id("r"), Comma, Sp, F.Id("i"), Colon, Sp,
        new Formula.TypeArrow(
            Seq(Mathbb, Grp(F.Id("N"))),
            Seq(Mathbb, Grp(F.Id("R")))), Comma,
        RowBreak,
        F.Id("HasFirstBreak"), Open, F.Id("r"), Close, Sp, Land, Sp,
        Neg, Sp, F.Id("Irrational"), Open, F.Id("r"), Open, D(1), Close, Close, Sp, Land,
        RowBreak,
        F.Id("HasFirstBreak"), Open, F.Id("i"), Close, Sp, Land, Sp,
        F.Id("Irrational"), Open, F.Id("i"), Open, D(1), Close, Close, Dot));
}
