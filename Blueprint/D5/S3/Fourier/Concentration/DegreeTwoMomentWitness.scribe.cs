using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class DegreeTwoMomentWitnessDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/DegreeTwoMomentWitness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two integer spectra share their first-degree data and have different disjoint residual masses.",
        H("Identical first-degree data and different directed-gap energies"),
        Blocks(Describe.Lean(
            DescribeId.Create("equal-first-data-distinct-degree-two"),
            DeclarationHandle.Create(Owner + ".exists_equal_first_data_distinct_degree_two"),
            H("A five-point witness"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The spectra A and B have unit weights at the respective points "
                    + "(0,1,5,6,13) and (0,2,3,7,13). Both sums of the points are 25, "
                    + "both sums of the squares are 231, and both bands have endpoints 0 and 13.")),
                Paragraph(Text(
                    "Here M₁ is the unit-weight degree-one near-collision mass including the "
                    + "diagonal, and R₂ is the unit-weight degree-two mass with disjoint supports. "
                    + "For any resolution η from zero inclusive to one exclusive, only equal "
                    + "integer frequencies count as close. Thus the degree-one mass is five "
                    + "in each spectrum and all five pairs are diagonal. The directed-gap "
                    + "collision counts are 28 for A and 20 for B. The shared-endpoint "
                    + "correction subtracts 40 and adds 20 in each spectrum.")),
                Paragraph(Text(
                    "The arithmetic relation 0+6=1+5 accounts for all nonzero disjoint "
                    + "degree-two mass of A. The two pair orders and the two orders within "
                    + "each pair give total mass eight. B has zero disjoint mass at the "
                    + "same resolutions."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("degree-one-determines-degree-two"),
                DeclarationHandle.Create(Owner + ".degreeOneDeterminesDegreeTwo"),
                H("Determination by first-degree observations"),
                StatementSource.FromAuthor(Determination()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For unit-weight, integer-valued maps on five indices with band [0,13], "
                    + "the premise fixes the endpoints at indices 0 and 4 in both maps. "
                    + "It also requires equal sums, equal sums of squares, and equal "
                    + "degree-one masses at every resolution in [0,1). The claim asks "
                    + "whether the degree-two disjoint masses must agree at every such resolution."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("degree-one-does-not-determine-degree-two"),
                DeclarationHandle.Create(Owner + ".degree_one_does_not_determine_degree_two"),
                H("The determination claim is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, F.Id("Determination")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two spectra above satisfy all the premises. At resolution zero "
                    + "their degree-two disjoint masses differ."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var a = F.Id("A");
        var b = F.Id("B");
        return Disp(new Formula.Aligned([
            Seq(Amp, Exists, Sp, a, Comma, b, Colon, Sp, Spectrum(), Comma),
            Seq(Amp, Moment(a), Sp, Eq, Sp, Moment(b), Sp, Eq, Sp, D(2, 5), Comma, Quad,
                Moment(a, squared: true), Sp, Eq, Sp, Moment(b, squared: true),
                Sp, Eq, Sp, D(2, 3, 1), Comma),
            Seq(Amp, Band(a, b), Comma),
            Seq(Amp, Forall, Sp, EtaInRange(), Comma, Quad,
                Mass("M", 1, a), Sp, Eq, Sp, Mass("M", 1, b), Sp, Eq, Sp, D(5), Comma),
            Seq(Amp, Quad, Mass("R", 2, a), Sp, Eq, Sp, D(8), Comma, Quad,
                Mass("R", 2, b), Sp, Eq, Sp, D(0), Dot)
        ]));
    }

    private static Formula Determination()
    {
        var a = F.Id("A");
        var b = F.Id("B");
        return Disp(new Formula.Aligned([
            Seq(Amp, F.Id("Determination"), Sp, Iff, Sp,
                Forall, Sp, a, Comma, b, Colon, Sp, Spectrum(), Comma),
            Seq(Amp, Open, Moment(a), Sp, Eq, Sp, Moment(b), Sp, Land, Sp,
                Moment(a, squared: true), Sp, Eq, Sp, Moment(b, squared: true),
                Sp, Land, Sp, Band(a, b)),
            Seq(Amp, Quad, Sp, Land, Sp, Open, Forall, Sp, EtaInRange(), Comma, Sp,
                Mass("M", 1, a), Sp, Eq, Sp, Mass("M", 1, b), Close, Close),
            Seq(Amp, Quad, Longrightarrow, Sp, Open, Forall, Sp, EtaInRange(), Comma, Sp,
                Mass("R", 2, a), Sp, Eq, Sp, Mass("R", 2, b), Close, Dot)
        ]));
    }

    private static Formula Spectrum() =>
        Seq(Call("Fin", D(5)), Sp, Rightarrow, Sp, Mathbb, Grp(F.Id("Z")));

    private static Formula Eta => F.Id("eta");

    private static Formula EtaInRange() =>
        Seq(Eta, Sp, InMacro, Sp, OpenBracket, D(0), Comma, D(1), Close);

    private static Formula Moment(Formula spectrum, bool squared = false)
    {
        var i = F.Id("i");
        var value = new Formula.Apply(spectrum, [i]);
        return Seq(new Formula.Subscript(Sum, i), Sp,
            squared ? new Formula.Power(value, D(2)) : value);
    }

    private static Formula Band(Formula a, Formula b) =>
        Seq(Open, Forall, Sp, F.Id("i"), Colon, Sp, Call("Fin", D(5)), Comma, Sp,
            new Formula.Apply(a, [F.Id("i")]), Comma, new Formula.Apply(b, [F.Id("i")]),
            Sp, InMacro, Sp, OpenBracket, D(0), Comma, D(1, 3), CloseBracket, Close,
            Sp, Land, Sp, new Formula.Apply(a, [D(0)]), Sp, Eq, Sp,
            new Formula.Apply(b, [D(0)]), Sp, Eq, Sp, D(0),
            Sp, Land, Sp, new Formula.Apply(a, [D(4)]), Sp, Eq, Sp,
            new Formula.Apply(b, [D(4)]), Sp, Eq, Sp, D(1, 3));

    private static Formula Mass(string name, byte degree, Formula spectrum) =>
        new Formula.Apply(new Formula.Subscript(F.Id(name), D(degree)), [spectrum, Eta]);
}
