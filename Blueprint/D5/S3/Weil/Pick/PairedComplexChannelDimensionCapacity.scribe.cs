using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class PairedComplexChannelDimensionCapacityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/PairedComplexChannelDimensionCapacity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paired complex channels have two complex dimensions of capacity per "
            + "finite sensor.",
        H("Paired Complex-Channel Dimension Capacity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paired-complex-channel-capacity"),
                DeclarationHandle.Create(Prefix + "pairedComplexChannelCapacity"),
                H("Paired-channel capacity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The capacity is the finite sensor cardinality multiplied by two, one "
                        + "complex coordinate for each member of the reflected channel pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("paired-complex-channel-dimension-capacity"),
                DeclarationHandle.Create(
                    Prefix + "paired_complex_channel_dimension_capacity"),
                H("Dimension excess forces a blind direction"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Injectivity into the paired observation codomain bounds the source "
                            + "finrank by the channel capacity. Rank-nullity also gives a "
                            + "quantitative lower bound on the blind-space dimension.")),
                    Paragraph(Text(
                        "When the source finrank strictly exceeds capacity, noninjectivity "
                            + "produces two distinct states with the same reading. Their "
                            + "difference is an explicit nonzero vector annihilated by every "
                            + "paired channel."))),
                DescribeRole.Theorem))));

    private static Formula ComplexNumbers() =>
        Seq(Mathbb, Grp(F.Id("C")));

    private static Formula TheoremFormula()
    {
        Formula index = F.Id("I");
        Formula state = F.Id("V");
        Formula observation = F.Id("O");
        Formula blind = F.Id("x");
        Formula capacity = Call("pairedComplexChannelCapacity", index);
        Formula stateRank = Call("finrank", ComplexNumbers(), state);
        Formula kernelRank = Call(
            "finrank", ComplexNumbers(), Call("ker", observation));
        Formula injectiveBound = Seq(
            Call("Injective", observation), Sp, Rightarrow, Sp,
            stateRank, Sp, Le, Sp, capacity);
        Formula nullityBound = Seq(
            stateRank, Sp, Minus, Sp, capacity, Sp, Le, Sp, kernelRank);
        Formula blindWitness = Seq(
            capacity, Sp, Lt, Sp, stateRank, Sp, Rightarrow, Sp,
            Exists, Sp, blind, Colon, Sp, state, Comma, Sp,
            blind, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Call("O", blind), Sp, Eq, Sp, D(0));

        Formula pairedCodomain = Grp(Seq(
            index, Sp, To, Sp, ComplexNumbers(), Sp, Times, Sp,
            ComplexNumbers()));
        Formula homSpace = Seq(
            new Formula.Subscript(
                Seq(Operatorname, Grp(F.Id("Hom"))), ComplexNumbers()),
            Open, state, Comma, Sp, pairedCodomain, Close);
        Formula observationBinder = Seq(
            Forall, Sp, observation, Sp, InMacro, Sp, homSpace, Colon);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            observationBinder,
            RowBreak, Grp(),
            Open, injectiveBound, Close, Sp, Land,
            RowBreak, Grp(),
            Open, nullityBound, Close, Sp, Land,
            RowBreak, Grp(),
            Open, blindWitness, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
