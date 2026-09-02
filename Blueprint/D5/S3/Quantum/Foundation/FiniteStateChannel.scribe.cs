using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FiniteStateChannelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical finite density states and completely positive "
            + "trace-preserving channels.",
        H("Finite Density States and Quantum Channels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-state-channel-composition"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteStateChannel.channel_comp_mapState"),
                H("Channel composition agrees with sequential state evolution"),
                StatementSource.FromAuthor(CompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A density state is a positive semidefinite CStarMatrix of trace one. A channel is a Mathlib completely positive map equipped with trace preservation.")),
                    Paragraph(Text(
                        "Complete positivity sends density matrices to positive matrices and trace preservation retains normalization, giving a canonical state action.")),
                    Paragraph(Text(
                        "Composition uses Mathlib's amplified positivity interface. Applying the composed channel to a density state equals applying the two channels sequentially."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ChannelOne() => Seq(Phi, Underscore, Grp(D(1)));

    private static Formula ChannelTwo() => Seq(Phi, Underscore, Grp(D(2)));

    private static Formula CompositionFormula() => Disp(Seq(
        Call("mapState",
            Seq(ChannelTwo(), Sp, Circ, Sp, ChannelOne()), Rho),
        Sp, Eq, Sp,
        Call("mapState", ChannelTwo(),
            Call("mapState", ChannelOne(), Rho))));
}
