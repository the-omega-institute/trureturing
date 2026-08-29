using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Bridges;

internal sealed class WormholeKernelTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Bridges/WormholeKernelTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Outer wormholes may enlarge observer kernels by collapsing intermediate distinctions.",
        H("Wormhole Kernel Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("injective-outer-wormhole-preserves-kernel"),
                DeclarationHandle.Create(
                    Prefix + "kernel_eq_composite_of_outer_injective"),
                H("Injective outer transport preserves the observer kernel"),
                StatementSource.FromAuthor(KernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Postcomposition cannot recover distinctions already forgotten by an "
                            + "inner bridge, so the composite kernel always contains the inner "
                            + "kernel.")),
                    Paragraph(Text(
                        "When the outer map is injective, no additional intermediate distinction "
                            + "is collapsed and the two kernels are equal.")),
                    Paragraph(Text(
                        "A concrete separated pair collapsed by the outer bridge yields strict "
                            + "kernel growth and therefore a certified information-loss witness."))),
                DescribeRole.Theorem))));

    private static Formula KernelFormula() => Disp(Seq(
        Call("Injective", F.Id("h2")), Sp, Rightarrow, Sp,
        Call("Kernel", Call("compose", F.Id("h2"), F.Id("h1"))),
        Sp, Eq, Sp, Call("Kernel", F.Id("h1"))));
}
