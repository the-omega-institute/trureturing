using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;
internal sealed class ActualKernelSmallWindowBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete actual-K small-window remainder.",
        H("Small-window remainder bounds"), Blocks(
            Describe.Lean(DescribeId.Create("small-window-v-absolute-bound"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelSmallWindowBounds.small_V_abs_bound"),
                H("The actual small-window continuum payment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the inclusive window 0<=D<=log 3, the retained exact finite-prime cases, scalar estimates and continuum integral bound control the actual V remainder. The proof includes the endpoints log 2 and log 3. These bounds are consumed by the complete-K q6 and q22 certificate and retain their original proof terms. They assert neither global positivity nor RH."))),
                DescribeRole.Theorem))));
}
