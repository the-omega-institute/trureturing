using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ActualGaussianLocalWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact complete local occurrence window.",
        H("The exact complete local occurrence window"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-gaussian-local-window"),
                DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualGaussianLocalWindow.mem_localWindow"),
                H("The exact complete local occurrence window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text("localWindow(gamma) starts from actualData.symmetricIndices(abs(gamma)+7), expands every finite analytic-multiplicity fiber, maps through actualOccurrenceEquiv and filters by abs(im(rho)-gamma)<=6. The actual strip gives spectralRadius(rho)<=abs(im(rho))+1. This proves the exact membership equivalence, including both distance-six boundary points.")),
                Paragraph(Text("For any finite occurrence set with abs(im(rho))<=T, its cardinality is at most T^2 times the inverse-square mass, hence at most 2*T^2. Taking T=gamma+10 for gamma>0 gives card(localWindow(gamma))<=2*(gamma+10)^2. ActualGaussianDirectTail uses both the exact membership and this count to select the original finite Cassel time. No local-finiteness or multiplicity premise is added."))),
                DescribeRole.Theorem))));
}
