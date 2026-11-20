using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour;

internal sealed class MaOrderFourCheckerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sound checking of equality branches for arbitrary order-four arrays.",
        H("Sound checking of equality branches for arbitrary order-four arrays"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-realizes-initial"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.realizes_initial"),
                H("realizes_initial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Singleton partition classes constrain no distinct cells to have equal labels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-known-of-mem"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.known_of_mem"),
                H("known_of_mem"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Retrieve the closure proposition for a partition found in the checked reuse list."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-sound"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.sound"),
                H("sound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A successful check closes the given equality state. Transversal branches cover all six row pairs, clashes contradict row or column injectivity, and exact partition matches allow reuse. A motif branch splits on the fifth cell equality. A columns leaf supplies a match for each row in each pair of columns."))),
                DescribeRole.Theorem))));
}
