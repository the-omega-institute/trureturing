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
                Blocks(
                    Paragraph(Text("A successful check closes the given equality state. Transversal branches cover all six row pairs, clashes contradict row or column injectivity, and exact partition matches allow reuse. A motif branch splits on the fifth cell equality. A columns leaf supplies a match for each row in each pair of columns.")),
                    Paragraph(Text(
                        "Certificate parts 1 through 17 supply the 319 checked inputs to this proof. "
                        + "Each check proves Boolean acceptance for its certificate, partition and reuse list. "
                        + "Soundness turns each accepted input and the earlier closures it uses into a closure for arbitrary realizing arrays. "
                        + "In part 17, check318 accepts certificate318 at the initial partition with thirteen previously closed states. "
                        + "MaLatin.orderFour applies the resulting initial_closed to the input array when it has no transversal."))),
                DescribeRole.Theorem))));
}
