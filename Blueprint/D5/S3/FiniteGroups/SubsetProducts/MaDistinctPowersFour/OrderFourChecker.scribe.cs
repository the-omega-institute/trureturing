using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour;

internal sealed class MaOrderFourCheckerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sound checking of equality branches for arbitrary order-four arrays.",
        H("Sound checking of equality branches for arbitrary order-four arrays"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-position"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Position"),
                H("Position"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A cell is a pair of indices in Fin 4 × Fin 4, with row first and column second."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-partition"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Partition"),
                H("Partition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An equality state is a Vector Nat 16 assigning a natural-number symbol to each cell."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-initial"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.initial"),
                H("initial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The initial Partition assigns each cell its own index in the sixteen-entry vector."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-symbol"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.symbol"),
                H("symbol"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Read the natural-number symbol of a Position in a Partition using the standard index equivalence from Fin 4 × Fin 4 to Fin 16."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-value"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.value"),
                H("value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Read the label of a Position in an array with rows and columns indexed by Fin 4 and labels in an arbitrary type."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-realizes"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Realizes"),
                H("Realizes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An array realizes a Partition if any two cells with equal partition symbols have equal array labels."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-merge"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.merge"),
                H("merge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given a Partition and two positions p and q, return the partition formed by replacing every occurrence of the symbol at q with the symbol at p."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-closed"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Closed"),
                H("Closed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every label type and every order-four array that is Latin, has no rainbow transversal and realizes the given Partition, the array has equal column symbol sets or the prescribed motif."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-known"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Known"),
                H("Known"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a List Partition, the empty list gives True and a nonempty list requires its first partition to be Closed and the remaining list to be Known."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-certificate"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Certificate"),
                H("Certificate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The certificate tree has a same-line clash with two positions, a columns leaf, a transversal with a row-to-column map and six subcertificates, a motif with three rows, three columns and one subcertificate, or reuse at a natural-number index."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-orderfourchecker-check"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.check"),
                H("check"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given a List Partition, the current Partition and a Certificate, return a Boolean. A clash tests two distinct cells on one line for equal symbols. A columns leaf tests for a symbol match for every row of each source column in each target column. A transversal tests the map for injectivity and checks all six pairwise merges. A motif tests distinct rows and columns and the first four equalities, then checks the merge for the fifth equality. Reuse tests for the exact current partition at the indicated list index."))),
                DescribeRole.Definition),
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
