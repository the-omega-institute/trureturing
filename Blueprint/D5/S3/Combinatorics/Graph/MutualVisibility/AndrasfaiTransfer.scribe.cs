using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class AndrasfaiTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact formal-series algebra for the four-state transfer traces.",
        H("The corrected transfer-trace series"),
        Blocks(
            Describe.Lean(DescribeId.Create("transfer"), DeclarationHandle.Create(Prefix + "transfer"),
                H("The labelled-edge matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In state order 0,1,2,3 the rational matrix M has rows (1,1,0,0), (1,0,1,0), (0,0,0,1), (0,2,0,0). The entry two retains the two distinct labels on the transition from state 3 to state 1."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trace-series"), DeclarationHandle.Create(Prefix + "traceSeries"),
                H("The uncorrected full trace series"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The series is X times the power series with coefficient j equal to tr(M^(3j+2)) for every natural j. Thus its constant coefficient is zero and its coefficient at every positive index n is tr(M^(3n-1)). The index-zero matrix trace is not a graph G_0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("denominator"), DeclarationHandle.Create(Prefix + "denominator"),
                H("The denominator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D = 1 - 10X + 29X^2 - 32X^3 + 8X^4 in Q[[X]]. Its constant coefficient is one, so its formal multiplicative inverse is valid."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("corrected-trace-series"),
                DeclarationHandle.Create(Prefix + "corrected_trace_series"),
                H("The complete corrected trace identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The identity is traceSeries + X = X(4 - 19X + 33X^2 - 40X^3 + 8X^4) D^(-1). For B=M^3 the explicitly checked rows are (3,2,1,1), (2,3,1,0), (2,0,2,0), (2,2,0,2). Kernel-checked rational arithmetic gives B^4 = 10B^3 - 29B^2 + 32B - 8I. Multiplying by M^2 B^j and taking the trace proves the recurrence at every natural j. The first four traces are 3,21,127,749, recomputed from the matrix definitions. If H has these trace coefficients, coefficient extensionality gives D H = 3 - 9X + 4X^2 - 8X^3, with all higher coefficients zero by the proved recurrence. Multiplying by X and adding X D yields the displayed numerator. The standard formal-series inverse theorem applies because D has constant coefficient one; no convergence or fitted recurrence is used."))), DescribeRole.Theorem),
            Paragraph(Text("This is a theorem about the displayed transfer matrix. The bijection between actual original-host visible subsets and uniquely lifted closed labelled automaton walks is a separate unproved obligation. The addition of X is explicit; identifying it with the original index-one correction requires that counting correspondence.")))));
}
