using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualBoundaryAdvanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualBoundaryAdvance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Advance Actual Native Boundaries with Retained Route Identities.",
        H("Advance Actual Native Boundaries with Retained Route Identities"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-actual-boundary-advance-native-actual-even-odd-boundary-advance"), DeclarationHandle.Create(Prefix + "native_actual_even_odd_boundary_advance"),
                H("Earn the Updated Boundary from Actual Slicing"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At order at least three, an actual old boundary path, disjoint restored pieces and a concrete updated joint partition on the same Hamilton cycle determine the next native even or odd boundary. Literal native ports transfer the endpoint template through the actual two-path restoration; the next endpoint law is earned from the supplied old data."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-actual-boundary-advance-native-actual-first-cut-even-odd-boundary-advance"), DeclarationHandle.Create(Prefix + "native_actual_first_cut_even_odd_boundary_advance"),
                H("Retain the Distinguished First-Cut Factorization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual first-cut update preserves the concrete route prefix and the same old boundary inventory while advancing the native endpoint template. Every supplied cycle, path and cut identity remains explicit; no arbitrary recursive existence premise closes an all-order theorem."))), DescribeRole.Theorem))));
}
