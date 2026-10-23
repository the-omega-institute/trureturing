using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class ActualCutPartitionClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionClassification.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common-suffix recutting exactly classifies recovery of complete literal rows.",
        H("All-source sparse cut recovery classification"),
        Blocks(
            Theorem("result", "Full common-suffix classification",
                "For arbitrary finite prefix-free P and Q, a unique factor from the realized image of canonicalRow P to that of canonicalRow Q exists exactly when P = Q S for some finite prefix-free S. The result also includes the explicit finite decoder, the executable Boolean criterion, uniqueness of S when Q is nonempty, all four empty/root boundaries, concrete absent-cut guards, and equivalence with the independently computed exterior-plus-partition record."),
            Paragraph(Text("Necessity first uses the uncovered-hole native pair to obtain prefix coverage. If two Q sections differ, the simultaneous one-class marker pair contradicts recovery; therefore every section is the same finite suffix. Sufficiency uses the finite source-free decoder. The realized-image factorization step directly applies realized_image_unique_factorization_iff_reverse_kernel. Empty P recovers every Q; empty Q requires empty P; root Q is recovered by every P; root P recovers only root Q. The scope remains all finite nonempty ordered Boolean trees, including absent cuts. The conclusion concerns the original row maps and makes no bounded-budget, physical execution, or broader calibration assertion."))
        )));

    private static DocumentBlock Theorem(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actualcutpartitionclassification-" + n.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
        DescribeRole.Theorem);

}
