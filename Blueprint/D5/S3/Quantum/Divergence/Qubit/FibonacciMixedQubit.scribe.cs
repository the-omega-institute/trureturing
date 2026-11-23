using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.Qubit;

internal sealed class FibonacciMixedQubitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quantitative Fibonacci trace-log gap for three mixed qubit preparations.",
        H("Fibonacci mixed qubit bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("fibonacci-mixed-qubit-benchmark-margin"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Divergence/Qubit/FibonacciMixedQubit.traceLog_le_benchmark_sub_margin"),
            H("Quantitative bound below the benchmark"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Divergence/trureturing2026fibonaccimixedqubit"),
                LibraryNoteRef.Create("D5/L/Divergence/trureturing2026fibonacciclippedprofile")),
            Blocks(
                Paragraph(Text(
                    "Take three complex two-by-two positive semidefinite matrices X₁, X₂, X₃, each of trace one. "
                    + "Form A with weights (88, 25, 28)/141 and C with weights (66, 15, 12)/141. "
                    + "The real trace of A(log A − log C) is at most "
                    + "(113/141) log(113/81) + (28/141) log(7/3) "
                    + "− (3(1 − Re Tr(X₁X₂)) + 11 Re Tr(X₁X₃))/63360.")),
                Paragraph(Text(
                    "Independently sample one rank-one spectral projection from each preparation with its "
                    + "eigenvalue as weight. The one-coordinate marginals recover both matrix mixtures. "
                    + "The two-coordinate marginals recover the two real trace overlaps in the deficit. "
                    + "Apply supported joint convexity, then average the pure-qubit bound with the full "
                    + "product weights. Positive reference coefficients guarantee kernel inclusion on each "
                    + "spectral choice, including singular references. Zero eigenvalues contribute zero "
                    + "through the homogeneous joint-convexity formula."))),
            DescribeRole.Theorem))));
}
