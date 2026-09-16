using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence.ConditionalComparison.ThreePrime;

internal sealed class ComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schroeder's conditional convex comparison for arbitrary finite histories and label supports.",
        H("Conditional Convex Comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conditional-convex-load-comparison"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.convex_load_comparison"),
                H("Actual conditional loads are dominated by aligned auxiliary loads"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Arith/schroeder2026noncoverage")),
                Blocks(
                    Paragraph(Text(
                        "This is a source transplant of Michael Schroeder's theorem "
                        + "Erdos7.ThreePrime.convex_load_comparison. The full MIT "
                        + "license, source archive and import mapping are recorded in "),
                        Ref("D5/L/Arith/schroeder2026noncoverage"), Text(".")),
                    Paragraph(Text(
                        "A KernelChain on a finite alphabet retains the complete "
                        + "preceding coordinate tuple in every conditional kernel. "
                        + "For every label and every history, HasCaps bounds its "
                        + "coordinate-event probability by the survival function "
                        + "of a finite auxiliary run at that label's depth. "
                        + "The finite depth bound and nonnegative rational weights "
                        + "are explicit hypotheses.")),
                    Paragraph(Text(
                        "For every increasing convex rational-valued function, "
                        + "the expected function of the actual active-label load "
                        + "is at most its expectation under the product of the "
                        + "auxiliary run laws, with a label active precisely when "
                        + "all its depths are below the auxiliary heights. "
                        + "The actual coordinate events need not be nested, and "
                        + "their law need not be a product law. There is no bound "
                        + "on the number of coordinates used by one label. "
                        + "Nonnegativity of the convex function is not required.")),
                    Paragraph(Text(
                        "The imported proof eliminates coordinates backwards "
                        + "using the finite increasing-supermodular rearrangement. "
                        + "The ThreePrime source directory name does not impose "
                        + "a three-prime hypothesis on this declaration. This "
                        + "module supplies the existing comparison theorem; "
                        + "a covering-system application must still construct "
                        + "its actual kernels and discharge every cap hypothesis."))),
                DescribeRole.Theorem))));
}
