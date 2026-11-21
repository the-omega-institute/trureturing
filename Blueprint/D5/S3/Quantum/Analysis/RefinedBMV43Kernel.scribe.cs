using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMV43KernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficient kernel for four and three factors",
        H("The coefficient kernel for four and three factors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinedbmv43kernel-defect-cyclic"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMV43Kernel.defect43_eq_cyclic"),
                H("Cyclic identity in cube-root variables"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A polynomial identity assigns the quartic trace coefficient to the three centers. The terms agree at zero eigenvalues after evaluating the kernel there."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refinedbmv43kernel-positive"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMV43Kernel.centeredKernel43_psd"),
                H("Positivity of the coefficient matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Four polynomial features give the Gram term. A diagonal congruence of a Cauchy matrix gives the other term."))),
                DescribeRole.Theorem))));
}
