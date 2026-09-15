using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class SignedFiniteMultiplicationResponseKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Multiplication and Division Response Kernels.",
        H("Finite Multiplication and Division Response Kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-finite-multiplication-response-kernel-classification"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenResource/SignedFiniteMultiplicationResponseKernel.eq_signed_iff"),
                H("The exact classification at every positive horizon"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a natural capacity vector on a finite coordinate set and a positive integer horizon. "
                    + "Each letter increases or decreases one coordinate by one, failing at capacity or at zero. "
                    + "A successful word returns the parity sign of its endpoint coordinate sum if every "
                    + "coordinate is at most one, and zero otherwise. Failure is a distinct response. "
                    + "The defect is the sum of the positive parts of each coordinate minus one. "
                    + "The guard code records each coordinate and its remaining capacity, both truncated "
                    + "at the horizon. Two states have equal responses on every word of length at most "
                    + "the horizon exactly when they are equal, or both defects exceed the horizon and "
                    + "their guard codes agree. Repeated letters recover both truncated boundary distances. "
                    + "Dividing each coordinate down to at most one separates every state whose defect "
                    + "does not exceed the horizon. States of larger defect retain zero readout on every "
                    + "successful word in the horizon, so their responses are determined by the guards. "
                    + "Zero capacities and an empty coordinate set are allowed."))),
                DescribeRole.Theorem))));
}
