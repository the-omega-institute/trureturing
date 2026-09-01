using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class HermitianKernelNegativeSquaresDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/HermitianKernelNegativeSquares.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Gram inertia defines the negative squares of a Hermitian kernel.",
        H("Hermitian Kernel Negative Squares"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hermitian-kernel"),
                DeclarationHandle.Create(Prefix + "HermitianKernel"),
                H("Hermitian kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A complex kernel is Hermitian when exchanging its two points and "
                        + "taking complex conjugation recovers the original value."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("has-negative-squares"),
                DeclarationHandle.Create(Prefix + "HasNegativeSquares"),
                H("Exactly kappa negative squares"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every finite sampling family produces a Hermitian Gram matrix. "
                            + "The kernel has exactly kappa negative squares when every "
                            + "such matrix has at most kappa negative eigenvalues and at "
                            + "least one finite family attains exactly kappa.")),
                    Paragraph(Text(
                        "Both the uniform upper bound and its finite attainment are part "
                            + "of the definition; neither clause is inferred from the other."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("one-negative-square-realization"),
                DeclarationHandle.Create(
                    Prefix + "exists_hermitian_kernel_with_one_negative_square"),
                H("A kernel with one negative square exists"),
                StatementSource.FromAuthor(ExistenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The constant minus-one kernel on Unit is a nontrivial realization. "
                            + "Every finite Gram matrix has negative index at most one by "
                            + "the rank-one positive-update bound.")),
                    Paragraph(Text(
                        "Sampling the unique point once gives the one-by-one matrix with "
                            + "entry minus one, whose sole eigenvalue is negative, so the "
                            + "upper bound is attained."))),
                DescribeRole.Theorem))));

    private static Formula ExistenceFormula()
    {
        Formula kernel = F.Id("K");
        return Disp(Seq(
            Exists, Sp, kernel, Colon, Sp,
            Call("HermitianKernel", F.Id("Unit")), Comma, Sp,
            Call("HasNegativeSquares", kernel, D(1)), Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
