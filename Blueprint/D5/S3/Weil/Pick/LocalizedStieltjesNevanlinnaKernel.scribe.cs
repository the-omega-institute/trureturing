using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class LocalizedStieltjesNevanlinnaKernelDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.";

    private static LibraryNoteRef Literature =>
        LibraryNoteRef.Create("D5/L/derkachkovalyov2017indefinitestieltjes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An atomic Stieltjes transform and its coordinate-localized transform "
            + "have exact Nevanlinna kernels whose scalar weights are mass and "
            + "mass times support.",
        H("Localized Stieltjes and Nevanlinna Kernels"),
        Blocks(
            DefinitionNode(
                "real-support-cauchy-feature",
                "stieltjesFeature",
                "Real-support Cauchy feature",
                "The inverse affine distance from a complex sample to a real support coordinate.",
                true),
            DefinitionNode(
                "atomic-stieltjes-transform",
                "atomicStieltjesTransform",
                "Atomic Stieltjes transform",
                "A real atomic mass divided by support minus the complex sample.",
                true),
            DefinitionNode(
                "coordinate-localized-atomic-stieltjes-transform",
                "localizedAtomicStieltjesTransform",
                "Coordinate-localized atomic Stieltjes transform",
                "Multiplication by the spectral coordinate is the first Stieltjes support localizer.",
                true),
            DefinitionNode(
                "regular-stieltjes-pair",
                "regularStieltjesPair",
                "Regular Stieltjes sample pair",
                "The support denominators and the Nevanlinna cross denominator are all nonzero.",
                false),
            DefinitionNode(
                "raw-nevanlinna-difference-quotient",
                "rawNevanlinnaDifferenceQuotient",
                "Raw Nevanlinna difference quotient",
                "The divided conjugate difference of the atomic Stieltjes transform.",
                true),
            DefinitionNode(
                "localized-nevanlinna-difference-quotient",
                "localizedNevanlinnaDifferenceQuotient",
                "Localized Nevanlinna difference quotient",
                "The divided conjugate difference after multiplying the transform by the spectral coordinate.",
                true),
            DefinitionNode(
                "atomic-mass-kernel",
                "atomicMassKernel",
                "Atomic mass kernel",
                "The rank-one Hermitian Cauchy kernel whose scalar weight is the atomic mass.",
                true),
            DefinitionNode(
                "atomic-support-kernel",
                "atomicSupportKernel",
                "Atomic support kernel",
                "The rank-one Hermitian Cauchy kernel whose scalar weight is mass times support.",
                true),
            DefinitionNode(
                "normalized-upper-sample",
                "normalizedUpperSample",
                "Normalized upper-half-plane sample",
                "The sample one imaginary unit above the real support atom.",
                false),
            Describe.Lean(
                DescribeId.Create("support-localizer-multiplies-the-mass-kernel"),
                DeclarationHandle.Create(
                    Prefix + "atomic_support_kernel_eq_support_mul_mass_kernel"),
                H("Support localization multiplies the mass kernel by support"),
                StatementSource.FromAuthor(SupportMultiplicationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two kernels use the same Cauchy feature. Their only difference is the "
                        + "support coordinate in the scalar weight, so localization is exact and "
                        + "does not require a limiting argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-difference-quotient-is-the-mass-kernel"),
                DeclarationHandle.Create(
                    Prefix + "raw_nevanlinna_difference_quotient_eq_mass_kernel"),
                H("The raw difference quotient is the mass kernel"),
                StatementSource.FromAuthor(RawKernelFormula()),
                AssessedProvenance.FromLiterature(Literature),
                Blocks(Paragraph(Text(
                    "For a regular sample pair, the conjugate divided difference of the atomic "
                        + "Stieltjes transform factors as the rank-one Cauchy kernel with mass weight."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("localized-difference-quotient-is-the-support-kernel"),
                DeclarationHandle.Create(
                    Prefix + "localized_nevanlinna_difference_quotient_eq_support_kernel"),
                H("The localized difference quotient is the support kernel"),
                StatementSource.FromAuthor(LocalizedKernelFormula()),
                AssessedProvenance.FromLiterature(Literature),
                Blocks(Paragraph(Text(
                    "Multiplication of the transform by z inserts the real support coordinate into "
                        + "the same rank-one Cauchy factor. This is the finite atomic form of the "
                        + "generalized Stieltjes distinction between f and z f."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-diagonal-separates-mass-and-support"),
                DeclarationHandle.Create(
                    Prefix + "normalized_diagonal_reads_mass_and_support"),
                H("The normalized diagonal separates mass from support"),
                StatementSource.FromAuthor(NormalizedDiagonalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At the sample support plus i, the Cauchy feature has unit modulus. The raw "
                            + "kernel therefore reads mass exactly, while the localized kernel reads "
                            + "mass times support exactly.")),
                    Paragraph(Text(
                        "For strictly positive mass, the localized diagonal is negative exactly when "
                            + "the support coordinate is negative. The raw diagonal contains no such "
                            + "support-sign information."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/Pick/HermitianKernelNegativeSquares")),
        ]));

    private static DocumentBlock.Describe DefinitionNode(
        string id,
        string declaration,
        string heading,
        string paragraph,
        bool literature) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            literature
                ? AssessedProvenance.FromLiterature(Literature)
                : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static Formula SupportMultiplicationFormula()
    {
        var m = Id("m");
        var x = Id("x");
        var z = Id("z");
        var w = Id("w");
        return Disp(Equal(
            Call("supportKernel", m, x, z, w),
            Multiply(x, Call("massKernel", m, x, z, w))));
    }

    private static Formula RawKernelFormula()
    {
        var m = Id("m");
        var x = Id("x");
        var z = Id("z");
        var w = Id("w");
        return Disp(Seq(
            Call("regularStieltjesPair", x, z, w), Sp, Rightarrow, Sp,
            Equal(
                Call("rawNevanlinnaDifferenceQuotient", m, x, z, w),
                Call("massKernel", m, x, z, w))));
    }

    private static Formula LocalizedKernelFormula()
    {
        var m = Id("m");
        var x = Id("x");
        var z = Id("z");
        var w = Id("w");
        return Disp(Seq(
            Call("regularStieltjesPair", x, z, w), Sp, Rightarrow, Sp,
            Equal(
                Call("localizedNevanlinnaDifferenceQuotient", m, x, z, w),
                Call("supportKernel", m, x, z, w))));
    }

    private static Formula NormalizedDiagonalFormula()
    {
        var m = Id("m");
        var x = Id("x");
        var massDiagonal = Call("massKernelDiagonal", m, x);
        var supportDiagonal = Call("supportKernelDiagonal", m, x);
        return Disp(Seq(
            m, Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp,
            Open,
            Equal(massDiagonal, m), Sp, Land, Sp,
            Equal(supportDiagonal, Multiply(m, x)), Sp, Land, Sp,
            Open, F.Re, Grp(supportDiagonal), Sp, Lt, Sp, D(0), Sp,
            Iff, Sp, x, Sp, Lt, Sp, D(0), Close,
            Close, Dot));
    }
}
