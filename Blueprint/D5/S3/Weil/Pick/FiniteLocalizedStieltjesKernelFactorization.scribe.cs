using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class FiniteLocalizedStieltjesKernelFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.";

    private static LibraryNoteRef Literature =>
        LibraryNoteRef.Create("D5/L/derkachkovalyov2017indefinitestieltjes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite atomic Stieltjes mass and support kernels factor through one "
            + "Cauchy feature matrix and two diagonal weight matrices.",
        H("Finite Localized Stieltjes Kernel Factorization"),
        Blocks(
            DefinitionNode(
                "finite-atomic-stieltjes-transform",
                "finiteAtomicStieltjesTransform",
                "Finite atomic Stieltjes transform",
                "The sum of the atomic Stieltjes transforms over a finite atom type."),
            DefinitionNode(
                "finite-localized-atomic-stieltjes-transform",
                "finiteLocalizedAtomicStieltjesTransform",
                "Finite localized atomic Stieltjes transform",
                "The finite sum after multiplication of every atomic transform by the spectral coordinate."),
            DefinitionNode(
                "finite-mass-kernel",
                "finiteMassKernel",
                "Finite mass kernel",
                "The Hermitian sum of the atomic mass kernels."),
            DefinitionNode(
                "finite-support-kernel",
                "finiteSupportKernel",
                "Finite support kernel",
                "The Hermitian sum of the mass-times-support atomic kernels."),
            DefinitionNode(
                "cauchy-feature-matrix",
                "cauchyFeatureMatrix",
                "Cauchy feature matrix",
                "Rows are sample points and columns are finite support atoms."),
            DefinitionNode(
                "mass-weight-matrix",
                "massWeightMatrix",
                "Mass weight matrix",
                "The diagonal matrix of real atomic masses."),
            DefinitionNode(
                "support-weight-matrix",
                "supportWeightMatrix",
                "Support weight matrix",
                "The diagonal matrix of mass-times-support localizing weights."),
            Describe.Lean(
                DescribeId.Create("finite-localization-commutes-with-summation"),
                DeclarationHandle.Create(
                    Prefix + "finite_localized_transform_eq_coordinate_mul"),
                H("Finite localization commutes with summation"),
                StatementSource.FromAuthor(LocalizationFormula()),
                AssessedProvenance.FromLiterature(Literature),
                Blocks(Paragraph(Text(
                    "A common spectral coordinate distributes across the finite atomic sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-support-kernel-is-the-support-weighted-atomic-sum"),
                DeclarationHandle.Create(
                    Prefix + "finite_support_kernel_eq_sum_support_mul_mass_kernel"),
                H("The finite support kernel is the support-weighted atomic sum"),
                StatementSource.FromAuthor(SupportSumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every atom keeps its own support coordinate, so no common scalar is extracted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-mass-gram-factorization"),
                DeclarationHandle.Create(Prefix + "finite_mass_gram_factorization"),
                H("The finite mass Gram matrix factors through Cauchy features"),
                StatementSource.FromAuthor(MassFactorizationFormula()),
                AssessedProvenance.FromLiterature(Literature),
                Blocks(Paragraph(Text(
                    "The ordinary finite Gram matrix is C times the mass diagonal times C adjoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-support-gram-factorization"),
                DeclarationHandle.Create(Prefix + "finite_support_gram_factorization"),
                H("The finite support Gram matrix factors through the localized diagonal"),
                StatementSource.FromAuthor(SupportFactorizationFormula()),
                AssessedProvenance.FromLiterature(Literature),
                Blocks(Paragraph(Text(
                    "Coordinate localization changes only the diagonal from mass to mass times support."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel")),
        ]));

    private static DocumentBlock.Describe DefinitionNode(
        string id,
        string declaration,
        string heading,
        string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Literature),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static Formula LocalizationFormula()
    {
        var m = F.Id("m");
        var x = F.Id("x");
        var z = F.Id("z");
        return Disp(Equal(
            Call("F_loc", m, x, z),
            Multiply(z, Call("F", m, x, z))));
    }

    private static Formula SupportSumFormula()
    {
        var m = F.Id("m");
        var x = F.Id("x");
        var z = F.Id("z");
        var w = F.Id("w");
        return Disp(Equal(
            Call("K_support", m, x, z, w),
            Call("sum_support_times_mass_kernel", m, x, z, w)));
    }

    private static Formula MassFactorizationFormula()
    {
        var m = F.Id("m");
        var x = F.Id("x");
        var p = F.Id("p");
        return Disp(Equal(
            Call("Gram_mass", m, x, p),
            Multiply(
                Multiply(Call("C", x, p), Call("D_mass", m)),
                Call("C_adjoint", x, p))));
    }

    private static Formula SupportFactorizationFormula()
    {
        var m = F.Id("m");
        var x = F.Id("x");
        var p = F.Id("p");
        return Disp(Equal(
            Call("Gram_support", m, x, p),
            Multiply(
                Multiply(Call("C", x, p), Call("D_mass_support", m, x)),
                Call("C_adjoint", x, p))));
    }
}
