using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class MassSupportKernelPencilDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/MassSupportKernelPencil.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dual Cauchy features recover finite support coordinates as genuine "
            + "generalized eigenvalues of the localized mass-support Gram pencil.",
        H("Mass-Support Kernel Pencil"),
        Blocks(
            DefinitionNode(
                "mass-gram-matrix", "massGramMatrix", "Mass Gram matrix",
                "The finite ordinary Stieltjes Gram matrix."),
            DefinitionNode(
                "support-gram-matrix", "supportGramMatrix", "Support Gram matrix",
                "The finite coordinate-localized Stieltjes Gram matrix."),
            DefinitionNode(
                "mass-support-kernel-pencil", "massSupportKernelPencil",
                "Mass-support kernel pencil",
                "The support Gram matrix minus a real parameter times the mass Gram matrix."),
            DefinitionNode(
                "shifted-support-weight-matrix", "shiftedSupportWeightMatrix",
                "Shifted support weight matrix",
                "The diagonal of mass times support minus the pencil parameter."),
            DefinitionNode(
                "cauchy-atom-vector", "cauchyAtomVector", "Cauchy atom vector",
                "The sampled Cauchy column associated with one support atom."),
            DefinitionNode(
                "cauchy-dual-certificate", "IsCauchyDual", "Cauchy dual certificate",
                "Cauchy analysis of the sample vector is the coordinate vector at one atom."),
            DefinitionNode(
                "supported-generalized-eigenpair", "IsSupportedGeneralizedEigenpair",
                "Supported generalized eigenpair",
                "A nonzero vector with nonzero mass action satisfying the relative Gram eigenrelation."),
            TheoremNode(
                "mass-support-pencil-factorization",
                "mass_support_kernel_pencil_factorization",
                "The mass-support pencil factors through shifted atomic weights",
                PencilFactorizationFormula(),
                "The common Cauchy feature matrix remains fixed and only the atomic diagonal is shifted."),
            TheoremNode(
                "cauchy-dual-vector-is-nonzero",
                "cauchy_dual_vector_ne_zero",
                "A Cauchy-dual vector is nonzero",
                DualNonzeroFormula(),
                "Its analyzed coordinate at the selected atom is one."),
            TheoremNode(
                "mass-gram-selects-the-dual-atom",
                "mass_gram_mulVec_of_dual",
                "The mass Gram matrix selects the dual atom",
                MassActionFormula(),
                "The dual certificate collapses every atomic column except the selected one."),
            TheoremNode(
                "support-gram-selects-the-dual-atom",
                "support_gram_mulVec_of_dual",
                "The support Gram matrix selects the dual atom",
                SupportActionFormula(),
                "The same selected column now carries mass times support."),
            TheoremNode(
                "dual-atom-obeys-the-support-eigenrelation",
                "support_gram_eigenrelation_of_dual",
                "A dual atom obeys the support eigenrelation",
                EigenrelationFormula(),
                "The support coordinate is the exact relative eigenvalue."),
            TheoremNode(
                "pencil-annihilates-at-the-recovered-support",
                "pencil_mulVec_at_support_of_dual",
                "The pencil annihilates the dual vector at the recovered support",
                PencilAnnihilationFormula(),
                "Substitution of the atom's support coordinate cancels the two Gram actions."),
            TheoremNode(
                "nondegenerate-dual-has-nonzero-mass-action",
                "mass_gram_mulVec_ne_zero_of_dual",
                "A nondegenerate dual has nonzero mass action",
                MassActionNonzeroFormula(),
                "A nonzero selected mass and one nonzero sampled feature exclude the zero action."),
            TheoremNode(
                "support-is-a-generalized-eigenvalue",
                "support_is_generalized_eigenvalue_of_dual",
                "The selected support is a generalized eigenvalue",
                GeneralizedEigenvalueFormula(),
                "The dual, mass, and sampled-feature hypotheses package a genuine supported generalized eigenpair.")),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization")),
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
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe TheoremNode(
        string id,
        string declaration,
        string heading,
        Formula formula,
        string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Theorem);

    private static Formula PencilFactorizationFormula()
    {
        var m = F.Id("m");
        var x = F.Id("x");
        var p = F.Id("p");
        var lambda = F.Id("lambda");
        return Disp(Equal(
            Call("P", m, x, p, lambda),
            Multiply(
                Multiply(Call("C", x, p), Call("Dshift", m, x, lambda)),
                Call("Cadjoint", x, p))));
    }

    private static Formula DualNonzeroFormula()
    {
        var x = F.Id("x");
        var p = F.Id("p");
        var a = F.Id("a");
        var v = F.Id("v");
        return Disp(Seq(
            Call("IsCauchyDual", x, p, a, v), Sp, Rightarrow, Sp,
            v, Sp, Neq, Sp, D(0)));
    }

    private static Formula MassActionFormula()
    {
        var m = F.Id("m");
        var x = F.Id("x");
        var p = F.Id("p");
        var a = F.Id("a");
        var v = F.Id("v");
        return Disp(Seq(
            Call("IsCauchyDual", x, p, a, v), Sp, Rightarrow, Sp,
            Equal(
                Call("KmassV", m, x, p, v),
                Multiply(Call("mass", m, a), Call("cauchyColumn", x, p, a)))));
    }

    private static Formula SupportActionFormula()
    {
        var m = F.Id("m");
        var x = F.Id("x");
        var p = F.Id("p");
        var a = F.Id("a");
        var v = F.Id("v");
        return Disp(Seq(
            Call("IsCauchyDual", x, p, a, v), Sp, Rightarrow, Sp,
            Equal(
                Call("KsupportV", m, x, p, v),
                Multiply(
                    Multiply(Call("mass", m, a), Call("support", x, a)),
                    Call("cauchyColumn", x, p, a)))));
    }

    private static Formula EigenrelationFormula()
    {
        var m = F.Id("m");
        var x = F.Id("x");
        var p = F.Id("p");
        var a = F.Id("a");
        var v = F.Id("v");
        return Disp(Seq(
            Call("IsCauchyDual", x, p, a, v), Sp, Rightarrow, Sp,
            Equal(
                Call("KsupportV", m, x, p, v),
                Multiply(Call("support", x, a), Call("KmassV", m, x, p, v)))));
    }

    private static Formula PencilAnnihilationFormula()
    {
        var m = F.Id("m");
        var x = F.Id("x");
        var p = F.Id("p");
        var a = F.Id("a");
        var v = F.Id("v");
        return Disp(Seq(
            Call("IsCauchyDual", x, p, a, v), Sp, Rightarrow, Sp,
            Equal(Call("PsupportAV", m, x, p, a, v), D(0))));
    }

    private static Formula MassActionNonzeroFormula()
    {
        var m = F.Id("m");
        var x = F.Id("x");
        var p = F.Id("p");
        var a = F.Id("a");
        var v = F.Id("v");
        return Disp(Seq(
            Call("NondegenerateCauchyDual", m, x, p, a, v), Sp,
            Rightarrow, Sp,
            Call("KmassV", m, x, p, v), Sp, Neq, Sp, D(0)));
    }

    private static Formula GeneralizedEigenvalueFormula()
    {
        var m = F.Id("m");
        var x = F.Id("x");
        var p = F.Id("p");
        var a = F.Id("a");
        var v = F.Id("v");
        return Disp(Seq(
            Call("NondegenerateCauchyDual", m, x, p, a, v), Sp,
            Rightarrow, Sp,
            Call("IsGeneralizedEigenpairAtSupport", m, x, p, a, v)));
    }
}
