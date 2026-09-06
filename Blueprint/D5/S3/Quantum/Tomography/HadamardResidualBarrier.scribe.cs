using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class HadamardResidualBarrierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual roots for nearby order-six matrices enter a certified sublevel set of the base residual.",
        H("Hadamard Residual Barrier"),
        Blocks(Describe.Lean(
            DescribeId.Create("common-unbiased-root-base-residual"),
            DeclarationHandle.Create("D5/S3/Quantum/Tomography/HadamardResidualBarrier.common_unbiased_root_has_small_base_residual"),
            H("Entry perturbations control the complete root residual"),
            StatementSource.FromAuthor(Disp(Seq(F.Id("NearbyCommonUnbiasedRootResidualBound"), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let H0 and H be complex six by six matrices, delta be nonnegative, and u have unit squared modulus in every coordinate. Assume every entry of H0-H has norm at most delta, and every coordinate of H-adjoint times u has squared modulus six. Then every coordinate of H0-adjoint times u has squared-modulus residual bounded by 30 delta plus 36 delta squared.")),
                Paragraph(Text("The transformed amplitudes change by at most six delta. At an actual root the reference amplitude has squared modulus six, hence norm at most five halves. The reverse triangle inequality and the difference-of-squares factorization yield the bound. No two-circulant symmetry or X-family parameterization is assumed.")),
                Paragraph(Text("The existing CayleyCoverAnalysis owns generic residual-gap transport. This theorem supplies its concrete matrix perturbation estimate. Exhaustive sublevel coverage, local uniqueness in each guard, and nonedge certification remain separate obligations. External verifier output does not discharge them in the Lean kernel. This source is submitted for elaboration; it has not been locally compiled."))),
            DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("common-unbiased-residual-column-perturbation"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Tomography/HadamardResidualBarrier."
                + "common_unbiased_residual_transfers_under_column_perturbation"),
            H("Approximate common-unbiased vectors remain in the seed sublevel"),
            StatementSource.FromAuthor(Disp(Seq(
                F.Id("UnitEntryVectorAndColumnPerturbationBound"), Sp, Land, Sp,
                F.Id("TargetSquaredModulusResidualAtMostTau"), Sp, Rightarrow, Sp,
                F.Id("SeedResidualAtMostTauPlusRhoTimesFivePlusRho"), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let H0 and H be six-by-six complex matrices, u a unit-entry vector, "
                    + "rho nonnegative, and tau at most one-quarter. Assume each column of "
                    + "H0-H has sum of entry norms at most rho and every entry of H* u has "
                    + "squared modulus within tau of six. The theorem bounds every corresponding "
                    + "seed residual by tau + rho(5+rho). It uses the actual Matrix.mulVec and "
                    + "conjugate-transpose expressions, not an assumed residual oracle.")),
                Paragraph(Text(
                    "The target residual gives norm at most five-halves for each transformed "
                    + "entry. The column bound gives displacement at most rho. Factoring the "
                    + "difference of squared norms and applying the reverse triangle inequality "
                    + "produces rho(5+rho). No fixed Hadamard family, regular Jacobian, root "
                    + "existence, uniqueness, or enumeration is assumed.")),
                Paragraph(Text(
                    "This transports a root or approximate root into a seed sublevel. "
                    + "The complete sublevel cover and tube-overlap inequalities are separate "
                    + "obligations. External interval reports do not discharge them in Lean. "
                    + "The source is logically reviewed but has not been locally elaborated."))),
            DescribeRole.Theorem))));
}
