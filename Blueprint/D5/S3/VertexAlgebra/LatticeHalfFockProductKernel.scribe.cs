using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockProductKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native pair-translation kernel has rectangular lower bounds and finite ordered diagonals.",
        H("Native Pair Kernel and Ordered Supports"),
        Blocks(
            Paragraph(Text("For arbitrary lattice data D and two charges, pairTranslation replaces "
                + "each oscillator creator X index by its constant lift minus the left pairing times "
                + "X 0 ^ omega(index) minus the right pairing times X 1 ^ omega(index). "
                + "pairConvolution evaluates the resulting finite bivariate polynomial against the "
                + "two halfCreationCoeff sequences. Their composition is the complex-linear "
                + "commonKernel, with two independent integer coefficient indices.")),
            Describe.Lean(
                DescribeId.Create("half-fock-pair-translation-composition"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.pair_translation_composition"),
                H("Successive single translations give the pair translation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every oscillator polynomial, lifting the right halfTranslatedPolynomial "
                    + "through secondTranslationLift D left equals pairTranslation D left right. "
                    + "Polynomial induction checks constants, addition and the actual creator images."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-kernel-constant"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.kernel_constant"),
                H("The constant kernel is the pair of creation coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For scalar:C, commonKernel at first,second on C scalar equals "
                    + "C scalar * (halfCreationCoeff D left first * halfCreationCoeff D right second). "
                    + "The finite convolution monomial identity proves this consumed constant case."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-kernel-creator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.kernel_creator"),
                H("A creator produces both independent kernel shifts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On X index * p, the kernel equals X index times its value on p, "
                    + "minus the left pairing smul the value at first+omega(index),second, minus the "
                    + "right pairing smul the value at first,second+omega(index). Pair translation "
                    + "composition and the two bivariate convolution shifts supply the recurrence."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-kernel-rectangular-support"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_rectangular_support"),
                H("Each polynomial has two integer lower support bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every p there exist firstBound and secondBound such that "
                    + "first<firstBound or second<secondBound forces commonKernel(first,second,p)=0. "
                    + "The bounds are negatives of the coordinate maxima in the finite pair-translated "
                    + "polynomial support; negative half-creation indices vanish."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-kernel-ordered-support"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_ordered_finite_support"),
                H("Both ordered diagonals have finite support after application"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For fixed first,second,p, both natural-degree sequences with "
                    + "indices first+d,second-d and first-d,second+d have finite support. "
                    + "The decreasing coordinate eventually crosses its lower bound. "
                    + "OrderedProducts and ClearedKernel consume this statewise finiteness."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-kernel-branch-exchange"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_branch_exchange"),
                H("Charge and coefficient-index exchange preserves the common kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all first,second,p, commonKernel D left right first second p "
                    + "equals commonKernel D right left second first p. Polynomial induction uses "
                    + "the constant and creator identities; ClearedKernel consumes this equality "
                    + "when reflecting its finite coefficient range."))), DescribeRole.Theorem),
            Paragraph(Text("These repository-derived identities reuse the inherited half-creation, "
                + "translation and finite convolution APIs. Rectangular lower support permits "
                + "infinite bivariate support. The finite ordered sums are per polynomial, and "
                + "no finite support in the endomorphism space, analytic convergence, actual ground "
                + "action or full charged tensor locality is claimed by this module alone.")))));
}
