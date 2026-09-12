using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class MUBCubeCompatibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorized cubes have cross-Gram identities; local Zauner factors have a swap symmetry.",
        H("MUB Cube Compatibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cube-factorized-matrix-definition"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility."
                    + "factorizedCubeMatrix"),
                H("Flattened cube matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For complex matrices H, X and Y, the matrix indexed by (i,j) and k has "
                    + "entry H(i,j) X(j,k) Y(i,k)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cube-cross-gram-entry-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility."
                    + "factorizedCube_crossGram_apply"),
                H("Entrywise cross-Gram identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite row types and an entrywise unit H, the (k,l) cross-Gram entry "
                    + "of the cubes formed from X,Y and Xprime,Yprime equals the product of the "
                    + "corresponding entries of X-adjoint times Xprime and Y-adjoint times "
                    + "Yprime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-cross-gram-matrix-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility."
                    + "factorizedCube_crossGram"),
                H("Matrix cross-Gram identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With finite row types and entrywise unit H, the cross-Gram matrix of two "
                    + "factorized cubes equals the entrywise product of the two factor "
                    + "cross-Gram matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-zauner-factor-definition"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility."
                    + "ZaunerTwoByTwoFactor"),
                H("Polynomial local factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A factor for complex entries a,b,c,d consists of u,v,x,y with u+v=2a, "
                    + "y(u-v)=2b, u-v=2cx and y(u+v)=2dx."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cube-zauner-upper-right-recovery"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility."
                    + "zaunerTwoByTwo_b_eq_y_mul_c_mul_x"),
                H("Upper-right entry recovery"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every local factor satisfies b=y c x."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-zauner-x-quadratic-law"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility."
                    + "zaunerTwoByTwo_x_quadratic"),
                H("Quadratic constraint on x"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every local factor satisfies c d x squared = a b."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-zauner-y-quadratic-law"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility."
                    + "zaunerTwoByTwo_y_quadratic"),
                H("Quadratic constraint on y"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every local factor satisfies a c y squared = b d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-zauner-x-sign-ambiguity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility."
                    + "zaunerTwoByTwo_x_eq_or_eq_neg"),
                H("Binary ambiguity of x"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If c d is nonzero, two local factors for the same entries have equal or "
                    + "opposite x coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-zauner-y-sign-ambiguity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility."
                    + "zaunerTwoByTwo_y_eq_or_eq_neg"),
                H("Binary ambiguity of y"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a c is nonzero, two local factors for the same entries have equal or "
                    + "opposite y coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-zauner-factor-swap-rigidity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility."
                    + "zaunerTwoByTwo_same_or_swap"),
                H("Rigidity up to swap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For factors z and w of the same entries, if c d and z.x are nonzero, "
                    + "then w equals z or z.swap."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-orientation-pointwise-counterexample"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility."
                    + "pointwise_product_zero_does_not_force_global_orientation"),
                H("Pointwise vanishing permits mixed orientation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There exist two nonnegative real families on Fin 2 with every pointwise "
                    + "product zero but with a nonzero product of their sums. The proof uses "
                    + "the families (1,0) and (0,1)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-orientation-global-implication"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility."
                    + "pointwise_product_zero_of_global_sum_product_zero"),
                H("Global vanishing implies pointwise vanishing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two nonnegative real families on a finite type, a zero product of "
                    + "their sums implies that every pointwise product is zero."))),
                DescribeRole.Theorem))));
}
