using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.ConicGDNN;

internal sealed class DualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dual trace positivity implies positive semidefiniteness and preservation of the product cone.",
        H("Sum of squares tests and cone duality"), Blocks(
            Describe.Lean(DescribeId.Create("conic-gdnn-duality-quartic-rankone"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/ConicGDNN/Duality.quartic_rankOne"),
                H("Rank-one tests"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real coordinate vector w, the symmetric rank-one matrix ww-transpose belongs to the zeroth approximation. Its quartic pullback is the square of the homogeneous quadratic polynomial obtained by pairing w with the Jordan square."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("conic-gdnn-duality-possemidef-of-mem-dnnnn"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/ConicGDNN/Duality.posSemidef_of_mem_dnnNN"),
                H("Positive semidefiniteness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A matrix in the dual approximation is positive semidefinite: testing its trace pairing on every rank-one matrix gives a nonnegative quadratic form. Symmetry is part of the definition of the dual approximation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("conic-gdnn-duality-sym-mem-knn0"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/ConicGDNN/Duality.sym_mem_knn0"),
                H("Products of cone pullbacks"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For u and v in the product cone, half the sum of uv-transpose and vu-transpose belongs to the zeroth approximation. The Lorentz certificates express both pullbacks as sums of squares of homogeneous linear polynomials. Their product is a sum of squares of homogeneous quadratics. Nonnegative scaling preserves the convex hull of quadratic squares, so finite sums belong to this convex hull."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("conic-gdnn-duality-mulvec-mem-cone"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/ConicGDNN/Duality.mulVec_mem_cone"),
                H("Preservation of the entire product cone"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If a matrix belongs to the dual approximation, multiplying any product-cone vector by that matrix gives another product-cone vector. Trace positivity on the symmetric tests gives nonnegative pairings with every cone member. Self-duality of the product cone then yields the conclusion, including empty orthants and blocks with zero spatial dimension."))),
                DescribeRole.Theorem))));
}
