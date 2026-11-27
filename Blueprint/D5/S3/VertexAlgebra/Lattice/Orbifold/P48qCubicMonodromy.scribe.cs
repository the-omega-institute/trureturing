using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qCubicMonodromyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicMonodromy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual P48q cubic twisted carrier has a conformal rotation with a primitive scalar cube.",
        H("Conformal Monodromy of the P48q Cubic Twisted Module"),
        Blocks(
            Describe.Lean(DescribeId.Create("p48q-conformal-monodromy-eigenphase"),
                DeclarationHandle.Create(Prefix + "conformalMonodromy_native_conformal_eigenvector"),
                H("Phase of the actual conformal coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The conformal coefficient at cover exponent −6 is the full zero mode. "
                    + "On a nonzero joint coefficient of an eigenvector, the zero mode determines the weight "
                    + "as 16/9 plus the grading index divided by three. Multiplying the normalized grading "
                    + "rotation by the vacuum phase gives exp(2πi times the weight) on the eigenvector."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("p48q-conformal-monodromy-cube"),
                DeclarationHandle.Create(Prefix + "conformalMonodromy_cube"),
                H("The primitive scalar cube"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized grading rotation cubes to the identity. The vacuum "
                    + "phase cubed is exp(2πi/3), since three times 16/9 is 5 + 1/3."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("p48q-cyclic-product-from-monodromy"),
                DeclarationHandle.Create(Prefix + "cyclicProduct_eq_zeta_of_nativeMonodromy"),
                H("The ambient cyclic product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given a projective centralizer action for the specified ambient "
                    + "associator with the constructed conformal rotation as its generator action, "
                    + "the operator power formula identifies the cyclic associator product with "
                    + "exp(2πi/3). Evaluating the operator identity on the nonzero vacuum cancels the vector. "
                    + "A subgroup trivializing the associator cannot contain the generator."))),
                DescribeRole.Theorem))));
}
