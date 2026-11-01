using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class GaussianSewingLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "GaussianSewingLimit", H("GaussianSewingLimit"), Blocks(
            Paragraph(Text("Hilbert-Schmidt coordinate tails control the ordered resolvents. The exact padded inverse retains the identity on omitted coordinates, whose mixed-vector contribution tends to zero.")),
            N("compressed_tendsto","HS tails imply the required operator norm limit","Two-coordinate Hilbert-Schmidt tails tend to zero. Square-summable-column synthesis bounds the operator norm by the Hilbert-Schmidt size, and equality on the coordinate basis identifies the synthesized operator with the compression error."),
            N("projection_vector_tendsto","Only strong coordinate projection convergence","For each actual l2 vector, the coordinate projection is its finite sum of coordinate basis components. The unconditional l2 expansion proves convergence to that vector. There is no operator norm convergence claim for P_F to the identity."),
            N("resolvent_tendsto","Ordered inverse convergence","The two given strict contraction bounds imply 1-BA is a unit. Apply continuity of Ring.inverse at that genuine unit to the operator norm limits of the compressed B and A. The order BA is preserved."),
            N("mixed_complement_tendsto","The omitted-coordinate correction","The exact correction is the bounded bilinear functional r applied to (1-P_F)s. Its limit is zero by the strong convergence on the actual l2 column s. This avoids a false norm limit of P_F-1."),
            N("padded_inverse","Exact complement in the padded inverse","The finite coordinate inclusion J_F and its adjoint satisfy J_F^*J_F=1 and J_F J_F^*=P_F. Embedding the finite inverse and using the two actual strict contraction bounds gives (1-Bbar_F Abar_F)^-1 = (1-P_F)+J_F(1-b_F a_F)^-1 J_F^*. The complement term is retained exactly."),
            N("padded_inverse_mul","The diagonal effective blocks","Multiplication by Bbar_F kills the omitted-coordinate complement, giving N_F Bbar_F=J_F(1-b_F a_F)^-1 b_F J_F^*. Swapping A and B supplies the other diagonal block."),
            N("bilinear_embedded","Native finite matrices and l2 rows","Expand the finite Euclidean basis and use the true coordinate restriction adjoint. Pairing r against the embedded finite operator applied to s is exactly the finite bilinear matrix sum sum_ij r_i M_ij s_j, without conjugation.")), []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("gaussiansewinglimit-" + name.Replace(".", "-").Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
