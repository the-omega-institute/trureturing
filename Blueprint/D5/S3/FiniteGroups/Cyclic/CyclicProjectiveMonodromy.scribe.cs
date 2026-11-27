using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Cyclic;

internal sealed class CyclicProjectiveMonodromyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/Cyclic/CyclicProjectiveMonodromy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The projective centralizer action on the generator determines the cyclic product of its associator.",
        H("Cyclic Projective Monodromy"),
        Blocks(
            Describe.Lean(DescribeId.Create("cyclic-projective-power"),
                DeclarationHandle.Create(Prefix + "pow_orderOf_eq_cyclicProduct_smul"),
                H("The cyclic product from the projective power"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The slant multiplier at powers x of g and y = g is α(g,x,g), "
                    + "because α(x,y,g) and α(x,g,y) then coincide. Repeated multiplication by T(g) "
                    + "accumulates these scalars. The last operator is T(1), which is the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eigenphase-detects-cyclic-product"),
                DeclarationHandle.Create(Prefix + "cyclicProduct_coe_eq_eigenvalue_pow"),
                H("Detection on a nonzero eigenvector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On a nonzero eigenvector of T(g), the same operator power acts "
                    + "by the eigenvalue raised to the order of g. Comparing the two scalar actions "
                    + "determines the cyclic product."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cubic-conformal-monodromy"),
                DeclarationHandle.Create(Prefix + "not_mem_of_order_three_monodromy"),
                H("Cubic conformal monodromy obstructs a subgroup restriction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At order three with conformal weight 16/9 + n/3, the cube of the "
                    + "monodromy eigenphase is exp(2πi/3). Every element of a subgroup trivializing the "
                    + "same associator has cyclic product one. The cubic generator therefore lies "
                    + "outside that subgroup."))),
                DescribeRole.Theorem),
            Paragraph(Text("Application to a lattice vertex operator algebra requires the projective law "
                + "for the ambient associator and the phase identification on the actual twisted module. "
                + "The conformal phase uses the generator-flux convention of Evans–Gannon, "
                + "arXiv:1804.11145, equation (2.14).")))));
}
