using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeDualCosetConformalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Conformal Action on Dual-Coset Modules",
        H("Original Conformal Action on Dual-Coset Modules"),
        Blocks(
            Paragraph(Text("D has any finite rank, including zero. Its Gram matrix is integral, symmetric and even on the diagonal. beta is integral. moduleL(H,m) is defined to be the normalized coefficient m+1 of the ACTUAL action of the ORIGINAL omega_D(H). It is not defined from a shifted diagonal formula. Borcherds supplies separate finite supports. Normal-product sums are evaluated on each vector before they are split; no globally finite endomorphism normal sum is asserted. Energy covariance uses both original inverse-Gram equations H G=1 and G H=1 and applies to every original input state and integer mode.")),
            Paragraph(Text("Classical construction context: Bakalov-Kac, math/0402315v1, section 4.1. The imported Sugawara architecture retains Kalle Kytola's Apache-2.0 attribution and VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. The finite reductions and actual-action connections are native mathematical proofs; no external novelty is asserted.")),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-moduleL"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.moduleL"),
                H("moduleL"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-commutatorTerm"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.commutatorTerm"),
                H("commutatorTerm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-commutator-terms-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.commutator_terms_finite"),
                H("commutator terms finite"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-mode-commutator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.mode_commutator"),
                H("mode commutator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-one-mode-commutator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.one_mode_commutator"),
                H("one mode commutator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-minus-one-product-field"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.minus_one_product_field"),
                H("minus one product field"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-action-current"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.action_current"),
                H("action current"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-moduleL-normal"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.moduleL_normal"),
                H("moduleL normal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-energy-covariance"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.energy_covariance"),
                H("energy covariance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem))));
}
