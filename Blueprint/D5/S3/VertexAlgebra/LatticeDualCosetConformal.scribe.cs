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
                DescribeId.Create("latticedualcosetconformal-modulel"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.moduleL"),
                H("moduleL"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("L_m is exactly action_D,beta(omega_D(H)) at normalized mode m+1 on the actual full carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-commutatorterm"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.commutatorTerm"),
                H("commutatorTerm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The j term is binom(p,j) times the module mode p+q-j of the ORIGINAL state product a_j b."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-commutator-terms-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.commutator_terms_finite"),
                H("commutator terms finite"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Original nonnegative state products have finite support before binomial weighting. Their module endomorphism terms therefore have finite support even for negative p."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-mode-commutator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.mode_commutator"),
                H("mode commutator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary original a,b and all integer p,q, the commutator of their actual module modes equals the finite sum of binomially weighted original state-product modes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-one-mode-commutator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.one_mode_commutator"),
                H("one mode commutator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mode-one commutator contains exactly the original products a_0 b and a_1 b, with output modes q+1 and q."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-minus-one-product-field"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.minus_one_product_field"),
                H("minus one product field"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual field of the original minus-one product equals the normal product of the actual module fields. The two separately finite vectorwise halves ADD."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-action-current"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.action_current"),
                H("action current"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer m, the actual module current is the original neutral current plus beta_i delta(m,0) times identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-modulel-normal"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.moduleL_normal"),
                H("moduleL normal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual original omega mode is one half of the H-weighted sum of normal products of the actual module currents."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-energy-covariance"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.energy_covariance"),
                H("energy covariance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original state a and integer q, [L_0,action(a)_q]=action(L_0_original a)_q-(q+1)action(a)_q. The original two-sided inverse identities are explicit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-ward-commutator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.ward_commutator"),
                H("ward commutator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer conformal mode m and original input mode q, the full Ward sum retains all original L_(j-1) a terms with binomial(m+1,j). Finite original state-product support precedes binomial weighting."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformal-translation-covariance"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetConformal.translation_covariance"),
                H("translation covariance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ACTUAL original-omega mode L_-1 satisfies [L_-1,action(a)_q]=-q action(a)_(q-1) for every original state a."))),
                DescribeRole.Theorem))));
}
