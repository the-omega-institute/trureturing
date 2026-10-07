using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIA2ScalarSupplyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II A2ScalarSupply.",
        H("Part II A2ScalarSupply"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2scalarsupply-actual-sl3-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2ScalarSupply.actual_SL3_scalar_product"),
                H("actual SL3 scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive q, M > q(4q+1), and finite field size greater than 4(4q+1)^q, every bare SL3 automorphism tuple satisfies PartIIScalarProductInput at length 25*(3M). For each positive divisor tuple e of q, one genuine correction tuple precedes every full-group target, and actual factor tuples produce the ordered q/e-powered values. The proved 25-factor decomposition combines actual upper and lower orbital products."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2scalarsupply-actual-sl3-uniform-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2ScalarSupply.actual_SL3_uniform_scalar_product"),
                H("actual SL3 uniform scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each positive q, take M=q(4q+1)+1, N=25*(3M), and C=4(4q+1)^q. Length N and field cutoff C are chosen before every finite field F of size greater than C, every bare SL3 automorphism tuple beta and every divisor tuple e. The literal scalar PRODUCT fixes one correction before all full-group targets and retains q/e powers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2scalarsupply-actual-sl3-twisted-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2ScalarSupply.actual_SL3_twisted_product"),
                H("actual SL3 twisted product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite field of size greater than 20, arbitrary pairs of prescribed bare SL3 automorphism tuples have genuine ordered twisted PRODUCT coverage of length 450. The q=1, M=6 scalar theorem supplies Lemma 4.1 with an actual PRODUCT input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2scalarsupply-uniform-sl3-transitive-coverage"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2ScalarSupply.uniform_SL3_transitive_coverage"),
                H("uniform SL3 transitive coverage"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive q set L=25*[3*(q(4q+1)+1)], K=4(4q+1)^q, m=904L(q+904), and C=max(K^9,20^9). Above C in actual SL3 cardinality, every finite nonempty coordinate rank and every compatible genuine component/permutation tuple satisfy PrescribedCommutatorCoverage. Compatibility is k_j(z)(sigma_j(i))=beta_j(i)(z(i)). The mixed powered-component reconstruction uses the proved scalar and 450-fold twisted products, preserving global correction-before-target order; this endpoint needs no separate transitivity premise."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
