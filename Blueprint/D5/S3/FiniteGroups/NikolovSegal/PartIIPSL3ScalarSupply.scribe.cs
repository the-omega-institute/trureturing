using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIPSL3ScalarSupplyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual PSL3 ScalarSupply.",
        H("Actual PSL3 ScalarSupply"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3scalarsupply-actual-psl3-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3ScalarSupply.actual_PSL3_scalar_product"),
                H("actual PSL3 scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For q>0, M>q(4q+1), and finite field size greater than 4(4q+1)^q, arbitrary bare PSL3 automorphism and divisor tuples satisfy the literal PartIIScalarProductInput at length25*(3M). Actual upper/lower orbital products and the consumed all-field Fin25 decomposition give every full-group target, with one actual correction tuple chosen before all targets and original q/e powers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3scalarsupply-actual-psl3-uniform-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3ScalarSupply.actual_PSL3_uniform_scalar_product"),
                H("actual PSL3 uniform scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each positive q, choose M=q(4q+1)+1, N=25*(3M), and field cutoff C=4(4q+1)^q before every finite field, arbitrary bare PSL3 automorphism tuple and prescribed divisor tuple. The exact PartIIScalarProductInput has genuine target-independent corrections and actual ordered q/e-powered full-group factor products."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3scalarsupply-actual-psl3-twisted-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3ScalarSupply.actual_PSL3_twisted_product"),
                H("actual PSL3 twisted product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite field of size greater than20 has genuine PSL3 ordered twisted PRODUCT coverage of length450 for arbitrary prescribed pairs of bare automorphism tuples. The actual scalar input with q=1 and M=6 supplies the admitted Lemma4.1; no twisted-coverage assumption is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3scalarsupply-uniform-psl3-transitive-coverage"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3ScalarSupply.uniform_PSL3_transitive_coverage"),
                H("uniform PSL3 transitive coverage"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive q, set L=25*[3*(q(4q+1)+1)], K=4(4q+1)^q, m=L*904*(q+904), and group cutoff max(K^9,20^9). Above that actual PSL3 cardinality cutoff, every finite nonempty coordinate rank and genuine compatible component/permutation tuple satisfies PrescribedCommutatorCoverage, with compatibility k_j(z)(sigma_j(i))=beta_j(i)(z(i)). The literal endpoint has no separate transitivity premise. Actual scalar and450-fold twisted products feed the admitted powered-component reconstruction, retaining the same correction before every target."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50) (pages228-232). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1 (pages247-248), Sections2 and6, Proposition6.2, and Lemma7.1(a) with its A2 orbital application (pages257-261). These are formal adaptations and consequences of published mathematics, using actual matrix/quotient geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. This package concerns the PSL3 family only. Other families, general-rank SLn/PSLn, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition10.2, width/RBP and strong completeness remain open. Registration remains unfinished under the current suspension.")))));
}
