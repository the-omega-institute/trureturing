using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIITransvectionSupplyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II TransvectionSupply.",
        H("Part II TransvectionSupply"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiitransvectionsupply-actual-transvection-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIITransvectionSupply.actual_transvection_scalar_product"),
                H("actual transvection scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary finite matrix index type and distinct i,j, let q be positive, M > q(2q+1), and let the finite field have size greater than 2(2q+1)^q. Suppose every prescribed automorphism acts on the actual (i,j) root as chi times a field automorphism, with chi nonzero. For positive exponents d dividing q, one determinant-one correction tuple is chosen before every field target; the ordered d-powered corrected values cover the actual root subgroup. The length and cutoff are independent of the matrix rank."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
