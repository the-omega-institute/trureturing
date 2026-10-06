using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIISL2ProjectiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II SL2Projective.",
        H("Part II SL2Projective"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2projective-actual-pgl2-semilinear-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2Projective.actual_PGL2_semilinear_scalar_product"),
                H("actual PGL2 semilinear scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The induced centre-quotient actions of arbitrary invertible matrices and field automorphisms satisfy the PSL2 scalar PRODUCT interface. Actual corrected powers and ordered products transfer through the quotient; the witnesses and corrections are group elements."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2projective-uniform-pgl2-semilinear-scalar-products"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2Projective.uniform_PGL2_semilinear_scalar_products"),
                H("uniform PGL2 semilinear scalar products"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each positive q, choose M = q(2q+1)+1, length 4M and cutoff [2(2q+1)^q]^4 before the finite field and all invertible-matrix, field-action and divisor tuples. The bound on the actual group cardinality forces the required field bound and supplies the literal projective scalar PRODUCT."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), and Lemma 7.1(a) with its A1 application (pages 257-261). These are formal adaptations and consequences of published mathematics, with explicit matrix, fixed-field and Sylow arguments. No originality claim or redistribution of the papers is made. Arbitrary automorphisms are handled for the A1 family; other finite-simple families, the full uniform scalar supplier, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain open.")))));
}
