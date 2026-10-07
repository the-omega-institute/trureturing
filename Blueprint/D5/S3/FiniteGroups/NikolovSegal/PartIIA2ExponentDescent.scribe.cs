using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIA2ExponentDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II A2ExponentDescent.",
        H("Part II A2ExponentDescent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2exponentdescent-actual-a2-power-value-descent"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2ExponentDescent.actual_A2_power_value_descent"),
                H("actual A2 power value descent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For automorphisms preserving actual upper-unitriangular SL3 matrices, upper-unitriangular witnesses x and arbitrary natural powers r, single-power witnesses c give the same ordered product as the r-powered values, up to one actual central factor upper3(0,0,z). Neither the factor order nor the central error is discarded."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2exponentdescent-actual-a2-power-descent-and-central-reconstruction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2ExponentDescent.actual_A2_power_descent_and_central_reconstruction"),
                H("actual A2 power descent and central reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume positive q, M > q(2q+1), field size greater than 2(2q+1)^q, upper-unitriangular-preserving gamma, and prescribed beta acting on the central root by nonzero chi times a field automorphism. For positive divisors e of q, one beta correction tuple is chosen before all upper-unitriangular x and all natural powers r. Single-power gamma witnesses and q/e-powered central witnesses then reconstruct the original ordered powered product exactly."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
