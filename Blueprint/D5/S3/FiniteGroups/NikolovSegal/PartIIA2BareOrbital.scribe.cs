using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIA2BareOrbitalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II A2BareOrbital.",
        H("Part II A2BareOrbital"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2bareorbital-actual-bare-sl3-u-action-model"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2BareOrbital.actual_bare_SL3_U_action_model"),
                H("actual bare SL3 U action model"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite field of size greater than four and every bare SL3 automorphism beta, there are an actual inner conjugating matrix, one diagonal unit tuple, one field automorphism and one graph choice agreeing with the corrected beta on every actual U3 element. No full-group classification hypothesis is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2bareorbital-actual-bare-sl3-orbital-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2BareOrbital.actual_bare_SL3_orbital_product"),
                H("actual bare SL3 orbital product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive q, M > q(4q+1), field size greater than 4(4q+1)^q, arbitrary three-by-M bare SL3 automorphisms and positive divisors e of q, one actual correction is fixed before every U3 target. Actual U3 factor tuples give the ordered three-block PRODUCT with exact q/e powers. Root geometry derives the common action models."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2bareorbital-actual-bare-sl3-ordered-orbital-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2BareOrbital.actual_bare_SL3_ordered_orbital_product"),
                H("actual bare SL3 ordered orbital product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive q, M > q(4q+1), and field size greater than 4(4q+1)^q, every bare SL3 automorphism tuple of length 3M and every positive divisor tuple e of q has actual U3 PRODUCT coverage. One correction precedes all U3 targets, and the ordered factor witnesses remain in U3 with powers q/e."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
