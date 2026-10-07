using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIA2RootNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II A2RootNormalization.",
        H("Part II A2RootNormalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2rootnormalization-actual-positive-root-field"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootNormalization.actual_positive_root_field"),
                H("actual positive root field"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If a genuine SL3 automorphism acts on each positive root through additive equivalences f0,f1,f2, there is one field automorphism phi with f0(t)=f0(1)*phi(t), f1(t)=f1(1)*phi(t), and f2(t)=f0(1)*f1(1)*phi(t). The root commutator relates all three parameter maps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2rootnormalization-actual-root-preserving-a2-orbital-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootNormalization.actual_root_preserving_A2_orbital_product"),
                H("actual root preserving A2 orbital product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive q, M > q(2q+1), field size greater than 2(2q+1)^q, and a length-3M tuple preserving each actual positive-root subgroup, positive divisors e of q yield one correction tuple before every upper-unitriangular target. The ordered q/e-powered values use actual upper-unitriangular witnesses; the common field law is derived from root preservation."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
