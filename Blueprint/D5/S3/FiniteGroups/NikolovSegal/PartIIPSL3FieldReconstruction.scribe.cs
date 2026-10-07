using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIPSL3FieldReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual PSL3 FieldReconstruction.",
        H("Actual PSL3 FieldReconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3fieldreconstruction-projectiveaut-apply"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3FieldReconstruction.projectiveAut_apply"),
                H("projectiveAut apply"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual SL3 automorphism induces its genuine automorphism on the literal central quotient, and application to a quotient representative equals the quotient of its actual image. This constructs model automorphisms for comparison; it does not assert a lift of every bare PSL3 automorphism."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3fieldreconstruction-actual-projective-positive-root-field"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3FieldReconstruction.actual_projective_positive_root_field"),
                H("actual projective positive root field"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given an actual projective automorphism and its additive actions on the three literal positive roots, the actual commutator identities reconstruct one common field automorphism phi. The two simple-root coefficients and their product are retained in all three root equations over every field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3fieldreconstruction-actual-bare-psl3-u-action-model"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3FieldReconstruction.actual_bare_PSL3_U_action_model"),
                H("actual bare PSL3 U action model"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite field of size greater than four and every bare PSL3 automorphism beta, one actual projective g, unit coefficient tuple a, field automorphism phi and graph sign eps describe (conj g^-1)*beta on every actual upper-unitriangular SL3 representative. The derived root geometry and field reconstruction give the quotient model without a general SL3 automorphism lift."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50) (pages228-232). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1 (pages247-248), Sections2 and6, Proposition6.2, and Lemma7.1(a) with its A2 orbital application (pages257-261). These are formal adaptations and consequences of published mathematics, using actual matrix/quotient geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. This package concerns the PSL3 family only. Other families, general-rank SLn/PSLn, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition10.2, width/RBP and strong completeness remain open. Registration remains unfinished under the current suspension.")))));
}
