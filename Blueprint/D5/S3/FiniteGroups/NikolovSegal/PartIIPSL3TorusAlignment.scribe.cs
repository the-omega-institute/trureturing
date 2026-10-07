using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIPSL3TorusAlignmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual PSL3 TorusAlignment.",
        H("Actual PSL3 TorusAlignment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3torusalignment-actual-projective-u-torus-alignment"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3TorusAlignment.actual_projective_U_torus_alignment"),
                H("actual projective U torus alignment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over a finite field, a genuine projective automorphism preserving actual U3 admits an actual upper-unitriangular SL3 correction whose projective inner conjugation preserves both U3 and the projective diagonal torus. Averaging uses the whole SL3 preimage of the torus image and its exact cardinality (|F|-1)^2, retaining the nontrivial scalar center."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3torusalignment-actual-bare-psl3-u-t-central-root-normalization"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3TorusAlignment.actual_bare_PSL3_U_T_central_root_normalization"),
                H("actual bare PSL3 U T central root normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every finite field, every bare PSL3 automorphism has one actual projective inner normalization preserving actual U3, the projective diagonal torus and its computed central root. The genuine Sylow correction and whole-preimage torus alignment are composed without an SL3 automorphism lift."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50) (pages228-232). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1 (pages247-248), Sections2 and6, Proposition6.2, and Lemma7.1(a) with its A2 orbital application (pages257-261). These are formal adaptations and consequences of published mathematics, using actual matrix/quotient geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. This package concerns the PSL3 family only. Other families, general-rank SLn/PSLn, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition10.2, width/RBP and strong completeness remain open. Registration remains unfinished under the current suspension.")))));
}
