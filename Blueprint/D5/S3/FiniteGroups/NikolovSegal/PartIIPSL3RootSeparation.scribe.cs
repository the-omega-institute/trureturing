using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIPSL3RootSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual PSL3 RootSeparation.",
        H("Actual PSL3 RootSeparation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3rootseparation-actual-normalized-projective-simple-root-permutation"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootSeparation.actual_normalized_projective_simple_root_permutation"),
                H("actual normalized projective simple root permutation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite field of size greater than four, a genuine projective automorphism preserving actual U3, diagonal torus and central root preserves the two actual simple root subgroups as a pair. Quotient torus preimages and actual kernel fixed-point arithmetic prove the alternatives, without assuming their images."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3rootseparation-actual-bare-psl3-root-normalization"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootSeparation.actual_bare_PSL3_root_normalization"),
                H("actual bare PSL3 root normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite field of size greater than four, every bare PSL3 automorphism admits one actual projective correction preserving U3 and the central root, with the two simple roots either retained or swapped. The real subgroup geometry supplies the root alternatives; no root-image or lift oracle is used."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50) (pages228-232). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1 (pages247-248), Sections2 and6, Proposition6.2, and Lemma7.1(a) with its A2 orbital application (pages257-261). These are formal adaptations and consequences of published mathematics, using actual matrix/quotient geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. This package concerns the PSL3 family only. Other families, general-rank SLn/PSLn, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition10.2, width/RBP and strong completeness remain open. Registration remains unfinished under the current suspension.")))));
}
