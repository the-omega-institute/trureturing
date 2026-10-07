using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIA2RootSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II A2RootSeparation.",
        H("Part II A2RootSeparation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2rootseparation-fixed-first-torus-kernel-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.fixed_first_torus_kernel_iff"),
                H("fixed first torus kernel iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite field of size greater than four and g in actual U3, commuting with every diagonalPair(x,x) is equivalent to membership in the first simple-root subgroup."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2rootseparation-fixed-second-torus-kernel-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.fixed_second_torus_kernel_iff"),
                H("fixed second torus kernel iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite field of size greater than four and g in actual U3, commuting with every diagonalPair((x*x) inverse,x) is equivalent to membership in the second simple-root subgroup."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2rootseparation-actual-torus-kernel-classification"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.actual_torus_kernel_classification"),
                H("actual torus kernel classification"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let L be a subgroup of the actual diagonal torus with cardinality equal to that of F units. If L centralizes upper3(a,b,c), where a or b is nonzero, then L is exactly firstKernel or secondKernel. The statement retains the exact cardinal equality and requires no field-size lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2rootseparation-actual-normalized-simple-root-permutation"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.actual_normalized_simple_root_permutation"),
                H("actual normalized simple root permutation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over a finite field of size greater than four, an automorphism preserving actual U3, the torus and the central root either preserves both simple-root subgroups or exchanges them. The possibilities follow from actual torus kernels and root incidence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2rootseparation-actual-bare-sl3-root-normalization"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.actual_bare_SL3_root_normalization"),
                H("actual bare SL3 root normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over a finite field of size greater than four, every bare SL3 automorphism has an actual inner correction preserving U3 and the central root and either preserving both simple roots or exchanging them. These subgroup laws are conclusions, not additional premises."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
