using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry;

internal sealed class PartIISLnSmallUClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Small UClassification.",
        H("Type-A SLn Small UClassification"),
        Blocks(
            Paragraph(Text("Actual common field/graph and whole-U action in rank>=5/cardF>2. The triangle/graph/generation kernels are reused unchanged.")),
            Describe.Lean(
                DescribeId.Create("typea-partiislnsmalluclassification-psl-bare-full-u-diagonal-field-graph"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnSmallUClassification.psl_bare_full_U_diagonal_field_graph"),
                H("psl bare full U diagonal field graph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n>4 and a finite field of size greater than2 in its defining prime characteristic, one inner correction of every bare projective automorphism agrees on the entire upper unitriangular subgroup with a diagonal, common field and optional graph action. The corrected action also preserves the actual projective diagonal torus."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
