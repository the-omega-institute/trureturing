using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo;

internal sealed class PartIISLnF2TransvectionRecognitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn F2 Transvection Recognition.",
        H("Type-A SLn F2 Transvection Recognition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2transvectionrecognition-top-commutes-u"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2TransvectionRecognition.top_commutes_U"),
                H("top commutes U"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual top-right root element centralizes the whole U, using the root generation body rather than a centre oracle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2transvectionrecognition-normalized-fixes-top"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2TransvectionRecognition.normalized_fixes_top"),
                H("normalized fixes top"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A U-normalized bare automorphism fixes the unique nonidentity actual central-U top-right transvection over F2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2transvectionrecognition-permutationsl"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2TransvectionRecognition.permutationSL"),
                H("permutationSL"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In a two-element field the actual permutation matrix has determinant1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2transvectionrecognition-transvection-conjugate-top"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2TransvectionRecognition.transvection_conjugate_top"),
                H("transvection conjugate top"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every literal elementary transvection is genuinely conjugate to the actual central-U element in SLn(F2), including the determinant-one condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2transvectionrecognition-conjugate-transvection-minors"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2TransvectionRecognition.conjugate_transvection_minors"),
                H("conjugate transvection minors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal rank-one minors of a conjugated elementary transvection; no rank/eigenvector or transvection-recognition premise is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2transvectionrecognition-normalized-transvection-image-minors"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2TransvectionRecognition.normalized_transvection_image_minors"),
                H("normalized transvection image minors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("U-normalization forces actual rank-one-minor equations on every image of an elementary transvection, derived from the full-group conjugacy relation."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
