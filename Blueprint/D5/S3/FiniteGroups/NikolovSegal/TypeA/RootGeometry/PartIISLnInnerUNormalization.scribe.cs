using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry;

internal sealed class PartIISLnInnerUNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Inner UNormalization.",
        H("Type-A SLn Inner UNormalization"),
        Blocks(
            Paragraph(Text("A pre-target inner correction preserves actual full U and Borel in SLn and PSLn. Sylow conjugacy and normalizer functoriality are consumed; the carrier, Sylow and normalizer proofs remain unchanged. No automorphism/root/field/graph classification is asserted.")),
            Describe.Lean(
                DescribeId.Create("typea-partiislninnerunormalization-sl-inner-u-borel-correction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnInnerUNormalization.sl_inner_U_Borel_correction"),
                H("sl inner U Borel correction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every bare SLn automorphism admits a genuine determinant-one inner correction, chosen before all targets, preserving the actual full Uplus and actual Borel, with exact subgroup maps and iff membership."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislninnerunormalization-psl-inner-u-borel-correction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnInnerUNormalization.psl_inner_U_Borel_correction"),
                H("psl inner U Borel correction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every bare PSLn automorphism admits a genuine projective inner correction preserving the actual quotient Uplus and the quotient image of Borel. No lift to SLn, classifying law, size bound or rank restriction is required."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
