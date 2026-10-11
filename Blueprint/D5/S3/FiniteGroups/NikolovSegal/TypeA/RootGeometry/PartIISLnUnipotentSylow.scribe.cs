using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry;

internal sealed class PartIISLnUnipotentSylowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Unipotent Sylow.",
        H("Type-A SLn Unipotent Sylow"),
        Blocks(
            Paragraph(Text("The actual SLn upper-unitriangular subgroup is Sylow in every finite field of defining characteristic. GL cardinality and Sylow pullback avoid a redundant SL group-order computation.")),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentsylow-card-gl-factor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.card_GL_factor"),
                H("card GL factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine GL order split into its upper-entry power and remaining factors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentsylow-glupper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.GLupper"),
                H("GLupper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual image of the literal Uplus in GL."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentsylow-glupper-index"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.GLupper_index"),
                H("GLupper index"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual GL index of Uplus, derived from GL order and proved entry bijection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentsylow-uplus-ispgroup"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.Uplus_isPGroup"),
                H("Uplus isPGroup"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Defining-characteristic p-group recognition from the actual cardinality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentsylow-glupper-index-not-dvd"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.GLupper_index_not_dvd"),
                H("GLupper index not dvd"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every remaining GL index factor is prime to the actual field characteristic."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentsylow-uplussylow"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.UplusSylow"),
                H("UplusSylow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A genuine Sylow with exactly the literal SLn unitriangular carrier. It is the injective pullback of the actual GL-image Sylow."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentsylow-uplussylow-tosubgroup"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.UplusSylow_toSubgroup"),
                H("UplusSylow toSubgroup"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal underlying-subgroup equality, not an assumed Sylow recognition premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentsylow-exists-uplus-sylow"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.exists_Uplus_sylow"),
                H("exists Uplus sylow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every prime, every finite field of characteristic p and every rank, including0/1."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
