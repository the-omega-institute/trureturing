using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class SLnUnitriangularCardDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Unitriangular Card.",
        H("Type-A SLn Unitriangular Card"),
        Blocks(
            Paragraph(Text("An actual entry-coordinate bijection for the full upper unitriangular subgroup, over every field and rank.")),
            Describe.Lean(
                DescribeId.Create("typea-slnunitriangularcard-upperentry"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.UpperEntry"),
                H("UpperEntry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One free coordinate for each entry strictly above the diagonal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-slnunitriangularcard-uppermatrix"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.upperMatrix"),
                H("upperMatrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal unitriangular matrix with the prescribed free upper entries."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-slnunitriangularcard-upperchart"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.upperChart"),
                H("upperChart"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every assignment of free entries is an actual determinant-one Uplus element."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-slnunitriangularcard-uppercoordinatesequiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.upperCoordinatesEquiv"),
                H("upperCoordinatesEquiv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual coordinate equivalence, not a group-order or coverage hypothesis."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-slnunitriangularcard-card-uplus-sum"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.card_Uplus_sum"),
                H("card Uplus sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact cardinality as the sum of column dimensions, valid also in ranks0/1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-slnunitriangularcard-card-uplus"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.card_Uplus"),
                H("card Uplus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal free-entry dimension n*(n-1)/2."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
