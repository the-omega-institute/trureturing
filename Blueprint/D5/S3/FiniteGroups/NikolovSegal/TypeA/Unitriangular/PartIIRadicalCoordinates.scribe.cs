using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIRadicalCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Radical Coordinates.",
        H("Type-A Radical Coordinates"),
        Blocks(
            Paragraph(Text("Actual radical of the first-row/last-column parabolic, Part II pp262–263. The corner is retained, including its ordered cross term.")),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalcoordinates-radical"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.radical"),
                H("radical"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine determinant-one radical matrix with all three coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalcoordinates-actual-radical-mul"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_mul"),
                H("actual radical mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact noncommutative radical multiplication: only the first row of THE LEFT factor pairs with the last column of THE RIGHT factor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalcoordinates-actual-radical-inverse"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_inverse"),
                H("actual radical inverse"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual inverse, including the central quadratic correction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalcoordinates-inradical"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.InRadical"),
                H("InRadical"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal first-row/last-column subgroup predicate, with genuine unitriangularity. This is not an abstract coverage assumption."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalcoordinates-actual-radical-coordinates"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_coordinates"),
                H("actual radical coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual radical target has these genuine matrix coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalcoordinates-actual-radical-row"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_row"),
                H("actual radical row"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual noncorner first-row coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalcoordinates-actual-radical-product-mem"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_product_mem"),
                H("actual radical product mem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Closure is proved for the literal matrix support, not postulated."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalcoordinates-actual-radical-product-row-column"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_product_row_column"),
                H("actual radical product row column"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact additive quotient coordinates, while the corner still uses actual_radical_mul's noncommutative cross term."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
