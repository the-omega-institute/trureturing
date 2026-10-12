using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class SLnUnitriangularDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Unitriangular.",
        H("Type-A SLn Unitriangular"),
        Blocks(
            Paragraph(Text("Actual upper unitriangular and upper triangular subgroups of SLn. block-triangular multiplication and inversion are reused.")),
            Describe.Lean(
                DescribeId.Create("typea-slnunitriangular-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.Upper"),
                H("Upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal zero entries strictly below the diagonal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-slnunitriangular-upper-mul-diag"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.upper_mul_diag"),
                H("upper mul diag"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Diagonal multiplication uses only the literal triangular entries."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-slnunitriangular-uplus"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.Uplus"),
                H("Uplus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual full upper-unitriangular subgroup, in every rank and field."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-slnunitriangular-borel"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.Borel"),
                H("Borel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual determinant-one upper triangular subgroup."))),
                DescribeRole.Definition),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
