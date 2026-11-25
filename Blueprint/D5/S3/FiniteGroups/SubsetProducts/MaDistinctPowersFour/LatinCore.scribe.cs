using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour;

internal sealed class MaLatinCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Row and column injectivity and the three array outcomes.",
        H("Row and column injectivity and the three array outcomes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-latincore-latin"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore.Latin"),
                H("Latin"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every row and every column is injective."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-latincore-rainbow"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore.Rainbow"),
                H("Rainbow"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A column permutation selects pairwise distinct values."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-latincore-equalcolumns"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore.EqualColumns"),
                H("EqualColumns"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every symbol in each source column occurs in every target column."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-latincore-motif"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore.Motif"),
                H("Motif"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Three distinct rows and columns carry four specified cell equalities and a fifth inequality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-latincore-allfin"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore.allFin"),
                H("allFin"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a Boolean function on Fin n, take the conjunction of its values over List.finRange n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-latincore-anyfin"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore.anyFin"),
                H("anyFin"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a Boolean function on Fin n, take the disjunction of its values over List.finRange n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-latincore-injectiveb"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore.injectiveB"),
                H("injectiveB"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a map from Fin n to Fin n, check that p(i) and p(j) differ for every pair i < j."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-latincore-allfin-true"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore.allFin_true"),
                H("allFin_true"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The universal Boolean test is true exactly when the predicate is true at each index."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ma-latincore-anyfin-true"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore.anyFin_true"),
                H("anyFin_true"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existential Boolean test is true exactly when there is a true index."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ma-latincore-injective-of-injectiveb"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore.injective_of_injectiveB"),
                H("injective_of_injectiveB"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An ordered-pair test with no equal outputs implies injectivity."))),
                DescribeRole.Theorem))));
}
