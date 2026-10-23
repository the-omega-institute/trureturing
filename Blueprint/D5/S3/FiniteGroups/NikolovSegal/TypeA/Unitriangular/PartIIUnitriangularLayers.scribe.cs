using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIUnitriangularLayersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Unitriangular Layers.",
        H("Type-A Unitriangular Layers"),
        Blocks(
            Paragraph(Text("Nikolov--Segal Part II p264 equation(13): the actual leading matrix commutator map of a proper unitriangular matrix. This is the rank-independent linear kernel needed by Proposition6.5, not full U coverage.")),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularlayers-layerstrip"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.layerStrip"),
                H("layerStrip"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal kth superdiagonal matrix, with every other entry zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularlayers-actual-layer-bracket-coordinate"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.actual_layer_bracket_coordinate"),
                H("actual layer bracket coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual matrix Lie commutator, preserving the genuine two unequal coefficients and their order. No constant-coefficient or graph hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularlayers-actual-proper-layer-bracket-surjective"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.actual_proper_layer_bracket_surjective"),
                H("actual proper layer bracket surjective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every prescribed next-layer coordinate is realized by the ACTUAL matrix commutator with a proper matrix. The recursively solved strip is one layer wide; the bound/length does not depend on n. This proves the surjectivity of the printed linear kernel before its group-filtration use."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularlayers-layerdepth"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.LayerDepth"),
                H("LayerDepth"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal matrix height filtration used in printed equation(13)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularlayers-stripunit"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.stripUnit"),
                H("stripUnit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual determinant-one strip witness in the genuine kth layer."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularlayers-actual-proper-group-layer-surjective"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.actual_proper_group_layer_surjective"),
                H("actual proper group layer surjective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Printed equation(13)'s ACTUAL group-commutator leading-layer surjectivity in arbitrary matrix rank. The witness lies in the true kth layer and is constructed, not assumed; the proper matrix is genuine SL. This does not yet assert Proposition6.5 or a full unbounded-rank supplier."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
