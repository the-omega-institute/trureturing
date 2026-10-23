using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIUnitriangularGraphLayersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Unitriangular Graph Layers.",
        H("Type-A Unitriangular Graph Layers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangulargraphlayers-mirrorweight"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.mirrorWeight"),
                H("mirrorWeight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Printed p265 symmetric alternating torus, as integral diagonal weights. For odd matrix size, opposite sides of the central unit have inverse weights; for even size the alternating zero and minus-one pattern works modulo scalars."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangulargraphlayers-actual-mirror-odd-root-weights"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.actual_mirror_odd_root_weights"),
                H("actual mirror odd root weights"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two quantitative torus facts are derived for ACTUAL matrix indices, including central-crossing roots. No sign/commutation law input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangulargraphlayers-mirrortorus"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.mirrorTorus"),
                H("mirrorTorus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine p265 reflection-invariant torus on arbitrary-rank SL."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangulargraphlayers-actual-mirror-field-graph-doubled-power"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.actual_mirror_field_graph_doubled_power"),
                H("actual mirror field graph doubled power"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual doubled-power odd-root transport for arbitrary prescribed field/positive-graph actions. Reflection-invariant torus weights and the component formula are proved, not assumed. This is the p265--266 scalar bridge; it does not assume scalar or matrix product coverage."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
