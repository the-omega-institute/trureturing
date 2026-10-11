using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIUnitriangularActionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Unitriangular Actions.",
        H("Type-A Unitriangular Actions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularactions-firstlayerconstant"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularActions.FirstLayerConstant"),
                H("FirstLayerConstant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine constant vector on the first superdiagonal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularactions-fieldaut"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularActions.fieldAut"),
                H("fieldAut"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Entrywise field action on actual determinant-one matrices, every rank."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularactions-heighttorus"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularActions.heightTorus"),
                H("heightTorus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual height torus diag(1,lambda^-1,lambda^-2,...), as a GL conjugation on SL. It has no determinant-root or rank restriction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularactions-positivegraph"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularActions.positiveGraph"),
                H("positiveGraph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pinned positive graph automorphism. The alternating torus corrects inverse-transpose's first-layer minus signs, so simple roots are permuted with coefficient +1, exactly as in printed Lemma9.1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularactions-fieldgraphaut"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularActions.fieldGraphAut"),
                H("fieldGraphAut"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual field/positive-graph action, not a supplied component-law premise."))),
                DescribeRole.Definition),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
