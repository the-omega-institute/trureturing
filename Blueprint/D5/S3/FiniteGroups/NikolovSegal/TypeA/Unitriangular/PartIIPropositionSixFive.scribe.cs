using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIPropositionSixFiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Proposition Six Five.",
        H("Type-A Proposition Six Five"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiipropositionsixfive-diagonalfieldgraph"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIPropositionSixFive.diagonalFieldGraph"),
                H("diagonalFieldGraph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual prescribed diagonal/field/positive-graph automorphism of SL."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiipropositionsixfive-actual-proposition6-5-uniform-diagonal-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIPropositionSixFive.actual_proposition6_5_uniform_diagonal_product"),
                H("actual proposition6 5 uniform diagonal product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Quantitative actual Proposition6.5 for every rank and prescribed DIAGONAL/field/positive-graph tuple. Length/cutoff are fixed before fields, ranks and all tuples. Actual diagonal corrections and unitriangular u are chosen before all nonlinear targets. Diagonal corrections are allowed by Proposition6.5; this does NOT assert they are inner SL automorphisms and does NOT close the uniform finite-simple scalar supplier."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
