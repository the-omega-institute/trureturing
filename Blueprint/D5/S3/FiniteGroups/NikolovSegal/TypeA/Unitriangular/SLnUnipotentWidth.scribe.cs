using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class SLnUnipotentWidthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Unipotent Width.",
        H("Type-A SLn Unipotent Width"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-slnunipotentwidth-four-factor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentWidth.four_factor"),
                H("four factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rank-independent unitriangular factorization over every field, including the trivial ranks. Last-row radicals are interleaved through the genuine Levi factors; no new factors accumulate when the rank increases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-slnunipotentwidth-upper-iff-literal"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentWidth.upper_iff_literal"),
                H("upper iff literal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact adapter to the prescribed literal upper-unitriangular carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-slnunipotentwidth-alternating-unipotent-25"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentWidth.alternating_unipotent_25"),
                H("alternating unipotent 25"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal arbitrary-rank, every-field full SLn width at the exact prescribed alternating length25. Identity padding retains the factor order and parity."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
