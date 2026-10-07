using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class FiniteGeneratingGrowthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict growth of finite product sets.",
        H("Strict growth of finite product sets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-finitegeneratinggrowth-finite-right-stable-inv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/FiniteGeneratingGrowth.finite_right_stable_inv"),
                H("finite right stable inv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite set stable under right multiplication by g is also stable under g inverse, by actual finite injectivity and surjectivity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-finitegeneratinggrowth-card-mul-strict-of-generating"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/FiniteGeneratingGrowth.card_mul_strict_of_generating"),
                H("card mul strict of generating"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a nonempty proper finite set A and a finite generating set T containing one, the actual product set A*T has strictly larger cardinality."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
