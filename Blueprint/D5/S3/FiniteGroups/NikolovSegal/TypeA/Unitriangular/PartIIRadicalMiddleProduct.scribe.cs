using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIRadicalMiddleProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Radical Middle Product.",
        H("Type-A Radical Middle Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalmiddleproduct-middle"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalMiddleProduct.Middle"),
                H("Middle"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual middle roots of the printed radical quotient. Both exceptional end pairs are excluded; the corner is not declared zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalmiddleproduct-actual-radical-middle-norm-value"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalMiddleProduct.actual_radical_middle_norm_value"),
                H("actual radical middle norm value"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual original-d-power value: norm witnesses are constructed inside V, and both real row/column coordinates consume the doubled field map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalmiddleproduct-actual-inner-radical-middle-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalMiddleProduct.actual_inner_radical_middle_product"),
                H("actual inner radical middle product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual p263 middle quotient product with determinant-one INNER corrections. One global h is chosen before every full radical target. The result matches all actual middle coordinates; it deliberately leaves boundary and corner residuals for the subsequent original V stages."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalmiddleproduct-actual-middle-residual"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalMiddleProduct.actual_middle_residual"),
                H("actual middle residual"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact remaining matrix after the consumed middle quotient product. All middle entries vanish in P^-1*b; its ordered corner and exceptional boundary coordinates are retained, not silently discarded."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
