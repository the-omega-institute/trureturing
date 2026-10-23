using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIRadicalInnerTorusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Radical Inner Torus.",
        H("Type-A Radical Inner Torus"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalinnertorus-actual-diagonal-inner-normalization"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus.actual_diagonal_inner_normalization"),
                H("actual diagonal inner normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The determinant equality is exactly the inner-correction obstruction. The actual determinant-one matrix is constructed and its FULL action is proved for every field/graph tuple, before any coordinate targets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalinnertorus-radicaldiagonal"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus.radicalDiagonal"),
                H("radicalDiagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual p263 diagonal pattern. Its two exceptional entries absorb all prescribed determinant obstruction; the length of the middle block has no effect on the scalar exponent."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalinnertorus-actual-radical-inner-torus"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus.actual_radical_inner_torus"),
                H("actual radical inner torus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact determinant-one INNER correction construction used by PartII Proposition6.7, p263. This consumes the actual determinant and full automorphism laws above, and leaves no supplied diagonal-normalization premise. The middle tuple is genuinely constant, even in unbounded rank. It is the correction step, not radical value coverage."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
