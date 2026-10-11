using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIFieldMapsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II FieldMaps.",
        H("Part II FieldMaps"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiifieldmaps-lemma7-1"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIFieldMaps.lemma7_1"),
                H("lemma7 1"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite field, positive q, M > q(cq+1), and field size greater than c(cq+1)^q, arbitrary field automorphisms, nonzero coefficients, positive divisors d of q, and weights between 1 and c admit one nonzero lambda tuple whose sum of genuine fieldValue maps is surjective. The coefficients are fixed before every additive target. The proof derives fixed-field power bounds and uses the one-map or two-map cases."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), and Lemma 7.1(a) with its A1 application (pages 257-261). These are formal adaptations and consequences of published mathematics, with explicit matrix, fixed-field and Sylow arguments. No originality claim or redistribution of the papers is made. Arbitrary automorphisms are handled for the A1 family; other finite-simple families, the full uniform scalar supplier, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain open.")))));
}
