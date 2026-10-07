using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIA2GraphReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II A2GraphReconstruction.",
        H("Part II A2GraphReconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphreconstruction-actual-a2-diagonal-field-graph-orbital-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphReconstruction.actual_A2_diagonal_field_graph_orbital_product"),
                H("actual A2 diagonal field graph orbital product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive q, M > q(4q+1), and field size greater than 4(4q+1)^q, three length-M blocks of arbitrary diagonal/field/graph automorphisms and positive divisors e of q admit one three-block correction before every actual U3 target. Ordered actual U3 witnesses use the original q/e powers. Power descent repairs simple-root graph cycles and one central block removes the residual."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphreconstruction-actual-a2-graph-orbital-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphReconstruction.actual_A2_graph_orbital_product"),
                H("actual A2 graph orbital product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under positive q, M > q(4q+1), and field-size > 4(4q+1)^q, arbitrary mixed diagonal/field/graph tuples of length 3M and positive divisors e of q have actual upper-unitriangular PRODUCT coverage. One correction tuple precedes every target, and flattening preserves the ordered q/e-powered values."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
