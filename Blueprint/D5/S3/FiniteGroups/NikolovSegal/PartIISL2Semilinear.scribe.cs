using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIISL2SemilinearDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II SL2Semilinear.",
        H("Part II SL2Semilinear"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2semilinear-actual-semilinear-sl2-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2Semilinear.actual_semilinear_SL2_scalar_product"),
                H("actual semilinear SL2 scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicitly defined diagonal unit and entrywise field automorphisms satisfy both genuine root laws and therefore the literal scalar PRODUCT interface at length 4M under the stated field and length bounds. Nonsquare diagonal units are allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2semilinear-actual-inner-semilinear-sl2-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2Semilinear.actual_inner_semilinear_SL2_scalar_product"),
                H("actual inner semilinear SL2 scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Arbitrary prescribed inner factors composed with the explicit diagonal and field actions are absorbed into the same correction tuple fixed before all targets. The scalar PRODUCT retains the original beta order and q/e powers under the same quantitative bounds."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), and Lemma 7.1(a) with its A1 application (pages 257-261). These are formal adaptations and consequences of published mathematics, with explicit matrix, fixed-field and Sylow arguments. No originality claim or redistribution of the papers is made. Arbitrary automorphisms are handled for the A1 family; other finite-simple families, the full uniform scalar supplier, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain open.")))));
}
