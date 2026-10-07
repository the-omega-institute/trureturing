using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIISL2ScalarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II SL2Scalar.",
        H("Part II SL2Scalar"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2scalar-actual-normalized-sl2-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2Scalar.actual_normalized_SL2_scalar_product"),
                H("actual normalized SL2 scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite fields satisfying M > q(2q+1) and field size greater than 2(2q+1)^q, automorphisms with the stated upper and lower semilinear laws satisfy the literal PartIIScalarProductInput at length 4M. Four consecutive blocks use an ordered ULUL matrix decomposition. The positive divisors e of q give powers q/e and one correction tuple before every full group target."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), and Lemma 7.1(a) with its A1 application (pages 257-261). These are formal adaptations and consequences of published mathematics, with explicit matrix, fixed-field and Sylow arguments. No originality claim or redistribution of the papers is made. Arbitrary automorphisms are handled for the A1 family; other finite-simple families, the full uniform scalar supplier, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain open.")))));
}
