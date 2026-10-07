using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class Equation47ValueContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact value-link elimination.",
        H("Exact value-link elimination"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47valuecontraction-actual-value-link-contraction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47ValueContraction.actual_value_link_contraction"),
                H("actual value link contraction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Eliminate a genuine nonbase value from a leaf equation by an ordered literal word. The construction retains all other values and gives an exact equivalence with the remaining equations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47valuecontraction-normalized-actual-variable-card"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47ValueContraction.normalized_actual_variable_card"),
                H("normalized actual variable card"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine free value variables plus the actual cycle count equal m times the number of coordinates."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
