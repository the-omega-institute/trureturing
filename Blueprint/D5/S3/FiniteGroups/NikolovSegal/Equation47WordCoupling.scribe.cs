using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class Equation47WordCouplingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal words and twisted products.",
        H("Literal words and twisted products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47wordcoupling-crossing-substitution"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47WordCoupling.crossing_substitution"),
                H("crossing substitution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two distinct keys occurring with opposite signs in a literal crossing can be replaced by genuine scalar witnesses for a twisted product, while every other key is retained. All automorphisms are arbitrary and the word order is preserved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47wordcoupling-solve-extracted-word"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47WordCoupling.solve_extracted_word"),
                H("solve extracted word"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual D-step extraction and the literal twisted PRODUCT input solve the original word for every target."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
