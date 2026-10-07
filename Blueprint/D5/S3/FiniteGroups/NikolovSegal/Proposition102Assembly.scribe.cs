using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class Proposition102AssemblyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional chosen-length centreless assembly.",
        H("Conditional chosen-length centreless assembly"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-proposition102assembly-prescribed-coverage-from-published-products"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Proposition102Assembly.prescribed_coverage_from_published_products"),
                H("prescribed coverage from published products"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume q and M positive, m at least M(4+2D)(q+4+2D), and the actual coordinate law. Literal scalar PRODUCT coverage for every M-tuple of automorphisms and periods, together with twisted PRODUCT coverage at D, gives one correction tuple y before every target. Hall-selected good intervals solve light components; constructed crossings solve heavy components."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-proposition102assembly-uniform-transitive-supplier-of-published-products"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Proposition102Assembly.uniform_transitive_supplier_of_published_products"),
                H("uniform transitive supplier of published products"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Uniform twisted existence at a positive D and uniform large-simple scalar PRODUCT existence at positive M(q) and cutoff C(q) imply the literal uniform transitive supplier. The group, arbitrary genuine automorphism tuple and target all follow the uniform lengths and cutoffs. Both PRODUCT existence premises remain hypotheses."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
