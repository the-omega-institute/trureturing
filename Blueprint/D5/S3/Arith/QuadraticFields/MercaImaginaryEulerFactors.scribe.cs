using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.QuadraticFields;

internal sealed class MercaImaginaryEulerFactorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/QuadraticFields/MercaImaginaryEulerFactors.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Imaginary Quadratic Euler Factors", H("Actual Imaginary Quadratic Euler Factors"), Blocks(
            Node("euler_polynomial", "euler_polynomial", "Every rational prime, including two and r, has the Euler polynomial given by the genuine negative-discriminant character. The proof uses an exponent-one generator of the actual maximal integer ring and quadratic reciprocity."),
            Paragraph(Text("Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. Successful scoped author verification does not replace independent whole-result acceptance.")),
            Paragraph(Text("Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number/Gauss sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices are retained. No novelty, priority, consent or publication claim is made.")))));
    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("mercaimaginaryeulerfactors-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
