using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class MercaImaginaryGaussDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CharacterSums/MercaImaginaryGauss.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Signed Conductor Four-r Gauss Sum", H("The Signed Conductor Four-r Gauss Sum"), Blocks(
            Node("gauss_sum", "gauss_sum", "A genuine CRT parametrization separates the character and additive phase. The conductor-four sum and positive Legendre Gauss sum give the positive imaginary sign at conductor four times r."),
            Paragraph(Text("Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. Successful scoped author verification does not replace independent whole-result acceptance.")),
            Paragraph(Text("Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number/Gauss sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices are retained. No novelty, priority, consent or publication claim is made.")))));
    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("mercaimaginarygauss-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
