using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class MercaPositiveGaussDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CharacterSums/MercaPositiveGauss.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Positive Quadratic Gauss Sign", H("The Positive Quadratic Gauss Sign"), Blocks(
            Node("square_sum", "square_sum", "The actual finite quadratic exponential sum equals the positive real square root. The existing Milgram theorem is applied to the actual rank-one even lattice with Gram matrix (2r), whose discriminant group and phase are identified explicitly."),
            Node("prime_gauss_sum", "prime_gauss_sum", "Root-fiber counting identifies the square exponential sum with the standard Gauss sum of the genuine Legendre character, fixing its positive sign."),
            Paragraph(Text("Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. Successful scoped author verification does not replace independent whole-result acceptance.")),
            Paragraph(Text("Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number/Gauss sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices are retained. No novelty, priority, consent or publication claim is made.")))));
    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("mercapositivegauss-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
