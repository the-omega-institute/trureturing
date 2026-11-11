using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class MercaQuadraticQuarterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CharacterSums/MercaQuadraticQuarter.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Literal Quadratic Quarter Sum",
        H("The Literal Quadratic Quarter Sum"),
        Blocks(
            Describe.Lean(DescribeId.Create("mercaquadraticquarter-quartersum"), DeclarationHandle.Create(Prefix + "quarterSum"), H("The literal quadratic quarter sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The sum uses the actual Legendre character on precisely the positive integers from one through (r-1)/4."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mercaquadraticquarter-nonresiduecount"), DeclarationHandle.Create(Prefix + "nonresidueCount"), H("The literal quarter nonresidue count"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The count uses the same positive interval and the Legendre value minus one."))), DescribeRole.Definition),
            Node("quarter_nonresidue", "The length-minus-twice-count identity", "Every interval element is a nonzero residue modulo r. The literal quadratic sum is the interval length minus twice the nonresidue count."),
            Node("LFunction_zero_quarter", "The signed finite L-zero bridge", "Four exact representative blocks, reflection of the quadratic character, and multiplication by four identify the actual conductor-four-r L-function at zero with twice the literal Legendre quarter sum. No class-number premise occurs."),
            Paragraph(Text("Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. Author kernel checks and this application exposition do not replace independent whole-result acceptance. MercaClassNumberCriterion separately combines these suppliers into the full class-number and sign criterion; independent whole-result acceptance remains pending.")),
            Paragraph(Text("Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices remain intact. No novelty, priority, consent or publication claim is made.")))));
    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("mercaquadraticquarter-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
