using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta;

internal sealed class MercaImaginaryCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Zeta/MercaImaginaryCharacter.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Actual Discriminant Character",
        H("The Actual Discriminant Character"),
        Blocks(
            Node("character_int", "Literal integer values", "At the actual modulus four times r, the character is the product of the lifted character modulo four and the genuine Legendre character. The formula holds on every integer, with zero at nonunits; neither a class number nor a norm table defines its values."),
            Node("character_properties", "Exact conductor and odd quadraticity", "For every prime r congruent to five modulo eight, the local conductors four and r are coprime. The product conductor is proved to be exactly four r, and the product is quadratic, odd and nonprincipal. These facts supply the imaginary Euler and signed L-value bridges."),
            Paragraph(Text("Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. Author kernel checks and this application exposition do not replace independent whole-result acceptance. MercaClassNumberCriterion separately combines these suppliers into the full class-number and sign criterion; independent whole-result acceptance remains pending.")),
            Paragraph(Text("Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices remain intact. No novelty, priority, consent or publication claim is made.")))));
    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("mercaimaginarycharacter-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
