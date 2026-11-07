using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CyclotomicFields;

internal sealed class MercaQuarticEulerFactorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CyclotomicFields/MercaQuarticEulerFactors.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Quartic Euler Factors",
        H("Actual Quartic Euler Factors"),
        Blocks(
            Node("inertia_degree", "Actual unramified residue degree", "The order of the normalized character value at p is the actual inertia degree of every maximal-order prime above p, for p distinct from r. The cyclotomic stabilizer theorem, surjective restriction to the actual fixed field, and genuine unramifiedness prove this; no splitting pattern is assumed."),
            Node("euler_polynomial", "All actual quartic Euler factors", "For every rational prime p, including two and the ramified conductor r, the product of one minus z to the actual inertia degrees is the product of the four character factors. The ramified factor is one minus z; the other factors follow from actual residue degrees and the number-field fundamental identity."),
            Paragraph(Text("Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. These author proofs are not independent whole-result acceptance. The signed conductor-4r class-number bridge and the remaining complete sign/MMZ application are separate obligations.")),
            Paragraph(Text("Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices remain intact. No novelty, priority, consent or publication claim is made.")))));
    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("mercaquarticeulerfactors-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
