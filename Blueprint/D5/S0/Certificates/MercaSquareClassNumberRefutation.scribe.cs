using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class MercaSquareClassNumberRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/MercaSquareClassNumberRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Historical Square-but-Unequal Counterexample",
        H("The Historical Square-but-Unequal Counterexample"),
        Blocks(
            Node("claim", "The square-only replacement", DescribeRole.Definition, "The refuted claim says that every prime r greater than five congruent to five modulo eight with a square genuine relative class number has equal absolute quartic coordinates. This is a tempting weakening, not the historical theorem."),
            Node("result", "The actual r181 refutation", DescribeRole.Theorem, "For r=181, the actual normalized character kernel is identified with the 45 distinct powers of two with exponents 4j. Kernel-checked finite sums are (3439,3982,4706,4163), giving k=-7 and t=-1. The proved universal actual-object norm theorem gives the genuine relative class number 25, and the signed quarter theorem gives the genuine imaginary class number h(-724)=10. Thus square alone does not force equal magnitudes. This refutation does not claim that the finite checker independently computes ideal class groups."),
            Paragraph(Text("Historical source: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Retained Yao Xu/catalan-lean4 supplier notices. No novelty, priority, author-consent or publication claim.")),
            Paragraph(Text("The original 313-prime census, first-ten signs and r13 reduced-form example remain finite source evidence: 24 equal-coordinate cases versus 49 square relative-class-number cases through 10000. No density or universal classification follows from it. Source-owner audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629; author evidence is distinct from independent acceptance.")))));
    private static DocumentBlock Node(string name, string title, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("merca-square-refutation-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role);
}
