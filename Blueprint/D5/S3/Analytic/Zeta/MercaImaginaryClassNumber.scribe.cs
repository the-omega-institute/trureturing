using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta;

internal sealed class MercaImaginaryClassNumberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Zeta/MercaImaginaryClassNumber.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Signed Actual Imaginary Class Number",
        H("The Signed Actual Imaginary Class Number"),
        Blocks(
            Node("zeta_factorization", "Actual imaginary zeta factorization", "Every rational-prime Euler factor, including both ramified primes, gives the factorization of the Dedekind zeta function of the actual maximal order for real part greater than one."),
            Node("LFunction_one", "The actual class-number value at one", "The actual field residue, maximal-order regulator one and torsion order two give pi times its genuine ideal class number divided by twice the positive square root of r."),
            Node("LFunction_zero", "The signed class-number value at zero", "The positive Gauss sign and the primitive odd quadratic functional equation give L(0,eta) equal to the genuine NumberField.classNumber, retaining the sign."),
            Node("class_number_quarter", "The exact class-number half", "The genuine ideal class number is twice the literal Legendre quarter sum. Its integer half is exact, with evenness proved before any sign interpretation."),
            Paragraph(Text("Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. Author kernel checks and this application exposition do not replace independent whole-result acceptance. MercaClassNumberCriterion separately combines these suppliers into the full class-number and sign criterion; independent whole-result acceptance remains pending.")),
            Paragraph(Text("Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices remain intact. No novelty, priority, consent or publication claim is made.")))));
    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("mercaimaginaryclassnumber-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
