using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta;

internal sealed class MercaRelativeClassNumberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Zeta/MercaRelativeClassNumber.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Actual Relative Ideal Class Number",
        H("The Actual Relative Ideal Class Number"),
        Blocks(
            Node("zeta_factorization", "Convergent relative zeta factorization", "For real part greater than one, the actual quartic Dedekind zeta function is the product of the actual maximal-real Dedekind zeta function and the L-functions of the normalized quartic character and its inverse. Actual local polynomials and convergent HasProd suppliers prove the equality, including ramified primes."),
            Node("residue_relation", "Actual Dedekind residue comparison", "Take right limits at one in the genuine factorization. Both nonprincipal L-functions are continuous there, and the actual number-field residue formulas identify the limits. This does not choose a quadratic Gauss-sum sign."),
            Node("LFunction_one_mul_inverse", "The one-side class-number product", "For r greater than five the proved CM unit index is one, both actual roots-of-unity groups have order two, and the actual regulator ratio is two. Actual discriminants r cubed and r and the genuine residue formula yield the classical inverse-character L-value product."),
            Node("relative_norm", "Norm and genuine relative class number", "The normalized coordinates satisfy k squared plus t squared equals twice the exact quotient of the genuine quartic and real quadratic ideal class numbers. The odd primitive inverse-character functional equation and actual Bernoulli/L-zero identities supply the bridge; the actual real class groups are transported through the proved algebra equivalence."),
            Node("relative_class_number_integral", "Integrality of the actual quotient", "The genuine ideal-class-number quotient is a nonnegative integer, proved from the norm identity and the odd integer coordinates. It is defined as a rational quotient and is never rounded by natural division."),
            Paragraph(Text("Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. These author proofs are not independent whole-result acceptance. The signed conductor-4r class-number bridge and the remaining complete sign/MMZ application are separate obligations.")),
            Paragraph(Text("Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices remain intact. No novelty, priority, consent or publication claim is made.")))));
    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("mercarelativeclassnumber-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
