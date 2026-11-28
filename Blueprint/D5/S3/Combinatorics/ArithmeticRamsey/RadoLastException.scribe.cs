using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ArithmeticRamsey;

internal sealed class RadoLastExceptionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/hughes2026radolastexception");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-colour Rado lower bound is exact above the explicit last exception for every k at least three.",
        H("The all-parameter Rado last-exception theorem"),
        Blocks(
            Node("exception-good", "Good colourings for the reflected equation", "Good",
                "Good records the absence of a monochromatic solution of x + y = k z + b in a finite interval and supplies the forcing and reflection mechanism.", DescribeRole.Definition),
            Node("exception-forced", "Forcing for every two-colouring", "Forced",
                "HasMono means that there exist positive x,y,z at most n with x+y+c=k*z and equal Boolean colours. Forced quantifies over every col : Nat to Bool; only its values on [1,n] enter the assertion. Repeated variables are allowed.", DescribeRole.Definition),
            Node("exception-valid", "The parity validity condition", "Valid",
                "A parameter is valid when k is odd or c is even, matching the parity range of the theorem.", DescribeRole.Definition),
            Node("exception-is-rado", "The least forcing endpoint", "IsRado",
                "IsRado(c,k,R) means forcing at R and non-forcing at every natural n smaller than R.", DescribeRole.Definition),
            Node("exception-complete", "The complete last-exception theorem", "rado_last_exception",
                "For every natural k at least three, cstar(k) is valid; every valid natural c strictly above cstar(k) has IsRado(c,k,LB(c,k)); and an explicit colouring avoids every monochromatic solution on the closed interval [1,LB(cstar(k),k)]. All three variables range independently over that interval and may repeat. IsRado includes every smaller endpoint, not only the endpoint forcing assertion. No finite existence of a boundary Rado number or negative-c classification is asserted.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
