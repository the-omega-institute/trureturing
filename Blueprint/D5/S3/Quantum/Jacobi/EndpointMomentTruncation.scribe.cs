using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Jacobi;

internal sealed class EndpointMomentTruncationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Jacobi/EndpointMomentTruncation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a Jacobi chain cut at site n, the first possible error in its endpoint moments occurs at order 2n and equals the product of squared couplings up to the cut.",
        H("Endpoint moments of a finite Jacobi section"),
        Blocks(
            Describe.Lean(DescribeId.Create("jacobi-amplitude"), DeclarationHandle.Create(Prefix + "amplitude"),
                H("Powers applied to the endpoint vector"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The initial vector is the unit mass at site zero. Each time step applies the tridiagonal recurrence with real diagonal entries and real symmetric nearest-neighbor couplings. With a cutoff n, every site starting at n is set to zero initially and after each step."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("first-omitted-moment"), DeclarationHandle.Create(Prefix + "first_omitted_moment"),
                H("The first possible endpoint moment error"),
                StatementSource.FromAuthor(Disp(Seq(new Formula.Subscript(F.Id("m"), Seq(D(2), F.Id("n"))), Sp, Minus, Sp,
                    new Formula.Power(new Formula.Subscript(F.Id("m"), Seq(D(2), F.Id("n"))), Seq(Open, F.Id("n"), Close)), Sp, Eq, Sp,
                    new Formula.Subscript(F.Prod, Seq(F.Id("j"), Lt, F.Id("n"))), new Formula.Power(new Formula.Subscript(F.Id("b"), F.Id("j")), D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The full endpoint moment at degree k equals the moment of the first n sites whenever k is below 2n. At degree 2n their difference is the product of the squares of the first n couplings. For the empty section the difference at degree zero is one.")),
                    Paragraph(Text("Reaching the first omitted site takes at least n steps, and returning to the endpoint takes n more. The outward and inward paths of minimal length both traverse each of the first n edges exactly once. For n at least one, if the product of the squares of the preceding n−1 couplings is known and nonzero, division by that product and taking the nonnegative square root gives the magnitude of the final coupling. A zero earlier coupling makes this readout vanish."))), DescribeRole.Theorem))));
}
