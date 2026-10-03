using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215KernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient recursions specify the common counting series and the small root of a bivariate kernel.",
        H("Kernel Coefficient Recursions"),
        Blocks(
            Node("weak-ascent-weakascent215kernel-positivestep", "The positive-series transformation", "positiveStep",
                "For a formal power series T over a commutative semiring, the positive-series transformation is (1 + xT) squared plus x squared times (1 + xT) squared times T.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215kernel-kernelcoefficients", "The natural-number coefficient recursion", "kernelCoefficients",
                "The coefficient c_d is defined recursively as the coefficient of degree d in the positive-series transformation applied to the series with coefficients c_i for i less than d and zero coefficients from degree d onward.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215kernel-targetseries", "The target counting series", "targetSeries",
                "The target series over the rational numbers is 1 + x times the series whose coefficient of degree d is c_d, where c_d is given by the natural-number kernel recursion.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215kernel-smallrootcoefficients", "Coefficients of the small root", "smallRootCoefficients",
                "For a bivariate rational power series K indexed by a distinguished coordinate and one other coordinate, define u_d recursively as the coefficient of degree d in x + x squared times K evaluated at x in the distinguished coordinate and at the series with coefficients u_i for i less than d and zero coefficients thereafter in the other coordinate.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215kernel-smallroot", "The small-root series", "smallRoot",
                "The small root associated with K is the rational power series whose coefficient of degree d is u_d from the small-root coefficient recursion.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
