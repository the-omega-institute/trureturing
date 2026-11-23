using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class GaussianCharacteristicWindowDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/GaussianCharacteristicWindow";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian smoothing bounds closed-window mass through the characteristic function.",
        H("Closed-Window Bounds from Characteristic Functions"),
        Blocks(
            Paragraph(Text(
                "Let μ be a finite measure on the real line and write χ for its characteristic function. "
                + "For a center b and positive radius r, write M(b,r) for the mass of the closed interval "
                + "with endpoints b−r and b+r. The Gaussian average G(r) is the integral of "
                + "exp(−t²)|χ(2t/r)| on the real line.")),
            Describe.Lean(
                DescribeId.Create("measure-real-closed-window-le-gaussian-char-fun"),
                DeclarationHandle.Create(Owner + ".measureReal_closedWindow_le_gaussian_charFun"),
                H("Gaussian smoothing of the closed-window indicator"),
                StatementSource.FromAuthor(GaussianBound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Inside the window, exp(−((x−b)/r)²) is at least exp(−1). It is "
                        + "positive everywhere. Thus e times this Gaussian majorizes the "
                        + "closed-window indicator, including both endpoints.")),
                    Paragraph(Text(
                        "The Fourier transform of exp(−t²) at frequency 2(x−b)/r is "
                        + "√π exp(−((x−b)/r)²). The modulus of the product integrand "
                        + "is exp(−t²), which is integrable against Lebesgue measure times μ. "
                        + "Fubini and the definition of χ give an average of χ(2t/r) with "
                        + "the Gaussian weight and the phase from b. Taking the modulus "
                        + "removes the phase and gives the bound."))), DescribeRole.Theorem),
            Paragraph(Text(
                "For k>0, define Q(k,r)=e√π r/(2√k). A reciprocal quadratic envelope "
                + "means |χ(t)|≤1/(1+kt²) for every real t.")),
            Describe.Lean(
                DescribeId.Create("measure-real-closed-window-le-of-quadratic-char-fun"),
                DeclarationHandle.Create(Owner + ".measureReal_closedWindow_le_of_quadratic_charFun"),
                H("A bound linear in the radius"),
                StatementSource.FromAuthor(QuadraticBound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the envelope, G(r) is at most the integral of "
                        + "1/(1+(2√k t/r)²), since the Gaussian weight is at most one. "
                        + "The latter integral is π r/(2√k). Dividing the Gaussian "
                        + "mass estimate by √π yields Q(k,r). The reciprocal quadratic "
                        + "estimate requires positive k, and the Gaussian rescaling "
                        + "requires positive r."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula GaussianBound()
    {
        var radius = F.Id("r");
        var mass = Call("M", F.Id("b"), radius);
        var normalizedMass = Multiply(Call("sqrt", Pi), mass);
        return Disp(new Formula.Relation(normalizedMass, FormulaRelationOperator.LessThanOrEqual,
            Multiply(F.Id("e"), Call("G", radius))));
    }

    private static Formula QuadraticBound()
    {
        var radius = F.Id("r");
        return Disp(new Formula.Relation(Call("M", F.Id("b"), radius),
            FormulaRelationOperator.LessThanOrEqual, Call("Q", F.Id("k"), radius)));
    }
}
