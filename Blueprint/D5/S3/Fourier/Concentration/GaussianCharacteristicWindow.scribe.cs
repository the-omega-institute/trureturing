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
                + "Write M(b,r) for the measure of |x−b|≤r. At any smoothing scale s>0, "
                + "let G(b,s) be the integral of exp(−t²)exp(−2itb/s)χ(2t/s) on the real line. "
                + "Write A(s) for the integral of exp(−t²)|χ(2t/s)|.")),
            Describe.Lean(
                DescribeId.Create("measure-real-closed-window-le-gaussian-char-fun"),
                DeclarationHandle.Create(Owner + ".measureReal_closedWindow_le_gaussian_charFun"),
                H("Gaussian smoothing of the closed-window indicator"),
                StatementSource.FromAuthor(GaussianBound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Inside the window, exp(−((x−b)/s)²) is at least exp(−(r/s)²). "
                        + "The Gaussian is positive everywhere. Multiplying by exp((r/s)²) "
                        + "majorizes the closed-window indicator, including both endpoints.")),
                    Paragraph(Text(
                        "With the factor exp(itξ), the Gaussian transform at ξ=2(x−b)/s is "
                        + "√π exp(−((x−b)/s)²). The modulus of the product integrand "
                        + "is exp(−t²), which is integrable against Lebesgue measure times μ. "
                        + "Fubini and the definition of χ give the phase-sensitive integral G(b,s). "
                        + "The triangle inequality bounds its modulus by A(s). The first inequality "
                        + "is an equality for a unit atom on the boundary |x−b|=r."))), DescribeRole.Theorem),
            Paragraph(Text(
                "For k>0 and r>0, define Q(k,r)=exp(1/2)√π r/(√2√k). A reciprocal quadratic envelope "
                + "means that χ satisfies the pointwise inequality in the hypothesis below.")),
            Describe.Lean(
                DescribeId.Create("measure-real-closed-window-le-of-quadratic-char-fun"),
                DeclarationHandle.Create(Owner + ".measureReal_closedWindow_le_of_quadratic_charFun"),
                H("A bound linear in the radius"),
                StatementSource.FromAuthor(QuadraticBound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the envelope, A(s) is at most the integral of "
                        + "1/(1+(2√k t/s)²), since the Gaussian weight is at most one. "
                        + "The latter integral is π s/(2√k). Choose s=√2 r. Then the "
                        + "indicator multiplier is exp(1/2), and dividing the mass estimate "
                        + "by √π yields Q(k,r)."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula GaussianBound()
    {
        var radius = F.Id("r");
        var mass = Call("M", F.Id("b"), radius);
        var normalizedMass = Multiply(Call("sqrt", Pi), mass);
        var scale = F.Id("s");
        var amplitude = new Formula.Absolute(Call("G", F.Id("b"), scale));
        var multiplier = Call("exp", new Formula.Power(new Formula.Fraction(radius, scale), D(2)));
        var massBound = new Formula.Relation(normalizedMass, FormulaRelationOperator.LessThanOrEqual,
            Multiply(multiplier, amplitude));
        var amplitudeBound = new Formula.Relation(amplitude, FormulaRelationOperator.LessThanOrEqual,
            Call("A", scale));
        return Disp(new Formula.Logic(massBound, FormulaLogicOperator.And, amplitudeBound));
    }

    private static Formula QuadraticBound()
    {
        var radius = F.Id("r");
        var parameter = F.Id("k");
        var frequency = F.Id("t");
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var envelope = new Formula.Fraction(D(1),
            Add(D(1), Multiply(parameter, new Formula.Power(frequency, D(2)))));
        var pointwiseBound = new Formula.Relation(new Formula.Absolute(Call("chi", frequency)),
            FormulaRelationOperator.LessThanOrEqual, envelope);
        var hypothesis = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("t"), reals, pointwiseBound);
        var massBound = new Formula.Relation(Call("M", F.Id("b"), radius),
            FormulaRelationOperator.LessThanOrEqual, Call("Q", parameter, radius));
        return Disp(new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, massBound));
    }
}
