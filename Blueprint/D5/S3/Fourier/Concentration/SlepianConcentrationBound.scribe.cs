using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class SlepianConcentrationBoundDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Fourier/Concentration/SlepianConcentrationBound."
            + "slepian_concentration_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximal eigenvalue of a positive Slepian concentration spectrum is bounded "
            + "by one and by the trace budget.",
        H("Slepian Concentration Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("slepian-concentration-bound"),
            DeclarationHandle.Create(Declaration),
            H("The maximal concentration rate is at most one and the trace"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let lambda be a nonnegative summable concentration spectrum, with every "
                        + "eigenvalue at most one. Its sum is the Slepian trace Lm/pi, and the "
                        + "maximum Lambda is assumed to be attained by one spectral mode.")),
                Paragraph(Text(
                    "The singleton finite sum is bounded by the total sum via Mathlib's "
                        + "Summable.sum_le_tsum. Hence the attained eigenvalue is at most the "
                        + "trace, while the pointwise contraction bound makes it at most one.")),
                Paragraph(Text(
                    "If Lm is zero, pi is nonzero and the trace is zero. Nonnegativity then "
                        + "squeezes the attained maximum to zero, supplying the boundary equality "
                        + "rather than only a one-sided estimate. The operator-theoretic trace "
                        + "and spectral facts are explicit hypotheses because pinned Mathlib has "
                        + "no suitable trace-class API."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula eigenvalue = F.LambdaLower;
        Formula intervalRadius = F.Id("L");
        Formula frequencyMeasure = F.Id("m");
        Formula maximum = F.Id("Lambda");
        Formula index = F.Id("j");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula eigenvalueAtIndex = Apply(eigenvalue, index);
        Formula budget = Seq(
            Frac, Grp(intervalRadius, Sp, frequencyMeasure), Grp(Pi));
        Formula trace = Seq(
            Sum, Underscore, Grp(index, Eq, D(0)), Caret, Grp(Infty), Sp,
            eigenvalueAtIndex);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, eigenvalue, Colon, Sp, natural, Sp, To, Sp, real,
                Comma, Sp, intervalRadius, Comma, Sp, frequencyMeasure,
                Comma, Sp, maximum, InMacro, real, Comma),
            Seq(
                D(0), Sp, Leq, Sp, intervalRadius, Sp, Land, Sp,
                D(0), Sp, Leq, Sp, frequencyMeasure, Sp, Land),
            Seq(
                Open, Forall, Sp, index, InMacro, natural, Comma, Sp,
                D(0), Sp, Leq, Sp, eigenvalueAtIndex, Sp, Leq, Sp, D(1),
                Close, Sp, Land, Sp, Call("Summable", eigenvalue), Sp, Land),
            Seq(
                trace, Sp, Eq, Sp, budget, Sp, Land, Sp,
                Open, Exists, Sp, index, InMacro, natural, Comma, Sp,
                maximum, Sp, Eq, Sp, eigenvalueAtIndex, Close, Sp, Rightarrow),
            Seq(
                maximum, Sp, Leq, Sp, Call("min", D(1), budget), Sp, Land),
            Seq(
                Open, intervalRadius, Sp, frequencyMeasure, Sp, Eq, Sp, D(0),
                Sp, Rightarrow, Sp, maximum, Sp, Eq, Sp, D(0), Close, Dot),
        ]));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
