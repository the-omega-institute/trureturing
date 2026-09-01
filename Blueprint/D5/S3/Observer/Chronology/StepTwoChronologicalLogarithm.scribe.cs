using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class StepTwoChronologicalLogarithmDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Step-two signature coordinates are multiplicatively equivalent to the "
            + "truncated BCH law, with an explicit antipode.",
        H("Step-Two Chronological Logarithm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("log-coordinate"),
                DeclarationHandle.Create(Prefix + "StepTwoLogarithm"),
                H("Step-two logarithmic coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coordinate stores degree one and the doubled degree-two Lie component."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("log"),
                DeclarationHandle.Create(Prefix + "chronologicalLog"),
                H("Chronological logarithm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The logarithm subtracts the square of degree one from doubled degree two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exp"),
                DeclarationHandle.Create(Prefix + "chronologicalExp"),
                H("Step-two exponential"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exponential restores signature coordinates by adding the square of degree one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exp-log"),
                DeclarationHandle.Create(Prefix + "chronological_exp_log"),
                H("Exponential after logarithm"),
                StatementSource.FromAuthor(ExpLogFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exponentiating a chronological logarithm exactly recovers its signature."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-exp"),
                DeclarationHandle.Create(Prefix + "chronological_log_exp"),
                H("Logarithm after exponential"),
                StatementSource.FromAuthor(LogExpFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Taking the logarithm of a step-two exponential exactly recovers its coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-mul"),
                DeclarationHandle.Create(Prefix + "chronological_log_mul"),
                H("Multiplicative BCH law"),
                StatementSource.FromAuthor(LogMulFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The complete logarithm converts Chen composition into the truncated BCH product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mul-equiv"),
                DeclarationHandle.Create(Prefix + "chronologicalLogMulEquiv"),
                H("Signature-BCH multiplicative equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Logarithm and exponential form an explicit multiplicative equivalence of the two coordinate systems."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("antipode"),
                DeclarationHandle.Create(Prefix + "signatureAntipode"),
                H("Signature antipode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The explicit inverse negates degree one and applies the transported quadratic correction at degree two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("log-antipode"),
                DeclarationHandle.Create(Prefix + "chronological_log_antipode"),
                H("Antipode in logarithmic coordinates"),
                StatementSource.FromAuthor(LogAntipodeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The logarithm maps the signature antipode to coordinatewise negation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("antipode-reversal"),
                DeclarationHandle.Create(Prefix + "signature_antipode_mul_rev"),
                H("Antipode reverses multiplication"),
                StatementSource.FromAuthor(AntipodeReversalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The antipode of a chronological product is the reversed product of the two antipodes."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/StepTwoChronologicalSignature")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula LogOf(Formula value) =>
        Call("chronologicalLog", value);

    private static Formula ExpOf(Formula value) =>
        Call("chronologicalExp", value);

    private static Formula AntipodeOf(Formula value) =>
        Call("signatureAntipode", value);

    private static Formula ExpLogFormula() => Disp(Seq(
        Forall, Sp, F.Id("a"), Comma, Sp,
        ExpOf(LogOf(F.Id("a"))), Sp, Eq, Sp, F.Id("a"), Dot));

    private static Formula LogExpFormula() => Disp(Seq(
        Forall, Sp, F.Id("c"), Comma, Sp,
        LogOf(ExpOf(F.Id("c"))), Sp, Eq, Sp, F.Id("c"), Dot));

    private static Formula LogMulFormula() => Disp(Seq(
        Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp,
        LogOf(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("b"))), Sp, Eq, Sp,
        LogOf(F.Id("a")), Sp, Cdot, Sp, LogOf(F.Id("b")), Dot));

    private static Formula LogAntipodeFormula() => Disp(Seq(
        Forall, Sp, F.Id("a"), Comma, Sp,
        LogOf(AntipodeOf(F.Id("a"))), Sp, Eq, Sp,
        Call("inverse", LogOf(F.Id("a"))), Dot));

    private static Formula AntipodeReversalFormula() => Disp(Seq(
        Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp,
        AntipodeOf(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("b"))), Sp, Eq, Sp,
        AntipodeOf(F.Id("b")), Sp, Cdot, Sp, AntipodeOf(F.Id("a")), Dot));
}
