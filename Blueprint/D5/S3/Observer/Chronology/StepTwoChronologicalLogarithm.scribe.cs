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
        "Step-two chronological logarithms identify Chen multiplication with the truncated BCH group and its antipode.",
        H("Step-Two Chronological Logarithm"),
        Blocks(
            Definition("log-coordinate", "StepTwoLogarithm",
                "Step-two logarithmic coordinate",
                "The coordinate stores degree one together with the doubled degree-two Lie component."),
            Definition("log", "chronologicalLog",
                "Chronological logarithm",
                "The logarithm subtracts the square of degree one from doubled degree two."),
            Definition("exp", "chronologicalExp",
                "Step-two exponential",
                "The exponential restores signature coordinates by adding the square of degree one."),
            Theorem("exp-log", "chronological_exp_log",
                "Exponential after logarithm", ExpLogFormula(),
                "Exponentiating a chronological logarithm exactly recovers its signature."),
            Theorem("log-exp", "chronological_log_exp",
                "Logarithm after exponential", LogExpFormula(),
                "Taking the logarithm of a step-two exponential exactly recovers its coordinate."),
            Theorem("log-mul", "chronological_log_mul",
                "Multiplicative BCH law", LogMulFormula(),
                "The complete logarithm converts Chen composition into the truncated BCH product."),
            Theorem("exp-mul", "chronological_exp_mul",
                "Exponential intertwines BCH and Chen multiplication", ExpMulFormula(),
                "The inverse exponential converts the truncated BCH product back into chronological signature composition."),
            Definition("mul-equiv", "chronologicalLogMulEquiv",
                "Signature-BCH multiplicative equivalence",
                "Logarithm and exponential form an explicit multiplicative equivalence of the two coordinate systems."),
            Definition("antipode", "signatureAntipode",
                "Signature antipode",
                "The explicit inverse negates degree one and applies the transported quadratic correction at degree two."),
            Theorem("antipode-left", "signature_antipode_mul",
                "Left antipode cancellation", AntipodeLeftFormula(),
                "The signature antipode cancels chronological multiplication on the left."),
            Theorem("antipode-right", "mul_signature_antipode",
                "Right antipode cancellation", AntipodeRightFormula(),
                "The signature antipode cancels chronological multiplication on the right."),
            Theorem("log-antipode", "chronological_log_antipode",
                "Antipode in logarithmic coordinates", LogAntipodeFormula(),
                "The logarithm maps the signature antipode to coordinatewise negation."),
            Theorem("antipode-involutive", "signature_antipode_involutive",
                "Antipode is involutive", AntipodeInvolutiveFormula(),
                "Applying the finite step-two antipode twice recovers the original signature."),
            Theorem("antipode-reversal", "signature_antipode_mul_rev",
                "Antipode reverses multiplication", AntipodeReversalFormula(),
                "The antipode of a chronological product is the reversed product of the two antipodes."),
            Theorem("antipode-event", "signature_antipode_event",
                "One-event antipode", AntipodeEventFormula(),
                "The antipode of a one-event signature is the signature of the negated event value.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/StepTwoChronologicalSignature")),
        ]));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, string heading,
        Formula formula, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Theorem);

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

    private static Formula Log(Formula signature) =>
        Call("chronologicalLog", signature);

    private static Formula Exp(Formula coordinate) =>
        Call("chronologicalExp", coordinate);

    private static Formula Antipode(Formula signature) =>
        Call("signatureAntipode", signature);

    private static Formula Inverse(Formula coordinate) =>
        Call("inverse", coordinate);

    private static Formula EventSignature(Formula value) =>
        Call("eventSignature", value);

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula ForAll2(
        Formula first, Formula second, Formula conclusion) =>
        Disp(Seq(
            Forall, Sp, first, Comma, Sp, second, Comma, Sp,
            conclusion, Dot));

    private static Formula ExpLogFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("S"), Comma, Sp,
            Exp(Log(F.Id("S"))), Sp, Eq, Sp, F.Id("S"), Dot));

    private static Formula LogExpFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("L"), Comma, Sp,
            Log(Exp(F.Id("L"))), Sp, Eq, Sp, F.Id("L"), Dot));

    private static Formula LogMulFormula() =>
        ForAll2(F.Id("S"), F.Id("T"),
            Seq(Log(Product(F.Id("S"), F.Id("T"))), Sp, Eq, Sp,
                Product(Log(F.Id("S")), Log(F.Id("T")))));

    private static Formula ExpMulFormula() =>
        ForAll2(F.Id("L"), F.Id("M"),
            Seq(Exp(Product(F.Id("L"), F.Id("M"))), Sp, Eq, Sp,
                Product(Exp(F.Id("L")), Exp(F.Id("M")))));

    private static Formula AntipodeLeftFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("S"), Comma, Sp,
            Product(Antipode(F.Id("S")), F.Id("S")),
            Sp, Eq, Sp, D(1), Dot));

    private static Formula AntipodeRightFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("S"), Comma, Sp,
            Product(F.Id("S"), Antipode(F.Id("S"))),
            Sp, Eq, Sp, D(1), Dot));

    private static Formula LogAntipodeFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("S"), Comma, Sp,
            Log(Antipode(F.Id("S"))), Sp, Eq, Sp,
            Inverse(Log(F.Id("S"))), Dot));

    private static Formula AntipodeInvolutiveFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("S"), Comma, Sp,
            Antipode(Antipode(F.Id("S"))), Sp, Eq, Sp,
            F.Id("S"), Dot));

    private static Formula AntipodeReversalFormula() =>
        ForAll2(F.Id("S"), F.Id("T"),
            Seq(Antipode(Product(F.Id("S"), F.Id("T"))), Sp, Eq, Sp,
                Product(Antipode(F.Id("T")), Antipode(F.Id("S")))));

    private static Formula AntipodeEventFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("x"), Comma, Sp,
            Antipode(EventSignature(F.Id("x"))), Sp, Eq, Sp,
            EventSignature(Seq(Minus, F.Id("x"))), Dot));
}
