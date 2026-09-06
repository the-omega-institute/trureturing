using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class QuquintCertificateSecondDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Magic/QuquintCertificateSecond.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact LDL factorizations for sixteen numerical branch matrices.",
        H("Ququint Certificate Second Half"),
        Blocks([
            Paragraph(Text("Each displayed identity uses branch from "
                + "D5.S3.Quantum.Magic.QuquintCertificateData and the public "
                + "lower and pivot declarations named in that identity. "
                + "Matrices are displayed as vectors of rows; radical denotes QuquintCertificateData.radical. "
                + "These are certificates for explicit numerical matrices. "
                + "QuquintCertificateBridge identifies their data with the phase-point "
                + "forms of QuquintWignerCriticalGeometry.")),
            .. Enumerable.Range(16, 16).SelectMany(index => Certificate(index, Num(index)))])));

    private static DocumentBlock[] Certificate(int index, Formula numeral) =>
    [
        Definition($"lower{index}", $"Unit-lower factor for branch {index}",
            Seq(Name("Matrix"), Sp, Parenthesized(Seq(Name("Fin"), Sp, D(4))), Sp,
                Parenthesized(Seq(Name("Fin"), Sp, D(4))), Sp, RealType), Lower(index),
            "The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, "
                + "entries above the diagonal zero, and six rational-polynomial entries in "
                + "QuquintCertificateData.radical below the diagonal."),
        Definition($"pivots{index}", $"Pivots for branch {index}",
            Seq(Name("Fin"), Sp, D(4), To, RealType), Pivots(index),
            "The four ordered quartic-field entries are the explicit pivot vector in Lean. "
                + "The corresponding ldl identity uses them in this order; positivity is proved in "
                + "QuquintCertificateAssembly."),
        Describe.Lean(
        DescribeId.Create($"ququint-ldl-{index}"),
        DeclarationHandle.Create(Module + $"ldl_{index}"),
        H($"Branch {index}"),
        StatementSource.FromAuthor(Disp(Seq(
            Minus, Branch, Parenthesized(Seq( numeral)), Eq,
            Name($"lower{index}"), Cdot, Name("Matrix"), Dot, Name("diagonal"),
            Parenthesized(Seq( Name($"pivots{index}"))), Cdot,
            Name("Matrix"), Dot, Name("transpose"), Parenthesized(Seq( Name($"lower{index}")))))),
        AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text("Exact arithmetic using radical_quartic verifies "
            + "every entry of the factorization. The matrices and pivots are "
            + "the public Lean declarations in this module; no positivity "
            + "claim is inferred from the factorization alone."))),
        DescribeRole.Theorem)
    ];

    private static DocumentBlock Definition(string name, string title, Formula type, Formula value, string explanation) =>
        Describe.Lean(DescribeId.Create("ququint-factor-" + name),
            DeclarationHandle.Create(Module + name), H(title),
            StatementSource.FromAuthor(Disp(Seq(Name(name), Colon, type, Eq, value))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static Formula Lower(int index) => index switch
    {
        16 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(88), Minus, Num(7), Cdot, Radical, Slash, Num(22)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(44), Plus, Num(8), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Minus, Num(13), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Plus, Num(29), Cdot, Radical, Slash, Num(44)), Seq(Minus, Num(39), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Plus, Num(62), Cdot, Radical, Slash, Num(55)), Seq(Num(7), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(62), Minus, Num(76), Slash, Num(93)), Num(1))),
        17 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Num(2), Cdot, Radical), Seq(Minus, Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(4), Plus, Num(53), Cdot, Radical, Slash, Num(5)), Num(1), Num(0)),
            Vector(Seq(Num(11), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(40), Minus, Num(15), Cdot, Radical, Slash, Num(4)), Seq(Num(37), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(40), Minus, Num(68), Cdot, Radical, Slash, Num(5)), Seq(Num(45), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(176), Minus, Num(127), Slash, Num(44)), Num(1))),
        18 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Radical, Slash, Num(2)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(2), Minus, Num(37), Cdot, Radical, Slash, Num(5)), Num(1), Num(0)),
            Vector(Seq(Num(5), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(8), Minus, Num(35), Cdot, Radical, Slash, Num(4)), Seq(Minus, Num(7), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(40), Plus, Num(12), Cdot, Radical, Slash, Num(5)), Seq(Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(1)), Num(1))),
        19 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Radical, Slash, Num(2)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(22), Plus, Num(23), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Num(5), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(88), Minus, Num(23), Cdot, Radical, Slash, Num(44)), Seq(Minus, Num(7), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Plus, Num(2), Cdot, Radical, Slash, Num(55)), Seq(Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(1)), Num(1))),
        20 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Minus, Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(10), Plus, Num(9), Cdot, Radical, Slash, Num(2)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(2), Minus, Num(37), Cdot, Radical, Slash, Num(5)), Num(1), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(10), Minus, Num(5), Cdot, Radical, Slash, Num(4)), Seq(Num(29), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(40), Minus, Num(53), Cdot, Radical, Slash, Num(5)), Seq(Num(39), Slash, Num(44), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(176)), Num(1))),
        21 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(220), Minus, Radical, Slash, Num(22)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(22), Plus, Num(23), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(440), Plus, Num(7), Cdot, Radical, Slash, Num(44)), Seq(Num(27), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Minus, Num(58), Cdot, Radical, Slash, Num(55)), Seq(Num(137), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(1448), Minus, Num(201), Slash, Num(362)), Num(1))),
        22 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(88), Plus, Radical, Slash, Num(22)), Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(44), Minus, Num(62), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Num(17), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Minus, Num(13), Cdot, Radical, Slash, Num(44)), Seq(Minus, Num(9), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Plus, Num(12), Cdot, Radical, Slash, Num(55)), Seq(Num(23), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(242), Minus, Num(139), Slash, Num(242)), Num(1))),
        23 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(11), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(380), Minus, Num(4), Cdot, Radical, Slash, Num(19)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(76), Minus, Num(3), Cdot, Radical, Slash, Num(95)), Num(1), Num(0)),
            Vector(Seq(Num(2), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(95), Minus, Num(3), Cdot, Radical, Slash, Num(76)), Seq(Minus, Num(9), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(760), Plus, Num(3), Cdot, Radical, Slash, Num(95)), Seq(Num(149), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(1364), Minus, Num(523), Slash, Num(682)), Num(1))),
        24 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(5), Minus, Num(17), Cdot, Radical, Slash, Num(2)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(2), Minus, Num(37), Cdot, Radical, Slash, Num(5)), Num(1), Num(0)),
            Vector(Seq(Minus, Num(7), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(40), Plus, Num(11), Cdot, Radical, Slash, Num(4)), Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(8), Minus, Num(28), Cdot, Radical, Slash, Num(5)), Seq(Num(81), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(872), Minus, Num(115), Slash, Num(218)), Num(1))),
        25 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(11), Minus, Num(25), Cdot, Radical, Slash, Num(22)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(22), Plus, Num(23), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(55), Plus, Num(21), Cdot, Radical, Slash, Num(44)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(40), Minus, Num(3), Cdot, Radical, Slash, Num(5)), Seq(Num(23), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(242), Minus, Num(139), Slash, Num(242)), Num(1))),
        26 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(39), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Minus, Num(23), Cdot, Radical, Slash, Num(22)), Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(44), Minus, Num(62), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(55), Plus, Radical, Slash, Num(44)), Seq(Minus, Num(5), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(88), Plus, Num(37), Cdot, Radical, Slash, Num(55)), Seq(Num(75), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(484), Minus, Num(345), Slash, Num(242)), Num(1))),
        27 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(27), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(380), Minus, Num(15), Cdot, Radical, Slash, Num(19)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(76), Minus, Num(3), Cdot, Radical, Slash, Num(95)), Num(1), Num(0)),
            Vector(Seq(Num(9), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(760), Plus, Num(9), Cdot, Radical, Slash, Num(76)), Seq(Minus, Num(27), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(760), Plus, Num(28), Cdot, Radical, Slash, Num(95)), Seq(Num(48), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(341), Minus, Num(841), Slash, Num(682)), Num(1))),
        28 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(23), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Minus, Num(13), Cdot, Radical, Slash, Num(22)), Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(44), Minus, Num(62), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Minus, Num(2), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(55), Plus, Num(31), Cdot, Radical, Slash, Num(44)), Seq(Num(9), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Minus, Num(23), Cdot, Radical, Slash, Num(55)), Seq(Num(225), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(1448), Minus, Num(523), Slash, Num(362)), Num(1))),
        29 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(9), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(190), Minus, Num(10), Cdot, Radical, Slash, Num(19)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(76), Minus, Num(3), Cdot, Radical, Slash, Num(95)), Num(1), Num(0)),
            Vector(Seq(Minus, Num(9), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(380), Plus, Num(39), Cdot, Radical, Slash, Num(76)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(152), Minus, Num(27), Cdot, Radical, Slash, Num(95)), Seq(Num(61), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(528), Minus, Num(115), Slash, Num(132)), Num(1))),
        30 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Radical, Slash, Num(2)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(19), Minus, Num(83), Cdot, Radical, Slash, Num(95)), Num(1), Num(0)),
            Vector(Seq(Radical, Slash, Num(4)), Seq(Minus, Num(23), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(760), Plus, Num(33), Cdot, Radical, Slash, Num(95)), Seq(Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(1)), Num(1))),
        31 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Radical, Slash, Num(2)), Seq(Minus, Radical, Slash, Num(5)), Num(1), Num(0)),
            Vector(Seq(Radical, Slash, Num(4)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(40), Plus, Radical, Slash, Num(5)), Seq(Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(1)), Num(1))),
        _ => throw new ArgumentOutOfRangeException(nameof(index))
    };

    private static Formula Pivots(int index) => index switch
    {
        16 => Vector(Seq(Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(2)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(3)), Seq(Num(114), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(55), Minus, Num(888), Slash, Num(55)), Seq(Num(542), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(465), Minus, Num(1120), Slash, Num(93))),
        17 => Vector(Seq(Num(7), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(4)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(7), Slash, Num(2)), Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Plus, Num(16), Slash, Num(5)), Seq(Num(39), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(110), Plus, Num(1), Slash, Num(11))),
        18 => Vector(Seq(Num(7), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(4)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(7), Slash, Num(2)), Seq(Num(8), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(8)), Seq(Num(134), Slash, Num(5), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(2))),
        19 => Vector(Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(6)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(4)), Seq(Num(24), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(11), Minus, Num(168), Slash, Num(11)), Seq(Num(17), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(22), Minus, Num(314), Slash, Num(55))),
        20 => Vector(Seq(Num(7), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(4)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(7), Slash, Num(2)), Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Plus, Num(16), Slash, Num(5)), Seq(Num(39), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(110), Plus, Num(1), Slash, Num(11))),
        21 => Vector(Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(6)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(4)), Seq(Num(114), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(55), Minus, Num(776), Slash, Num(55)), Seq(Num(1638), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(1991), Minus, Num(12522), Slash, Num(1991))),
        22 => Vector(Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(6)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(4)), Seq(Num(2), Cdot, Radical, Caret, Grp(Num(2)), Minus, Num(64), Slash, Num(5)), Seq(Num(2433), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(2662), Minus, Num(10248), Slash, Num(1331))),
        23 => Vector(Seq(Num(9), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(8)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(9), Slash, Num(2)), Seq(Num(214), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(95), Minus, Num(1432), Slash, Num(95)), Seq(Num(3227), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(3410), Minus, Num(2654), Slash, Num(341))),
        24 => Vector(Seq(Num(7), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(4)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(7), Slash, Num(2)), Seq(Num(104), Slash, Num(5), Minus, Num(2), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5)), Seq(Num(262), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(545), Minus, Num(198), Slash, Num(109))),
        25 => Vector(Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(6)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(4)), Seq(Num(2), Cdot, Radical, Caret, Grp(Num(2)), Minus, Num(64), Slash, Num(5)), Seq(Num(2433), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(2662), Minus, Num(10248), Slash, Num(1331))),
        26 => Vector(Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(6)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(4)), Seq(Num(2), Cdot, Radical, Caret, Grp(Num(2)), Minus, Num(64), Slash, Num(5)), Seq(Num(2433), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(2662), Minus, Num(10248), Slash, Num(1331))),
        27 => Vector(Seq(Num(9), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(8)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(9), Slash, Num(2)), Seq(Num(214), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(95), Minus, Num(1432), Slash, Num(95)), Seq(Num(3227), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(3410), Minus, Num(2654), Slash, Num(341))),
        28 => Vector(Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(6)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(4)), Seq(Num(114), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(55), Minus, Num(776), Slash, Num(55)), Seq(Num(1638), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(1991), Minus, Num(12522), Slash, Num(1991))),
        29 => Vector(Seq(Num(9), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(8)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(9), Slash, Num(2)), Seq(Num(216), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(95), Minus, Num(1488), Slash, Num(95)), Seq(Num(201), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(220), Minus, Num(238), Slash, Num(33))),
        30 => Vector(Seq(Num(9), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(8)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(9), Slash, Num(2)), Seq(Num(206), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(95), Minus, Num(272), Slash, Num(19)), Seq(Radical, Caret, Grp(Num(2)), Minus, Num(42), Slash, Num(5))),
        31 => Vector(Seq(Radical, Caret, Grp(Num(2)), Minus, Num(10)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(5)), Seq(Num(12), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(16)), Seq(Radical, Caret, Grp(Num(2)), Minus, Num(8))),
        _ => throw new ArgumentOutOfRangeException(nameof(index))
    };

    private static Formula Radical => Name("radical");

    private static Formula Vector(params Formula[] entries) => Seq(OpenBracket,
        Seq(entries.SelectMany((v, i) => i == 0 ? new[] { v } : new[] { Comma, v }).ToArray()), CloseBracket);

    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Branch => Seq(Name("D5"), Dot, Name("S3"), Dot,
        Name("Quantum"), Dot, Name("Magic"), Dot, Name("QuquintCertificateData"),
        Dot, Name("branch"));
    private static Formula Name(string name) => Seq(Mathrm, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
