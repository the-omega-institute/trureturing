using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class QuquintCertificateFirstDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Magic/QuquintCertificateFirst.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact LDL factorizations for sixteen numerical branch matrices.",
        H("Ququint Certificate First Half"),
        Blocks([
            Paragraph(Text("Each displayed identity uses branch from "
                + "D5.S3.Quantum.Magic.QuquintCertificateData and the public "
                + "lower and pivot declarations named in that identity. "
                + "Matrices are displayed as vectors of rows; radical denotes QuquintCertificateData.radical. "
                + "These are certificates for explicit numerical matrices. "
                + "QuquintCertificateBridge identifies their data with the phase-point "
                + "forms of QuquintWignerCriticalGeometry.")),
            .. Enumerable.Range(0, 16).SelectMany(index => Certificate(index, Num(index)))])));

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
        0 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Radical, Slash, Num(2)), Seq(Minus, Radical, Slash, Num(5)), Num(1), Num(0)),
            Vector(Seq(Radical, Slash, Num(4)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(40), Plus, Radical, Slash, Num(5)), Seq(Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(1)), Num(1))),
        1 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Radical, Slash, Num(2)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(11), Minus, Num(87), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Radical, Slash, Num(4)), Seq(Minus, Num(27), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Plus, Num(37), Cdot, Radical, Slash, Num(55)), Seq(Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(1)), Num(1))),
        2 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(29), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Minus, Num(15), Cdot, Radical, Slash, Num(22)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(44), Plus, Num(8), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Minus, Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(110), Plus, Num(31), Cdot, Radical, Slash, Num(44)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(88), Minus, Num(53), Cdot, Radical, Slash, Num(55)), Seq(Num(17), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(124), Minus, Num(110), Slash, Num(93)), Num(1))),
        3 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(20), Plus, Radical), Seq(Minus, Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(4), Plus, Num(53), Cdot, Radical, Slash, Num(5)), Num(1), Num(0)),
            Vector(Seq(Num(7), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Num(19), Cdot, Radical, Slash, Num(4)), Seq(Minus, Num(21), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(40), Plus, Num(37), Cdot, Radical, Slash, Num(5)), Seq(Num(39), Slash, Num(44), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(176)), Num(1))),
        4 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(41), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Minus, Num(25), Cdot, Radical, Slash, Num(22)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(44), Plus, Num(8), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(220), Plus, Radical, Slash, Num(44)), Seq(Minus, Num(13), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Plus, Num(17), Cdot, Radical, Slash, Num(55)), Seq(Num(75), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(698), Minus, Num(262), Slash, Num(349)), Num(1))),
        5 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Minus, Num(2), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(5), Plus, Num(6), Cdot, Radical), Seq(Minus, Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(4), Plus, Num(53), Cdot, Radical, Slash, Num(5)), Num(1), Num(0)),
            Vector(Seq(Minus, Num(7), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(40), Plus, Num(11), Cdot, Radical, Slash, Num(4)), Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(8), Minus, Num(28), Cdot, Radical, Slash, Num(5)), Seq(Num(81), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(872), Minus, Num(115), Slash, Num(218)), Num(1))),
        6 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(2), Plus, Num(15), Cdot, Radical, Slash, Num(2)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(2), Minus, Num(37), Cdot, Radical, Slash, Num(5)), Num(1), Num(0)),
            Vector(Seq(Num(7), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(40), Minus, Num(9), Cdot, Radical, Slash, Num(4)), Seq(Minus, Num(29), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(40), Plus, Num(52), Cdot, Radical, Slash, Num(5)), Seq(Num(137), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(872), Minus, Num(321), Slash, Num(218)), Num(1))),
        7 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(110), Plus, Num(3), Cdot, Radical, Slash, Num(22)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(22), Plus, Num(23), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(55), Plus, Radical, Slash, Num(44)), Seq(Minus, Num(5), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(88), Plus, Num(37), Cdot, Radical, Slash, Num(55)), Seq(Num(75), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(484), Minus, Num(345), Slash, Num(242)), Num(1))),
        8 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Plus, Num(3), Cdot, Radical, Slash, Num(22)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(44), Plus, Num(8), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Num(19), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Minus, Num(17), Cdot, Radical, Slash, Num(44)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(440), Minus, Num(8), Cdot, Radical, Slash, Num(55)), Seq(Num(199), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(1396), Minus, Num(436), Slash, Num(349)), Num(1))),
        9 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(2), Minus, Num(7), Cdot, Radical), Seq(Minus, Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(4), Plus, Num(53), Cdot, Radical, Slash, Num(5)), Num(1), Num(0)),
            Vector(Seq(Minus, Num(9), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(20), Plus, Num(27), Cdot, Radical, Slash, Num(4)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(40), Minus, Num(3), Cdot, Radical, Slash, Num(5)), Seq(Num(137), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(872), Minus, Num(321), Slash, Num(218)), Num(1))),
        10 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(2), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(5), Minus, Num(11), Cdot, Radical, Slash, Num(2)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(2), Minus, Num(37), Cdot, Radical, Slash, Num(5)), Num(1), Num(0)),
            Vector(Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(10), Plus, Num(7), Cdot, Radical, Slash, Num(4)), Seq(Minus, Num(43), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(40), Plus, Num(77), Cdot, Radical, Slash, Num(5)), Seq(Num(45), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(176), Minus, Num(127), Slash, Num(44)), Num(1))),
        11 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(19), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(220), Minus, Num(21), Cdot, Radical, Slash, Num(22)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(22), Plus, Num(23), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(440), Plus, Num(15), Cdot, Radical, Slash, Num(44)), Seq(Minus, Num(41), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Plus, Num(62), Cdot, Radical, Slash, Num(55)), Seq(Num(225), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(1448), Minus, Num(523), Slash, Num(362)), Num(1))),
        12 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Radical, Slash, Num(2)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(2), Minus, Num(37), Cdot, Radical, Slash, Num(5)), Num(1), Num(0)),
            Vector(Seq(Minus, Num(5), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(8), Plus, Num(37), Cdot, Radical, Slash, Num(4)), Seq(Minus, Num(7), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(40), Plus, Num(12), Cdot, Radical, Slash, Num(5)), Seq(Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(1)), Num(1))),
        13 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Radical, Slash, Num(2)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(22), Plus, Num(23), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Minus, Num(5), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(88), Plus, Num(45), Cdot, Radical, Slash, Num(44)), Seq(Minus, Num(7), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Plus, Num(2), Cdot, Radical, Slash, Num(55)), Seq(Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(1)), Num(1))),
        14 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Num(21), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Minus, Num(9), Cdot, Radical, Slash, Num(22)), Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(44), Minus, Num(62), Cdot, Radical, Slash, Num(55)), Num(1), Num(0)),
            Vector(Seq(Minus, Num(9), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Plus, Num(25), Cdot, Radical, Slash, Num(44)), Seq(Minus, Num(43), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(440), Plus, Num(72), Cdot, Radical, Slash, Num(55)), Seq(Num(137), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(1448), Minus, Num(201), Slash, Num(362)), Num(1))),
        15 => Vector(
            Vector(Num(1), Num(0), Num(0), Num(0)),
            Vector(Seq(Num(3), Slash, Num(2), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(8)), Num(1), Num(0), Num(0)),
            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(19), Minus, Num(9), Cdot, Radical, Slash, Num(19)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(76), Minus, Num(3), Cdot, Radical, Slash, Num(95)), Num(1), Num(0)),
            Vector(Seq(Minus, Num(7), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(760), Plus, Num(31), Cdot, Radical, Slash, Num(76)), Seq(Minus, Num(41), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(760), Plus, Num(58), Cdot, Radical, Slash, Num(95)), Seq(Num(71), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(528), Minus, Num(149), Slash, Num(132)), Num(1))),
        _ => throw new ArgumentOutOfRangeException(nameof(index))
    };

    private static Formula Pivots(int index) => index switch
    {
        0 => Vector(Seq(Radical, Caret, Grp(Num(2)), Slash, Num(2)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(5), Slash, Num(2)), Seq(Num(2), Cdot, Radical, Caret, Grp(Num(2)), Minus, Num(16)), Seq(Radical, Caret, Grp(Num(2)), Minus, Num(10))),
        1 => Vector(Seq(Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(2)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(3)), Seq(Num(124), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(55), Minus, Num(208), Slash, Num(11)), Seq(Radical, Caret, Grp(Num(2)), Minus, Num(48), Slash, Num(5))),
        2 => Vector(Seq(Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(2)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(3)), Seq(Num(114), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(55), Minus, Num(888), Slash, Num(55)), Seq(Num(542), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(465), Minus, Num(1120), Slash, Num(93))),
        3 => Vector(Seq(Num(7), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(4)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(7), Slash, Num(2)), Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Plus, Num(16), Slash, Num(5)), Seq(Num(39), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(110), Plus, Num(1), Slash, Num(11))),
        4 => Vector(Seq(Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(2)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(3)), Seq(Num(122), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(55), Minus, Num(992), Slash, Num(55)), Seq(Num(1814), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(1745), Minus, Num(3592), Slash, Num(349))),
        5 => Vector(Seq(Num(7), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(4)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(7), Slash, Num(2)), Seq(Num(104), Slash, Num(5), Minus, Num(2), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5)), Seq(Num(262), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(545), Minus, Num(198), Slash, Num(109))),
        6 => Vector(Seq(Num(7), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(4)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(7), Slash, Num(2)), Seq(Num(104), Slash, Num(5), Minus, Num(2), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5)), Seq(Num(262), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(545), Minus, Num(198), Slash, Num(109))),
        7 => Vector(Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(6)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(4)), Seq(Num(2), Cdot, Radical, Caret, Grp(Num(2)), Minus, Num(64), Slash, Num(5)), Seq(Num(2433), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(2662), Minus, Num(10248), Slash, Num(1331))),
        8 => Vector(Seq(Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(2)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(3)), Seq(Num(122), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(55), Minus, Num(992), Slash, Num(55)), Seq(Num(1814), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(1745), Minus, Num(3592), Slash, Num(349))),
        9 => Vector(Seq(Num(7), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(4)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(7), Slash, Num(2)), Seq(Num(104), Slash, Num(5), Minus, Num(2), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5)), Seq(Num(262), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(545), Minus, Num(198), Slash, Num(109))),
        10 => Vector(Seq(Num(7), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(4)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(7), Slash, Num(2)), Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Plus, Num(16), Slash, Num(5)), Seq(Num(39), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(110), Plus, Num(1), Slash, Num(11))),
        11 => Vector(Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(6)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(4)), Seq(Num(114), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(55), Minus, Num(776), Slash, Num(55)), Seq(Num(1638), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(1991), Minus, Num(12522), Slash, Num(1991))),
        12 => Vector(Seq(Num(7), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(4)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(7), Slash, Num(2)), Seq(Num(8), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(8)), Seq(Num(134), Slash, Num(5), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(2))),
        13 => Vector(Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(6)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(4)), Seq(Num(24), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(11), Minus, Num(168), Slash, Num(11)), Seq(Num(17), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(22), Minus, Num(314), Slash, Num(55))),
        14 => Vector(Seq(Num(4), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(5), Minus, Num(6)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(4)), Seq(Num(114), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(55), Minus, Num(776), Slash, Num(55)), Seq(Num(1638), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(1991), Minus, Num(12522), Slash, Num(1991))),
        15 => Vector(Seq(Num(9), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(10), Minus, Num(8)), Seq(Num(5), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(8), Minus, Num(9), Slash, Num(2)), Seq(Num(216), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(95), Minus, Num(1488), Slash, Num(95)), Seq(Num(201), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(220), Minus, Num(238), Slash, Num(33))),
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
