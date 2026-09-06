using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class QuquintCertificateDataDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Magic/QuquintCertificateData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact numerical branch data in a real quartic field.",
        H("Ququint Numerical Certificate Data"),
        Blocks(
            Describe.Lean(DescribeId.Create("ququint-certificate-radical"),
                DeclarationHandle.Create(Module + "radical"), H("The real radical"),
                StatementSource.FromAuthor(Disp(Seq(Name("radical"), Eq,
                    Sqrt, Grp(Seq(D(1, 0), Plus, D(2), Cdot, Sqrt, Grp(D(5))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive real square root fixes the radical used in every numerical entry."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ququint-certificate-square"),
                DeclarationHandle.Create(Module + "radical_sq"), H("Square identity"),
                StatementSource.FromAuthor(Disp(Seq(Radical, Caret, Grp(D(2)), Eq,
                    D(1, 0), Plus, D(2), Cdot, Sqrt, Grp(D(5))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Real.sq_sqrt gives the shared square identity used by the quartic relation and bounds."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ququint-certificate-quartic"),
                DeclarationHandle.Create(Module + "radical_quartic"), H("Quartic identity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Name("radical"), Caret, Grp(D(4)), Minus, D(2, 0), Cdot,
                    Name("radical"), Caret, Grp(D(2)), Plus, D(8, 0), Eq, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Squaring the defining radical and using Real.sq_sqrt gives the exact quartic relation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ququint-certificate-radical-bounds"),
                DeclarationHandle.Create(Module + "radical_bounds"), H("Bounds for the squared radical"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(1, 4), Lt, Name("radical"), Caret, Grp(D(2)), Sp, Land, Sp,
                    Name("radical"), Caret, Grp(D(2)), Lt, D(1, 5)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The squared radical lies strictly between fourteen and fifteen; these bounds certify the pivots."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ququint-certificate-base"),
                DeclarationHandle.Create(Module + "base"), H("The numerical base matrix"),
                StatementSource.FromAuthor(Disp(Seq(Name("base"), Eq,
                    Vector(
                        Vector(Seq(Num(5), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(4)), Seq(Radical, Caret, Grp(Num(2)), Slash, Num(8)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(8), Plus, Radical, Slash, Num(2)), Seq(Minus, Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(16), Plus, Num(5), Cdot, Radical, Slash, Num(4))),
                        Vector(Seq(Radical, Caret, Grp(Num(2)), Slash, Num(8)), Seq(Num(5), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(4)), Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(16), Minus, Num(5), Cdot, Radical, Slash, Num(4)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(8), Minus, Radical, Slash, Num(2))),
                        Vector(Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(8), Plus, Radical, Slash, Num(2)), Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(16), Minus, Num(5), Cdot, Radical, Slash, Num(4)), Seq(Num(21), Minus, Num(61), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(20)), Seq(Num(10), Minus, Num(83), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(40))),
                        Vector(Seq(Minus, Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(16), Plus, Num(5), Cdot, Radical, Slash, Num(4)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(8), Minus, Radical, Slash, Num(2)), Seq(Num(10), Minus, Num(83), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(40)), Seq(Num(21), Minus, Num(61), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(20))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Matrices are vectors of rows. QuquintCertificateBridge.base_eq identifies "
                    + "base with the signed nonzero phase-point contribution minus the norm contribution."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ququint-certificate-zero-forms"),
                DeclarationHandle.Create(Module + "zeroQ"), H("The five numerical matrices"),
                StatementSource.FromAuthor(Disp(Seq(Name("zeroQ"), Eq, Vector(
                        Vector(
                            Vector(Seq(Num(1), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(20)), Seq(Num(1), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(40)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Radical, Slash, Num(2)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(80), Minus, Radical, Slash, Num(20))),
                            Vector(Seq(Num(1), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(40)), Seq(Num(1), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(20)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(80), Minus, Num(7), Cdot, Radical, Slash, Num(20)), Seq(Minus, Radical, Slash, Num(10))),
                            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Radical, Slash, Num(2)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(80), Minus, Num(7), Cdot, Radical, Slash, Num(20)), Seq(Num(9), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(100), Minus, Num(1), Slash, Num(5)), Seq(Num(17), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(200), Minus, Num(2), Slash, Num(5))),
                            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(80), Minus, Radical, Slash, Num(20)), Seq(Minus, Radical, Slash, Num(10)), Seq(Num(17), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(200), Minus, Num(2), Slash, Num(5)), Seq(Num(9), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(100), Minus, Num(1)))),
                        Vector(
                            Vector(Seq(Num(1), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(20)), Seq(Num(1), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(40)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Num(7), Cdot, Radical, Slash, Num(10)), Seq(Minus, Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(80), Plus, Num(13), Cdot, Radical, Slash, Num(20))),
                            Vector(Seq(Num(1), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(40)), Seq(Num(1), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(20)), Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(80), Minus, Num(13), Cdot, Radical, Slash, Num(20)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(20), Plus, Num(7), Cdot, Radical, Slash, Num(10))),
                            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(20), Minus, Num(7), Cdot, Radical, Slash, Num(10)), Seq(Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(80), Minus, Num(13), Cdot, Radical, Slash, Num(20)), Seq(Num(7), Slash, Num(5), Minus, Num(11), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(100)), Seq(Num(17), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(200), Minus, Num(7), Slash, Num(5))),
                            Vector(Seq(Minus, Num(3), Cdot, Radical, Caret, Grp(Num(3)), Slash, Num(80), Plus, Num(13), Cdot, Radical, Slash, Num(20)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(20), Plus, Num(7), Cdot, Radical, Slash, Num(10)), Seq(Num(17), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(200), Minus, Num(7), Slash, Num(5)), Seq(Num(7), Slash, Num(5), Minus, Num(11), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(100)))),
                        Vector(
                            Vector(Seq(Num(1), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(20)), Seq(Num(1), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(40)), Seq(Radical, Slash, Num(10)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(80), Plus, Num(7), Cdot, Radical, Slash, Num(20))),
                            Vector(Seq(Num(1), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(40)), Seq(Num(1), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(20)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(80), Plus, Radical, Slash, Num(20)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(20), Plus, Radical, Slash, Num(2))),
                            Vector(Seq(Radical, Slash, Num(10)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(80), Plus, Radical, Slash, Num(20)), Seq(Num(9), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(100), Minus, Num(1)), Seq(Num(17), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(200), Minus, Num(2), Slash, Num(5))),
                            Vector(Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(80), Plus, Num(7), Cdot, Radical, Slash, Num(20)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(20), Plus, Radical, Slash, Num(2)), Seq(Num(17), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(200), Minus, Num(2), Slash, Num(5)), Seq(Num(9), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(100), Minus, Num(1), Slash, Num(5)))),
                        Vector(
                            Vector(Seq(Num(1), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(20)), Seq(Num(1), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(40)), Seq(Minus, Radical, Slash, Num(10)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(80), Plus, Radical, Slash, Num(20))),
                            Vector(Seq(Num(1), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(40)), Seq(Num(1), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(20)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(80), Minus, Radical, Slash, Num(4)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(40), Plus, Num(3), Cdot, Radical, Slash, Num(10))),
                            Vector(Seq(Minus, Radical, Slash, Num(10)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(80), Minus, Radical, Slash, Num(4)), Seq(Num(3), Slash, Num(5), Minus, Num(11), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(100)), Seq(Num(3), Slash, Num(5), Minus, Num(23), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(200))),
                            Vector(Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(80), Plus, Radical, Slash, Num(20)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(40), Plus, Num(3), Cdot, Radical, Slash, Num(10)), Seq(Num(3), Slash, Num(5), Minus, Num(23), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(200)), Seq(Num(1), Slash, Num(5), Minus, Num(11), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(100)))),
                        Vector(
                            Vector(Seq(Num(1), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(20)), Seq(Num(1), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(40)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(40), Minus, Num(3), Cdot, Radical, Slash, Num(10)), Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(80), Plus, Radical, Slash, Num(4))),
                            Vector(Seq(Num(1), Minus, Num(3), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(40)), Seq(Num(1), Minus, Radical, Caret, Grp(Num(2)), Slash, Num(20)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(80), Minus, Radical, Slash, Num(20)), Seq(Radical, Slash, Num(10))),
                            Vector(Seq(Radical, Caret, Grp(Num(3)), Slash, Num(40), Minus, Num(3), Cdot, Radical, Slash, Num(10)), Seq(Radical, Caret, Grp(Num(3)), Slash, Num(80), Minus, Radical, Slash, Num(20)), Seq(Num(1), Slash, Num(5), Minus, Num(11), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(100)), Seq(Num(3), Slash, Num(5), Minus, Num(23), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(200))),
                            Vector(Seq(Minus, Radical, Caret, Grp(Num(3)), Slash, Num(80), Plus, Radical, Slash, Num(4)), Seq(Radical, Slash, Num(10)), Seq(Num(3), Slash, Num(5), Minus, Num(23), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(200)), Seq(Num(3), Slash, Num(5), Minus, Num(11), Cdot, Radical, Caret, Grp(Num(2)), Slash, Num(100)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("These five matrices use the same row convention and index order as "
                    + "QuquintCertificateBridge.zeroIndex. QuquintCertificateBridge.zeroQ_eq "
                    + "identifies them with the five vanishing phase-point forms."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ququint-certificate-branch"),
                DeclarationHandle.Create(Module + "branch"), H("The thirty-two branches"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Colon, Name("Fin"), Sp, D(3, 2), Comma,
                    Call(Name("branch"), F.Id("s")), Eq, Name("base"), Plus,
                    Sum, Underscore, Grp(Seq(F.Id("i"), Colon, Name("Fin"), Sp, D(5))),
                    Call(Name("ite"), Equal(Call(Seq(Name("Nat"), Dot, Name("mod")),
                        Call(Seq(Name("Nat"), Dot, Name("div")), Call(Name("val"), F.Id("s")),
                            Seq(D(2), Caret, Grp(Seq(D(4), Minus, Call(Name("val"), F.Id("i")))))), D(2)), D(0)),
                        Seq(Minus, D(1)), D(1)), Cdot, Call(Name("zeroQ"), F.Id("i"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nat.div denotes natural-number quotient and Nat.mod denotes remainder; they extract "
                    + "the five bits of the branch index, with the highest bit first. "
                    + "A zero bit contributes minus one and a one bit contributes plus one."))),
                DescribeRole.Definition))));
    
    private static Formula Radical => Name("radical");

    private static Formula Vector(params Formula[] entries) => Seq(OpenBracket,
        Seq(entries.SelectMany((v, i) => i == 0 ? new[] { v } : new[] { Comma, v }).ToArray()), CloseBracket);

    private static Formula Call(Formula f, params Formula[] args) => Seq(f, Parenthesized(
        Seq(args.SelectMany((arg, i) => i == 0 ? new[] { arg } : new[] { Comma, arg }).ToArray())));
    private static Formula Name(string name) => Seq(Mathrm, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
