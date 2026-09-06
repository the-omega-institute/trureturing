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
            Describe.Remark(DescribeId.Create("ququint-certificate-base"),
                DeclarationHandle.Create(Module + "base"), H("The numerical base matrix"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("base is the explicit four-by-four real matrix "
                    + "whose entries are rational polynomials in radical. "
                    + "QuquintCertificateBridge.base_eq identifies it with the signed "
                    + "nonzero phase-point contribution minus the norm contribution.")))),
            Describe.Remark(DescribeId.Create("ququint-certificate-zero-forms"),
                DeclarationHandle.Create(Module + "zeroQ"), H("The five numerical matrices"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("zeroQ lists five explicit four-by-four real matrices "
                    + "with entries in the same quartic field. QuquintCertificateBridge.zeroQ_eq "
                    + "identifies them with the five vanishing phase-point forms.")))),
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
    
    private static Formula Call(Formula f, params Formula[] args) => Seq(f, Parenthesized(
        Seq(args.SelectMany((arg, i) => i == 0 ? new[] { arg } : new[] { Comma, arg }).ToArray())));
    private static Formula Name(string name) => Seq(Mathrm, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
