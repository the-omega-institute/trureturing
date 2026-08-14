using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.Interference;

internal sealed class DedekindBhkCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational Dedekind sums are periodic in the numerator and satisfy two exact finite BHK certificates.",
        H("Dedekind Sum Foundations and BHK Certificates"),
        Blocks(
            Paragraph(Text(
                "The sawtooth and Dedekind sum are defined over exact rationals. The finite "
                    + "certificates use the frozen alternating walk and verify every displayed "
                    + "continued-fraction, inverse, walk, and correction clause.")),
            Describe.Lean(
                DescribeId.Create("rational-sawtooth"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkCertificates.sawtooth"),
                H("The rational sawtooth"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Q")),
                    Comma, Esc,
                    Operatorname, Grp(F.Id("sawtooth")), Open, F.Id("x"), Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("if")), Open,
                    Operatorname, Grp(F.Id("fract")), Open, F.Id("x"), Close,
                    Sp, Eq, Sp, D(0), Comma, Sp,
                    D(0), Comma, Sp,
                    Operatorname, Grp(F.Id("fract")), Open, F.Id("x"), Close,
                    Sp, Minus, Sp, Frac, Grp(D(1)), Grp(D(2)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At an integral rational the value is zero; otherwise it is the fractional "
                        + "part minus one half."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sawtooth-on-integers"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkCertificates.sawtooth_int"),
                H("The sawtooth vanishes on integers"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("z"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")),
                    Comma, Esc,
                    Operatorname, Grp(F.Id("sawtooth")), Open,
                    OpenBracket, F.Id("z"), CloseBracket, Underscore,
                    Grp(Mathbb, Grp(F.Id("Q"))), Close,
                    Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Casting any integer to the rationals gives an integral sawtooth input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sawtooth-integer-translation"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkCertificates.sawtooth_add_int"),
                H("Integer translation preserves the sawtooth"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Q")),
                    Comma, Esc,
                    Forall, Sp, F.Id("z"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")),
                    Comma, Esc,
                    Operatorname, Grp(F.Id("sawtooth")), Open,
                    F.Id("x"), Sp, Plus, Sp,
                    OpenBracket, F.Id("z"), CloseBracket, Underscore,
                    Grp(Mathbb, Grp(F.Id("Q"))), Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("sawtooth")), Open, F.Id("x"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fractional part, and hence the sawtooth, is invariant under an integral translation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-dedekind-sum"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkCertificates.dedekindSum"),
                H("The rational Dedekind sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("d"), Comma, Sp, F.Id("c"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    F.Id("d"), Comma, Sp, F.Id("c"), Close,
                    Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("k"), Eq, D(1)),
                    Caret, Grp(F.Id("c"), Minus, D(1)),
                    Operatorname, Grp(F.Id("sawtooth")), Open,
                    Frac,
                    Grp(OpenBracket, F.Id("k"), CloseBracket, Underscore,
                        Grp(Mathbb, Grp(F.Id("Q")))),
                    Grp(OpenBracket, F.Id("c"), CloseBracket, Underscore,
                        Grp(Mathbb, Grp(F.Id("Q")))), Close,
                    Operatorname, Grp(F.Id("sawtooth")), Open,
                    Frac,
                    Grp(OpenBracket, F.Id("k"), Thin, F.Id("d"), CloseBracket, Underscore,
                        Grp(Mathbb, Grp(F.Id("Q")))),
                    Grp(OpenBracket, F.Id("c"), CloseBracket, Underscore,
                        Grp(Mathbb, Grp(F.Id("Q")))), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite interval is exactly the natural range from one through c minus one, "
                        + "and both factors are evaluated in the rationals."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dedekind-sum-modulus-periodicity"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkCertificates.s_mod"),
                H("The numerator reduces modulo the denominator"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("d"), Comma, Sp, F.Id("c"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    F.Id("d"), Sp, Operatorname, Grp(F.Id("mod")), Sp, F.Id("c"),
                    Comma, Sp, F.Id("c"), Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    F.Id("d"), Comma, Sp, F.Id("c"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each second sawtooth factor has the same fractional part after reducing d modulo c."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dedekind-sum-one-two"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkCertificates.dedekind_sum_one_two"),
                H("The sum at one over two is zero"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("dedekindSum")), Open, D(1), Comma, Sp, D(2), Close,
                    Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exact finite rational normalization evaluates the single summand to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dedekind-sum-three-four"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkCertificates.dedekind_sum_three_four"),
                H("The sum at three over four"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("dedekindSum")), Open, D(3), Comma, Sp, D(4), Close,
                    Sp, Eq, Sp, Minus, Frac, Grp(D(1)), Grp(D(8))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The three exact rational summands total minus one eighth."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dedekind-sum-four-nine"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkCertificates.dedekind_sum_four_nine"),
                H("The sum at four over nine"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("dedekindSum")), Open, D(4), Comma, Sp, D(9), Close,
                    Sp, Eq, Sp, Minus, Frac, Grp(D(4)), Grp(D(2, 7))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The eight exact rational summands total minus four twenty-sevenths."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bhk-three-four-certificate"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkCertificates.bhk_three_four_certificate"),
                H("An exact BHK certificate at three over four"),
                StatementSource.FromAuthor(Disp(Seq(
                    Frac, Grp(D(1)), Grp(D(1), Plus,
                        Frac, Grp(D(1)), Grp(D(2), Plus, Frac, Grp(D(1)), Grp(D(1)))),
                    Sp, Eq, Sp, Frac, Grp(D(3)), Grp(D(4)), Sp, Land, Sp,
                    Open, D(3), Times, D(3), Close, Sp,
                    Operatorname, Grp(F.Id("mod")), Sp, D(4), Sp, Eq, Sp, D(1),
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("alternatingWalk")), Open,
                    OpenBracket, D(1), Comma, Sp, D(2), Comma, Sp, D(1), CloseBracket, Close,
                    Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    D(1, 2), Times,
                    Operatorname, Grp(F.Id("dedekindSum")), Open, D(3), Comma, Sp, D(4), Close,
                    Sp, Eq, Sp, Minus, D(3), Sp, Plus, Sp,
                    Frac, Grp(D(3), Plus, D(3)), Grp(D(4)), Sp, Minus, Sp,
                    Operatorname, Grp(F.Id("alternatingWalk")), Open,
                    OpenBracket, D(1), Comma, Sp, D(2), Comma, Sp, D(1), CloseBracket, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The odd normalized continued fraction [0; 1, 2, 1] equals three fourths, "
                        + "three is its inverse modulo four, the frozen alternating walk is zero, "
                        + "and the displayed BHK correction identity holds exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bhk-four-nine-certificate"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkCertificates.bhk_four_nine_certificate"),
                H("An exact BHK certificate at four over nine"),
                StatementSource.FromAuthor(Disp(Seq(
                    Frac, Grp(D(1)), Grp(D(2), Plus,
                        Frac, Grp(D(1)), Grp(D(3), Plus, Frac, Grp(D(1)), Grp(D(1)))),
                    Sp, Eq, Sp, Frac, Grp(D(4)), Grp(D(9)), Sp, Land, Sp,
                    Open, D(7), Times, D(4), Close, Sp,
                    Operatorname, Grp(F.Id("mod")), Sp, D(9), Sp, Eq, Sp, D(1),
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("alternatingWalk")), Open,
                    OpenBracket, D(2), Comma, Sp, D(3), Comma, Sp, D(1), CloseBracket, Close,
                    Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    D(1, 2), Times,
                    Operatorname, Grp(F.Id("dedekindSum")), Open, D(4), Comma, Sp, D(9), Close,
                    Sp, Eq, Sp, Minus, D(3), Sp, Plus, Sp,
                    Frac, Grp(D(7), Plus, D(4)), Grp(D(9)), Sp, Minus, Sp,
                    Operatorname, Grp(F.Id("alternatingWalk")), Open,
                    OpenBracket, D(2), Comma, Sp, D(3), Comma, Sp, D(1), CloseBracket, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The odd normalized continued fraction [0; 2, 3, 1] equals four ninths, "
                        + "seven is its inverse modulo nine, the frozen alternating walk is zero, "
                        + "and the displayed BHK correction identity holds exactly."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The suggested [0; 2] case does not satisfy the source's displayed minus-sign "
                    + "formula under the standard positive continued-fraction convention. No general "
                    + "BHK theorem or theorem-shaped placeholder is asserted here; resolving that "
                    + "orientation convention and proving the continued-fraction induction remain Phase 2 work."))),
        []));
}
