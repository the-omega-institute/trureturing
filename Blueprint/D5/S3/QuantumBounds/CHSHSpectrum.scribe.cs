using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class CHSHSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/QuantumBounds/CHSHSpectrum",
            "A conditional CHSH spectral bound supports an exact cubic coefficient."),
        H("CHSH Spectrum and Cubic Coefficient"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-paired-gap-coefficient-has-a-closed-form"),
                H("The paired gap coefficient has a closed form"),
                LeanTheorem(
                    "D5/S3/QuantumBounds/CHSHSpectrum.chsh_cubic_coefficient"),
                CubicCoefficientFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let N, a, and b be real, with 0 < N < 4, a squared equal to 4 + N, "
                        + "and b squared equal to 4 - N. The formal statement starts from the "
                        + "paired four-vertex gap expression: the two vertices of magnitude a "
                        + "contribute the first summand, and the two vertices of magnitude b "
                        + "contribute the second. Clearing its nonzero denominators and using "
                        + "a squared times b squared equal to 16 - N squared gives the displayed "
                        + "rational function exactly.")),
                    Paragraph(Text(
                        "This is the real-algebra coefficient identity. It introduces no random "
                        + "state or observable measure and makes no asymptotic assertion.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("landaus-square-law-constrains-the-chsh-spectrum"),
                H("Landau's square law constrains the CHSH spectrum"),
                LeanTheorem("D5/S3/QuantumBounds/CHSHSpectrum.chsh_spectrum"),
                SpectrumFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The formal theorem proves the algebraic kernel under an explicit spectral "
                        + "hypothesis. It takes four finite complex Hermitian involutions, forms "
                        + "their CHSH matrix S and the negative Kronecker product C of the two "
                        + "local commutators, and assumes the two-point bound `hC`, namely that the "
                        + "real spectrum of C is contained in {N, -N}. It reuses `landau_identity` "
                        + "for S squared equal to 4I + C and proves S Hermitian from the four input "
                        + "observables. Power spectral mapping sends each real eigenvalue of S to "
                        + "the spectrum of S squared; scalar-shift transport and `hC` then yield "
                        + "the displayed four-point spectral inclusion for S.")),
                    Paragraph(Text(
                        "Accordingly, the conclusion is an inclusion rather than an equality: it "
                        + "does not assert that all four values occur or establish their "
                        + "multiplicities. Deriving `hC` from the norm identity N equal to the norm "
                        + "of the tensor product of the two local commutators is an independent "
                        + "tensor-commutator obligation and remains open beyond this module. The "
                        + "epsilon-cubed probability law and its Dirichlet-volume argument are "
                        + "likewise outside this module's scope; no probability formula, volume "
                        + "coefficient, or limiting error term is asserted here.")))))));

    private static Formula CubicCoefficientFormula() => Disp(Seq(
        D(0), Lt, F.Id("N"), Lt, D(4), Comma, Quad, Sp,
        F.Id("a"), Caret, Grp(D(2)), Eq, D(4), Plus, F.Id("N"), Comma, Quad, Sp,
        F.Id("b"), Caret, Grp(D(2)), Eq, D(4), Minus, F.Id("N"),
        Rightarrow, Sp,
        F.Id("K"), Open, F.Id("N"), Close, Colon, Eq,
        Frac,
        Grp(D(2)),
        Grp(D(1, 6), F.Id("N"), Caret, Grp(D(2)), F.Id("a"), Caret, Grp(D(2))),
        Plus,
        Frac,
        Grp(D(2)),
        Grp(D(1, 6), F.Id("N"), Caret, Grp(D(2)), F.Id("b"), Caret, Grp(D(2))),
        Eq,
        Frac,
        Grp(D(1)),
        Grp(F.Id("N"), Caret, Grp(D(2)),
            Open, D(1, 6), Minus, F.Id("N"), Caret, Grp(D(2)), Close),
        Dot));

    private static Formula SpectrumFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")), Sp,
        D(0), Lt, F.Id("N"), Lt, D(4), Comma, Quad, Sp,
        F.Id("S"), Caret, Grp(D(2)), Eq, D(4), F.Id("I"), Plus, F.Id("C"), Comma, RowBreak, Sp,
        Operatorname, Grp(F.Id("spectrum")), Underscore,
        Grp(Mathbb, Grp(F.Id("R"))), Open, F.Id("C"), Close,
        Subseteq, Sp, OpenBrace, F.Id("N"), Comma, Minus, F.Id("N"), CloseBrace,
        Rightarrow, Sp, RowBreak, Sp,
        Operatorname, Grp(F.Id("spectrum")), Underscore,
        Grp(Mathbb, Grp(F.Id("R"))), Open, F.Id("S"), Close,
        Subseteq, Sp, OpenBrace,
        Sqrt, Grp(D(4), Plus, F.Id("N")), Comma,
        Minus, Sqrt, Grp(D(4), Plus, F.Id("N")), Comma,
        Sqrt, Grp(D(4), Minus, F.Id("N")), Comma,
        Minus, Sqrt, Grp(D(4), Minus, F.Id("N")),
        CloseBrace, Dot, Sp,
        End, Grp(F.Id("gathered"))));
}
