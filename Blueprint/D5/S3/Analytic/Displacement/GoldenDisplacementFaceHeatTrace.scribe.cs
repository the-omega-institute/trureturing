using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Displacement;

internal sealed class GoldenDisplacementFaceHeatTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The expansion face supplies the golden germ heat trace, with its heat abscissa honestly bracketed in the golden window; the contraction face has no summable heat coefficient.",
        H("Golden Displacement Face Heat Trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-power-face-length-is-the-golden-spectrum"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.lambdaPlus_prime_pow_eq_goldenSpectrum"),
                H("Prime-power face lengths are the golden spectrum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("p"), Sp, F.Text, Grp(F.Id("prime")), Comma, Sp,
                    Forall, Sp, F.Id("k"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("lambdaPlus")), Open,
                    F.Id("p"), Caret, Grp(F.Id("k"), Plus, D(1)), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("goldenSpectrum")), Open,
                    F.Id("p"), Comma, Sp, F.Id("k"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The prime-power hidden-product formula turns the expansion-face closed form into a substitution-start exponent. The conjugate correction is exactly o5Beta, so the resulting logarithmic length is the corresponding golden-spectrum coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-germ-term-is-the-face-heat-coefficient"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.dTermC_germ_eq_heatCoefficient"),
                H("Positive germ terms are face heat coefficients"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Forall, Sp, F.Id("k"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("dTermC")), Open,
                    F.Id("s"), Comma, Sp, Minus, Psi, Sp, Cdot, Sp, F.Id("s"), Comma, Sp,
                    F.Id("k"), Plus, D(1), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("heatCoefficient")), Open,
                    F.Id("faceLength"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("k"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive natural base, Mathlib's cpow definition rewrites both displacement powers as complex exponentials of real logarithms. The expansion-face closed form combines their exponents into minus s times faceLength k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("face-heat-trace-is-the-complex-germ-product"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.heat_trace_eq_complex_displacement_germ_product"),
                H("The face heat trace is the complex germ product"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    D(1), Sp, Lt, Sp, Varphi, Sp, Cdot, Sp,
                    Operatorname, Grp(F.Id("Re")), Grp(F.Id("s")), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("heatTrace")), Open,
                    F.Id("faceLength"), Comma, Sp, F.Id("s"), Close, Sp, Eq, Sp,
                    Prod, Underscore, Grp(F.Id("p"), Sp, F.Text, Grp(F.Id("prime"))),
                    Open, Sum, Underscore, Grp(F.Id("e"), InMacro, Sp, Mathbb, Grp(F.Id("N"))),
                    F.Id("p"), Caret, Grp(
                        Minus, F.Id("s"), Sp, Cdot, Sp, F.Id("o5Beta"), Grp(F.Id("e"))),
                    Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coefficient identity rewrites the heat trace as the positive-index displacement sum. The zero displacement term vanishes, so the shifted sum is the frozen complex germ section and hence its convergent prime product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("face-heat-converges-above-the-golden-window"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.summable_faceLength_heat"),
                H("Face heat converges above the golden window"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, SigmaLower, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Frac, Grp(D(1)), Grp(Varphi), Sp, Lt, Sp, SigmaLower, Sp,
                    Rightarrow, Sp, Operatorname, Grp(F.Id("Summable")), Open,
                    F.Id("k"), Mapsto, Sp, F.Id("e"), Caret, Grp(
                        Minus, SigmaLower, Sp, Operatorname, Grp(F.Id("faceLength")),
                        Open, F.Id("k"), Close), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Beyond one over phi, the conjugate displacement section lies in the absolute-convergence half-plane. Restricting its summable norm series to positive indices and using the exact coefficient norm gives the face heat series."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("face-heat-diverges-below-the-golden-window"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.not_summable_faceLength_heat"),
                H("Face heat diverges below the golden window"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, SigmaLower, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    SigmaLower, Sp, Leq, Sp,
                    Frac, Grp(D(1)), Grp(Varphi, Caret, Grp(D(2))), Sp,
                    Rightarrow, Sp, Neg, Sp, Operatorname, Grp(F.Id("Summable")), Open,
                    F.Id("k"), Mapsto, Sp, F.Id("e"), Caret, Grp(
                        Minus, SigmaLower, Sp, Operatorname, Grp(F.Id("faceLength")),
                        Open, F.Id("k"), Close), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A summable face series would remain summable on the injectively embedded prime indices. Their exact face lengths reduce the subseries to the prime rpow series with exponent at least minus one, contradicting Mathlib's sharp prime-series criterion, including at the boundary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("face-heat-abscissa-is-bracketed-in-the-golden-window"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.faceLength_heat_abscissa_bracket"),
                H("The face heat abscissa is bracketed in the golden window"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsHeatAbscissa")), Open,
                    F.Id("faceLength"), Comma, Sp, Alpha, Close, Sp, Rightarrow, Sp,
                    Frac, Grp(D(1)), Grp(Varphi, Caret, Grp(D(2))), Sp,
                    Leq, Sp, Alpha, Sp, Leq, Sp, Frac, Grp(D(1)), Grp(Varphi)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The prime subfamily forces every abscissa to be at least one over phi squared, while displacement-series convergence forces it to be at most one over phi. This is only a bracket: an exact value would require a local-to-global summability lemma not present in the pinned library."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("contraction-face-heat-is-never-summable"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.not_summable_contraction_face_heat"),
                H("Contraction-face heat is never summable"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Neg, Sp, Operatorname, Grp(F.Id("Summable")), Open,
                    Operatorname, Grp(F.Id("heatCoefficient")), Open,
                    F.Id("contractionLength"), Comma, Sp, F.Id("s"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Along the powers of two, the prime radical is fixed at two. The contraction radical bound therefore keeps every selected length in one bounded interval, giving the heat coefficients a uniform positive norm lower bound and contradicting the zero-term condition for a summable series."))),
                DescribeRole.Theorem))));
}
