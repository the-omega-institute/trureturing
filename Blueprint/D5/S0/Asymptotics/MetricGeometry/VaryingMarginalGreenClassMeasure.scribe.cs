using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.MetricGeometry;

internal sealed class VaryingMarginalGreenClassMeasureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Varying probability marginals give exact green-class product mass and critical Hausdorff measure comparisons.",
        H("Varying-Marginal Green-Class Measure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("varying-green-class-measure"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.varying_greenClass_measure"),
                H("A green class has the product of its pinned marginal masses"),
                StatementSource.FromAuthor(Disp(Seq(
                    Mu, Underscore, Grp(Infty), Open,
                    F.Id("G"), Open, F.Id("S"), Comma, Sp, F.Id("t"), Close, Close,
                    Sp, Eq, Sp,
                    Prod, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("S")), Sp,
                    Mu, Underscore, Grp(F.Id("i")), Open,
                    OpenBrace, Grp(F.Id("t"), Underscore, Grp(F.Id("i"))), CloseBrace, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let mu_i be probability measures on a common measurable alphabet whose singletons "
                        + "are measurable. The green class G(S,t) is the finite cylinder that pins coordinate "
                        + "i to t_i for each i in S.")),
                    Paragraph(Text(
                        "Mathlib's infinitePi_pi theorem evaluates this cylinder directly. Its measure is "
                        + "the finite product over i in S of the singleton masses mu_i({t_i}); no uniformity "
                        + "or finiteness assumption on the alphabet is needed for this identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("varying-green-class-measure-positive-iff"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.varying_greenClass_measure_pos_iff"),
                H("Green-class mass is positive exactly when every pinned mass is positive"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Sp, Lt, Sp,
                    Mu, Underscore, Grp(Infty), Open,
                    F.Id("G"), Open, F.Id("S"), Comma, Sp, F.Id("t"), Close, Close,
                    Sp, Iff, Sp,
                    Forall, Sp, F.Id("i"), Sp, InMacro, Sp, F.Id("S"), Comma, Sp,
                    D(0), Sp, Lt, Sp, Mu, Underscore, Grp(F.Id("i")), Open,
                    OpenBrace, Grp(F.Id("t"), Underscore, Grp(F.Id("i"))), CloseBrace, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Substituting the exact cylinder formula reduces positivity to positivity of a "
                        + "finite product in the extended nonnegative reals.")),
                    Paragraph(Text(
                        "CanonicallyOrderedAdd.prod_pos states that such a finite product is strictly "
                        + "positive exactly when every factor indexed by S is strictly positive, including "
                        + "the empty-support case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("varying-mass-below-hausdorff-measure"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.varying_greenClass_measure_le_hausdorffMeasure"),
                H("Upper marginal bounds place varying mass below critical Hausdorff measure"),
                StatementSource.FromAuthor(Disp(Seq(
                    Mu, Underscore, Grp(Infty), Open,
                    F.Id("G"), Open, F.Id("S"), Comma, Sp, F.Id("t"), Close, Close,
                    Sp, Leq, Sp,
                    Mu, Underscore, Grp(F.Id("H")), Caret, Grp(F.Id("d")), Open,
                    F.Id("G"), Open, F.Id("S"), Comma, Sp, F.Id("t"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let n = card O and d = namingDim O. If every pinned singleton mass is at most "
                        + "n^(-1), finite-product monotonicity bounds the varying cylinder mass by n^(-|S|).")),
                    Paragraph(Text(
                        "The uniform green-class formula identifies n^(-|S|) with uniform string measure "
                        + "of G(S,t), and the frozen critical-measure equality identifies that value with "
                        + "the Hausdorff measure at exponent d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hausdorff-measure-below-varying-mass"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.hausdorffMeasure_le_varying_greenClass_measure"),
                H("Lower marginal bounds place critical Hausdorff measure below varying mass"),
                StatementSource.FromAuthor(Disp(Seq(
                    Mu, Underscore, Grp(F.Id("H")), Caret, Grp(F.Id("d")), Open,
                    F.Id("G"), Open, F.Id("S"), Comma, Sp, F.Id("t"), Close, Close,
                    Sp, Leq, Sp,
                    Mu, Underscore, Grp(Infty), Open,
                    F.Id("G"), Open, F.Id("S"), Comma, Sp, F.Id("t"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If every pinned singleton mass is at least n^(-1), finite-product monotonicity "
                        + "places n^(-|S|) below the varying cylinder mass.")),
                    Paragraph(Text(
                        "Rewriting the critical Hausdorff measure of G(S,t) as uniform string measure, "
                        + "then applying the uniform cylinder value, supplies exactly that lower product."))),
                DescribeRole.Theorem))));
}
