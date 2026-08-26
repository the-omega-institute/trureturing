using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PrimeProducts;

internal sealed class FormalFactorTableCounterexamplesDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Formal local-factor data alone supplies neither convergence, a nonzero limit, "
            + "nor locally uniform convergence; an explicit summability admission does.",
        H("Formal Factor Tables Are Not Analytic Functions"),
        Blocks(
            Theorem(
                "constant-two-not-multipliable",
                "constant_two_not_multipliable",
                "The constant-two table is not multipliable",
                ConstantTwoFormula(),
                "Finite products are powers of two. Their values tend to infinity as the "
                    + "finite index set grows, so they cannot converge to a real number."),
            Theorem(
                "constant-half-has-product-zero",
                "constant_half_hasProd_zero",
                "The constant-half table has product zero",
                ConstantHalfFormula(),
                "Finite products are powers of one half. Cardinality tends to infinity, "
                    + "so the unconditional finite-set net converges to zero."),
            Theorem(
                "parameter-factor-has-product-pointwise",
                "parameter_factor_hasProd_pointwise",
                "The power family converges pointwise on its exact elementary domain",
                PointwiseFormula(),
                "At an interior parameter the products are contracting powers and tend "
                    + "to zero. At one every finite product is one."),
            Theorem(
                "pointwise-domain-hypothesis-is-necessary",
                "pointwise_domain_hypothesis_is_necessary",
                "The pointwise domain condition cannot be dropped",
                DomainHypothesisFormula(),
                "At parameter two every factor is two, so the finite products diverge "
                    + "instead of having the claimed endpoint product."),
            Theorem(
                "parameter-factor-not-locally-uniform",
                "parameter_factor_not_locally_uniform",
                "The pointwise power product is not locally uniform",
                LocalUniformFormula(),
                "Every finite product is continuous, while the pointwise limit jumps at "
                    + "one on the closed unit interval. A locally uniform limit would be "
                    + "continuous there."),
            Theorem(
                "absolute-admission-gives-multipliable",
                "absolute_convergence_admission_gives_multipliable",
                "Summable deviations provide an actual product",
                AdmissionFormula(),
                "Pinned Mathlib turns absolute summability of the deviations from one into "
                    + "multipliability of the corresponding one-plus-deviation factors."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string heading,
        Formula formula,
        string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Theorem);

    private static Formula ConstantTwoFormula() => F.Disp(F.Seq(
        F.Neg, Call("Multipliable", ConstantTable(F.D(2))), F.Dot));

    private static Formula ConstantHalfFormula() => F.Disp(Call(
        "HasProd",
        ConstantTable(F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(F.D(2)))),
        F.D(0)));

    private static Formula PointwiseFormula()
    {
        Formula x = F.Id("x");
        Formula premise = F.Seq(
            F.Lvert, F.Sp, x, F.Rvert, F.Sp, F.Lt, F.Sp, F.D(1),
            F.Sp, F.Lor, F.Sp, x, F.Sp, F.Eq, F.Sp, F.D(1));
        Formula factors = F.Seq(
            F.Id("n"), F.Mapsto, F.Sp, Call("parameterFactorTable", F.Id("n"), x));
        return F.Disp(F.Seq(
            F.Forall, F.Sp, x, F.InMacro, F.Sp, RealNumbers(), F.Comma, F.Sp,
            premise, F.Sp, F.Rightarrow, F.Sp,
            Call("HasProd", factors, Call("endpointProductLimit", x)), F.Dot));
    }

    private static Formula LocalUniformFormula() => F.Disp(F.Seq(
        F.Neg,
        Call(
            "HasProdLocallyUniformlyOn",
            F.Id("parameterFactorTable"),
            F.Id("endpointProductLimit"),
            Call("Icc", F.D(0), F.D(1))),
        F.Dot));

    private static Formula DomainHypothesisFormula()
    {
        Formula two = F.D(2);
        Formula factors = F.Seq(
            F.Id("n"), F.Mapsto, F.Sp,
            Call("parameterFactorTable", F.Id("n"), two));
        return F.Disp(F.Seq(
            F.Neg,
            Call("HasProd", factors, Call("endpointProductLimit", two)),
            F.Dot));
    }

    private static Formula AdmissionFormula()
    {
        Formula f = F.Id("f");
        return F.Disp(F.Seq(
            F.Forall, F.Sp, f, F.Comma, F.Sp,
            Call("AbsoluteConvergenceAdmission", f),
            F.Sp, F.Rightarrow, F.Sp, Call("Multipliable", f), F.Dot));
    }

    private static Formula ConstantTable(Formula value) =>
        Call("constantFactorTable", value);

    private static Formula RealNumbers() => F.Seq(F.Mathbb, F.Grp(F.Id("R")));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
