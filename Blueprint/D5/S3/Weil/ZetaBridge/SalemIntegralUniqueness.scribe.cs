using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class SalemIntegralUniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/SalemIntegralUniqueness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Weil/salem1953integralequation");
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Delta => F.Id("delta");
    private static Formula Y => F.Id("y");
    private static Formula T => F.Id("t");
    private static Formula U => F.Id("u");
    private static Formula Mu => Call("restrict", Call("volume"), Call("Ioi", D(0)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Salem integral equation has only the almost-everywhere zero bounded "
            + "completed-measurable complex solution for every delta in (1/2,1) exactly when RH holds.",
        H("Salem Integral Uniqueness"),
        Blocks(
            Paragraph(Text(
                "Volume is real Lebesgue measure, and mu is its restriction to (0,infinity). "
                    + "All displayed powers of positive t in the original integral are real "
                    + "powers included in the complex numbers. NullMeasurable means measurable "
                    + "on the completed sigma algebra of mu; it allows arbitrary representatives "
                    + "on null sets. The conclusion is mu-almost-everywhere equality.")),
            Describe.Lean(DescribeId.Create("salem-kernel"),
                DeclarationHandle.Create(Prefix + "salemKernel"), H("The logarithmic kernel"),
                StatementSource.FromAuthor(Disp(All("delta", R, All("u", R,
                    Equal(Call("salemKernel", Delta, U), new Formula.Fraction(
                        Call("exp", Seq(Delta, Thin, U)),
                        Seq(Call("exp", Call("exp", U)), Plus, D(1)))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is Salem's kernel on page 1128, regarded as complex-valued. "
                        + "For delta > 0 it belongs to L1: the exponential Jacobian "
                        + "integrability equivalence transfers the existing Fermi Mellin "
                        + "integrability theorem at scale one. The Fourier convention "
                        + "exp(-2 pi i u xi) identifies its transform with the Mellin "
                        + "integral at delta - 2 pi i xi."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-integral-convolution-transport"),
                DeclarationHandle.Create(Prefix + "salem_integral_eq_convolution"),
                H("Original integral in convolution coordinates"),
                StatementSource.FromAuthor(Disp(All("delta", R, All("y", R,
                    All("f", Seq(R, To, C), Equal(Original(Call("exp", Y)),
                        Seq(Call("exp", Seq(Minus, Delta, Thin, Y)), Thin, Convolution()))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Apply the positive-logarithmic Mellin dilation identity, then "
                            + "translate by y. The exponent contributes the factor exp(-delta y). "
                            + "This equality holds for arbitrary delta, y and f using totalized "
                            + "Bochner integrals; it does not assert convergence by itself.")),
                    Paragraph(Text(
                        "For delta > 0 and bounded NullMeasurable f, positive-scale Fermi "
                            + "Mellin integrability and bounded multiplication prove genuine "
                            + "integrability of the original integrand. Kernel integrability "
                            + "and the transported bound prove genuine convolution integrability. "
                            + "The completed measure agrees on every set and has the same AE "
                            + "filter. Trimming it to the original sigma algebra and applying "
                            + "the Bochner integral trim theorem identifies its integral with "
                            + "the one displayed here."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-bounded-measurable-uniqueness-iff-rh"),
                DeclarationHandle.Create(Prefix + "salem_bounded_measurable_uniqueness_iff_rh"),
                H("Full bounded measurable uniqueness iff RH"),
                StatementSource.FromAuthor(Disp(Criterion())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "The quantifiers include every real delta strictly between 1/2 and 1, "
                            + "every complex function on the real line whose restriction to the "
                            + "positive half-line is completed-measurable, and one finite "
                            + "nonnegative real bound B valid at every positive t. The equation "
                            + "holds for every positive scale x. Values at nonpositive t have "
                            + "no effect. No integrability or regularity of f is assumed.")),
                    Paragraph(Text(
                        "For RH implies uniqueness, put g(v) = f(exp(-v)). The maps exp(-v) "
                            + "and -log(t) preserve null sets in both directions, using the "
                            + "differentiability of their inverses on the appropriate domains. "
                            + "Complex separability converts NullMeasurable to AE strong "
                            + "measurability. Thus g meets the measurability and bound required "
                            + "by the existing bounded convolution cancellation theorem.")),
                    Paragraph(Text(
                        "The existing Fermi Mellin criterion gives a nowhere-zero spectrum. "
                            + "Gamma(s)(1-2^(1-s))zeta(s) is holomorphic on 0 < Re(s) < 1. "
                            + "Real scalar restriction and composition with s = delta - 2 pi i xi "
                            + "give its real infinite differentiability. Convolution "
                            + "cancellation makes g zero AE; inverse logarithmic transport "
                            + "returns the conclusion on the original positive half-line.")),
                    Paragraph(Text(
                        "For the converse, a Mellin zero at delta + i gamma supplies "
                            + "f(t) = exp(i gamma log t). This measurable function has norm one, "
                            + "so it cannot vanish AE on the positive-measure interval (1,2]. "
                            + "Its original integrals are integrable, and positive Mellin "
                            + "scaling multiplies the zero at one by x^(-delta-i gamma). "
                            + "Uniqueness excludes every such zero; the existing Mellin "
                            + "nonvanishing equivalence yields RH.")),
                    Paragraph(Text(
                        "Salem's 1953 note gives the bounded-equation and Wiener-transform "
                            + "argument. The explicit complex, completed-measure and AE "
                            + "conventions, and the all-delta right-half-strip formulation, "
                            + "are the modern original-integral statement explained in the "
                            + "Library note. FermiMellin and SmoothConvolutionUniqueness "
                            + "provide the separately attributed implementation results."))),
                DescribeRole.Theorem))));

    private static Formula Criterion()
    {
        var bound = new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("B"), R)],
            And(Rel(D(0), FormulaRelationOperator.LessThanOrEqual, F.Id("B")),
                All("t", R, Implies(Less(D(0), T),
                    Rel(Seq(Vert, Call("f", T), Vert),
                        FormulaRelationOperator.LessThanOrEqual, F.Id("B"))))));
        var equation = All("x", R, Implies(Less(D(0), F.Id("x")),
            Equal(Original(F.Id("x")), D(0))));
        var conclusion = Seq(Forall, Underscore, Grp(Mathrm, Grp(F.Id("ae")), Sp, Mu),
            Sp, T, InMacro, R, Comma, Sp, Call("f", T), Eq, D(0));
        return new Formula.Logic(Call("RiemannHypothesis"), FormulaLogicOperator.Iff,
            All("delta", R, Implies(Less(new Formula.Fraction(D(1), D(2)), Delta),
                Implies(Less(Delta, D(1)), All("f", Seq(R, To, C),
                    Implies(Call("NullMeasurable", F.Id("f"), Mu),
                        Implies(bound, Implies(equation, conclusion))))))));
    }

    private static Formula Original(Formula x) => Seq(Int, Underscore, Grp(D(0)),
        Caret, Grp(Infty), Sp, new Formula.Fraction(
            Seq(T, Caret, Grp(Delta, Minus, D(1)), Thin, Call("f", T)),
            Seq(Call("exp", Seq(x, Thin, T)), Plus, D(1))), Thin, F.Id("d"), T);
    private static Formula Convolution() => Seq(Int, Underscore, Grp(R), Sp,
        Call("salemKernel", Delta, U), Thin,
        Call("f", Call("exp", Seq(U, Minus, Y))), Thin, F.Id("d"), U);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
