using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class SmoothConvolutionUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A smooth nowhere-zero kernel spectrum forces bounded complex convolution solutions to vanish almost everywhere.",
        H("Smooth Convolution Uniqueness"),
        Blocks(Describe.Lean(
            DescribeId.Create("bounded-complex-convolution-cancellation"),
            DeclarationHandle.Create(
                "D5/S3/Fourier/SmoothConvolutionUniqueness."
                    + "ae_eq_zero_of_smooth_fourier_convolution_eq_zero"),
            H("Bounded convolution cancellation with a smooth nonvanishing spectrum"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Fourier/fulsche2025wiener")),
            Blocks(
                Paragraph(Text(
                    "All variables range over the real line unless a complex codomain is shown. "
                        + "Volume denotes Lebesgue measure. FT is the Fourier transform with "
                        + "phase exp(-2 pi i u xi). The conclusion holds for volume-almost every y. "
                        + "AEStronglyMeasurable means almost-everywhere strong measurability. "
                        + "The bound uses one real constant M, nonnegative and valid at every y.")),
                Paragraph(Text(
                    "This is a smooth-spectrum specialization of the bounded cancellation "
                        + "corollary of Wiener's approximation theorem. The source states "
                        + "density of translates in L1, and its complex dual pairing has no "
                        + "conjugation. The functional h mapped to the integral of h(u)g(-u) "
                        + "annihilates every translate of k. Density makes the functional zero; "
                        + "duality and measure-preserving reflection give g = 0 almost everywhere. "
                        + "The source angular frequency is 2 pi times xi. Its general theorem "
                        + "does not require the additional smoothness hypothesis.")),
                Paragraph(Text(
                    "For the smooth-spectrum argument, divide a compact smooth frequency test "
                        + "by FT(k). The quotient remains smooth with compact support, and its "
                        + "inverse Fourier transform is a Schwartz function h whose convolution "
                        + "with k equals the inverse transform of the test. An integrable product "
                        + "majorant permits Fubini with bounded g, so this factor also annihilates g.")),
                Paragraph(Text(
                    "A compact frequency bump equal to one at zero has inverse transform of "
                        + "integral one. Scaling, translation continuity in L1 and dominated "
                        + "convergence approximate each compact smooth spatial test in L1 by "
                        + "inverse transforms of compact smooth frequency tests. The bounded "
                        + "reflected pairing passes to the limit. Local integrability and "
                        + "separation by compact smooth tests yield the almost-everywhere conclusion."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula function = Seq(real, To, complex);
        Formula k = F.Id("k");
        Formula g = F.Id("g");
        Formula m = F.Id("M");
        Formula volume = Call("volume");
        Formula convolution = Seq(
            Int, Underscore, Grp(real), Sp,
            Call("k", F.Id("u")), Thin,
            Call("g", Seq(F.Id("y"), Minus, F.Id("u"))), Thin,
            Mathrm, Grp(F.Id("d")), F.Id("u"));
        Formula bound = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("M", real)], All(
                Rel(D(0), FormulaRelationOperator.LessThanOrEqual, m),
                ForAll([Bound("y", real)], Rel(
                    Seq(Vert, Call("g", F.Id("y")), Vert),
                    FormulaRelationOperator.LessThanOrEqual, m))));
        Formula hypotheses = All(
            Call("Integrable", k, volume),
            Call("ContDiff", real, Infty, Call("FT", k)),
            ForAll([Bound("xi", real)], Rel(
                Call("FT", k, F.Id("xi")), FormulaRelationOperator.NotEqual, D(0))),
            Call("AEStronglyMeasurable", g, volume),
            bound,
            ForAll([Bound("y", real)], Rel(convolution, FormulaRelationOperator.Equal, D(0))));
        Formula conclusion = Seq(
            Forall, Underscore, Grp(Mathrm, Grp(F.Id("ae")), Sp, volume), Sp,
            F.Id("y"), InMacro, real, Comma, Sp, Call("g", F.Id("y")), Eq, D(0));
        return Disp(ForAll([Bound("k", function), Bound("g", function)],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate((left, right) => new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
}
