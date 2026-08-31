using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class FiniteRankConcentrationModeBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite trace budget bounds and finitely supports every positive spectral superlevel.",
        H("Finite-Rank Concentration Mode Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-rank-concentration-mode-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/FiniteRankConcentrationModeBound."
                        + "finite_rank_concentration_mode_bound"),
                H("Finite trace permits only finitely many strong modes"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let lambda be a nonnegative summable sequence of concentration "
                            + "eigenvalues. Its trace is the interval radius L times the finite "
                            + "frequency measure m, divided by pi.")),
                    Paragraph(Text(
                        "For every positive threshold eta, summability forces the eta-superlevel "
                            + "set to be finite. The frozen innovation-count owner then bounds "
                            + "its cardinality by the total trace divided by eta, which is exactly "
                            + "L m divided by pi eta.")),
                    Paragraph(Text(
                        "Repository search found the frozen general count owner and this theorem "
                            + "applies it directly. Pinned Mathlib has the supporting convergence "
                            + "and finite-sum estimates but no theorem exposing both finiteness and "
                            + "the trace-normalized cardinality bound."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula eigenvalue = F.LambdaLower;
        Formula intervalRadius = F.Id("L");
        Formula frequencyMeasure = F.Id("m");
        Formula threshold = F.Id("eta");
        Formula index = F.Id("j");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula indexedEigenvalue = Apply(eigenvalue, index);
        Formula strongModes = Seq(
            OpenBrace, index, Sp, InMacro, Sp, natural, Sp, Mid, Sp,
            threshold, Sp, Leq, Sp, indexedEigenvalue, CloseBrace);
        Formula trace = Seq(
            Sum, Underscore, Grp(index, Eq, D(0)), Caret, Grp(Infty), Sp,
            indexedEigenvalue);
        Formula traceValue = Seq(
            Frac, Grp(intervalRadius, Sp, frequencyMeasure), Grp(Pi));
        Formula countBound = Seq(
            Frac, Grp(intervalRadius, Sp, frequencyMeasure),
            Grp(Pi, Sp, threshold));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, eigenvalue, Colon, Sp, natural, Sp, To, Sp, real, Comma, Sp,
            intervalRadius, Comma, Sp, frequencyMeasure, Comma, Sp, threshold,
            Sp, InMacro, Sp, real, Comma, RowBreak,
            Open, Forall, Sp, index, Sp, InMacro, Sp, natural, Comma, Sp,
            D(0), Sp, Leq, Sp, indexedEigenvalue, Close, Sp, Land, Sp,
            Call("Summable", eigenvalue), Sp, Land, Sp,
            trace, Sp, Eq, Sp, traceValue, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, threshold, Sp, Rightarrow, RowBreak,
            Call("Finite", strongModes), Sp, Land, Sp,
            Call("ncard", strongModes), Sp, Leq, Sp, countBound, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
