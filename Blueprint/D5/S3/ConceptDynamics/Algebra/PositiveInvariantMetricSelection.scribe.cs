using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Algebra;

internal sealed class PositiveInvariantMetricSelectionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Algebra/PositiveInvariantMetricSelection."
            + "positive_invariant_metric_selection";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero real drift, unit spectrum, and a positive invariant metric are equivalent.",
        H("Positive Invariant Metric Selection"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-invariant-metric-selection"),
            DeclarationHandle.Create(Declaration),
            H("Positive metric selection is equivalent to zero drift"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The two diagonal modes are constructed from real drift, oscillation, "
                        + "and a strictly positive period.")),
                Paragraph(Text(
                    "The equivalence retains all three clauses: zero drift, unit norm for "
                        + "every spectral value, and preservation of a positive definite "
                        + "Hermitian metric."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula delta = DeltaLower;
        Formula gamma = GammaLower;
        Formula period = F.Id("P");
        Formula lambda = LambdaLower;
        Formula forward = F.Id("u");
        Formula backward = F.Id("v");
        Formula monodromy = F.Id("M");
        Formula metric = F.Id("H");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), complex);
        Formula exponent = Seq(
            Open, delta, Sp, Plus, Sp, F.Id("i"), gamma, Close,
            Sp, Cdot, Sp, period);
        Formula forwardValue = Call("exp", exponent);
        Formula backwardValue = Call("exp", Seq(Minus, Open, exponent, Close));
        Formula modeVector = Grp(
            OpenBracket, forward, Comma, Sp, backward, CloseBracket);
        Formula forwardDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            Typed(forward, complex), Sp, Eq, Sp, forwardValue, Semi, Sp);
        Formula backwardDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            Typed(backward, complex), Sp, Eq, Sp, backwardValue, Semi, Sp);
        Formula matrixDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            Typed(monodromy, matrix), Sp, Eq, Sp,
            Call("diagonal", modeVector), Semi, Sp);
        Formula zeroDrift = Seq(delta, Sp, Eq, Sp, D(0));
        Formula unitSpectrum = Seq(
            Forall, Sp, Typed(lambda, complex), Comma, Sp,
            lambda, Sp, InMacro, Sp, Call("spectrum", complex, monodromy), Comma, Sp,
            new Formula.Norm(lambda), Sp, Eq, Sp, D(1));
        Formula invariantMetric = Seq(
            Exists, Sp, Typed(metric, matrix), Comma, Sp,
            Call("PosDef", metric), Sp, Land, Sp,
            monodromy, Caret, Grp(Star), Sp, Cdot, Sp,
            metric, Sp, Cdot, Sp, monodromy, Sp, Eq, Sp, metric);
        Formula conditions = Grp(
            OpenBracket,
            zeroDrift, Comma, RowBreak, Grp(),
            unitSpectrum, Comma, RowBreak, Grp(),
            invariantMetric,
            CloseBracket);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, delta, Comma, Sp, gamma, Comma, Sp,
            period, Colon, Sp, real, Comma,
            RowBreak, Grp(),
            D(0), Sp, Lt, Sp, period, Sp, Rightarrow,
            RowBreak, Grp(),
            forwardDefinition, backwardDefinition, matrixDefinition,
            RowBreak, Grp(),
            Call("ListTFAE", conditions), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
