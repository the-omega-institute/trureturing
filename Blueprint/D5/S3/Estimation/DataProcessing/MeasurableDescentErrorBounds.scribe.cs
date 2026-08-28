using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class MeasurableDescentErrorBoundsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/DataProcessing/MeasurableDescentErrorBounds."
            + "best_measurable_descent_error_bounds";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The best measurable Markov descent error is bounded below by half the observable "
            + "fiber defect and above by that defect when measurable representatives exist.",
        H("Measurable Descent Error Bounds"),
        Blocks(Describe.Lean(
            DescribeId.Create("measurable-descent-error-bounds"),
            DeclarationHandle.Create(Declaration),
            H("Best measurable descent error lies between half and all of the fiber defect"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every candidate Markov kernel on the observable carrier, the measure-level "
                        + "triangle inequality bounds each same-fiber pair distance by twice its "
                        + "uniform descent error. Suprema over pairs and the infimum over candidates "
                        + "give the lower bound.")),
                Paragraph(Text(
                    "A measurable representative map pulls the observed-law kernel back to the "
                        + "observable carrier. Its error at each source state is one of the "
                        + "same-fiber distances, which proves the conditional upper bound."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula source = F.Id("X");
        Formula observable = F.Id("B");
        Formula kernel = F.Id("K");
        Formula readout = F.Id("q");
        Formula representative = F.Id("rep");
        Formula state = F.Id("x");
        Formula defect = Call("observableKernelDefect", kernel, readout);
        Formula best = Call("bestMeasurableDescentError", kernel, readout);

        Formula lower = Seq(
            new Formula.Fraction(defect, D(2)), Sp, Leq, Sp, best);
        Formula sectionLaw = Seq(
            Forall, Sp, Typed(state, source), Comma, Sp,
            Apply(readout, Apply(representative, Apply(readout, state))),
            Sp, Eq, Sp, Apply(readout, state));
        Formula upper = Seq(best, Sp, Leq, Sp, defect);
        Formula representatives = Seq(
            Forall, Sp, Typed(representative, Arrow(observable, source)), Comma, Sp,
            Call("Measurable", representative), Sp, Rightarrow, Sp,
            Open, sectionLaw, Close, Sp, Rightarrow, Sp, upper);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(source, Comma, Sp, observable), type), Comma, RowBreak, Grp(),
            Call("MeasurableSpace", source), Comma, Sp,
            Call("MeasurableSpace", observable), Comma, RowBreak, Grp(),
            Typed(kernel, Call("Kernel", source, source)), Comma, Sp,
            Call("IsMarkovKernel", kernel), Comma, RowBreak, Grp(),
            Typed(readout, Arrow(source, observable)), Comma, Sp,
            Call("Measurable", readout), Sp, Rightarrow, RowBreak, Grp(),
            And(lower, representatives), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
