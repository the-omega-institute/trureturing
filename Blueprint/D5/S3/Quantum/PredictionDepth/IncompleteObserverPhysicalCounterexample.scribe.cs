using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PredictionDepth;

internal sealed class IncompleteObserverPhysicalCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/PredictionDepth/IncompleteObserverPhysicalCounterexample."
            + "incomplete_observer_physical_counterexample";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An incomplete finite observer has distinct symmetric states with equal readouts.",
        H("Incomplete Observer Physical Counterexample"),
        Blocks(Describe.Lean(
            DescribeId.Create("incomplete-observer-has-distinct-indistinguishable-physical-states"),
            DeclarationHandle.Create(Declaration),
            H("An incomplete observer admits distinct indistinguishable physical states"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The visible real Hermitian subspace is constructed from the scalar identity "
                        + "line and the embedded span of the centered effects. Incompleteness means "
                        + "that its orthogonal residual contains a nonzero direction.")),
                Paragraph(Text(
                    "A sufficiently small positive perturbation in both signs around the maximally "
                        + "mixed state remains positive and trace one. Orthogonality to every "
                        + "centered effect makes the two real trace signatures equal, while the "
                        + "nonzero direction makes the states distinct."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), indexType = F.Id("Index"), effects = F.Id("E");
        Formula index = F.Id("i"), direction = F.Id("D"), eps = F.Id("eps");
        Formula rhoPlus = F.Id("rhoPlus"), rhoMinus = F.Id("rhoMinus");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula hermitian = Seq(Operatorname, Grp(F.Id("Herm")), Underscore, Grp(d));
        Formula traceZero = Seq(hermitian, Caret, Grp(D(0)));
        Formula stateType = Call("DensityState", Call("Fin", d));
        Formula effect = Apply(effects, index);
        Formula centeredVisible = Call(
            "span", reals,
            Seq(OpenBrace, effect, Sp, Mid, Sp, index, Colon, Sp, indexType, CloseBrace));
        Formula visible = Seq(reals, F.Id("I"), Sp, Plus, Sp, centeredVisible);
        Formula residual = Seq(Open, visible, Close, Caret, Grp(Perp));
        Formula matrixPlus = Call("matrix", rhoPlus);
        Formula matrixMinus = Call("matrix", rhoMinus);
        Formula inverseDimension = new Formula.Power(d, Grp(Seq(Minus, D(1))));
        Formula plusEquation = Seq(
            matrixPlus, Sp, Eq, Sp, inverseDimension, F.Id("I"), Sp, Plus, Sp,
            eps, direction);
        Formula minusEquation = Seq(
            matrixMinus, Sp, Eq, Sp, inverseDimension, F.Id("I"), Sp, Minus, Sp,
            eps, direction);
        Formula readout(Formula state) => Seq(
            Re, Sp, Call("Tr", Seq(Call("matrix", state), Sp, effect)));
        Formula equalReadouts = Seq(
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            readout(rhoPlus), Sp, Eq, Sp, readout(rhoMinus));

        return Disp(Seq(
            Forall, Sp, d, InMacro, Sp, naturals, Comma, Sp,
            Call("NeZero", d), Comma, Sp,
            indexType, Colon, Sp, Seq(Operatorname, Grp(F.Id("Type"))), Comma, RowBreak,
            Grp(), effects, Colon, Sp, indexType, Sp, To, Sp, traceZero, Comma, RowBreak,
            Grp(), residual, Sp, Neq, Sp, OpenBrace, D(0), CloseBrace, Sp,
            Rightarrow, RowBreak,
            Grp(), Exists, Sp,
            direction, Colon, Sp, hermitian, Comma, Sp,
            eps, Colon, Sp, reals, Comma, Sp,
            rhoPlus, Comma, Sp, rhoMinus, Colon, Sp, stateType, Comma, RowBreak,
            Grp(), direction, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            direction, Sp, InMacro, Sp, residual, Sp, Land, RowBreak,
            Grp(), D(0), Sp, Lt, Sp, eps, Sp, Land, RowBreak,
            Grp(), plusEquation, Sp, Land, RowBreak,
            Grp(), minusEquation, Sp, Land, RowBreak,
            Grp(), rhoPlus, Sp, Neq, Sp, rhoMinus, Sp, Land, RowBreak,
            Grp(), equalReadouts, Dot));
    }
}
