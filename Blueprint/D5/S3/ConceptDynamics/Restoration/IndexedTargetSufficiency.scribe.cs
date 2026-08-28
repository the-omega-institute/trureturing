using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Restoration;

internal sealed class IndexedTargetSufficiencyDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Restoration/IndexedTargetSufficiency."
            + "indexed_target_sufficiency";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An indexed local readout is target-sufficient exactly when its complete readout "
            + "has no target-sensitive defect.",
        H("Indexed Target Sufficiency"),
        Blocks(Describe.Lean(
            DescribeId.Create("indexed-target-sufficiency-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Target stability, recovery, and empty defect are equivalent"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The complete readout is constructed from the indexed local channels by "
                        + "collecting every coordinate into one dependent tuple. Its target "
                        + "defect contains exactly the state pairs that all channels merge "
                        + "while the target separates them.")),
                Paragraph(Text(
                    "On an inhabited state space, the accepted recovery criterion supplies a "
                        + "factor on the full dependent output type. Function extensionality "
                        + "identifies equality of complete readouts with coordinatewise local "
                        + "equivalence.")),
                Paragraph(Text(
                    "The final public witness uses the same constant local readout and constant "
                        + "target for its empty defect, recovery factor, and failure of state "
                        + "injectivity. It therefore shows that task sufficiency does not require "
                        + "recovering complete identity."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Applied(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula targetType = F.Id("T");
        Formula output = F.Id("O");
        Formula index = F.Id("i");
        Formula readout = F.Id("q");
        Formula target = F.Id("t");
        Formula completeReadout = new Formula.Subscript(F.Id("q"), F.Id("all"));
        Formula targetResidual = Call("defectRelation", completeReadout, target);
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula recover = F.Id("r");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula outputAtIndex = Applied(output, index);
        Formula outputProduct = Seq(
            Prod, Underscore, Grp(index, Colon, Sp, indexType), outputAtIndex);
        Formula locallyStable = Seq(
            Forall, Sp, left, Comma, Sp, right, Colon, Sp, stateType, Comma, Sp,
            Open, Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            Equal(Call("q", index, left), Call("q", index, right)), Close,
            Sp, Rightarrow, Sp,
            Equal(Applied(target, left), Applied(target, right)));
        Formula recoverable = Seq(
            Exists, Sp, recover, Colon, Sp, Arrow(outputProduct, targetType), Comma, Sp,
            Equal(target, Seq(recover, Sp, Circ, Sp, completeReadout)));

        Formula witnessReadout = F.Id("q0");
        Formula witnessTarget = F.Id("t0");
        Formula witnessComplete = Call("jointReadout", witnessReadout);
        Formula witnessResidual = Call("defectRelation", witnessComplete, witnessTarget);
        Formula witnessFactorization = Seq(
            Exists, Sp, recover, Colon, Sp,
            Arrow(Seq(Open, Arrow(F.Id("Unit"), F.Id("Unit")), Close), F.Id("Unit")),
            Comma, Sp,
            Equal(witnessTarget, Seq(recover, Sp, Circ, Sp, witnessComplete)));
        Formula witness = Seq(
            Exists, Sp, witnessReadout, Colon, Sp,
            Forall, Sp, index, Colon, Sp, F.Id("Unit"), Comma, Sp,
            Arrow(F.Id("Bool"), F.Id("Unit")), Comma, Sp,
            witnessTarget, Colon, Sp, Arrow(F.Id("Bool"), F.Id("Unit")), Comma,
            RowBreak, Grp(),
            Equal(witnessResidual, Emptyset), Sp, Land, Sp,
            witnessFactorization, Sp, Land, Sp,
            Neg, Sp, Call("Injective", witnessComplete));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Comma, Sp, stateType, Comma, Sp,
                targetType, Colon, Sp, type, Comma, Sp,
                output, Colon, Sp, Arrow(indexType, type), Comma),
            Seq(
                Call("Nonempty", stateType), Comma, Sp,
                readout, Colon, Sp, Forall, Sp, index, Colon, Sp, indexType,
                Comma, Sp, Arrow(stateType, outputAtIndex), Comma, Sp,
                target, Colon, Sp, Arrow(stateType, targetType), Sp, Rightarrow),
            Seq(
                completeReadout, Sp, Eq, Sp, Call("jointReadout", readout), Comma),
            Seq(
                Open, Equal(targetResidual, Emptyset), Sp, Leftrightarrow, Sp,
                locallyStable, Close, Sp, Land),
            Seq(Open, Open, locallyStable, Close, Sp, Leftrightarrow, Sp,
                recoverable, Close, Sp, Land),
            Seq(
                Open, Equal(targetResidual, Emptyset), Sp, Leftrightarrow, Sp,
                recoverable, Close, Sp, Land),
            Seq(witness, Dot),
        ]));
    }
}
