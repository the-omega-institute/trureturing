using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementDescent;

internal sealed class ControlledCompletionDescentDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/RefinementDescent/ControlledCompletionDescent."
            + "controlled_completion_update_and_readout_descend";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical controlled updates and readouts are the unique maps descending to completion.",
        H("Controlled Completion Descent"),
        Blocks(Describe.Lean(
            DescribeId.Create("controlled-completion-update-and-readout-descend"),
            DeclarationHandle.Create(Declaration),
            H("Controlled updates and the joint readout descend canonically"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The carrier is the existing quotient by equality of all readouts after "
                        + "finite input words. Its projection, input-indexed updates, and current "
                        + "readout are the canonical controlled-completion objects.")),
                Paragraph(Text(
                    "For every input, an endomap commutes with the quotient projection exactly "
                        + "when it is the canonical completion update. A readout from the "
                        + "quotient factors the original readout exactly when it is the canonical "
                        + "completion readout.")),
                Paragraph(Text(
                    "The update half applies the frozen unique controlled-descent theorem. The "
                        + "readout half uses surjectivity of the quotient projection to prove "
                        + "uniqueness on every completed state.")),
                Paragraph(Text(
                    "Repository search found the update-only unique descent theorem but no "
                        + "statement carrying the joint-readout descent clause as well."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula controls = F.Id("U");
        Formula states = F.Id("Y");
        Formula outputs = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula control = F.Id("u");
        Formula descended = F.Id("G");
        Formula descendedReadout = F.Id("r");
        Formula completion = Call("ControlledCompletion", update, readout);
        Formula projection = Call("completionProjection", update, readout);
        Formula canonicalUpdate = Call("completionUpdate", update, readout, control);
        Formula canonicalReadout = Call("completionReadout", update, readout);
        Formula updateSquare = EqualTo(
            Seq(projection, Sp, Circ, Sp, Apply(update, control)),
            Seq(descended, Sp, Circ, Sp, projection));
        Formula readoutSquare = EqualTo(
            readout,
            Seq(descendedReadout, Sp, Circ, Sp, projection));
        Formula updateCharacterization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("u", controls), Bound("G", Arrow(completion, completion))],
            Seq(Open, updateSquare, Close, Sp, Iff, Sp,
                EqualTo(descended, canonicalUpdate)));
        Formula readoutCharacterization = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("r"),
            Arrow(completion, outputs),
            Seq(Open, readoutSquare, Close, Sp, Iff, Sp,
                EqualTo(descendedReadout, canonicalReadout)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("U", type),
                Bound("Y", type),
                Bound("O", type),
                Bound("F", Arrow(controls, Arrow(states, states))),
                Bound("q", Arrow(states, outputs)),
            ],
            new Formula.Logic(
                Seq(Open, updateCharacterization, Close),
                FormulaLogicOperator.And,
                Seq(Open, readoutCharacterization, Close))));
    }
}
