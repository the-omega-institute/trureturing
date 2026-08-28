using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementAlgebra;

internal sealed class ObservableEventAtomsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAtoms."
            + "nonzero_observable_atoms_are_effective_fibers";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nonempty atoms of a finite observable-event algebra are exactly its effective fibers.",
        H("Atoms of a Finite Observable-Event Algebra"),
        Blocks(Describe.Lean(
            DescribeId.Create("nonzero-observable-atoms-are-effective-fibers"),
            DeclarationHandle.Create(Declaration),
            H("Nonzero observable atoms are the realized readout fibers"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let X be finite and let q be a readout. An observable event is a subset "
                        + "whose membership is constant on each q-fiber, using the existing "
                        + "observable-event algebra on the exact set carrier.")),
                Paragraph(Text(
                    "A nonempty event is an atom when every nonempty observable subevent "
                        + "contained in it contains it in return. Such an event is exactly the "
                        + "fiber over one value in the realized range of q.")),
                Paragraph(Text(
                    "The forward direction chooses a state in the event and compares it with "
                        + "that state's observable fiber. The reverse direction chooses a "
                        + "representative of the realized value and uses fiber constancy to "
                        + "show that every nonempty observable subevent contains the fiber.")),
                Paragraph(Text(
                    "Pinned Mathlib atom lemmas concern the full powerset lattice. Repository "
                        + "and library searches found no theorem for this observable subalgebra."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(params Formula[] formulas)
    {
        Formula result = formulas[^1];
        for (var index = formulas.Length - 2; index >= 0; index--)
            result = new Formula.Logic(formulas[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("O");
        Formula readout = F.Id("q");
        Formula eventFormula = F.Id("A");
        Formula candidate = F.Id("B");
        Formula observed = F.Id("o");
        Formula setX = Call("Set", stateType);
        Formula observable(Formula value) =>
            Seq(value, Sp, InMacro, Sp, Call("observableEventAlgebra", readout));
        Formula minimal = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("B"),
            setX,
            new Formula.Logic(
                And(
                    Call("Nonempty", candidate),
                    observable(candidate),
                    Seq(candidate, Sp, Subseteq, Sp, eventFormula)),
                FormulaLogicOperator.Implies,
                Seq(eventFormula, Sp, Subseteq, Sp, candidate)));
        Formula atom = And(
            Call("Nonempty", eventFormula), observable(eventFormula), minimal);
        Formula fiber = new Formula.SetBuilder(
            Seq(Apply(readout, F.Id("x")), Sp, Eq, Sp, observed),
            F.Id("x"),
            stateType);
        Formula effectiveFiber = Seq(
            Exists, Sp, observed, InMacro, Sp, Call("range", readout), Comma, Sp,
            eventFormula, Sp, Eq, Sp, fiber);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("O", type),
                Bound("q", Arrow(stateType, outputType)),
                Bound("A", setX),
            ],
            new Formula.Logic(
                Call("Finite", stateType),
                FormulaLogicOperator.Implies,
                Seq(Open, atom, Close, Sp, Iff, Sp, effectiveFiber))));
    }
}
