using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Adjunction;

internal sealed class ProcessConceptAdjunctionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Adjunction/ProcessConceptAdjunction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Process pullback is left adjoint to the maximal predictable future concept.",
        H("Process Concept Adjunction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("process-concept-adjunction"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "process_concept_adjunction"),
                H("Process pullback is left adjoint to predictable future"),
                StatementSource.FromAuthor(AdjunctionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any process, future readout D, and current readout C, the "
                            + "pullback of D refines C exactly when D refines the maximal "
                            + "future readout predictable from C.")),
                    Paragraph(Text(
                        "The future readout is constructed by quotienting future states and "
                            + "current coordinates by the identifications generated along the "
                            + "process. A factor through the pullback descends to this quotient, "
                            + "and a factor from the quotient restricts back to current "
                            + "coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("process-concept-galois-connection"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "process_concept_galois_connection"),
                H("The concept constructions form a Galois connection"),
                StatementSource.FromAuthor(GaloisConnectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The pointwise adjunction equivalence packages the process pullback and "
                        + "maximal predictable future operators as a Galois connection between "
                        + "the refinement preorders on future and current readout concepts."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("process-pullback-is-monotone"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "pullback_concept_monotone"),
                H("Process pullback preserves refinement"),
                StatementSource.FromAuthor(PullbackMonotoneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If one future readout refines another, composing both readouts with the "
                        + "same process preserves that refinement. This monotonicity is the "
                        + "left-side order law supplied by the Galois connection."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("predictable-future-is-monotone"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "pushforward_concept_monotone"),
                H("Predictable future preserves refinement"),
                StatementSource.FromAuthor(PushforwardMonotoneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Refining the current readout refines its maximal predictable future "
                        + "readout as well. This is the right-side monotonicity law obtained "
                        + "from the same Galois connection."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("pullback-of-predictable-future-refines-current"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "pullback_pushforward_refines"),
                H("The predictable future pulls back below the current concept"),
                StatementSource.FromAuthor(CounitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "After constructing the maximal future readout predictable from a current "
                        + "concept and pulling it back along the process, the resulting current "
                        + "readout refines the original concept. This is the counit inequality "
                        + "of the adjunction."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Refines(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Pullback(Formula process, Formula concept) =>
        Call("pullbackConcept", process, concept);

    private static Formula Pullback(Formula process) =>
        Apply(F.Id("pullbackConcept"), process);

    private static Formula Pushforward(Formula process, Formula concept) =>
        Call("pushforwardConcept", process, concept);

    private static Formula Pushforward(Formula process) =>
        Apply(F.Id("pushforwardConcept"), process);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula.BoundVariable[] ProcessContext(
        Formula source,
        Formula target,
        Formula process) =>
        [
            Bound("X", F.Id("Type")),
            Bound("Y", F.Id("Type")),
            Bound("p", Arrow(source, target)),
        ];

    private static Formula AdjunctionFormula()
    {
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula process = F.Id("p");
        Formula future = F.Id("D");
        Formula current = F.Id("C");
        Formula statement = new Formula.Logic(
            Refines(Pullback(process, future), current),
            FormulaLogicOperator.Iff,
            Refines(future, Pushforward(process, current)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                .. ProcessContext(source, target, process),
                Bound("D", Call("ReadoutConcept", target)),
                Bound("C", Call("ReadoutConcept", source)),
            ],
            statement));
    }

    private static Formula GaloisConnectionFormula()
    {
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula process = F.Id("p");
        Formula statement = Call(
            "GaloisConnection",
            Pullback(process),
            Pushforward(process));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. ProcessContext(source, target, process)],
            statement));
    }

    private static Formula PullbackMonotoneFormula() =>
        MonotoneFormula(Pullback);

    private static Formula PushforwardMonotoneFormula() =>
        MonotoneFormula(Pushforward);

    private static Formula MonotoneFormula(Func<Formula, Formula> construction)
    {
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula process = F.Id("p");

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. ProcessContext(source, target, process)],
            Call("Monotone", construction(process))));
    }

    private static Formula CounitFormula()
    {
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula process = F.Id("p");
        Formula current = F.Id("C");
        Formula statement = Refines(
            Pullback(process, Pushforward(process, current)),
            current);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                .. ProcessContext(source, target, process),
                Bound("C", Call("ReadoutConcept", source)),
            ],
            statement));
    }
}
