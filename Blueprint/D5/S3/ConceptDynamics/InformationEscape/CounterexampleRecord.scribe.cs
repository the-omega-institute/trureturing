using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class CounterexampleRecordDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite witness carrier refutes a universal claim through its predicate readout and a reverse bridge.",
        H("CounterexampleRecord"),
        Blocks(
            Node("witness-arena", "WitnessArena", "Witness arena",
                "The arena stores a finite carrier, the claim's quantifier domain, a predicate, "
                    + "an embedding, and a predicate decision at each embedded point. Its signature "
                    + "is a single Boolean CUT; its fixed law requires a false readout at some "
                    + "carrier point. The computed realization uses the stored decisions."),
            Node("strict-witness-arena", "StrictWitnessArena", "Infinite domain and embedded carrier",
                "The strengthened arena carries proofs that its domain is infinite and its embedding "
                    + "is injective, and coerces to the underlying witness arena."),
            Node("counterexample-realization", "counterexampleRealization", "Counterexample template",
                "The enrolled template accepts a Boolean check and exposes it unchanged as a CUT readout. "
                    + "The arena's computed realization is the required definitional tie for that check. "
                    + "The four-slot interpretation uses the quantifier domain as origin, the finite "
                    + "predicate check as handling, the negated claim as new information, and open "
                    + "as continuation. Full witness registration requires separate judge support."),
            Node("witness-primitive-realization", "WitnessPrimitiveRealization", "Reverse bridge",
                "A Prop-valued reverse bridge turns the law of the selected actual realization into "
                    + "the statement. Its theorem-unit conversion consumes a proof of that law, "
                    + "applies the backward bridge, and retains the actual realization's compiled bundle."),
            Node("witness-obligations", "WitnessArena", "Defining record obligations",
                "The law of the arena's computed realization refutes the universal predicate. "
                    + "Given the selected actual realization's law, variation pairs that same law "
                    + "with failure of the constant-true law, and sensitivity witnesses the CUT "
                    + "slot's effect. These generic obligations are Prop-valued definitions."))));

    private static DocumentBlock.Describe Node(
        string id, string declaration, string title, string text) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Definition);
}
