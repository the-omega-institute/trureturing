using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class RefutationEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-way refutation encodings isolate the model-to-SAT implication sufficient for sound UNSAT lower bounds, while exact encodings additionally decode satisfying assignments.",
        H("Refutation and Exact Encodings"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("one-way-refutation-excludes-models"),
                DeclarationHandle.Create(
                    "D5/S0/Certificates/RefutationEncoding.RefutationEncoding.false_of_refutation"),
                H("A checked refutation of a one-way encoding excludes the problem"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every mathematical model supplies a satisfying valuation. A kernel-checked LRAT contradiction therefore rules out the mathematical model predicate even when the formula contains additional spurious satisfying assignments."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-encoding-satisfiability-characterization"),
                DeclarationHandle.Create(
                    "D5/S0/Certificates/RefutationEncoding.ExactEncoding.satisfiable_iff"),
                H("Exact encodings characterize satisfiability"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An exact encoding extends the one-way interface with a satisfying-assignment-to-model theorem, recovering a full equivalence between the mathematical problem and propositional satisfiability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stable-right-refutation-excludes-identification"),
                DeclarationHandle.Create(
                    "D5/S0/Certificates/RefutationEncoding.no_identification_of_stable_right_coloring_refutation"),
                H("A stable-right-coloring refutation excludes exact DFA identifications"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The formula need only contain every stable right coloring. Exact identifications enter that relaxation through the frozen automata theorem, so a checked contradiction excludes all exact finite identifications on the selected color carrier."))),
                DescribeRole.Theorem)),
        []));
}
