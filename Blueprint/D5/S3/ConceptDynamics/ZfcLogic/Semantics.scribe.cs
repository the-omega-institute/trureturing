using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ZfcLogic;

internal sealed class SemanticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/ZfcLogic/Semantics.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/foundation2026firstorder");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Licensed Foundation.Logic.Semantics source for the concrete first-order pair extension.",
        H("Semantics"),
        Blocks(
            Paragraph(Text("Source-command excerpt selected within Foundation.Logic.Semantics, lines 1-363, at Foundation revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. The optional Semantics.Top (Set M) instance command at upstream line 251 is omitted. All other selected mathematical commands and their proofs retain the upstream source.")),
            Paragraph(Text("The Lean file retains selected upstream commands and their compiler companions. "
                + "The immutable source map, modification notices, full Apache-2.0 license "
                + "and retirement condition are in Library/ConceptDynamics/foundation2026firstorder.md.")),
            Describe.Remark(
                DescribeId.Create("set-models-iff"),
                DeclarationHandle.Create(Prefix + "set_models_iff"),
                H("Satisfaction by a set of models"),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A set satisfies a formula exactly when each of its members satisfies that formula.")))),
            Describe.Remark(
                DescribeId.Create("set-meaningful-iff-nonempty"),
                DeclarationHandle.Create(Prefix + "set_meaningful_iff_nonempty"),
                H("Meaningful sets of models"),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Assuming every individual model is meaningful, a set of models is meaningful exactly when it is nonempty. The original proof uses set_models_iff to normalize satisfaction.")))),
            Describe.Remark(
                DescribeId.Create("meaningful-iff-satisfiable-set"),
                DeclarationHandle.Create(Prefix + "meaningful_iff_satisfiableSet"),
                H("Satisfiability and meaningful model classes"),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Under the same individual-model assumption, a theory is satisfiable exactly when its set of models is meaningful.")))),
            Paragraph(Text("This excerpt supplies semantic interfaces and proofs for downstream first-order developments. It does not represent the full upstream module or establish the complete CSA definition-elimination claim.")))));
}
