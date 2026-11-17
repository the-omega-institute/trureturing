using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class CorrelationMinorNormDesignObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No paired coherent pure designs above dimension four", H("No paired coherent pure designs above dimension four"), Blocks(
            Describe.Lean(DescribeId.Create("pure-design"), DeclarationHandle.Create("D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.PureDesign"),
                H("The precise conditional construction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/peledteenicarmicohen2021minor")),
                Blocks(Paragraph(Text("A nonempty family consists of actual complex rank-one density projectors, is coherent with sum (v/n)I, and has a common real distinct-pair trace overlap. Design existence is an input to the original conditional constructions, not a theorem for all dimensions or cardinalities."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qubit-design-cardinality"), DeclarationHandle.Create("D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.qubit_design_cardinality"),
                H("A global qubit cardinality bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/peledteenicarmicohen2021minor")),
                Blocks(Paragraph(Text("Every such actual qubit design has 2≤v≤4. Coherence excludes a common overlap of one. Taking traces of a vanishing linear combination, then pairing it with each projector, proves complex linear independence. The full complex qubit matrix space has dimension four. The one-member case contradicts coherence and idempotence. The received written derivation also gives the overlap (v-2)/(2(v-1)) and the positive-definite Gram form (1-mu)I+mu*11 transpose; the formal proof uses the equivalent direct linear-independence argument. No finite cardinality search is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("design-dimension-le-cardinality"), DeclarationHandle.Create("D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.design_dimension_le_cardinality"),
                H("Coherence needs enough pure projectors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/peledteenicarmicohen2021minor")),
                Blocks(Paragraph(Text("In every positive local dimension n, a coherent pure design has n≤v. The proof pairs the coherent sum with any projector, retains its unit self-pairing, and uses positivity of every other actual PSD trace pairing."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("no-coherent-pair"), DeclarationHandle.Create("D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.no_coherent_pair"),
                H("The exact coherent-pair obstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/peledteenicarmicohen2021minor")),
                Blocks(Paragraph(Text("For every integer D≥5 there is no common-size nonempty pair of the specified regular coherent degree-one pure designs in dimensions 2 and D. The preceding global bounds give D≤v≤4. This excludes precisely that paired construction; it does not refute arbitrary designs or every interpretation of Peled et al.’s broad general-p design characterization. Attainment of the unrestricted fourth-order maximum is proved separately by CorrelationMinorNormQubitBound.coherent_pair_obstruction_with_attainment using the actual zero-noise tetrahedral state for every D>=5. No design-existence premise supplies that attainment. Source: the CC BY 4.0 return note by Haobo Ma (Chrono AI, Singapore) and Wenlin Zhang (NUS and Chrono AI, Singapore). No novelty, consent, publication or submission claim."))), DescribeRole.Theorem))));
}
