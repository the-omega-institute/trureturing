using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class ObserverCrossedProductEntropyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.";
    private static readonly LibraryNoteRef Observer =
        LibraryNoteRef.Create("D5/L/HilbertOperators/chandrasekaran2023desitter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive observer clock gives a normalized faithful trace and a unique entropy-maximizing density in the finite Gibbs model.",
        H("Trace entropy for a finite Gibbs system and an observer clock"),
        Blocks(
            Entry("clock-cutoff", "dressed_clock_cutoff", "The positive-clock projection in total energy",
                "Shifting the ith clock coordinate by its matter energy turns the total energy into the common coordinate y. "
                + "The positive-clock projection becomes diagonal and keeps precisely the entries with Eᵢ ≤ y."),
            Entry("core-weight-semifinite", "coreWeight_semifinite", "Semifinite trace weight",
                "Cut a bounded positive field to total energies y ≥ −k. Each cut has finite weight, "
                + "since the exponential is integrable on that half-line. The supremum of the cut weights is the weight of the field."),
            Entry("trace-normalization", "observer_trace_one", "Normalization of the corner trace",
                "The exponential weight is β exp(−βy)/Z, with β > 0 and Z the Gibbs partition function. "
                + "For the ith diagonal entry, change variables to x = y − Eᵢ. Its contribution is the Gibbs probability of i."),
            Entry("trace-faithfulness", "observer_trace_faithful", "Faithfulness of the trace",
                "A positive integrable field with zero trace has vanishing ordinary matrix trace almost everywhere, "
                + "since the exponential weight is strictly positive. A positive semidefinite matrix with zero trace vanishes."),
            Entry("trace-cyclicity", "observer_trace_mul_comm", "Cyclicity in the total-energy fibers",
                "Ordinary matrix trace is cyclic in each fiber. Its scalar-weighted integrals therefore agree on the two products."),
            Entry("gibbs-clock-moments", "gibbs_clock_moments", "Gibbs and exponential clock moments",
                "The trace of a compressed matter observable times a physical clock function is the Gibbs expectation "
                + "of the matter observable times the expectation of the clock function under β exp(−βx) on x > 0."),
            Entry("entropy-maximizer", "trace_entropy_eq_zero_iff", "Unique entropy maximizer",
                "The scalar gap r log r − r + 1 is nonnegative for r ≥ 0 and vanishes exactly at r = 1. "
                + "Functional calculus and faithfulness make the extended trace entropy vanish precisely at the compressed unit."),
            Entry("generalized-entropy", "observer_generalized_entropy", "The physical-clock entropy identity",
                "For a classical clock density p and a matter density σ in the Gibbs centralizer, "
                + "the entropy is the differential entropy of p minus the p-weighted observer energy βx and matter "
                + "relative entropy to the Gibbs state, plus log β. The finite identity assumes integrable p log p and xp. The constant comes from the normalization of the exponential clock density."),
            Entry("coherence-defect", "observer_entropy_coherence_defect", "Entropy gained by restriction to the energy blocks",
                "Pinching deletes matrix entries between distinct Gibbs energies and preserves the diagonal energy blocks. "
                + "The gain is the p-weighted relative entropy from the unpinched state to its pinching. "
                + "For integrable p log p and xp, the defect vanishes exactly when the state belongs to the centralizer almost everywhere for the clock law."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Observer),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
