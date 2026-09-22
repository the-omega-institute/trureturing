using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentBoundary;

internal sealed class BoundedRunSpaceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Run restrictions, finite words, and coherent prefixes share one Boolean coordinate alphabet.",
        H("Bounded Runs and Coherent Prefixes"),
        Blocks(
            Definition("bounded", "Infinite run restriction",
                "A stream is a function from the natural numbers to Bool. For every starting "
                + "coordinate j, bounded(read,k) requires an index i less than k whose observed "
                + "bit read(x(j+i)) is false. The identity readout forbids k consecutive true bits."),
            Definition("language", "Finite run language",
                "A word of length n is a function from Fin n to Bool. The same run condition "
                + "is checked precisely at starts j with j+k at most n. Length zero has the "
                + "unique empty word. Truncation restricts coordinates; zeroExtend appends false bits."),
            Definition("union", "Union over run bounds",
                "The union ranges over every natural k at least two. A member has one bound "
                + "that controls all starting coordinates, rather than a bound chosen separately "
                + "at each finite length."),
            Definition("Threads", "Coherent prefixes",
                "A thread contains one word of every natural length, including zero. Restricting "
                + "the word at length n+1 to length n gives the preceding word. prefixes sends "
                + "a stream to its prefixes; threadStream reads coordinate j at length j+1."),
            Definition("comparison", "Comparison of the two limits",
                "fixedLimit requires every word in a thread to satisfy one fixed run bound. "
                + "unionLimits takes their ordinary union over bounds at least two. limitUnions "
                + "allows a separate bound at each length. comparison retains exactly the same "
                + "thread and only changes its membership proof."),
            Definition("fairMeasure", "Fair independent product law",
                "The measure is productLaw at success probability one half, on the ambient "
                + "Boolean stream space with its product topology and Borel sigma algebra. "
                + "It is the independent product of equal point masses at true and false."),
            Definition("aligned", "Aligned block event",
                "The event checks m disjoint blocks of length k, at starts r*k for r in Fin m. "
                + "Each checked block contains a false observed bit. Sliding windows that cross "
                + "block boundaries impose additional conditions in bounded(read,k)."),
            Definition("Boundary", "Complete union boundary",
                "Boundary collects strict inclusion, closedness, exact prefix images, finite "
                + "language and truncation compatibility, density, properness, Borel measurability, "
                + "the null measure and full-measure closure, the continuous coherent-prefix "
                + "identification, the non-surjective comparison, both quantifier orders, "
                + "and the exact aligned-block probability."))));

    private static DocumentBlock.Describe Definition(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("bounded-run-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
