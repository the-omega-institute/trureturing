using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class DegeneracyGraphDeterminantMultiplicityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Algebra/DegeneracyGraphDeterminantMultiplicity";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/kempramgoolam2026degeneracy");
    private static DocumentBlock.Describe Declaration(int number, string name) =>
        Describe.Lean(DescribeId.Create($"declaration-{number:00}"), DeclarationHandle.Create($"{Module}.{name}"), H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("This declaration records the literal two-root tail truncation, its source-bounded positive thresholds, or the resulting degree and pruning equivalence. The witness is counted in the actual parent-dependent tree, not in a uniform grid."))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-root tail witnesses give the exact arbitrary-depth multiplicities in the determinant recurrence.",
        H("Degeneracy Graph Determinant: Multiplicity"),
        Blocks(
            Paragraph(Text("The multiplicity owner implements source equations (6.23)–(6.27) literally. StrictTailLevel, PairDescendantParent, and pairDescendantFiberMax retain actual descendant fibers; SourcePairTailWitness is the finite source witness whose cardinality becomes the exponent. Ambient witnesses and the restriction/lift/pruning equivalences establish the recurrence's multiplicity bijection without assuming a global coordinate grid.")),
            Declaration(1, "StrictTailLevel"), Declaration(2, "PairDescendantParent"), Declaration(3, "pairDescendantFiberCard"), Declaration(4, "pairDescendantFiberMax"), Declaration(5, "SourcePairTailVector"), Declaration(6, "sourcePairTailThreshold"), Declaration(7, "pairRootSurvivalSet"), Declaration(8, "SourcePairTailWitness"), Declaration(9, "AmbientPairTailWitness"), Declaration(10, "sourcePairTailExponents"), Declaration(11, "sourcePairTailWitnessEquivAmbient"), Declaration(12, "PairRetainingDegree"), Declaration(13, "ambientPairDegree"), Declaration(14, "restrictAmbientPairExponents"), Declaration(15, "restrictAmbientPairWitness"), Declaration(16, "liftAmbientPairWitness"), Declaration(17, "ambientPairDegreeFiberEquiv"), Declaration(18, "ambientPairTailPruningEquiv"), Declaration(19, "sourcePairTailPruningEquiv"))));
}
