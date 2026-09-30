using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class BottomSiblingBlockResolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual reset prefixes satisfy the complete bottom-sibling identification criterion for globally attached successful words.",
        H("Actual Bottom Sibling Resolution"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-bottom-sibling-resolution"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/BottomSiblingBlockResolution.result"),
            H("Actual prefixes are identifiable exactly by bottom sibling coverage"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every H at least two, window limit t including zero, and "
                + "reachable actual modular next row (u,v), result inhabits all "
                + "seven clauses of BottomSiblingBlockCriterion.Target. Every residue "
                + "has an actual source at one shared past depth, and every actual "
                + "source number is positive. Equal original raw gcd futures are "
                + "precisely equal source residues; replacing gcd by H/gcd preserves "
                + "the full future equivalence, including failed End queries. For "
                + "any finite available family of successful literal words, a finite "
                + "adaptive protocol identifies the residue exactly when the "
                + "globally attached centers cover all but at most one leaf of "
                + "every prime-power bottom sibling block. The proof derives the "
                + "actual query equation, prime-depth factorization and CRT "
                + "injectivity, then uses the passive transcript bound and a fixed "
                + "finite scan. Bottom coverage for all bounded successful words "
                + "forces the Fibonacci cardinality bound, while the actual H=4 "
                + "family with centers {0,2} shows cardinality alone is insufficient. "
                + "Local prime-power centers are only projections of the same "
                + "available global words."))),
            DescribeRole.Theorem))));
}
