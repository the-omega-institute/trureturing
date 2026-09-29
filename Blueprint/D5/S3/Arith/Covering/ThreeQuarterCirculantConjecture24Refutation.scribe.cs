using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class ThreeQuarterCirculantConjecture24RefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/dalfofiolreyes2026threequarters");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjecture 2.4's literal positive-integer quantifier conflicts with its "
            + "degree-two graph convention at k equal to one.",
        H("The Boundary of Conjecture 2.4"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-quarter-conjecture-24-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The literal source claim"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every k at least one, the proposed order, two lattice columns, "
                    + "full radius-k coverage, exact-radius witness, and two-element outgoing "
                    + "neighbor set all hold simultaneously. The final clause is the source's "
                    + "degree-two digraph requirement with arcs treated as a set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-quarter-conjecture-24-boundary-facts"),
                DeclarationHandle.Create(Prefix + "boundary_facts"),
                H("The one-neighbor boundary retains its sector and lattice properties"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At k=1 the order is three, both steps are residue one, and each "
                    + "vertex has one distinct outgoing neighbor. Radius-one sector "
                    + "coverage, the exact-radius witness, and the lattice kernel "
                    + "identity still hold."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-quarter-conjecture-24-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The degree-two assertion fails at k equal to one"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At k=1 the order is three and both proposed steps are residue one. "
                    + "Every vertex therefore has one distinct outgoing neighbor. This "
                    + "refutes the literal degree-two graph assertion; it does not refute "
                    + "the sector-distance or lattice clauses, which hold at k=1."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dalfo-fiol-reyes-three-quarter-conjecture-24"),
                    ResolutionKind.Refuted)))));
}
