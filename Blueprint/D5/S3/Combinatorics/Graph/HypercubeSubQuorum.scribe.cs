using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class HypercubeSubQuorumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HypercubeSubQuorum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/sahbi2026subquorum");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every Boolean cube of dimension at least two, the largest number of colors in "
            + "a sub-quorum coloring is exactly one parity class, namely two to the power n-1.",
        H("Sahbi's hypercube sub-quorum conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sub-quorum-coloring"),
                DeclarationHandle.Create(Prefix + "IsSubQuorumColoring"),
                H("Source-faithful partial colorings"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A coloring consists of a finite colored support S in the Boolean cube and "
                        + "an onto map from S to the positive color type Fin k. At every colored "
                        + "vertex, the center together with its same-color colored neighbors is "
                        + "at least half of the center together with all colored neighbors. The "
                        + "center occurs once on each side, while uncolored neighbors do not enter "
                        + "either count. This is exactly Definition 2.2 of the source."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sub-quorum-attainable"),
                DeclarationHandle.Create(Prefix + "SubQuorumAttainable"),
                H("Attainable color counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A natural number k is attainable in dimension n when some finite support "
                        + "and onto admissible partial coloring use exactly k colors. Positivity "
                        + "is part of admissibility, rather than an external convention."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sub-quorum-chromatic-number"),
                DeclarationHandle.Create(Prefix + "subQuorumChromaticNumber"),
                H("The attained bounded maximum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The invariant is Nat.findGreatest over attainable k bounded by the number "
                        + "of cube vertices. Surjectivity bounds every attainable k by 2^n. A "
                        + "one-vertex, one-color support proves positive attainment in every "
                        + "dimension, so the default zero behavior of findGreatest on an empty "
                        + "predicate is never used; the selected maximum is itself attainable."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hypercube-sub-quorum-exact"),
                DeclarationHandle.Create(Prefix + "subQuorumChromaticNumber_hypercube"),
                H("The exact value in every dimension at least two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix an arbitrary admissible k-coloring. Split its colors into E, those "
                            + "with a colored internal edge, and N, those with none. Choose both "
                            + "ends of one edge for each color in E and one representative for "
                            + "each color in N. Distinct colors separate the choices, and the two "
                            + "ends of an edge differ, so the selected map is injective. If A is "
                            + "the set of all selected vertices and T the representatives of N, "
                            + "then |A|=|N|+2|E|, |T|=|N|, and |A|+|T|=2k.")),
                    Paragraph(Text(
                        "For t in T there is no same-color neighbor. The sub-quorum inequality "
                            + "therefore gives colored degree at most one, hence t has at most one "
                            + "neighbor in A. Conversely each a in A has at most n-1 neighbors in "
                            + "T. This follows from the preceding bound when a lies in T, using "
                            + "n>=2. When a is selected from an edged class, its selected partner "
                            + "is a cube neighbor outside T, while every cube vertex has degree n.")),
                    Paragraph(Text(
                        "The proof privately bridges the repository hypercube to Huang's symmetric "
                            + "signed adjacency operator from pinned Archive.Sensitivity. Its "
                            + "entries have absolute value one exactly on cube edges and its square "
                            + "is n times the identity. These matrix facts are Huang's Lemma 2.2, "
                            + "not a new result of this module. For a real vector supported on T, "
                            + "rowwise finite Cauchy-Schwarz and reverse summation give energy at "
                            + "most (n-1)||x||^2 on A. The full signed-cube identity gives total "
                            + "energy n||x||^2, leaving at least ||x||^2 on B, the complement of A.")),
                    Paragraph(Text(
                        "Thus restriction of the signed operator defines an injective linear map "
                            + "from real functions on T to real functions on B. Finite-dimensional "
                            + "rank comparison yields |T|<=|B|. Combining |A|+|B|=2^n with "
                            + "|A|+|T|=2k gives k<=2^(n-1). For the reverse inequality, the "
                            + "even-parity vertices form an edgeless support and receive distinct "
                            + "colors; this is onto and admissible and has 2^(n-1) colors. Since "
                            + "the bounded maximum is attained, the two inequalities give equality.")),
                    Paragraph(Text(
                        "Sahbi supplies Definition 2.2, the selection idea of Lemma 5.4, the cases "
                            + "through dimension six, and Conjecture 6.4. The repository-derived "
                            + "content is the restricted signed-matrix norm and dimension argument "
                            + "for arbitrary partial colorings. Prior-resolution searches are "
                            + "bounded and do not establish a worldwide novelty or priority claim."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sahbi-hypercube-subquorum"),
                    ResolutionKind.Proved))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/Hypercube"))
        ]));
}
