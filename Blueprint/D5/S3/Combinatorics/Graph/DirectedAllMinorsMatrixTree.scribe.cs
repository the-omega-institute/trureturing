using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DirectedAllMinorsMatrixTreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed directed spanning forests compute every ascending complementary minor over an arbitrary commutative ring.",
        H("Directed all-minors matrix-tree identity"),
        Blocks(Describe.Lean(
            DescribeId.Create("directed-all-minors-matrix-tree"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/DirectedAllMinorsMatrixTree.directed_all_minors_matrix_tree"),
            H("The complete signed complementary-minor identity"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Combinatorics/zernik2013allminors")),
            Blocks(
                Paragraph(Text(
                    "For every commutative ring R, every finite size n, every column-sum-zero matrix M, "
                    + "and equal-cardinality root sets U and W with k at least one, delete rows W and "
                    + "columns U in inherited ascending order. The determinant is the sum over literal "
                    + "directed spanning forests without loops, with every component acyclic and containing exactly one "
                    + "U root and one W mark. Every arrow points away from its U root and has weight Mij.")),
                Paragraph(Text(
                    "The Lean declaration is authoritative. The statement projector has no fixture entry "
                    + "for this declaration; this narrative specifies its conventions and scope without "
                    + "providing a second formal statement.")),
                Paragraph(Text(
                    "The theorem constructs a permutation of Fin k by locating each ascending U root's "
                    + "unique W mark in the same actual component. Its sign is multiplied by (-1) raised "
                    + "to n + k + the sums of the zero-based U and W labels. The summand uses the product "
                    + "of Mij over the actual directed edge set; the carrier has no determinant condition.")),
                Paragraph(Text(
                    "The integer coefficient proof rules out cyclic and antiparallel parent choices "
                    + "by path-telescoping column dependence. Tree edge counts establish root uniqueness; "
                    + "missing marks give an integer component-indicator row dependence. Actual rooted "
                    + "paths establish orientation, preserve all edges in the reindexing, and move the "
                    + "root columns. Native block-triangular determinants and antisymmetric finite-order "
                    + "products compute the exact nonprincipal shuffle and matching sign.")),
                Paragraph(Text(
                    "Only the fixed integer incidence coefficients are cast into R. No field, domain, "
                    + "nontriviality, positivity, connected-support, weight-nonvanishing, or bounded-size "
                    + "assumption is imposed. This includes Int, every positive characteristic, the zero "
                    + "ring, overlapping roots, nonprincipal minors, and k = n with the empty forest and "
                    + "empty determinant. The reference's real derivative proof is not used for transfer.")),
                Paragraph(Text(
                    "This unbounded structural theorem is not a bounded enumeration, checker, numeric "
                    + "reduction, or certified finite instance. Computational-content kind is none; "
                    + "computational utility fields are not applicable. The indispensable new Lean "
                    + "inference is the actual signed parent-choice/forest correspondence, not a wrapper "
                    + "around supplied determinant expansion or incidence total unimodularity."))),
            DescribeRole.Theorem)),
        []));
}
