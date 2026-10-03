using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.CayleyGrowth;

internal sealed class CayleyPyConjectureOneRefutationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Chervov2025 =
        LibraryNoteRef.Create("D5/L/CayleyGrowth/chervov2025cayleypy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A polynomial-size generator family with non-quasipolynomial Cayley diameter.",
        H("CayleyPy Conjecture One Refutation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cayleypyconjectureonerefutation-triple-products"),
                DeclarationHandle.Create(
                    "D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation."
                    + "tripleTranspositionProducts"),
                H("Products of at most three transpositions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The set contains exactly the products of lists of at most three swaps "
                    + "of Fin n, including the empty product."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayleypyconjectureonerefutation-triple-upper"),
                DeclarationHandle.Create(
                    "D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation."
                    + "tripleTranspositionProducts_diameter_upper"),
                H("Triple-product diameter upper bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every permutation of Fin n is factored into at most n transpositions. "
                    + "Grouping factors in blocks of at most three gives a Cayley diameter "
                    + "at most (n + 2) / 3 with integer division."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayleypyconjectureonerefutation-slope-gap"),
                DeclarationHandle.Create(
                    "D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation."
                    + "not_eventuallyQuasipolynomial_of_square_diameter_gap"),
                H("Separated square and nonsquare slopes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In one residue class, large squares and nearby nonsquares force a proposed "
                    + "constituent polynomial onto opposite sides of the line 5n/12. A polynomial "
                    + "has a fixed eventual sign relative to that line."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayleypyconjectureonerefutation-generators"),
                DeclarationHandle.Create(
                    "D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation."
                    + "conjectureOneGenerators"),
                H("Square-dependent generator family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At square sizes the generators are products of at most three "
                    + "transpositions; at other sizes they are all transpositions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayleypyconjectureonerefutation-diameter"),
                DeclarationHandle.Create(
                    "D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation."
                    + "conjectureOneDiameter"),
                H("Square-dependent Cayley diameter"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The rational-valued function is the diameter of the undirected "
                    + "multiplicative Cayley graph of the square-dependent generators."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayleypyconjectureonerefutation-conjecture-one"),
                DeclarationHandle.Create(
                    "D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.cayleyPy_conjecture1_refuted"),
                H("Refutation of CayleyPy Growth Conjecture 1"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Chervov2025),
                Blocks(Paragraph(Text(
                    "At square sizes use products of at most three transpositions; otherwise use "
                    + "all transpositions. Both generator sets have polynomial-size explicit "
                    + "enumerations. The full-support rotation gives the nonsquare lower bound, "
                    + "and the triple-product bound gives the square upper bound. The output-time "
                    + "estimate is discharged outside Lean."))),
                DescribeRole.Theorem))));
}
