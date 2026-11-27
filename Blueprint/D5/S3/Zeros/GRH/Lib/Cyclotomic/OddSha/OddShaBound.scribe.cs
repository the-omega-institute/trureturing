using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cyclotomic.OddSha;

internal sealed class OddShaBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd Sha Bound", H("Odd Sha Bound"),
        Blocks(
            Paragraph(Text("Ray class group generators detect cocycles unramified off l; crude count by Minkowski. One non-zero integer, at most an explicit quantity times the class number, bounds lengths of odd Tate-twisted Sha groups at all primes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cyclotomic/OddSha/OddShaBound.exists_length_shaOdd_le"),
                H("exists_length_shaOdd_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a CM field E in ℚ(ζ_N), some integer 1 ≤ X ≤ 2^{4(N+t+3)^27}·h_E, h_E the class number, has length of shaOdd in O/lⁿ(−e) at most v(X), for all primes l, 0 ≤ e < t, n, and characteristic zero discrete valuation rings (O, v) over ℤ_l with all O/l^m finite, containing a primitive root of unity of order the exponent of (ℤ/N)^×.")))))));
}
