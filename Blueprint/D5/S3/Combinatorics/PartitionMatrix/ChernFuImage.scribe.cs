using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PartitionMatrix;

internal sealed class ChernFuImageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.";
    private static readonly LibraryNoteRef CF = LibraryNoteRef.Create("D5/L/PermutationPatterns/chernfu2026signed");
    private static readonly LibraryNoteRef CDK = LibraryNoteRef.Create("D5/L/PermutationPatterns/claesson2011partition");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed Claesson-Dukes-Kubitzke image of improper partition matrices is characterized by the gaps in the whole alphabet of an inversion sequence.",
        H("Improper partition matrices and alphabet gaps"),
        Blocks(
            Node("native", "Native partition matrices", "NativePM",
                "For arbitrary natural numbers n and k, a native matrix is a k by k matrix of finite subsets of [n]. Each label belongs to exactly one cell, every row and column is nonempty, cells below the diagonal are empty, and smaller labels have weakly smaller column indices. Lean represents native label i by the element i - 1 of Fin n, and numbers rows and columns from zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(CF)),
            Node("coordinates", "Coordinates of every label", "Coordinates",
                "A coordinate representation consists of a row map and a column map from Fin n to Fin k. Both maps are onto, the row of each label is at most its column, and the column map is monotone. There is no restriction involving improperness or an inversion-sequence criterion.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(CF)),
            Node("equivalence", "Faithful set-entry correspondence", "nativeEquiv",
                "At each n and k, native matrices and coordinate representations correspond bijectively. A matrix gives each label its unique cell. Conversely, cell (r,c) is the fiber of the coordinate pair (r,c). Both composites are identities, so all native cells, dimensions, empty cells and label positions are preserved.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(CF)),
            Node("column", "The labels in a column", "column",
                "A column consists of the labels belonging to some cell in that column. Unique cell membership makes its cardinality equal to the sum of the cardinalities of its cells. Shifting between native labels and Fin n preserves cardinalities.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(CF)),
            Node("pi", "The fixed column-cardinality map", "fixedPi",
                "For each native label t, Pi(P) at t is the sum of the cardinalities of all columns strictly before row_P(t). The summands are column cardinalities. Row zero gives the empty sum. For an arbitrary native matrix, monotonicity makes the labels before a column an initial segment; thus this sum is the least native label of the column indexed by row_P(t), minus one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(CF)),
            Node("alphabet", "The entire alphabet", "alphabet",
                "For a function e on Fin n, A(e) is the set of all values e(t) for every t in Fin n. For a list of length n, this ranges over every list position, not a prefix.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(CDK)),
            Node("previous", "The previous occurring value", "previous",
                "For a natural number i, b_e(i) is the maximum of the set containing zero and all values in A(e) strictly less than i. Finset.sup includes zero even when there is no such occurring value. For an inversion sequence of positive length, zero occurs, and b_e(i) belongs to A(e) whenever i is positive.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(CF)),
            Node("phi", "The gap condition", "Phi",
                "For every native index i with 1 <= i < n, if i does not belong to the whole alphabet A(e) and i - b_e(i) is odd, then e_i = e_(i+1). In Lean i is j.val + 1, and the two entries are at Fin indices j and j.val + 1. When n = 1 there is no adjacent index, so the condition is vacuous.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(CF)),
            Node("least", "The least native label", "columnLeast",
                "The least label of a column is its least Fin n index plus one. Native nonempty-column validity makes the minimum defined. Proper parity is therefore measured against a native label, rather than against a list index.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(CF)),
            Node("improper", "Absence of proper ascents and descents", "Improper",
                "For every adjacent native pair i,i+1, neither strict row order in a common column may have i congruent modulo two to the least label of that column. The two row orders cover ascents and descents. Two labels in the same cell have equal rows and are neither an ascent nor a descent.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(CF)),
            Node("reconstruct", "The CDK reconstruction", "reconstruct",
                "Let A(e) = {y_1 < ... < y_k} and append y_(k+1) = n. Row r consists of labels t with e_t = y_r, and column c consists of labels y_c < t <= y_(c+1). Equivalently, the row of t is the rank of e_t, and its column is the rank of b_e(t). The inversion bounds alone ensure upper triangularity, nonempty rows and columns, unique membership and monotone column indices. The least label of column c is y_c + 1, so the fixed Pi sends this native matrix back to e. No gap-condition assumption is used to make the matrix valid.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(CDK)),
            Node("result", "The complete image characterization", "result",
                "In the formula, entries(e,n) denotes the function on Fin n sending t to e.getD t.val 0. For every natural n >= 1 and every list e of length n satisfying 0 <= e_i <= i - 1 at all native indices, e is the fixed Pi image of an improper native partition matrix, of some dimension k with no dimension restriction, if and only if Phi(e). In every native matrix, equal adjacent columns are equivalent to i not occurring in A(Pi(P)); the preceding value b_(Pi(P))(i) is the least label in that column minus one. The two row indices agree exactly when the corresponding Pi entries agree. Proper parity becomes oddness of i - b_(Pi(P))(i), so absence of both proper row orders gives precisely Phi. Conversely, the CDK reconstruction is a valid native matrix for every inversion sequence; Phi makes this matrix improper, and its fixed Pi image is e.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(CF),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("chern-fu-improper-partition-matrix-fixed-image"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("chernfu-image-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), declaration == "result"
                ? StatementSource.FromAuthor(ResultFormula())
                : StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), e = F.Id("e"), k = F.Id("k"), p = F.Id("P");
        Formula f = Call("entries", e, n);
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula hypothesis = Seq(D(1), Sp, Le, Sp, n, Sp, Land, Sp,
            Call("length", e), Sp, Eq, Sp, n, Sp, Land, Sp,
            Call("IsInversionSeq", e));
        Formula image = Seq(Exists, Sp, k, Sp, InMacro, Sp, naturals, Comma, Sp,
            Exists, Sp, p, Sp, InMacro, Sp, Call("NativePM", n, k), Comma, Sp,
            Call("Improper", p), Sp, Land, Sp, Call("fixedPi", p), Sp, Eq, Sp, f);
        return Disp(Seq(Forall, Sp, n, Sp, InMacro, Sp, naturals, Comma, Sp,
            Forall, Sp, e, Sp, InMacro, Sp, Call("List", naturals), Comma, Sp,
            Open, hypothesis, Close, Sp, Rightarrow, Sp, Open,
            Open, image, Close, Sp, Leftrightarrow, Sp, Call("Phi", f), Close));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Seq(Operatorname, Grp(F.Id(name)), Open,
            Seq(arguments.SelectMany((a, i) => i == 0
                ? new[] { a } : new[] { Comma, Sp, a }).ToArray()), Close);
}
