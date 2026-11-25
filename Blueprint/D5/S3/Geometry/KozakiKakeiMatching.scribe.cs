using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiMatchingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiMatching.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The even-frieze equation compares two literal determinant products on the full space of rectangular matrices.",
        H("Even frieze matrices and alternating matchings"),
        Blocks(
            Definition("K", "Coefficient field",
                "The coefficients are complex rational functions in one indeterminate."),
            Definition("Col", "Column labels",
                "The column set is Fin (2m), indexed from zero."),
            Definition("Chart", "Matrix carrier",
                "The carrier consists of every matrix with two rows and 2m columns over the given ring."),
            Definition("first", "First column",
                "The first column has index zero."),
            Definition("second", "Second column",
                "The second column has index one."),
            Definition("third", "Third column",
                "The third column has index two."),
            Definition("last", "Last column",
                "The last column has index 2m − 1."),
            Definition("oddVertex", "Odd matching endpoints",
                "At edge index e the ordered endpoints have indices 2e and 2e + 1."),
            Definition("evenVertex", "Even matching endpoints",
                "Edge zero is ordered from the first column to the last. At positive edge index e the ordered endpoints have indices 2e − 1 and 2e."),
            Definition("oddMatching", "Odd matching",
                "Every column occurs exactly once among the ordered odd edges."),
            Definition("evenMatching", "Even matching",
                "Every column occurs exactly once among the even edges, including the ordered closing edge."),
            Definition("minor", "Oriented minor",
                "The ordered minor is the upper entry of the first column times the lower entry of the second minus the lower entry of the first times the upper entry of the second."),
            Theorem("minor_swap", "Reversing an ordered minor",
                "Exchanging the two arguments of a minor multiplies it by minus one.",
                MinorSwap()),
            Definition("Admissible", "Admissible matrices",
                "Every ordered pair of distinct columns has a nonzero minor. This is the nonvanishing condition for all two-column minors."),
            Definition("reorder", "Column reordering",
                "The column at index i of the reordered matrix is the original column at index σ(i)."),
            Definition("oddProduct", "Odd determinant product",
                "In one-based notation the factors are D(1,2), D(3,4), through D(2m−1,2m)."),
            Definition("evenProduct", "Even determinant product",
                "In one-based notation the factors are D(2,3), D(4,5), through D(2m−2,2m−1), and D(1,2m)."),
            Definition("PreservesLevel", "Preservation on all admissible matrices",
                "A permutation preserves the level when equality of the two literal products implies equality after reordering for every admissible matrix over the complex rational function field."),
            Definition("Normalized", "Ordered normalization",
                "A matrix is admissible, its first three columns are (0,−1), (1,0), and (1,1), and every consecutive minor and the ordered closing minor D(1,2m) equals one."),
            Definition("MatEquivalent", "Matrix equivalence",
                "Two matrices are equivalent when one is obtained from the other by invertible left multiplication and an invertible diagonal matrix acting on the right."),
            Definition("Allowable", "Allowable permutations",
                "For every normalized input, reordering by the permutation has exactly one matrix-equivalent normalized representative."),
            Definition("Dihedral", "Dihedral permutations",
                "For some column a, the permutation sends every column i to a+i or sends every column i to a−i, with arithmetic modulo 2m."),
            Definition("affine", "Affine matrices",
                "The first row is all ones and the second row contains the given coordinates."),
            Theorem("minor_affine", "Affine minor",
                "The ordered minor at i and j is the coordinate at j minus the coordinate at i.",
                MinorAffine()),
            Definition("diff", "Polynomial difference",
                "The oriented linear factor is the variable at j minus the variable at i."),
            Definition("matchingPolynomial", "Oriented matching polynomial",
                "Multiply one oriented linear factor for each ordered pair of the matching."),
            Definition("F", "Signed level polynomial",
                "The even matching polynomial minus the odd matching polynomial is the affine form of the level equation."),
            Theorem("eval_matchingPolynomial", "Evaluation of a matching product",
                "Evaluating the matching polynomial multiplies the oriented coordinate differences.",
                EvalMatchingPolynomial()),
            Theorem("eval_F", "The affine level equation",
                "The polynomial evaluates to the even determinant product minus the odd product of the affine matrix.",
                EvalF()),
            Theorem("affine_constants_admissible", "Admissible constant matrices",
                "Injective complex coordinates give a matrix whose minors stay nonzero under the inclusion into rational functions.",
                AffineConstantsAdmissible()),
            Theorem("constant_matrix_implication", "Transfer to the affine locus",
                "A permutation preserving the matrix level sends each zero of the signed polynomial with injective complex coordinates to another zero. The constant inclusion carries the two products separately and is injective.",
                ConstantMatrixImplication()))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose, Formula statement) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Theorem);

    private static Formula MinorSwap() => Seq(
        Forall, Sp, F.Id("R"), Sp, Colon, Sp, Word("Type"), Comma, Sp, OpenBracket, Word("CommRing"), Open,
        F.Id("R"), Close, CloseBracket, Comma, Sp, Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("Z"), Sp, Colon, Sp, Word("Chart"), Open, F.Id("R"),
        Comma, F.Id("m"), Close, Comma, Sp, F.Id("i"), Comma, F.Id("j"), Sp, Colon, Sp, Word("Col"), Open,
        F.Id("m"), Close, Comma, Sp, Word("minor"), Open, F.Id("Z"), Comma, F.Id("i"), Comma, F.Id("j"), Close,
        Sp, Eq, Sp, Minus, Word("minor"), Open, F.Id("Z"), Comma, F.Id("j"), Comma, F.Id("i"), Close);

    private static Formula MinorAffine() => Seq(
        Forall, Sp, F.Id("R"), Sp, Colon, Sp, Word("Type"), Comma, Sp, OpenBracket, Word("CommRing"), Open,
        F.Id("R"), Close, CloseBracket, Comma, Sp, Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("t"), Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close,
        Sp, To, Sp, F.Id("R"), Comma, Sp, F.Id("i"), Comma, F.Id("j"), Sp, Colon, Sp, Word("Col"), Open,
        F.Id("m"), Close, Comma, Sp, Word("minor"), Open, Word("affine"), Open, F.Id("t"), Close, Comma,
        F.Id("i"), Comma, F.Id("j"), Close, Sp, Eq, Sp, F.Id("t"), Open, F.Id("j"), Close, Sp, Minus, Sp,
        F.Id("t"), Open, F.Id("i"), Close);

    private static Formula EvalMatchingPolynomial() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("M"),
        Sp, Colon, Sp, Word("Matching"), Open, F.Id("m"), Close, Comma, Sp, F.Id("t"), Sp, Colon, Sp,
        Word("Col"), Open, F.Id("m"), Close, Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))), Comma, Sp, Word("eval"),
        Open, F.Id("t"), Comma, Word("matchingPolynomial"), Open, F.Id("M"), Close, Close, Sp, Eq, Sp, Prod,
        Underscore, Grp(F.Id("e"), InMacro, Word("Fin"), Open, F.Id("m"), Close), Sp, Open, F.Id("t"), Open,
        F.Id("M"), Open, F.Id("e"), Comma, Word("true"), Close, Close, Sp, Minus, Sp, F.Id("t"), Open,
        F.Id("M"), Open, F.Id("e"), Comma, Word("false"), Close, Close, Close);

    private static Formula EvalF() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("t"),
        Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))), Comma, Sp,
        Word("eval"), Open, F.Id("t"), Comma, F.Id("F"), Open, F.Id("m"), Close, Close, Sp, Eq, Sp,
        Word("evenProduct"), Open, Word("affine"), Open, F.Id("t"), Close, Close, Sp, Minus, Sp,
        Word("oddProduct"), Open, Word("affine"), Open, F.Id("t"), Close, Close);

    private static Formula AffineConstantsAdmissible() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("t"),
        Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))), Comma, Sp,
        Word("Injective"), Open, F.Id("t"), Close, Sp, Implies, Sp, Word("Admissible"), Open, Word("affine"),
        Open, Word("RatFuncC"), Sp, Circ, Sp, F.Id("t"), Close, Close);

    private static Formula ConstantMatrixImplication() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("s"),
        Sp, Colon, Sp, Word("Perm"), Open, Word("Col"), Open, F.Id("m"), Close, Close, Comma, Sp, F.Id("t"),
        Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))), Comma, Sp,
        Word("PreservesLevel"), Open, F.Id("s"), Close, Sp, Implies, Sp, Word("Injective"), Open, F.Id("t"),
        Close, Sp, Implies, Sp, Word("eval"), Open, F.Id("t"), Comma, F.Id("F"), Open, F.Id("m"), Close, Close,
        Sp, Eq, Sp, D(0), Sp, Implies, Sp, Word("eval"), Open, F.Id("t"), Comma, Word("rename"), Open,
        F.Id("s"), Comma, F.Id("F"), Open, F.Id("m"), Close, Close, Close, Sp, Eq, Sp, D(0));

    private static Formula Word(string value) => Seq(Operatorname, Grp(F.Id(value)));

    private static string NodeId(string name) =>
        "frieze-matching-" + name.ToLowerInvariant().Replace('_', '-');
}
