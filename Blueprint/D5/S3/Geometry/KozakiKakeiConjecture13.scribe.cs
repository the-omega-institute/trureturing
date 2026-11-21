using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiConjecture13Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiConjecture13.";
    private static readonly LibraryNoteRef Primary = LibraryNoteRef.Create("D5/L/FiniteGeometry/kozakikakei2026coxeterfriezes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The allowable reorderings of the double-normalized even frieze matrices are exactly the rotations and reflections throughout the stated size range.",
        H("Kozaki–Kakei Conjecture 13"),
        Blocks(
            Theorem("allowable_iff_preservesLevel", "The normalized action and the full level locus",
                "Every admissible matrix on the level has a unique ordered representative. Reordering transports matrix equivalence, so existence and uniqueness after reordering each normalized input is equivalent to preserving the written equality on all admissible inputs."),
            Claim("conjecture_13", "Exact classification of allowable permutations",
                "Kozaki and Kakei, arXiv:2611.25785v1, section 3, printed page 9, Conjecture 13, identify the subgroup of the symmetric group whose reorderings admit the source normalization on every normalized input. Use columns zero through 2m−1 over the complex rational function field. A reordering uses the original column at σ(i) in position i. The normal form has first three columns (0,−1), (1,0), (1,1), all distinct-column minors nonzero, and every consecutive minor and D(1,2m) equal to one in one-based notation. The representative is unique under invertible left multiplication and invertible diagonal column rescaling. Dihedral permutations preserve the level by matching transport. In the reverse direction the constant-matrix bridge yields a scalar symmetry, and the signed four-column evaluation or the large-size support count recovers the cycle."))));

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(ClaimFormula())), AssessedProvenance.FromRepo(Primary),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula ClaimFormula()
    {
        var m = F.Id("m");
        var s = F.Id("s");
        var columns = Call("Fin", Seq(D(2), Sp, m));
        var classification = new Formula.Logic(Call("Allowable", m, s),
            FormulaLogicOperator.Iff, Call("Dihedral", s));
        var restrictions = new Formula.Logic(
            new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, m),
            FormulaLogicOperator.And, NotEqual(m, D(3)));
        return All("m", Seq(Mathbb, Grp(F.Id("N"))),
            new Formula.Logic(restrictions, FormulaLogicOperator.Implies,
                All("s", Call("Perm", columns), classification)));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static string NodeId(string name) =>
        "frieze-conjecture13-" + name.ToLowerInvariant().Replace('_', '-');
}
