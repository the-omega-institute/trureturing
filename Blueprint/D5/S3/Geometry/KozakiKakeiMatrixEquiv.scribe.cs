using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiMatrixEquivDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiMatrixEquiv.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Row operations and column scalings multiply both determinant products by the same nonzero factor.",
        H("Invertible matrix operations and the level equation"),
        Blocks(
            Definition("Square", "Row operations",
                "The square matrix type has two rows and two columns over the rational function field."),
            Definition("scaled", "Left and right multiplication",
                "Apply the square matrix on the left and the diagonal of the column factors on the right."),
            Theorem("scaled_apply", "Entries after scaling",
                "Take the two-term row combination and multiply by the column factor.",
                ScaledApply()),
            Theorem("minor_scaled", "Determinant transformation",
                "Each minor acquires the determinant of the left matrix and the two column factors.",
                MinorScaled()),
            Theorem("scaled_admissible", "Admissibility after invertible scaling",
                "All the factors in the scaled minor remain nonzero.",
                ScaledAdmissible()),
            Theorem("unit_det_ne_zero", "Invertible matrices have nonzero determinant",
                "An invertible square matrix has unit determinant in the coefficient field.",
                UnitDetNeZero()),
            Theorem("level_scaled_iff", "Invariance of the written level",
                "Each matching uses every column once. Both products acquire the determinant to the m-th power times the product of all column factors, which can be canceled.",
                LevelScaledIff()),
            Theorem("scaled_comp", "Composition of row and column operations",
                "Left factors multiply in application order and right scalars multiply pointwise.",
                ScaledComp()),
            Theorem("matEquivalent_symm", "Symmetry of matrix equivalence",
                "Invert the left matrix and each column factor.",
                MatEquivalentSymm()),
            Theorem("matEquivalent_trans", "Transitivity of matrix equivalence",
                "Compose the left operations and multiply the diagonal factors pointwise.",
                MatEquivalentTrans()),
            Theorem("reorder_equiv", "Transport of matrix equivalence",
                "The same left matrix and the correspondingly permuted diagonal factors implement equivalence after column reordering.",
                ReorderEquiv()),
            Theorem("reorder_admissible", "Transport of admissibility",
                "A permutation takes distinct columns to distinct columns.",
                ReorderAdmissible()),
            Theorem("level_equiv", "Level invariance under matrix equivalence",
                "The unit witnesses make the common factor nonzero, so matrix-equivalent inputs satisfy the same level equation.",
                LevelEquiv()))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose, Formula statement) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Theorem);

    private static Formula ScaledApply() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("L"),
        Sp, Colon, Sp, Word("Square"), Comma, Sp, F.Id("d"), Sp, Colon, Sp, Word("Col"), Open, F.Id("m"),
        Close, Sp, To, Sp, F.Id("K"), Comma, Sp, F.Id("Z"), Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"),
        Comma, F.Id("m"), Close, Comma, Sp, F.Id("a"), Sp, Colon, Sp, Word("Fin"), Open, D(2), Close, Comma,
        Sp, F.Id("i"), Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Comma, Sp, Word("scaled"), Open,
        F.Id("L"), Comma, F.Id("d"), Comma, F.Id("Z"), Close, Open, F.Id("a"), Comma, F.Id("i"), Close, Sp, Eq,
        Sp, Open, F.Id("L"), Open, F.Id("a"), Comma, D(0), Close, Sp, Cdot, Sp, F.Id("Z"), Open, D(0), Comma,
        F.Id("i"), Close, Sp, Plus, Sp, F.Id("L"), Open, F.Id("a"), Comma, D(1), Close, Sp, Cdot, Sp,
        F.Id("Z"), Open, D(1), Comma, F.Id("i"), Close, Close, Sp, Cdot, Sp, F.Id("d"), Open, F.Id("i"), Close);

    private static Formula MinorScaled() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("L"),
        Sp, Colon, Sp, Word("Square"), Comma, Sp, F.Id("d"), Sp, Colon, Sp, Word("Col"), Open, F.Id("m"),
        Close, Sp, To, Sp, F.Id("K"), Comma, Sp, F.Id("Z"), Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"),
        Comma, F.Id("m"), Close, Comma, Sp, F.Id("i"), Comma, F.Id("j"), Sp, Colon, Sp, Word("Col"), Open,
        F.Id("m"), Close, Comma, Sp, Word("minor"), Open, Word("scaled"), Open, F.Id("L"), Comma, F.Id("d"),
        Comma, F.Id("Z"), Close, Comma, F.Id("i"), Comma, F.Id("j"), Close, Sp, Eq, Sp, Word("det"), Open,
        F.Id("L"), Close, Sp, Cdot, Sp, F.Id("d"), Open, F.Id("i"), Close, Sp, Cdot, Sp, F.Id("d"), Open,
        F.Id("j"), Close, Sp, Cdot, Sp, Word("minor"), Open, F.Id("Z"), Comma, F.Id("i"), Comma, F.Id("j"),
        Close);

    private static Formula ScaledAdmissible() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("L"),
        Sp, Colon, Sp, Word("Square"), Comma, Sp, F.Id("d"), Sp, Colon, Sp, Word("Col"), Open, F.Id("m"),
        Close, Sp, To, Sp, F.Id("K"), Comma, Sp, F.Id("Z"), Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"),
        Comma, F.Id("m"), Close, Comma, Sp, Word("det"), Open, F.Id("L"), Close, Sp, Neq, Sp, D(0), Sp,
        Implies, Sp, Open, Forall, Sp, F.Id("i"), Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Comma,
        Sp, F.Id("d"), Open, F.Id("i"), Close, Sp, Neq, Sp, D(0), Close, Sp, Implies, Sp, Word("Admissible"),
        Open, F.Id("Z"), Close, Sp, Implies, Sp, Word("Admissible"), Open, Word("scaled"), Open, F.Id("L"),
        Comma, F.Id("d"), Comma, F.Id("Z"), Close, Close);

    private static Formula UnitDetNeZero() => Seq(
        Forall, Sp, F.Id("L"), Sp, Colon, Sp, Word("Units"), Open, Word("Square"), Close, Comma, Sp,
        Word("det"), Open, F.Id("L"), Close, Sp, Neq, Sp, D(0));

    private static Formula LevelScaledIff() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("L"),
        Sp, Colon, Sp, Word("Square"), Comma, Sp, F.Id("d"), Sp, Colon, Sp, Word("Col"), Open, F.Id("m"),
        Close, Sp, To, Sp, F.Id("K"), Comma, Sp, F.Id("Z"), Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"),
        Comma, F.Id("m"), Close, Comma, Sp, Word("det"), Open, F.Id("L"), Close, Sp, Neq, Sp, D(0), Sp,
        Implies, Sp, Open, Forall, Sp, F.Id("i"), Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Comma,
        Sp, F.Id("d"), Open, F.Id("i"), Close, Sp, Neq, Sp, D(0), Close, Sp, Implies, Sp, Open,
        Word("evenProduct"), Open, Word("scaled"), Open, F.Id("L"), Comma, F.Id("d"), Comma, F.Id("Z"), Close,
        Close, Sp, Eq, Sp, Word("oddProduct"), Open, Word("scaled"), Open, F.Id("L"), Comma, F.Id("d"), Comma,
        F.Id("Z"), Close, Close, Sp, Iff, Sp, Word("evenProduct"), Open, F.Id("Z"), Close, Sp, Eq, Sp,
        Word("oddProduct"), Open, F.Id("Z"), Close, Close);

    private static Formula ScaledComp() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("L"),
        Comma, F.Id("M"), Sp, Colon, Sp, Word("Square"), Comma, Sp, F.Id("d"), Comma, F.Id("e"), Sp, Colon, Sp,
        Word("Col"), Open, F.Id("m"), Close, Sp, To, Sp, F.Id("K"), Comma, Sp, F.Id("Z"), Sp, Colon, Sp,
        Word("Chart"), Open, F.Id("K"), Comma, F.Id("m"), Close, Comma, Sp, Word("scaled"), Open, F.Id("L"),
        Comma, F.Id("d"), Comma, Word("scaled"), Open, F.Id("M"), Comma, F.Id("e"), Comma, F.Id("Z"), Close,
        Close, Sp, Eq, Sp, Word("scaled"), Open, F.Id("L"), Sp, Cdot, Sp, F.Id("M"), Comma, Open, F.Id("i"),
        Sp, Mapsto, Sp, F.Id("e"), Open, F.Id("i"), Close, Sp, Cdot, Sp, F.Id("d"), Open, F.Id("i"), Close,
        Close, Comma, F.Id("Z"), Close);

    private static Formula MatEquivalentSymm() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("Z"),
        Comma, F.Id("W"), Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"), Comma, F.Id("m"), Close, Comma, Sp,
        Word("MatEquivalent"), Open, F.Id("W"), Comma, F.Id("Z"), Close, Sp, Implies, Sp,
        Word("MatEquivalent"), Open, F.Id("Z"), Comma, F.Id("W"), Close);

    private static Formula MatEquivalentTrans() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("X"),
        Comma, F.Id("Y"), Comma, F.Id("Z"), Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"), Comma, F.Id("m"),
        Close, Comma, Sp, Word("MatEquivalent"), Open, F.Id("X"), Comma, F.Id("Y"), Close, Sp, Implies, Sp,
        Word("MatEquivalent"), Open, F.Id("Y"), Comma, F.Id("Z"), Close, Sp, Implies, Sp,
        Word("MatEquivalent"), Open, F.Id("X"), Comma, F.Id("Z"), Close);

    private static Formula ReorderEquiv() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("Z"),
        Comma, F.Id("W"), Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"), Comma, F.Id("m"), Close, Comma, Sp,
        F.Id("s"), Sp, Colon, Sp, Word("Perm"), Open, Word("Col"), Open, F.Id("m"), Close, Close, Comma, Sp,
        Word("MatEquivalent"), Open, F.Id("W"), Comma, F.Id("Z"), Close, Sp, Implies, Sp,
        Word("MatEquivalent"), Open, Word("reorder"), Open, F.Id("s"), Comma, F.Id("W"), Close, Comma,
        Word("reorder"), Open, F.Id("s"), Comma, F.Id("Z"), Close, Close);

    private static Formula ReorderAdmissible() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("Z"),
        Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"), Comma, F.Id("m"), Close, Comma, Sp, F.Id("s"), Sp,
        Colon, Sp, Word("Perm"), Open, Word("Col"), Open, F.Id("m"), Close, Close, Comma, Sp,
        Word("Admissible"), Open, F.Id("Z"), Close, Sp, Implies, Sp, Word("Admissible"), Open, Word("reorder"),
        Open, F.Id("s"), Comma, F.Id("Z"), Close, Close);

    private static Formula LevelEquiv() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("Z"),
        Comma, F.Id("W"), Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"), Comma, F.Id("m"), Close, Comma, Sp,
        Word("MatEquivalent"), Open, F.Id("W"), Comma, F.Id("Z"), Close, Sp, Implies, Sp, Open,
        Word("evenProduct"), Open, F.Id("W"), Close, Sp, Eq, Sp, Word("oddProduct"), Open, F.Id("W"), Close,
        Sp, Iff, Sp, Word("evenProduct"), Open, F.Id("Z"), Close, Sp, Eq, Sp, Word("oddProduct"), Open,
        F.Id("Z"), Close, Close);

    private static Formula Word(string value) => Seq(Operatorname, Grp(F.Id(value)));

    private static string NodeId(string name) =>
        "frieze-matrixequiv-" + name.ToLowerInvariant().Replace('_', '-');
}
