using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class CubeGapFiveNoSquareDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/CubeGapFiveNoSquare.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/oeis2026a038867");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cubes five apart differ by two modulo three, and no square does.",
        H("Cube Gaps at Five"),
        Blocks(
            Paragraph(Text(
                "Indices and values are natural numbers. Subtraction of naturals truncates, "
                + "so the difference is defined in expanded form and the subtracted form is "
                + "recovered from an identity that shows the subtraction is exact here.")),
            Node("gap", "The difference in expanded form", GapFormula(),
                "Five times a quadratic. Every term but the constant carries a factor of "
                + "three, and the constant leaves two.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gap_eq_cube_sub", "The subtracted form", CubeFormula(),
                "The larger cube exceeds the smaller by exactly this amount, so the "
                + "truncating subtraction agrees with the expansion. This is what lets the "
                + "conclusion be stated in the source's own notation.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("gap_mod_three", "The residue is always two", ResidueFormula(),
                "Immediate from the expansion: three divides every term except the "
                + "constant, and five times twenty-five leaves two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("sq_mod_three_ne_two", "No square leaves two", SquareFormula(),
                "Split the base by its own residue and expand. The cross terms carry a "
                + "factor of three, so only the squared residue survives, and the three "
                + "possible values leave zero, one and one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("cube_gap_five_ne_sq", "The conjecture", MainFormula(),
                "The two residue sets do not meet, so no index gives a square. No size "
                + "estimate or descent is needed.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a038867-cube-gap-five-no-square"),
                    ResolutionKind.Proved)),
            Node("cube_gap_five_ne_sq_sub", "The conjecture in the source's form",
                MainSubFormula(),
                "The same statement with the difference written as a subtraction, which is "
                + "how the source prints it.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Paragraph(Text(
                "Nothing here applies to cube differences at other gaps. The argument uses "
                + "that the constant term leaves two modulo three, which is particular to "
                + "this gap.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a038867-" + name.Replace('_', '-')
            .ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula GapFormula() => Universal(Seq(
        Call("gap", N()), Sp, Eq, Sp,
        Mul(D(5), Grp(Add(Add(Mul(D(3), Sq(N())), Mul(D(1, 5), N())), D(2, 5))))));

    private static Formula CubeFormula() => Universal(Seq(
        Call("gap", N()), Sp, Eq, Sp, Sub(Cube(Grp(Add(N(), D(5)))), Cube(N()))));

    private static Formula ResidueFormula() => Universal(Seq(
        Mod(Call("gap", N()), D(3)), Sp, Eq, Sp, D(2)));

    private static Formula SquareFormula() => Disp(Seq(
        Forall, Sp, M(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Mod(Sq(M()), D(3)), Sp, Neq, Sp, D(2)));

    private static Formula MainFormula() => Disp(Seq(
        Forall, Sp, N(), Comma, Sp, M(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Sq(M()), Sp, Neq, Sp, Call("gap", N())));

    private static Formula MainSubFormula() => Disp(Seq(
        Forall, Sp, N(), Comma, Sp, M(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Sq(M()), Sp, Neq, Sp, Sub(Cube(Grp(Add(N(), D(5)))), Cube(N()))));

    private static Formula Universal(Formula body) => Disp(Seq(
        Forall, Sp, N(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp, body));
    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula Sq(Formula v) => Seq(Grp(v), Caret, Grp(D(2)));
    private static Formula Cube(Formula v) => Seq(Grp(v), Caret, Grp(D(3)));
    private static Formula Mod(Formula a, Formula b) => new Formula.Modulo(a, b);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
