using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class PowerResidueRecursionFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/PowerResidueRecursionFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/oeis2024a374911");
    private static readonly LibraryNoteRef Residues =
        LibraryNoteRef.Create("D5/L/ArithSums/oeis2026a036236");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original power-residue recursion has value four exactly at three and nine.",
        H("Value Four in OEIS A374911"),
        Blocks(
            Node("seq", "The recursive sequence", DefinitionFormula(),
                "The zero case is selected before either recursive call. At a positive "
                    + "index both remainders are strictly smaller than that index, so "
                    + "well-founded recursion defines the sequence on every natural number. "
                    + "In the displayed formula, ite selects the second argument when "
                    + "the first argument holds and the third otherwise.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("seq_eq_one", "Value one", LevelFormula(1, Equal(N(), D(0))),
                "Strong induction proves every term positive. At a nonzero index the "
                    + "sum of two positive recursive terms is at least two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("seq_eq_two", "Value two", LevelFormula(2, Equal(N(), D(1))),
                "Both recursive terms must equal one, making the index divide both "
                    + "two to the index and three to the index. These powers are coprime, "
                    + "so the index is one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("seq_eq_three", "Value three", LevelFormula(3, PositivePowerOfTwo()),
                "A least-prime-divisor and multiplicative-order argument excludes "
                    + "two to the index having remainder one at every index greater than one. "
                    + "Thus the left recursive term must be one, forcing a power of two. "
                    + "Euler's theorem supplies the converse for every positive exponent. "
                    + "The modular exclusion is also proved in the A036236 comments.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source, Residues)),
            Node("a374911_eq_four", "Value four", LevelFormula(4,
                    Seq(Equal(N(), D(3)), Sp, Lor, Sp, Equal(N(), D(9)))),
                "Values one and two for the left recursive term are impossible. The "
                    + "right term is therefore one, forcing the index to be a power of three. "
                    + "Addition lifting of the exponent gives remainder three to the k "
                    + "minus one for the left argument. For even k, two-adic lifting gives "
                    + "j = 2 + v₂(k) when that remainder is two to the j; this implies "
                    + "two to the j is at most 4k, contradicting exponential growth for k "
                    + "at least three. Odd k at least three is excluded modulo four. "
                    + "The remaining exponents one and two give precisely three and nine. "
                    + "This proves the question explicitly posed by A374911; the proof "
                    + "is derived here from the preceding arithmetic ingredients.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source, Residues)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("power-residue-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role);

    private static Formula DefinitionFormula() => Disp(Seq(Bound(N()),
        Equal(A(N()), Call("ite", Equal(N(), D(0)), D(1),
            new Formula.Binary(A(new Formula.Modulo(Pow(D(2), N()), N())),
                FormulaBinaryOperator.Add, A(new Formula.Modulo(Pow(D(3), N()), N())))))));

    private static Formula LevelFormula(byte value, Formula indices) =>
        Disp(Seq(Bound(N()), Equal(A(N()), D(value)), Sp, Leftrightarrow, Sp,
            Open, indices, Close));

    private static Formula PositivePowerOfTwo() => Seq(Exists, Sp, F.Id("k"),
        Colon, Sp, Naturals(), Comma, Sp, D(0), Sp, Lt, Sp, F.Id("k"), Sp,
        Land, Sp, Equal(N(), Pow(D(2), F.Id("k"))));

    private static Formula Bound(Formula n) =>
        Seq(Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula N() => F.Id("n");
    private static Formula A(Formula n) => Call("seq", n);
}
