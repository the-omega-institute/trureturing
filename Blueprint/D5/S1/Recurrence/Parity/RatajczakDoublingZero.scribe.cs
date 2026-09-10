using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class RatajczakDoublingZeroDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/RatajczakDoublingZero.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/oeis2025a378252");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A running-sum residue recurrence is a doubling in disguise, so it vanishes "
        + "exactly when its modulus is a power of two.",
        H("Running-Sum Residue Zeros"),
        Blocks(
            Paragraph(Text(
                "Indices and values are natural numbers. The recurrence enters as a "
                + "hypothesis on an arbitrary sequence rather than as a construction, so "
                + "the results apply to any sequence satisfying it. Reduction is natural "
                + "remainder, and the empty sum is zero, which makes the first term the "
                + "start value reduced.")),
            Node("IsRunningSumResidue", "The recurrence", RecurrenceFormula(),
                "Each term is the start value plus every earlier term, reduced. At index "
                + "zero the range is empty, so the first term is the start value reduced.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("residue_eq_two_pow_mul", "The accumulation is a doubling", ClosedFormFormula(),
                "The partial sum advances by the previous term, and that term is the "
                + "previous partial sum reduced. Reducing before adding therefore replaces "
                + "the partial sum by the term itself, turning the step into a doubling. "
                + "Induction then gives the start value scaled by a power of two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("exists_zero_iff_modulus_pow_two", "The vanishing criterion", CriterionFormula(),
                "Vanishing says the modulus divides a power of two times the start value. "
                + "Coprimality moves the entire power onto the modulus, and a divisor of a "
                + "prime power is a power of that prime. Conversely a power-of-two modulus "
                + "divides the term whose exponent matches. The start value is not required "
                + "to exceed the modulus; neither direction uses that.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a378252-running-sum-residue-zero"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a378252-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula RecurrenceFormula() => Disp(Seq(
        Bound("n"), Sp, Call("b", Add(N(), D(1))), Sp, Eq, Sp,
        Mod(Add(I(), Seq(new Formula.Subscript(F.Sum,
            Seq(F.Id("k"), Sp, InMacro, Sp, Call("range", N()))), Sp,
            Call("b", Add(F.Id("k"), D(1))))), J())));

    private static Formula ClosedFormFormula() => Disp(Seq(
        Bound("n"), Sp, Call("b", Add(N(), D(1))), Sp, Eq, Sp,
        Mod(Mul(Pow(D(2), N()), I()), J())));

    private static Formula CriterionFormula() => Disp(Seq(
        Call("Coprime", I(), J()), Sp, Rightarrow, Sp, Open,
        Exists, Sp, F.Id("t"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Call("b", Add(F.Id("t"), D(1))), Sp, Eq, Sp, D(0), Close,
        Sp, Iff, Sp, Open,
        Exists, Sp, F.Id("m"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        J(), Sp, Eq, Sp, Pow(D(2), F.Id("m")), Close));

    private static Formula N() => F.Id("n");
    private static Formula I() => F.Id("i");
    private static Formula J() => F.Id("j");
    private static Formula Bound(string name) => Seq(Forall, Sp, F.Id(name), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Comma, Sp);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Mod(Formula a, Formula b) =>
        new Formula.Modulo(a, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
}
