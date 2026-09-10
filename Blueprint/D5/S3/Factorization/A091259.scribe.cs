using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class A091259Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/A091259.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/oeis2024a091259");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reduction can consume whatever it likes: if every divisor on the denominator "
        + "side is one modulo three, the reduced numerator is determined anyway.",
        H("Reduced Numerators Modulo Three"),
        Blocks(
            Paragraph(Text(
                "Arguments are positive naturals. The quadratic below is the one whose "
                + "roots are the primitive cube roots of unity, written out rather than "
                + "taken from a cyclotomic library so the arithmetic stays elementary.")),
            Node("reduced_numerator_mod_three", "Reduction without tracking", ReductionFormula(),
                "This is the step the printed material does not supply. Cancelling a "
                + "fraction could consume a factor of three or leave one behind, and "
                + "following that through the exponents is delicate. It is also "
                + "unnecessary: after cancelling, the two cofactors are coprime, so the "
                + "denominator cofactor divides the other side's denominator, and the "
                + "remaining factor divides it too. Every divisor there being one modulo "
                + "three fixes the answer regardless of what was cancelled.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("cyclotomicThree", "The quadratic", QuadraticFormula(),
                "Its values at prime powers carry the whole local behaviour.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("localNumerator_mod", "The local classification", LocalFormula(),
                "A prime congruent to two contributes zero at odd exponents and one at "
                + "even ones; the prime three contributes one throughout; a prime "
                + "congruent to one contributes a single factor of three on each side and "
                + "the quotients are one. The exponent parity is what the indicator on the "
                + "other side is reading.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("a091259_mod_three", "The conjecture", MainFormula(),
                "The divisor sums are multiplicative, so the cross-multiplication holds "
                + "factor by factor, with the denominator side built from the local "
                + "factors with their threes stripped. Every divisor there is one modulo "
                + "three, so the reduction lemma applies and the local classification "
                + "assembles into the indicator.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a091259-reduced-numerator-mod-three"),
                    ResolutionKind.Proved)),
            Paragraph(Text(
                "The classical criterion behind the indicator is taken as printed on the "
                + "source's neighbouring entry and is not reproved here. The adjacent "
                + "conjecture about which denominators occur is untouched; only its easy "
                + "direction enters, and that direction is what the stripped construction "
                + "supplies.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a091259-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula ReductionFormula() => Disp(Seq(
        Forall, Sp, A(), Comma, Sp, B(), Comma, Sp, AA(), Comma, Sp, BB(), Sp,
        InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Open, D(0), Sp, Lt, Sp, B(), Sp, Land, Sp,
        Open, Forall, Sp, F.Id("d"), Sp, Mid, Sp, BB(), Comma, Sp,
        Mod(F.Id("d"), D(3)), Sp, Eq, Sp, D(1), Close, Sp, Land, Sp,
        Mul(A(), BB()), Sp, Eq, Sp, Mul(B(), AA()), Close, Sp, Rightarrow, Sp,
        Mod(Frac2(A(), Call("gcd", A(), B())), D(3)), Sp, Eq, Sp, Mod(AA(), D(3))));

    private static Formula QuadraticFormula() => Disp(Seq(
        Forall, Sp, T(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Call("cyclotomicThree", T()), Sp, Eq, Sp,
        Add(Add(Pow(T(), D(2)), T()), D(1))));

    private static Formula LocalFormula() => Disp(Seq(
        Forall, Sp, P(), Comma, Sp, E(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Mod(Call("localNumerator", P(), E()), D(3)), Sp, Eq, Sp,
        Open, D(0), Sp, Mathrm, Grp(F.Id("if")), Sp, Mod(P(), D(3)), Sp, Eq, Sp, D(2),
        Sp, Land, Sp, Mathrm, Grp(F.Id("odd")), Sp, E(), Comma, Sp,
        D(1), Sp, Mathrm, Grp(F.Id("otherwise")), Close));

    private static Formula MainFormula() => Disp(Seq(
        Forall, Sp, N(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        D(0), Sp, Lt, Sp, N(), Sp, Rightarrow, Sp,
        Mod(Frac2(Call("sigma", D(3), N()),
            Call("gcd", Call("sigma", D(3), N()), Call("sigma", D(1), N()))), D(3)),
        Sp, Eq, Sp, Call("indicator", N())));

    private static Formula Frac2(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Mod(Formula a, Formula b) => new Formula.Modulo(a, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula A() => F.Id("a");
    private static Formula B() => F.Id("b");
    private static Formula AA() => F.Id("A");
    private static Formula BB() => F.Id("B");
    private static Formula N() => F.Id("n");
    private static Formula P() => F.Id("p");
    private static Formula E() => F.Id("e");
    private static Formula T() => F.Id("t");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
