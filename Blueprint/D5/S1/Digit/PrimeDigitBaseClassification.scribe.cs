using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class PrimeDigitBaseClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/PrimeDigitBaseClassification.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/oeis2025a390088");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two certificates cover every argument above nine, leaving five exceptions "
        + "below it.",
        H("Prime Digit Bases"),
        Blocks(
            Paragraph(Text(
                "Digit lists are little-endian, so the pair written two-two appears as the "
                + "list with two twice and the pair written two-three appears with three "
                + "first. The empty list of the zero argument is why that argument is "
                + "excluded explicitly: a condition quantified over an empty list holds "
                + "vacuously, which would otherwise admit it.")),
            Node("HasPrimeDigitBase", "The condition", ConditionFormula(),
                "Some base above one writes the argument with every digit prime. The "
                + "argument being nonzero is part of the condition, not an afterthought.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("prime_digit_base_certificate", "Two certificates above nine",
                CertificateFormula(),
                "An even argument is two more than twice half of two less than it, and an "
                + "odd argument is three more than twice half of three less than it. Each "
                + "gives a two-digit representation whose digits are prime and below the "
                + "base. The statement is an equality of digit lists, not merely existence.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("a390088", "The exception set", MainFormula(),
                "Above nine the certificates apply. Below it the question is finite: four "
                + "arguments admit no base, the zero argument is excluded by the condition "
                + "itself, and the rest admit one, of which a single argument admits only "
                + "one base. For nonexistence, split on whether the argument is below the "
                + "base; if it is, the digit list is a singleton and primality is direct, "
                + "and if it is not, the base is small too and a bounded enumeration ends "
                + "it.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a390088-prime-digit-base-existence"),
                    ResolutionKind.Proved)),
            Paragraph(Text(
                "The least such base, which is what the source's sequence records, is not "
                + "formalized here; only the existence question the conjecture asks.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a390088-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula ConditionFormula() => Universal(Seq(
        Call("HasPrimeDigitBase", N()), Sp, Iff, Sp,
        N(), Sp, Neq, Sp, D(0), Sp, Land, Sp,
        Exists, Sp, B(), Comma, Sp, D(1), Sp, Lt, Sp, B(), Sp, Land, Sp,
        Forall, Sp, F.Id("d"), Sp, InMacro, Sp, Call("digits", B(), N()), Comma, Sp,
        Call("Prime", F.Id("d"))));

    private static Formula CertificateFormula() => Universal(Seq(
        D(1, 0), Sp, Leq, Sp, N(), Sp, Rightarrow, Sp,
        Open, Call("digits", Half(D(2)), N()), Sp, Eq, Sp,
        Bracket(Seq(D(2), Comma, Sp, D(2))), Close, Sp, Lor, Sp,
        Open, Call("digits", Half(D(3)), N()), Sp, Eq, Sp,
        Bracket(Seq(D(3), Comma, Sp, D(2))), Close));

    private static Formula MainFormula() => Universal(Seq(
        Call("HasPrimeDigitBase", N()), Sp, Iff, Sp,
        Neg, Sp, Grp(N(), Sp, InMacro, Sp, Bracket(Seq(
            D(0), Comma, Sp, D(1), Comma, Sp, D(4), Comma, Sp, D(6), Comma, Sp, D(9))))));

    private static Formula Half(Formula c) => Seq(Frac, Grp(Sub(N(), c)), Grp(D(2)));
    private static Formula Universal(Formula body) => Disp(Seq(
        Forall, Sp, N(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp, body));
    private static Formula Bracket(Formula b) => Seq(OpenBrace, b, CloseBrace);
    private static Formula N() => F.Id("n");
    private static Formula B() => F.Id("b");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
}
