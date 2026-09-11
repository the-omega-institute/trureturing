using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class QuarticEGFModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/QuarticEGFModFour.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/hanna2026a396804");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive-index EGF coefficient in OEIS A396804 is congruent to its index modulo four.",
        H("A396804 Modulo Four"),
        Blocks(
            Paragraph(Text("The symbols A and a denote the rational series and natural "
                + "sequence in QuarticEGFFixedPoint. That module proves the exact "
                + "zero-constant source equation, existence, uniqueness, and natural "
                + "integrality. The proof here assumes none of the source's conjectures.")),
            Note("F", "The comparison series",
                "F=X exp(X). Its factorial-normalized degree-n coefficient is n, including zero."),
            Note("square_coeff", "Exact square coefficients",
                "The degree-n EGF coefficient of F composed with F is the sum of "
                + "binomial(n,k) k k^(n-k) for 0<=k<=n. In characteristic two, "
                + "k k^(n-k)=k, so the sum is n times 2^(n-1), zero for n>=2."),
            Note("linear_fourth_mod_four", "The active fourth-iterate escape",
                "The square has integral EGF coefficients and equals X+2H for an "
                + "integral half-series H. Substitution preserves coefficient congruences, "
                + "so H composed with the square equals H modulo two. Composing the "
                + "square with itself therefore gives X modulo four. This new arithmetic "
                + "fact is used by the invariant of the natural fixed-point approximations."),
            Note("fourth_coeff_divisible", "The proposed companion divisibility",
                "For each n>=2 there is a natural k such that n! [X^n](A fourth)=4k. "
                + "The proof transfers the comparison-series iterate to the constructed A. "
                + "This is an all-degree statement, not a finite residue table."),
            Describe.Lean(DescribeId.Create("a396804-mod-four"),
                DeclarationHandle.Create(Prefix + "mod_four"), H("The OEIS conjecture"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(1), Leq, Sp, F.Id("n"), Implies, Sp,
                    new Formula.Modulo(Call("a", F.Id("n")), D(4)), Eq,
                    new Formula.Modulo(F.Id("n"), D(4))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The initial approximation is F in EGF coordinates. "
                    + "The fourth-iterate identity and integral composition show that step "
                    + "preserves coefficient n modulo four. Stabilization gives the claimed "
                    + "congruence for every positive n. The independently computed examples "
                    + "a(2)=2, a(3)=27 and the fourth iterate's second EGF coefficient 8 "
                    + "check nonempty values; they are not used as a bounded proof."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396804-quartic-egf-mod-four"), ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static DocumentBlock Note(string name, string title, string prose) =>
        Describe.Remark(DescribeId.Create("a396804-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))));
}
