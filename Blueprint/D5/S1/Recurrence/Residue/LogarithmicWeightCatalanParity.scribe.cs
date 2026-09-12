using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class LogarithmicWeightCatalanParityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/LogarithmicWeightCatalanParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2026a397349");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OEIS A397349 alternates 1, 2 modulo three at positive indices; its parity conjecture remains open.",
        H("Logarithmic-Weight Coefficients Modulo Three"),
        Blocks(
            Paragraph(Text("The NAME and both conjecture COMMENTS are quoted in hanna2026a397349. "
                + "Only the modulo-three statement is proved below. The separate statement that a(n) "
                + "is odd exactly at powers of two is not proved: parity_conjecture is a "
                + "proposition definition carrying no proof, and is not a theorem.")),
            Paragraph(Text("Write a for the module's function from natural numbers to integers. "
                + "The displayed mod denotes the remainder operation: integer remainder for "
                + "a(n) mod 3, natural-number remainder for n mod 2. The words if, then, else "
                + "denote Lean's conditional, with integer-valued branches 1 and 2. "
                + "A single well-founded recursion constructs s with s(0)=s(1)=0. "
                + "Define a(k)=1 if k=1 and (3*k^2-1)*s(k) otherwise; "
                + "b(m)=1 if m<=1 and 3*m*s(m) otherwise. For n>=2, s_eq_sum gives "
                + "s(n)=sum over 1<=k<n of a(k)*b(n-k). No uniqueness or formal "
                + "identification with the logarithmic generating function is proved here.")),
            Node("hanna_conjecture_a397349_mod_three", "Hanna's modulo-three conjecture",
                ConjectureFormula(),
                "For m>=2, b_mod_three uses the explicit factor of three in b(m). "
                + "In s_eq_sum only k=n-1 survives modulo three, since b(1)=1; "
                + "the lemma s_mod_three proves s(n) mod 3 = a(n-1) mod 3. "
                + "The factor 3*n^2-1 has remainder 2, so a_mod_three_step gives "
                + "a(n) mod 3 = (2*(a(n-1) mod 3)) mod 3. Induction from a(1)=1 "
                + "proves the displayed alternation. This argument does not prove the "
                + "parity conjecture, which remains open.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397349-logarithmic-weight-mod-three"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim claim) =>
        Describe.Lean(DescribeId.Create("a397349-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula N() => F.Id("n");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Remainder(Formula value, Formula modulus) =>
        Parenthesized(Seq(value, Sp, Named("mod"), Sp, modulus));
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Le, Sp, N()),
            Equal(Remainder(Call("a", N()), D(3)),
                Seq(Named("if"), Sp, Equal(Remainder(N(), D(2)), D(1)),
                    Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(2))))));
}
