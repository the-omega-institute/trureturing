using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class LogarithmicWeightBinaryParityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/LogarithmicWeightBinaryParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2026a397349");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic-weight coefficients are odd exactly at powers of two.",
        H("Logarithmic-Weight Coefficients Modulo Two"),
        Blocks(
            Paragraph(Text("The parity clause of OEIS A397349 is quoted in hanna2026a397349. "
                + "The frozen module LogarithmicWeightCatalanParity states this parity property "
                + "as the proposition parity_conjecture without proof; this document records "
                + "its proof. The entry's modulo-three clause is settled separately and is "
                + "not restated here.")),
            Paragraph(Text("Write a for the frozen integer-valued function "
                + "LogarithmicWeightCatalanParity.a. All indices and exponents are natural "
                + "numbers. The result concerns that constructed sequence; no identification "
                + "with the logarithmic generating function in the entry's NAME is asserted.")),
            Node("parity_conjecture_holds", "Hanna's parity conjecture",
                ConjectureFormula(),
                "Let A be the coefficient series of a reduced modulo two, with X the "
                + "indeterminate. Its constant coefficient is zero and its derivative is one. "
                + "The convolution identities and their derivatives give A = X + A^2, "
                + "the equation characterising the binary Catalan series with zero constant "
                + "coefficient. Uniqueness identifies the two series, so the coefficients "
                + "are odd exactly at powers of two, including n=1 and excluding n=0.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397349-logarithmic-weight-parity"),
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
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Parenthesized(Seq(Call("Odd", Call("a", N())), Sp, Iff, Sp,
            Parenthesized(Seq(Exists, Sp, F.Id("k"), Colon, Sp, Naturals(), Comma, Sp,
                Equal(N(), new Formula.Power(D(2), F.Id("k")))))))));
}
