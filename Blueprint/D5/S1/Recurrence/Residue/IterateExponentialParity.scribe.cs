using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class IterateExponentialParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/IterateExponentialParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every compositional iterate count gives fixed-point EGF coefficients odd exactly at positive odd indices.",
        H("Parity of the Iterated-Exponential Family"),
        Blocks(
            Paragraph(Text("The OEIS entries A396803, A396805 and A396806 specify "
                + "A=X*exp(A^{[k]}) for k=3, 5 and 6, respectively. Here A^{[k]} "
                + "is the k-fold compositional iterate, not an ordinary power; the zeroth "
                + "iterate is the identity series X. Each entry carries further residue "
                + "conjectures that are not proved here.")),
            Paragraph(Text("For natural k, the natural sequence aK(k,n) is the "
                + "coefficientwise limit of a contracting stage sequence starting at n. "
                + "Agreement below degree d becomes agreement below degree d+1 after "
                + "one step, so coefficient n stabilizes at stage n+1. The series AK(k) "
                + "encodes aK(k,n) as an exponential generating series over Q: its "
                + "ordinary coefficient at degree n is aK(k,n)/n!. All series are formal; "
                + "no analytic convergence is asserted.")),
            Paragraph(Text("In the formulas, k and n are natural numbers, f and g are "
                + "rational power series, constantCoeff extracts the constant coefficient, "
                + "and iterateComp(f,k) denotes compositional iteration. The expression "
                + "subst(exp(Q),h) means the exponential series with h substituted for X. "
                + "A_equation and fixed_unique identify AK(k), and hence its EGF "
                + "coefficient sequence aK(k,n), with the defining equation's unique "
                + "zero-constant solution.")),
            Node("A_equation", "The defining series equation", EquationFormula(),
                "For every k, AK(k) has constant coefficient zero and satisfies "
                + "A=X*exp(A^{[k]}). The stabilized coefficient sequence is a fixed "
                + "point of the integral coefficient transformation."),
            Node("fixed_unique", "Uniqueness of the formal solution", UniqueFormula(),
                "Any two rational series with zero constant coefficient satisfying "
                + "the equation agree in every degree by contraction. In particular, "
                + "each such series equals AK(k), which A_equation supplies."),
            Node("odd_iff_odd", "Parity for every iterate count",
                Disp(Seq(Bound("k", Naturals()), Bound("n", Naturals()), ParityBody(K()))),
                "For every natural iterate count and positive index n, aK(k,n) is "
                + "odd exactly when n is odd. The coefficient transformation preserves "
                + "the sequence n modulo two, and induction carries this congruence "
                + "through all stages to the stabilized sequence."),
            Node("parity_iterate_three", "A396803 parity", EndpointFormula(3),
                "Specializing odd_iff_odd at k=3 proves the positive-index parity "
                + "conjecture for the third compositional iterate. The further residue "
                + "conjecture modulo three is not proved here.",
                "oeis-a396803-iterate-exponential-parity"),
            Node("parity_iterate_five", "A396805 parity", EndpointFormula(5),
                "Specializing odd_iff_odd at k=5 proves the positive-index parity "
                + "conjecture for the fifth compositional iterate. The further residue "
                + "conjectures modulo three and five are not proved here.",
                "oeis-a396805-iterate-exponential-parity", note: "hanna2026a396805"),
            Node("parity_iterate_six", "A396806 parity", EndpointFormula(6),
                "Specializing odd_iff_odd at k=6 proves the positive-index parity "
                + "conjecture for the sixth compositional iterate. The further residue "
                + "conjectures modulo three and six are not proved here.",
                "oeis-a396806-iterate-exponential-parity", note: "hanna2026a396806"))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        string? slug = null, string note = "hanna2026a396family") =>
        Describe.Lean(DescribeId.Create("a396family-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            slug is null ? AssessedProvenance.FromRepo() :
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/ArithSums/" + note)),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem,
            slug is null ? null : new OpenProblemResolutionClaim(
                ProblemSlugRef.Create(slug), ResolutionKind.Proved));

    private static Formula K() => F.Id("k");
    private static Formula N() => F.Id("n");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula ZeroConstant(Formula series) => Equal(Call("constantCoeff", series), D(0));
    private static Formula FixedEquation(Formula series) => Equal(series,
        Seq(F.Id("X"), Sp, Star, Sp,
            Call("subst", Call("exp", Rationals()), Call("iterateComp", series, K()))));
    private static Formula EquationFormula() => Disp(Seq(Bound("k", Naturals()),
        Conjunction(ZeroConstant(Call("AK", K())), FixedEquation(Call("AK", K())))));
    private static Formula UniqueFormula()
    {
        Formula f = F.Id("f"), g = F.Id("g");
        Formula seriesType = Call("PowerSeries", Rationals());
        return Disp(Seq(Bound("k", Naturals()), Bound("f", seriesType), Bound("g", seriesType),
            Implication(ZeroConstant(f), Implication(ZeroConstant(g),
                Implication(FixedEquation(f), Implication(FixedEquation(g), Equal(f, g)))))));
    }
    private static Formula ParityBody(Formula k) =>
        Implication(Seq(D(1), Sp, Le, Sp, N()),
            Parenthesized(Seq(Call("Odd", Call("aK", k, N())), Sp, Iff, Sp, Call("Odd", N()))));
    private static Formula EndpointFormula(byte k) =>
        Disp(Seq(Bound("n", Naturals()), ParityBody(D(k))));
}
