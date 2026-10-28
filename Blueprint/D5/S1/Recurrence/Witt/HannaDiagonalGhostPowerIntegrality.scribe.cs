using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Witt;

internal sealed class HannaDiagonalGhostPowerIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.";
    private const string SourceSentence =
        "More generally, if exp( Sum_{n>=1} C(n) * x^n/n ) equals a power series in x with integer coefficients, then exp( Sum_{n>=1} C(n)^n * x^n/n ) also equals a power series in x with integer coefficients (conjecture).";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2009a156216");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal self-powers preserve integrality of formal exponential ghost series.",
        H("Hanna's Diagonal Ghost-Power Integrality"),
        Blocks(
            Paragraph(Text("All series are ordinary formal power series. K is an arbitrary "
                + "characteristic-zero field, and the integer image is its canonical one. "
                + "The zeroth sequence entry is ignored. The logarithmic input has constant "
                + "coefficient zero, so formal exponential substitution is defined. Division "
                + "in the displayed logarithmic input is division in K. No positivity, "
                + "nonzero-ghost or convergence hypothesis occurs.")),
            Node("logarithmicInput", "The positive-degree logarithmic input",
                LogarithmicInputFormula(),
                "OEIS A156216, internal revision #3, second comment (unpaginated): \""
                    + SourceSentence + "\" The expression Sum_{n>=1} C(n) * x^n/n "
                    + "is encoded coefficientwise by PowerSeries.mk, with degree zero set "
                    + "to zero and coefficient C(n)/(n:K) at every positive degree.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("exponentialSum", "The literal formal exponential",
                ExponentialSumFormula(),
                "OEIS A156216, internal revision #3, second comment (unpaginated): \""
                    + SourceSentence + "\" The exponential is PowerSeries.exp over K, "
                    + "substituted at the positive-degree logarithmic input.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's second-comment conjecture",
                Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                "OEIS A156216, internal revision #3, second comment (unpaginated): \""
                    + SourceSentence + "\" The sequence C ranges over all natural "
                    + "indices, its entry at zero is unused, and C(n)^n raises the nth "
                    + "entry to its own natural index. IntegralSeries is the existing "
                    + "predicate asserting that every ordinary coefficient is an embedded "
                    + "integer. All fields and both field instances are quantified.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Diagonal self-powers preserve integrality",
                Disp(ClaimBody()),
                "The integral input series has an integer Euler ledger b. Its formal "
                    + "logarithmic derivative identifies each positive ghost C(n) with "
                    + "the integer divisor sum of d*b(d). Nested divisor sums give local "
                    + "Gauss congruences. Fermat lifting together with power preservation "
                    + "of base congruences proves those congruences for C(n)^n, including "
                    + "signed and zero ghosts. Integer Moebius inversion supplies the "
                    + "output Euler ledger. Coefficientwise uniqueness of the differential "
                    + "equation X*f'=L*f with prescribed constant coefficient identifies "
                    + "the integer Euler series with the displayed formal exponential. "
                    + "Each coefficient involves only finite sums and finite Euler prefixes.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("a156216-diagonalghost"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create("hanna-diagonal-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula LogarithmicInputFormula()
    {
        var coefficient = Call("ite", Equal(V("n"), D(0)), D(0),
            new Formula.Fraction(App(V("C"), V("n")),
                Parenthesized(Seq(V("n"), Colon, Sp, V("K")))));
        return Disp(Seq(Context(Seq(V("Type"), Star)), Equal(Call("logarithmicInput", V("C")),
            App(Q("PowerSeries", "mk"), Lambda("n", Nat(), coefficient)))));
    }

    private static Formula ExponentialSumFormula() => Disp(Seq(Context(Seq(V("Type"), Star)),
        Equal(Call("exponentialSum", V("C")),
            App(Q("PowerSeries", "subst"), Call("logarithmicInput", V("C")),
                App(Q("PowerSeries", "exp"), V("K"))))));

    private static Formula ClaimBody() => Seq(Context(V("Type")),
        new Formula.Logic(
            App(Q("HannaLogarithmicPowerClosure", "IntegralSeries"),
                Call("exponentialSum", V("C"))),
            FormulaLogicOperator.Implies,
            App(Q("HannaLogarithmicPowerClosure", "IntegralSeries"),
                Call("exponentialSum", Lambda("n", Nat(),
                    new Formula.Power(App(V("C"), V("n")), V("n")))))));
    private static Formula Context(Formula carrierType) => Seq(Bound("K", carrierType),
        OpenBracket, Call("Field", V("K")), CloseBracket, Sp,
        OpenBracket, Call("CharZero", V("K")), CloseBracket, Comma, Sp,
        Bound("C", Seq(Nat(), Sp, To, Sp, V("K"))));
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
}
