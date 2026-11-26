using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class AbedNikolaevaNovikovItemSixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/abednikolaevanovikov2026traces");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The spectral geometric mean has sharp relative trace-violation envelope 1/√(1−δ²)−1 in complex dimension two.",
        H("The sharp qubit spectral-mean envelope"),
        Blocks(
            Entry("fixed-density", "V", "Relative violation for a fixed density", Violation(),
                "Section 3.4, p. 10: “For a fixed density V(ρ) denotes its supremum, and the envelope Vₙ(δ) is the supremum of V(ρ) over all ρ in Mₙ with OMC(ρ) = δ.” "
                + "V is the real supremum of (L−R)/R for item 6. The real trace functional is Complex.re of FiniteDimensional.bornProbability. "
                + "The spectral geometric mean is SpectralGeometricLogEuclideanRefutation.specMean at real weight 1/2. "
                + "A and B range over all positive definite complex 2×2 matrices; no commutation or trace-one assumption is imposed.", true),
            Entry("envelope", "envelope", "Envelope at a prescribed contrast", Envelope(),
                "Section 3.4, p. 10: “For a fixed density V(ρ) denotes its supremum, and the envelope Vₙ(δ) is the supremum of V(ρ) over all ρ in Mₙ with OMC(ρ) = δ.” "
                + "The contrast is (M−m)/(M+m), with M the supremum and m the infimum of the real spectrum, as in Section 3.2. "
                + "The supremum ranges over every positive definite complex qubit density with this contrast, with arbitrary positive scale.", true),
            Entry("claim", "claim", "Conjecture 11.1, item 6", Eqn(Id("claim"), ClaimBody()),
                SourceQuotation + " The selected clause is V₂=G−1 for item 6. Here G=1/√(1−δ²), δ ranges over [0,1), and envelope is V₂. "
                + "The other clauses of the conjecture are separate assertions.", true),
            Entry("result", "result", "The sharp spectral-mean envelope", ClaimBody(),
                SourceQuotation + " The item-6 equality holds for the entire faithful interval. "
                + "A completed square controls the two-dimensional off-diagonal contribution. The trace/determinant identity for contrast yields the uniform upper bound after unitary diagonalization. "
                + "Positive definite matrices approaching a rank-one limit give the lower bound for a density of each contrast. "
                + "Both suprema are nonempty and bounded above on this interval. A written corollary transfers the value to each faithful qubit density of the prescribed contrast by unitary conjugation and positive rescaling.", false, DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ann-item-six"),
                    ResolutionKind.Proved)))));

    private const string SourceQuotation =
        "Abed, Nikolaeva and Novikov, arXiv:2610.34388v1, p. 57, Conjecture 11.1: “Vₙ = G² − 1 for item 7 and Vₙ = g₂₅(δ) for item 25 in every dimension; V₂ = G − 1 for item 6; the value of Proposition 5.17 holds for item 9 in every dimension; and the lower bound of Proposition 5.22 is the two-contrast envelope of item 8 for even n.”";

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, bool literature, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Id(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(Id("C")));
    private static Formula Mat => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Complex);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Conj(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Land, Sp, b));
    private static Formula ImpliesF(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Rightarrow, Sp, b));
    private static Formula Sub(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Minus, Sp, b));
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sq(Formula a) => new Formula.Power(a, D(2));
    private static Formula Weight(Formula rho, Formula y) =>
        Seq(Parenthesized(Call("bornProbability", rho, y)), Dot, Id("re"));
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, Id(name), Colon, Sp, type, Sp, Bar, Sp, body, CloseBrace);
    private static Formula Violation()
    {
        var rho = Id("rho"); var a = Id("A"); var b = Id("B"); var r = Id("r");
        var denominator = Call("sqrt", Mul(Weight(rho, a), Weight(rho, b)));
        return All("rho", Mat, Eqn(Call("V", rho), Call("sSup", SetOf("r", Real,
            Ex("A", Mat, Ex("B", Mat, Conj(Call("PosDef", a), Conj(Call("PosDef", b),
                Eqn(r, Fraction(Sub(Weight(rho, Call("specMean", a, b, Fraction(D(1), D(2)))),
                    denominator), denominator))))))))));
    }
    private static Formula Envelope()
    {
        var delta = Id("delta"); var rho = Id("rho"); var r = Id("r");
        return All("delta", Real, Eqn(Call("envelope", delta), Call("sSup", SetOf("r", Real,
            Ex("rho", Mat, Conj(Call("PosDef", rho), Conj(Eqn(Call("contrast", rho), delta),
                Eqn(r, Call("V", rho)))))))));
    }
    private static Formula ClaimBody()
    {
        var delta = Id("delta");
        return All("delta", Real, ImpliesF(Seq(D(0), Sp, Le, Sp, delta),
            ImpliesF(Seq(delta, Sp, Lt, Sp, D(1)), Eqn(Call("envelope", delta),
                Sub(Fraction(D(1), Call("sqrt", Sub(D(1), Sq(delta)))), D(1))))));
    }
}
