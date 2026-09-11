using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class LucasEvenPeriodsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/LucasEvenPeriods.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/fiebigmbirikaspilker2025lucas");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two even-parameter open period questions are settled: the matrix and companion periods agree exactly outside q = 1, modulus 4, and 4 dividing p.",
        H("Even Lucas Periods"),
        Blocks(
            Paragraph(Text(
                "Fiebig, Mbirika and Spilker's Questions 5.3 and 5.4 ask whether the "
                    + "matrix and companion periods agree when p and the modulus are both even. "
                    + "This theorem settles both questions as an iff: the periods agree exactly "
                    + "outside the single case q = 1, m = 4, and 4 divides p. The proof here is "
                    + "repository work and uses neither Ballot's equality theorem nor McDaniel's "
                    + "1991 gcd theorem; the paper's Corollary 3.13 does not reach the case where "
                    + "p and m are both even.")),
            Paragraph(Text(
                "The exception is sharp. Over ZMod(2^v), a zero of the companion sequence and "
                    + "Cayley--Hamilton give M^2 = -q. For q = 1 the trace sequence is "
                    + "2, 0, -2, 0, ...; it drops to period 2 exactly when 2 = -2, namely v = 2. "
                    + "For p congruent to 2 modulo 4 and modulus 4, the companion sequence is "
                    + "constantly 2 modulo 4, so no zero exists and the hypothesis is vacuous; "
                    + "this confines the exception to 4 dividing p rather than all even p.")),
            Node("even_lucas_periods", "Exact equality criterion for even Lucas periods",
                PeriodFormula(),
                "This is the settled result corresponding to the paper's Questions 5.3 and "
                    + "5.4. Its hypotheses include even p, even m with 2 < m, and a positive "
                    + "companion zero modulo m. Integer units encode q = plus or minus 1. "
                    + "All definitions and the proof route are from this repository.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("lucas-even-periods-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Typed(string name, Formula type) => Seq(F.Id(name), Colon, Sp, type);
    private static Formula Bind(string name, Formula type) => Seq(Forall, Sp, Typed(name, type), Comma);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Divides(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);
    private static Formula Not(Formula a) => Seq(Neg, Sp, a);
    private static Formula Even(Formula a) => Call("Even", a);
    private static Formula Positive(Formula a) => Seq(D(0), Sp, Lt, Sp, a);
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ZMod(Formula a) => Call("ZMod", a);
    private static Formula Units(Formula a) => Call("Units", a);
    private static Formula Cast(Formula a, Formula t) => Call("Cast", a, t);
    private static Formula P() => F.Id("p");
    private static Formula Q() => F.Id("q");
    private static Formula M() => F.Id("m");
    private static Formula RUnit() => Call("reducedUnit", M(), Q());
    private static Formula V(Formula n) => Call("lucasV", Cast(P(), ZMod(M())), RUnit(), n);
    private static Formula PeriodFormula() => Disp(new Formula.Aligned([
        Bind("p", Integers()), Bind("q", Units(Integers())), Bind("m", Naturals()),
        Seq(Even(P()), Sp, Rightarrow, Sp, Even(M()), Sp, Rightarrow, Sp,
            Seq(D(2), Sp, Lt, Sp, M()), Sp, Rightarrow, Sp),
        Seq(Exists, Sp, Typed("r", Naturals()), Comma, Sp, Positive(F.Id("r")), Sp, Land, Sp,
            Equal(V(F.Id("r")), D(0))), Sp, Rightarrow, Sp,
        Seq(Equal(Call("matrixPeriod", Cast(P(), ZMod(M())), RUnit()),
            Call("companionPeriod", Cast(P(), ZMod(M())), RUnit())), Sp, Iff, Sp,
            Not(Seq(Q(), Sp, Eq, Sp, D(1), Sp, Land, Sp,
                Equal(M(), D(4)), Sp, Land, Sp,
                Divides(D(4), Cast(P(), Integers()))))),
    ]));
}
