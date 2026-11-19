using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaA300595IntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaA300595Integrality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/hanna2018a300595");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cubic exponential coefficient equations have a unique normalized rational ordinary series, and every positive ordinary coefficient is an integer.",
        H("Hanna A300595: ordinary integrality"), Blocks(
            Node("IsSource", "The normalized rational ordinary series",
                All("F", Series(), Iffn(Call("IsSource", V("F")), SourceBody(V("F")))),
                "The ambient series ring is Q[[x]]. The constant coefficient is zero. For every natural n>=1, " +
                "the scalar is the rational cube of n, and both extractions are ordinary coefficients. " +
                "The subtraction n-1 is used only in this positive-index domain. This is the normalized " +
                "ordinary generating function specified by OEIS A300595 NAME and OFFSET; no integrality " +
                "condition is included in its definition. Formal exp(t F) means the preexisting " +
                "HannaA300591RationalModel.expSeries t F, namely substitution of C(t)F into PowerSeries.exp Q. " +
                "All substitutions used below have zero constant input.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsCompanion", "The normalized A300594 companion",
                All("B", Series(), Iffn(Call("IsCompanion", V("B")), CompanionBody(V("B")))),
                "The companion B has constant coefficient one. Its natural power n^3 satisfies the displayed " +
                "ordinary coefficient equation for every n>=1. A300594 presents B as an exponential generating " +
                "function, with entries beta(r)=r! times its ordinary degree-r coefficient, for every r>=0. " +
                "This convention applies to B alone. The coefficients of A300595 remain the unscaled " +
                "ordinary coefficients of F=log(B). The companion's integer wording is not an assumption.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The complete cubic source event", ResultBody(),
                "The first conjunct proves existence and uniqueness among all normalized rational solutions " +
                "of the source identity. It uses the preexisting triangular_exists_unique with both scalar " +
                "functions equal to n^3; their nonvanishing follows from n>=1. This rational construction " +
                "precedes every integrality argument. The second conjunct applies to every rational source F " +
                "and every positive natural m, and supplies an integer equal to its ordinary coefficient. " +
                "The zero coefficient is already zero by IsSource. No integral ambient object, cutoff, " +
                "sign assumption or rescaling is used. The result also proves the normalized companion, " +
                "log(exp(F))=F, exp(n^3 F)=exp(F)^(n^3) for every natural n including zero, uniqueness of " +
                "every normalized companion B, and reconstruction of exp(F) from eCoeff(exp(F),r)/r! " +
                "in every degree r>=0. Formal exp/log inverses and the exponential power identity are " +
                "reused from their actual owners. Thus the primary ordinary definition and the companion " +
                "EGF/log convention describe the same unique rational object. The illustrative source " +
                "programs and the separate displayed recurrence supply no arithmetic premise here. " +
                "The integrality induction uses the actual strict integral prefix. Coefficient agreement " +
                "transfers every lower cubic equation to that prefix. At primes not dividing the index, " +
                "MarkedAssemblyCoefficients with three independent marker coordinates proves local " +
                "integrality of the residual by the full Sylow order, with the original ambient marker " +
                "set retained after root removal. Division by the cube is a local unit. At primes dividing " +
                "the index, local_automatic_bound applies to the cube and the strict local prefix. " +
                "The factorial valuation estimate gives a nonnegative coefficient valuation, including " +
                "the prime two. A nonintegral rational coefficient would have a prime dividing its reduced " +
                "denominator, contradicting these two exhaustive cases. The degree-one identity forces " +
                "coefficient one directly, and strong induction covers every subsequent index.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula statement, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hannaa300595-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(statement)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Series() => Call("PowerSeries", Q());
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        Seq(a, Sp, Le, Sp, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Iffn(Formula a, Formula b) =>
        Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a) => new Formula.Power(Par(a), D(3));
    private static Formula Cast(Formula a) => Par(Seq(a, Colon, Sp, Q()));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Unique(string name, Formula type, System.Func<Formula, Formula> property) =>
        Ex(name, type, And(property(V(name)),
            All("G", type, Imp(property(V("G")), Eqn(V("G"), V(name))))));
    private static Formula E(Formula f) => Call("expSeries", D(1), f);
    private static Formula Coeff(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula SourceBody(Formula f) =>
        And(Eqn(Call("constantCoeff", f), D(0)), All("n", N(),
            Imp(Leq(D(1), V("n")), Eqn(
                Coeff(V("n"), Call("expSeries", Pow(Cast(V("n"))), f)),
                Mul(Pow(Cast(V("n"))), Coeff(Sub(V("n"), D(1)),
                    Call("expSeries", Pow(Cast(V("n"))), f)))))));
    private static Formula CompanionBody(Formula b) =>
        And(Eqn(Call("constantCoeff", b), D(1)), All("n", N(),
            Imp(Leq(D(1), V("n")), Eqn(
                Coeff(V("n"), new Formula.Power(Par(b), Pow(V("n")))),
                Mul(Pow(Cast(V("n"))), Coeff(Sub(V("n"), D(1)),
                    new Formula.Power(Par(b), Pow(V("n")))))))));
    private static Formula ResultBody() => And(
        Unique("F", Series(), f => Call("IsSource", f)),
        All("F", Series(), Imp(Call("IsSource", V("F")),
            And(All("m", N(), Imp(Leq(D(1), V("m")),
                    Ex("z", Z(), Eqn(Coeff(V("m"), V("F")), Cast(V("z")))))),
                And(Call("IsCompanion", E(V("F"))),
                    And(Eqn(Call("logOf", E(V("F"))), V("F")),
                        And(All("n", N(), Eqn(Call("expSeries", Pow(Cast(V("n"))), V("F")),
                                new Formula.Power(Par(E(V("F"))), Pow(V("n"))))),
                            And(All("B", Series(), Imp(Call("IsCompanion", V("B")), Eqn(V("B"), E(V("F"))))),
                                EgfBody(V("F"))))))))));
    private static Formula EgfBody(Formula f) =>
        Eqn(Call("mk", Par(Seq(V("fun"), Sp, V("r"), Colon, Sp, N(), Sp, Mapsto, Sp,
            new Formula.Fraction(Call("eCoeff", E(f), V("r")), Cast(Call("factorial", V("r"))))))), E(f));
}
