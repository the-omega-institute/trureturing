using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaLogarithmicPowerClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2009logarithmicclosure");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's integer-series closure holds for every positive pointwise power.",
        H("Universal Logarithmic Integer-Series Power Closure"),
        Blocks(
            Paragraph(Text("Let K be any characteristic-zero field. Every natural sequence "
                + "index and ordinary degree begins at zero. The arbitrary sequence L takes "
                + "values in K. The canonical integer and rational embeddings are used; "
                + "cast(K,z) denotes the integer embedding. No convergence, positivity, "
                + "support restriction or normalization of L(0) is assumed. The series "
                + "log(K) is the formal log(1+X), with constant zero and degree-r coefficient "
                + "(-1)^(r+1)/r for r positive. Division in K is field division. The symbols "
                + "mk, coeff, subst and factorial denote coefficient assembly, ordinary "
                + "coefficient extraction, formal substitution and natural factorial. "
                + "Substitution is legitimate because log(K) has constant coefficient zero.")),
            Node("egf", "The exponential generating series",
                Disp(Seq(Context(), Sp, Equality(Call("egf", L()),
                    Call("mk", Lambda("n", Nat(),
                        new Formula.Fraction(Call("L", V("n")),
                            Call("castNat", K(), Call("factorial", V("n"))))))))),
                "Assemble every exponential coefficient L(n)/n!, including n=0. "
                    + "Characteristic zero makes every factorial denominator nonzero.",
                DescribeRole.Definition),
            Node("logarithmicTransform", "Logarithmic coordinates",
                Disp(Seq(Context(), Sp, Equality(Call("logarithmicTransform", L()),
                    Call("subst", Call("egf", L()), Call("log", K()))))),
                "Substitute the formal logarithm into the exponential generating series.",
                DescribeRole.Definition),
            Node("IntegralSeries", "Integral ordinary coefficients",
                Disp(Seq(FieldContext(), Sp, Bound("f", Call("PowerSeries", K())), Sp,
                    Equality(Call("IntegralSeries", V("f")),
                        Seq(Bound("n", Nat()), Sp, Exists, Sp, V("z"), Colon, Sp, Int(), Comma, Sp,
                            Equality(Call("coeff", V("n"), V("f")),
                                Call("cast", K(), V("z"))))))),
                "Every ordinary coefficient lies in the canonical image of the integers. "
                    + "The integer can vary with the degree; no sign or size bound is imposed.",
                DescribeRole.Definition),
            Node("result", "Hanna's full closure conjecture",
                Disp(Seq(Context(), Sp, Bound("m", Nat()), Sp,
                    Implication(Call("IntegralSeries", Call("logarithmicTransform", L())),
                        Implication(Seq(D(0), Sp, Lt, Sp, V("m")),
                            Call("IntegralSeries", Call("logarithmicTransform",
                                Lambda("n", Nat(), new Formula.Power(Call("L", V("n")), V("m"))))))))),
                "Hanna's same conjecture on A167138, A167139 and A167141 is one "
                    + "question. Integral logarithmic coefficients a reconstruct L(n) as "
                    + "the embedded integer sum T(a,n)=sum_(i<=n) a(i)i!S(n,i), by "
                    + "composing with exp(t)-1. Thus integral values of L are derived "
                    + "from the premise. Put q_i(n)=i!S(n,i). Its product with q_j has "
                    + "logarithmic generating series P_ij=sum_(s<=i) (-1)^(i-s) "
                    + "binomial(i,s)((1+X)^s-1)^j, an integer polynomial. This finite "
                    + "column identity is the factorial-scaled formal form of "
                    + "Boyadzhiev-Frontczak Corollary 3.1. At degree r, only n,i,j at "
                    + "most r contribute: q_i(n)=0 when i>n and log(K)^n has no "
                    + "coefficient below n. The product coefficient is therefore the "
                    + "finite integer sum of a(i)b(j) times coeff(r,P_ij). Binary "
                    + "closure and induction prove every positive power, then the "
                    + "canonical rational map transports the identity into the original "
                    + "K. In degree zero the conclusion retains L(0)^m. The natural "
                    + "positive exponent represents exactly the positive integers.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a167138-logarithmic-power-closure"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("hanna-logarithmic-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Context() => Seq(FieldContext(), Sp,
        Bound("L", Seq(Nat(), Sp, To, Sp, K())));
    private static Formula FieldContext() => Seq(Bound("K", V("Type")), Sp,
        OpenBracket, Call("Field", K()), CloseBracket, Sp,
        OpenBracket, Call("CharZero", K()), CloseBracket, Comma);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Par(Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Equality(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Implication(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Int() => Seq(Mathbb, Grp(V("Z")));
    private static Formula V(string name) => F.Id(name);
    private static Formula K() => V("K");
    private static Formula L() => V("L");
}
