using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaLogarithmicAffineClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral logarithmic series remain integral under every positive affine extraction.",
        H("Hanna's Arithmetic-Subsequence Closure"),
        Blocks(
            Paragraph(Text("Let K be any characteristic-zero field and L any sequence "
                + "from the natural numbers to K. All indices and ordinary degrees start "
                + "at zero. Write egf(L)=sum_n L(n)X^n/n! and "
                + "logarithmicTransform(L)=egf(L).subst(log(K)), where log(K) is the "
                + "formal log(1+X). IntegralSeries means that every ordinary coefficient "
                + "belongs to the canonical image of Z in K. No convergence, sign, "
                + "support, degree bound or normalization of L(0) is imposed.")),
            Describe.Lean(
                DescribeId.Create("hanna-logarithmic-affine-result"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Algebraic/HannaLogarithmicAffineClosure.result"),
                H("The full A167540 implication"),
                StatementSource.FromAuthor(Disp(Seq(
                    Bound("K", V("Type")), Sp,
                    OpenBracket, Call("Field", V("K")), CloseBracket, Sp,
                    OpenBracket, Call("CharZero", V("K")), CloseBracket, Sp,
                    Bound("L", Seq(Nat(), Sp, To, Sp, V("K"))), Sp,
                    Bound("m", Nat()), Sp, Bound("b", Nat()), Sp,
                    Implication(Call("IntegralSeries", Call("logarithmicTransform", V("L"))),
                        Implication(Seq(D(0), Sp, Lt, Sp, V("m")),
                            Call("IntegralSeries", Call("logarithmicTransform",
                                Lambda("n", Nat(), Call("L",
                                    Add(Mul(V("m"), V("n")), V("b"))))))))))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2009affineclosure")),
                Blocks(
                    Paragraph(Text("If the whole input transform is integral, the whole "
                        + "transform of n -> L(m*n+b) is integral for every positive m "
                        + "and every nonnegative b. Positive naturals represent exactly "
                        + "the source's positive integers, and b ranges over all naturals.")),
                    Paragraph(Text("Put q_k(N)=k!S(N,k). Original exp/log inversion and "
                        + "reconstruction supply an integer sequence a with "
                        + "L(N)=sum_(k<=N) a(k)q_k(N); integral values of L are derived "
                        + "from the premise. Factorial-weighted inclusion-exclusion "
                        + "and exp(Q)^t=rescale(t,exp(Q)) identify the affine column's "
                        + "rational EGF as sum_(j<=k) (-1)^(k-j) binomial(k,j) "
                        + "j^b exp(Q)^(j^m). The original subst_exp_log identity then "
                        + "turns its logarithmic transform into the integer polynomial "
                        + "P_(k,m,b)=sum_(j<=k) (-1)^(k-j) binomial(k,j) "
                        + "j^b (1+X)^(j^m). All zero bases and exponents retain 0^0=1.")),
                    Paragraph(Text("At an arbitrary degree r, log(K)^n contributes only "
                        + "for n<=r. The original finite-window identity expands "
                        + "T(a,m*n+b) using k<=m*r+b, since m*n+b<=m*r+b. Both sums "
                        + "are therefore finite, and the coefficient equals the integer "
                        + "sum sum_(k<=m*r+b) a(k) coeff(r,P_(k,m,b)). This is a bound "
                        + "for each arbitrary degree, with no bound on the whole series. "
                        + "The canonical rational-map compatibility transports this "
                        + "identity into K. At degree zero the output constant is L(b); "
                        + "when b=0 it retains arbitrary L(0). Signed and infinitely "
                        + "supported coordinates a are included.")),
                    Paragraph(Text("The original finite-sum suppliers coeff_transform "
                        + "and T_window are applied directly."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a167540-logarithmic-affine-closure"),
                    ResolutionKind.Proved)))));

    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Par(Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula a, Formula b) =>
        Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula V(string name) => F.Id(name);
}
