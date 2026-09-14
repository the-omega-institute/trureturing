using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class JacobsthalTailPeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/JacobsthalTailPeriod.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Jacobsthal recurrence has an exact divisibility criterion for a shift valid "
            + "at every index in a specified tail. At an even modulus it has no "
            + "positive period starting at index zero.",
        H("Jacobsthal Tail Periods"),
        Blocks(
            Describe.Lean(DescribeId.Create("jacobsthal-original-recurrence"),
                DeclarationHandle.Create(Prefix + "jacobsthal"),
                H("The original second-order sequence"),
                StatementSource.FromAuthor(Recurrence()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("jacobsthal maps natural indices to integers. Its "
                    + "two initial values are zero and one. The coefficient of the "
                    + "two-steps-earlier term is two. This is the Jacobsthal sequence "
                    + "used in Benfield and Lippard, Fixed Points of K-Fibonacci "
                    + "Sequences, Conjecture 6.3, and OEIS A001045."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jacobsthal-period-from-definition"),
                DeclarationHandle.Create(Prefix + "PeriodFrom"),
                H("A period on an actual tail"),
                StatementSource.FromAuthor(PeriodDefinition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All four indices m,N,t,n are natural numbers. "
                    + "The divisibility is in the integers. PeriodFrom does not itself "
                    + "require a positive shift, so t=0 is included. A least eventual "
                    + "period separately requires t>0 and existentially quantifies N."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jacobsthal-defining-relation"),
                DeclarationHandle.Create(Prefix + "defining_relation"),
                H("Source recurrence and initial values"),
                StatementSource.FromAuthor(Recurrence()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The conjunction states both initial values "
                    + "and the recurrence at every natural n. The sequence is not "
                    + "defined from an order formula or from its proposed fixed points."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jacobsthal-complete-tail-criterion"),
                DeclarationHandle.Create(Prefix + "period_from_iff"),
                H("Every tail start and every shift"),
                StatementSource.FromAuthor(TailCriterion()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For m>2, a shift t works from N if and only if "
                        + "t is even and m divides 2^N times jacobsthal(t). The statement "
                        + "quantifies every m,N,t and includes the zero shift.")),
                    Paragraph(Text("The identity J(n+1)=2*J(n)+(-1)^n gives "
                        + "D(n+1)-2*D(n)=(-1)^n*((-1)^t-1) for the actual difference "
                        + "D(n)=J(n+t)-J(n). Two consecutive divisibilities force t "
                        + "even when m>2. The integer Binet identity then yields "
                        + "D(n)=2^n*J(t), which proves both directions. No division by "
                        + "three is performed in a residue ring."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jacobsthal-no-even-pure-period"),
                DeclarationHandle.Create(Prefix + "no_positive_pure_period_even"),
                H("The initial transient cannot be omitted"),
                StatementSource.FromAuthor(NoPurePeriod()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every even natural m and every t>0, "
                    + "PeriodFrom(m,0,t) is false. Indeed it would force m to divide "
                    + "J(t), but every positive-index Jacobsthal number is odd. The "
                    + "statement includes m=2; it also uses the integer divisibility "
                    + "interpretation when m=0."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula All(string v, Formula body) =>
        Seq(Forall, Sp, V(v), Sp, InMacro, Sp, NatType(), Comma, Sp, body);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) { parts.Add(Comma); parts.Add(Sp); }
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Sub(Formula a, Formula b) => Call("sub", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("mul", a, b);
    private static Formula J(Formula n) => Call("jacobsthal", n);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Period(Formula n) => Call("PeriodFrom", V("m"), n, V("t"));
    private static Formula Divides(Formula x) => Call("Divides", Call("Nat.cast", V("m")), x);
    private static Formula Recurrence() => Disp(Call("And",
        Eqn(J(V("0")), V("0")), Eqn(J(V("1")), V("1")),
        All("n", Eqn(J(Add(V("n"), V("2"))),
            Add(J(Add(V("n"), V("1"))), Mul(V("2"), J(V("n"))))))));
    private static Formula PeriodDefinition() => Disp(All("m", All("N", All("t",
        Call("Iff", Period(V("N")), All("n", Call("Implies", Call("Le", V("N"), V("n")),
            Divides(Sub(J(Add(V("n"), V("t"))), J(V("n")))))))))));
    private static Formula TailCriterion() => Disp(All("m", All("N", All("t",
        Call("Implies", Call("Lt", V("2"), V("m")),
            Call("Iff", Period(V("N")), Call("And", Call("Even", V("t")),
                Divides(Mul(new Formula.Power(V("2"), V("N")), J(V("t")))))))))));
    private static Formula NoPurePeriod() => Disp(All("m", All("t",
        Call("Implies", Call("And", Call("Even", V("m")), Call("Lt", V("0"), V("t"))),
            Call("Not", Period(V("0")))))));
}
