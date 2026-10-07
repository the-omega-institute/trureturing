using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class HeterogeneousHammingSeparationDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        Seq(Par(premise), Sp, Implies, Sp, Par(conclusion));
    private static Formula And(params Formula[] terms) =>
        Seq([.. terms.SelectMany((term, i) => i == 0 ? new[] { Par(term) }
            : new[] { Sp, Land, Sp, Par(term) })]);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classification disagreement for independent heterogeneous whole-window laws has a sharp "
            + "constant strictly smaller than squared teacher separation.",
        H("Sharp Heterogeneous Hamming Separation"),
        Blocks(
            Paragraph(Text("Use the existing five-window alphabet 000,100,010,101,001 in "
                + "low-to-high bit order. Laws(n), Admissible(rho,mu), Roles(n), classValue, "
                + "and gamma are the heterogeneous teacher objects. All n windows are independent "
                + "and each of the five actual masses at every position is at least rho and sums "
                + "to one. Within one window, the joint endpoint mass is the mass of 101.")),
            Paragraph(Text("hamming(mu,t,u) is the product expectation of the indicator that "
                + "classValue(t,w) differs from classValue(u,w). The sharp constant eta(rho) is "
                + "4 rho squared times (1-2 rho) times (1+3 rho). The law tilted(rho) has masses "
                + "(rho,rho,rho,rho,1-4 rho). attainingLaw(n,rho) uses tilted at position zero "
                + "and the existing extremal law ((1-3 rho)/2,rho,(1-3 rho)/2,rho,rho) elsewhere. "
                + "The notation triple(n,p,q,r) denotes the increasing triple with those "
                + "zero-based coordinates in Fin(n).")),
            Describe.Lean(DescribeId.Create("heterogeneous-hamming-sharp-separation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/HeterogeneousHammingSeparation.result"),
                H("Uniform lower bound, simultaneous equality, and strict comparison"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For different first position pairs, first-gate disagreement "
                        + "forces classification disagreement. Its probability is at least gamma. "
                        + "For equal first pairs (p,q) and distinct last positions r,s, the exact "
                        + "Hamming expectation is (H(q)-H(p) mu(q,101)) times "
                        + "(L(r)+L(s)-2 L(r)L(s)). Here H(i)=mu(i,101)+mu(i,001) and "
                        + "L(i)=mu(i,101)+mu(i,100). Independence is used only between different "
                        + "positions; the middle window retains its actual joint endpoint mass.")),
                    Paragraph(Text("The first factor equals mu(q,001)+mu(q,101)(1-H(p)) "
                        + "and is at least rho(1+3 rho). The second is at least 4 rho(1-2 rho). "
                        + "Both equalities hold in the same product law: H(0)=1-3 rho, "
                        + "mu(1,001)=mu(1,101)=rho, and L(2)=L(3)=2 rho. "
                        + "The pairs (0,1,2) and (0,1,3) therefore attain eta. "
                        + "Changing any later position to another admissible law preserves equality. "
                        + "The universal lower bound and this attained value determine the "
                        + "infimum of the minimum over distinct role triples.")),
                    Paragraph(Text("For 0<rho<=1/8, eta/gamma=(1+3 rho)/2 is strictly less "
                        + "than one. The theorem is about the deterministic original teacher "
                        + "classes under the actual input law; it asserts no label-channel or "
                        + "training-risk guarantee."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var n = V("n");
        var rho = V("rho");
        var mu = V("mu");
        var v = V("v");
        var w = V("w");
        var i = V("i");
        var laws = Call("Laws", n);
        var roles = Call("Roles", n);
        var eta = Call("eta", rho);
        var law = Call("attainingLaw", n, rho);
        var t = Call("triple", n, D(0), D(1), D(2));
        var u = Call("triple", n, D(0), D(1), D(3));
        var lower = All(mu, laws, Imp(Call("Admissible", rho, mu),
            All(v, roles, All(w, roles, Imp(Seq(v, Sp, Neq, Sp, w),
                Seq(eta, Sp, Le, Sp, Call("hamming", mu, v, w)))))));
        var firstFour = All(i, Call("Fin", n),
            Imp(Seq(Call("val", i), Sp, Lt, Sp, D(4)),
                Equal(Call("apply", mu, i), Call("apply", law, i))));
        var attained = And(Seq(t, Sp, Neq, Sp, u), Call("Admissible", rho, law),
            Equal(Call("hamming", law, t, u), eta),
            All(mu, laws, Imp(Call("Admissible", rho, mu),
                Imp(firstFour, Equal(Call("hamming", mu, t, u), eta)))));
        var premises = And(Seq(D(4), Sp, Le, Sp, n), Seq(D(0), Sp, Lt, Sp, rho),
            Seq(rho, Sp, Le, Sp, new Formula.Fraction(D(1), D(8))));
        return All(n, Seq(Mathbb, Grp(V("N"))),
            All(rho, Seq(Mathbb, Grp(V("R"))),
                Imp(premises, And(lower, attained,
                    Seq(eta, Sp, Lt, Sp, Call("gamma", rho))))));
    }
}
