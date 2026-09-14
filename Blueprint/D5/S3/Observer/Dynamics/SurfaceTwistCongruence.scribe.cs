using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class SurfaceTwistCongruenceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Dynamics/SurfaceTwistCongruence.finite_characteristic_twist_detector";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit fully invariant finite quotient detects exactly the multiples of a prescribed separating-twist power in every genus at least two.",
        H("Finite nonabelian observation of a separating twist"),
        Blocks(
            Paragraph(Text("For e in N, G_e is the actual presented group on 4+2e generators "
                + "with the ordered surface relator, of genus e+2. The first handle has generators "
                + "a,b and boundary h=aba^-1b^-1. The endomorphism tau conjugates a,b by h and "
                + "fixes every other generator. Its inverse is constructed in the proof.")),
            Paragraph(Text("D_m is the dihedral group with rotation order 4m and total order 8m. "
                + "Let Rep be Hom(G_e,D_m). The map E sends x to the function rho -> rho(x). "
                + "Q is its actual image subgroup and q is E with codomain restricted to that image. "
                + "P_n is repeated composition of tau, with P_0 the identity and P_(n+1)=tau composed with P_n.")),
            Describe.Lean(
                DescribeId.Create("finite-characteristic-twist-detector"),
                DeclarationHandle.Create(Declaration),
                H("A finite fully invariant quotient with exact outer period m"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("OrbitReturn(q,P_n,w) means that q(P_n(w)) and q(w) are conjugate in Q, where w=a d^-1. FullInvariantKernel(q) means that for every group endomorphism f "
                        + "of G_e and every x, q(x)=1 implies q(f(x))=1. Inner(q,P_n) means that "
                        + "there exists one z in Q such that q(P_n(x))=z q(x) z^-1 for every x. "
                        + "It is the literal innerness condition for the induced quotient automorphism, "
                        + "not separate conjugacy tests for separate generators.")),
                    Paragraph(Text("A homomorphism is determined by its finitely many generator images. "
                        + "Hence Rep, the ambient product and Q are finite for m>0. The kernel is "
                        + "fully invariant because rho composed with any endomorphism is another member "
                        + "of Rep. The selected dihedral representation alone is never assumed to have "
                        + "characteristic kernel.")),
                    Paragraph(Text("Every dihedral commutator is an even rotation. Its m-th power is "
                        + "central, so every representation is fixed by tau^n whenever m divides n. "
                        + "For the converse, map (a,b,c,d) to (s,r,r,s) and the extra generators to one. "
                        + "The surface relation holds. Under tau^n the first image is sr^(4n), "
                        + "while the fourth stays s. Since a and d initially have equal images, "
                        + "one common conjugator can exist only when 4m divides 4n. "
                        + "The mixed word w=a d^-1 has image one, while its nth image is r^(-4n). "
                        + "Thus the same characteristic quotient detects its conjugacy-class orbit with exact period m.")),
                    Paragraph(Text("All abelian observations kill the boundary commutator and are "
                        + "unchanged by tau. The finite nonabelian detector therefore retains information "
                        + "lost by every abelian target. Klukowski, arXiv:2411.06867v2, Definition 3, "
                        + "Corollary 7 and Conjecture 13 provide the congruence-subgroup context. "
                        + "The qualitative cyclic consequence is known. No solution of the full "
                        + "curve-orbit conjecture, topological surface identification, or three-manifold "
                        + "rigidity theorem is asserted here."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula e = F.Id("e");
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula q = F.Id("q");
        Formula tau = F.Id("tau");
        Formula pn = Call("P", n);
        Formula x = F.Id("x");
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, e, Comma, Sp, m, Colon, Sp, Call("Nat"), Comma, Sp,
                D(0), Sp, Lt, Sp, m, Sp, Rightarrow),
            Seq(Call("Finite", F.Id("Q")), Sp, Land, Sp,
                Call("Surjective", q), Sp, Land, Sp, Call("FullInvariantKernel", q), Sp, Land),
            Seq(Call("Bijective", tau), Sp, Land),
            Seq(Open, Forall, Sp, n, Colon, Sp, Call("Nat"), Comma, Sp,
                Call("Inner", q, pn), Sp, Call("iff"), Sp, Call("Divides", m, n), Close, Sp, Land),
            Seq(Open, Forall, Sp, n, Colon, Sp, Call("Nat"), Comma, Sp,
                Call("OrbitReturn", q, pn, F.Id("w")), Sp, Call("iff"), Sp,
                Call("Divides", m, n), Close, Sp, Land),
            Seq(Open, Forall, Sp, n, Colon, Sp, Call("Nat"), Comma, Sp,
                Call("Divides", m, n), Sp, Rightarrow, Sp,
                Forall, Sp, x, Colon, Sp, F.Id("G"), Comma, Sp,
                Call("apply", q, Call("apply", pn, x)), Sp, Eq, Sp,
                Call("apply", q, x), Close, Sp, Land),
            Seq(Open, Forall, Sp, F.Id("A"), Comma, Sp, Call("CommGroup", F.Id("A")), Sp,
                Rightarrow, Sp, Forall, Sp, F.Id("f"), Colon, Sp,
                Call("Hom", F.Id("G"), F.Id("A")), Comma, Sp,
                Call("comp", F.Id("f"), tau), Sp, Eq, Sp, F.Id("f"), Close, Dot)
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[i]);
        }
        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
