using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class SurfaceDerivedOrbitDetectorDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Dynamics/SurfaceDerivedOrbitDetector.finite_second_derived_orbit_detector";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite fully invariant matrix quotient resolves a second-derived surface-word orbit on every prescribed finite time window.",
        H("Finite observation beyond the metabelian quotient"),
        Blocks(
            Paragraph(Text("Fix e in N and m>0. G is the previous actual surface presentation "
                + "of genus e+3, and tau is the same first-handle twist. Let "
                + "u=[[a1,a2],[b1,b3]]. Let F be the unit group of seven-by-seven matrices "
                + "over ZMod(m). The map E evaluates each x in every homomorphism G to F. "
                + "Q is the actual image subgroup and q is its surjective image restriction.")),
            Describe.Lean(
                DescribeId.Create("finite-second-derived-orbit-detector"),
                DeclarationHandle.Create(Declaration),
                H("A characteristic quotient with residue-sensitive word orbits"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("FullKernel(q) means that q(x)=1 implies q(f(x))=1 "
                        + "for every endomorphism f of G and every x. C(n,p) means there is "
                        + "one z in Q with q(tau^n u)=z q(tau^p u) z^-1. "
                        + "Metabelian(F) is the explicit law [[a,b],[c,d]]=1 for all four elements. "
                        + "Blind(u) quantifies over all such groups F, homomorphisms f:G to F, "
                        + "and natural n, and states f(tau^n u)=1.")),
                    Paragraph(Text("The witness uses A=I+E12+E23+E34+E56 and "
                        + "B=I+E45+E67 in one-based matrix coordinates. Writing H=[A,B], "
                        + "N=H-I, we have N^3=0. Define P(t,s)=I+tN+sN^2. "
                        + "Its inverse is P(-t,t^2-s), and its multiplication law is "
                        + "P(t,s)P(v,w)=P(t+v,s+w+tv). All formulas are polynomial and "
                        + "valid over any commutative ring, including even characteristic.")),
                    Paragraph(Text("For each t, the first three handle images are "
                        + "(P(t,0)AP(t,0)^-1,P(t,0)BP(t,0)^-1), (A,I), (B,A). "
                        + "Remaining handle images are identity. The surface relation holds "
                        + "because P(t,0) commutes with H and [B,A]=H^-1. "
                        + "The exact matrix word calculation gives rho_t(tau^n u)=I-(n+t)E17. "
                        + "This evaluates genuine iterates of the original twist.")),
                    Paragraph(Text("To separate times n,p, evaluate a claimed conjugacy at "
                        + "rho_(-p). The time-p image is identity, whose conjugacy class is a singleton. "
                        + "The (1,7) entry forces n=p modulo m. For 0<=n,p<m, this is actual equality. "
                        + "Every metabelian representation instead sends this double commutator to identity.")),
                    Paragraph(Text("The source uses all matrix-group representations for the characteristic "
                        + "quotient. Consequently its all-time modular condition is necessary, "
                        + "and is not asserted sufficient. The smaller unitriangular-family exact-period "
                        + "theorem and class-six threshold are recorded only as ordinary mathematical "
                        + "proofs in the existing theory. The word u is not being identified with a "
                        + "simple closed curve. No general curve-orbit CSP result is claimed."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, F.Id("e"), Comma, Sp, F.Id("m"), Colon, Sp, Call("Nat"), Comma, Sp,
            D(0), Sp, Lt, Sp, F.Id("m"), Sp, Rightarrow),
        Seq(Call("Finite", F.Id("Q")), Sp, Land, Sp, Call("Surjective", F.Id("q")), Sp, Land),
        Seq(Call("FullKernel", F.Id("q")), Sp, Land),
        Seq(Open, Forall, Sp, F.Id("n"), Comma, Sp, F.Id("p"), Colon, Sp, Call("Nat"), Comma, Sp,
            Call("C", F.Id("n"), F.Id("p")), Sp, Rightarrow, Sp,
            Call("castZMod", F.Id("n"), F.Id("m")), Sp, Eq, Sp,
            Call("castZMod", F.Id("p"), F.Id("m")), Close, Sp, Land),
        Seq(Open, Forall, Sp, F.Id("n"), Comma, Sp, F.Id("p"), Colon, Sp, Call("Nat"), Comma, Sp,
            F.Id("n"), Sp, Lt, Sp, F.Id("m"), Sp, Land, Sp,
            F.Id("p"), Sp, Lt, Sp, F.Id("m"), Sp, Rightarrow, Sp,
            Call("C", F.Id("n"), F.Id("p")), Sp, Call("iff"), Sp,
            F.Id("n"), Sp, Eq, Sp, F.Id("p"), Close, Sp, Land),
        Seq(Call("Blind", F.Id("u")), Dot)
    ]));

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
