using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class GraftLocalBehaviorLabelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical local records classify every future Fibonacci reading at prime-power precision.",
        H("Local Fibonacci Behavior Records"),
        Blocks(
            Node("reducePair", "Reduction of a pair",
                "For all natural p,H,i and x in (Z/(p^H)Z)^2, reducePair(p,H,i,x) is obtained by applying ZMod.cast into Z/(p^i)Z to each coordinate. For i<=H this is the product of the natural ring homomorphisms.", DescribeRole.Definition),
            Node("topHit", "The maximal zero-hit layer",
                "For all natural p,H,m and x in (Z/(p^H)Z)^2, topHit(p,H,m,x) is the greatest i<=m for which there exists a natural k with the first coordinate of S^k(reducePair(p,H,i,x)) equal to zero. The default value is zero.", DescribeRole.Definition),
            Node("direction", "The unit orbit",
                "For all natural p,H,i and x in (Z/(p^H)Z)^2, direction(p,H,i,x) is the orbit of reducePair(p,H,i,x) under simultaneous multiplication of both coordinates by a unit of Z/(p^i)Z. Its interpretation as a primitive projective direction requires a unit coordinate.", DescribeRole.Definition),
            Describe.Lean(
            DescribeId.Create("graft-primitive-hit-phase"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.primitive_hit_phase"),
            H("The zero phase of a primitive state"),
            StatementSource.FromAuthor(PhaseFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let p be any prime and m be any natural number. The step S(a,b)=(b,a+b) acts on pairs over Z/(p^m)Z. A pair is primitive when at least one coordinate is a unit. Let r be the least positive index with p^m dividing the Fibonacci number F(r), with F(0)=0 and F(1)=1.")),
                Paragraph(Text("If the first coordinate of S^t(x) is zero, then the first coordinate of S^k(x) is zero exactly when k and t have the same residue modulo r. Both t and k are arbitrary natural numbers, including zero. There is no restriction to odd primes and no assumption that the zero rank grows at every precision.")),
                Paragraph(Text("The coordinates of a primitive pair remain coprime under the step. At a zero hit, the second coordinate is consequently a unit. Forward from this hit, the first coordinate is F(d) times that unit, so its zeros are precisely the multiples of r. A finite common return period transfers this criterion to times before the chosen hit."))),
            DescribeRole.Theorem),
            Node("primitive_no_hit_profile", "The low divisibility profile",
                "Let p be any prime, H and m be natural numbers with m<=H, and let x and y be pairs over Z/(p^H)Z, each with at least one unit coordinate. Suppose neither reduced pair at precision m has a zero first coordinate at any natural time. The following are equivalent: for every natural k and every i<=m, the first coordinates of S^k(reducePair(p,H,i,x)) and S^k(reducePair(p,H,i,y)) vanish simultaneously; there exists a natural j<m such that both maximal hit layers are j and their unit orbits at layer j are equal. Layer zero has the unique residue pair modulo one. The times include zero.",
                DescribeRole.Theorem,
                "Simultaneous zero readings at the maximal positive hit layer put both primitive states on the same kernel line. Their unit second coordinates give a common unit multiple after that time, and the common finite return period transports this relation to their initial states. Reduction transports the unit relation to every lower layer. Neither state hits any higher layer, so the maximal layer and its orbit determine every divisibility reading."),
            Node("content", "Common saturated depth",
                "For all natural p,h and x in (Z/(p^h)Z)^2, content(p,h,x) is the minimum of depth(p,h,val(x.1)) and depth(p,h,val(x.2)), using the integer casts of the natural representatives and the existing saturated-depth function.", DescribeRole.Definition),
            Node("scaledPair", "Normalized residue coordinates",
                "For all natural p,h,s and x in (Z/(p^h)Z)^2, scaledPair(p,h,s,x) applies eta(p,h,s,-) to each integer representative and retains the residue component, discarding the tag and any depth field. The resulting pair is over Z/(p^(h-s))Z. When s is at most each coordinate depth, both eta values use their high branch and retain the quotients by p^s.", DescribeRole.Definition),
            Node("LocalLabel", "Three record types",
                "For all natural p,h,e, a LocalLabel(p,h,e) is one of three disjoint records. High retains a pair over Z/(p^h)Z. NoHit retains natural s,j and an optional unit-orbit set over (Z/(p^j)Z)^2. Hit retains natural s,t, a residue A over Z/(p^h)Z and a residue U over Z/(p^ell)Z, where ell=h-s-c, c is the p-adic valuation of F(zeroRank(p^(e-s))), and subtraction is saturated natural subtraction.", DescribeRole.Definition),
            Node("localLabel", "Canonical local records",
                "For all natural p,h,e and x in (Z/(p^h)Z)^2, put s=content(p,h,x). If e<=s, the record is High(x), including the zero pair. Otherwise set u=scaledPair(p,h,s,x) and m=e-s. If the reduction of u to precision m has a zero first coordinate at some natural time, choose its least such time t and return Hit(s,t,(S^t(x)).1,U), where U is the second coordinate of scaledPair(p,h,s,S^t(x)) reduced to the prescribed exponent ell. If there is no hit, put j=topHit(p,h-s,m,u) and return NoHit(s,j,None) for j=0, or NoHit(s,j,Some(direction(p,h-s,j,u))) otherwise. The local classification below identifies equality of these records with equality of all future psi readings.", DescribeRole.Definition),
            Node("result", "Complete local behavior classification",
                "For every natural prime p, every natural h>=1, every natural e<=h, and all x,y in (Z/(p^h)Z)^2, the following are equivalent: for every natural k>=0, psi(p,h,e,val(fst(S^k(x)))) equals psi(p,h,e,val(fst(S^k(y)))); localLabel(p,h,e,x) equals localLabel(p,h,e,y). Here S(a,b)=(b,a+b), and psi retains the saturated depth when it is below e and the full residue modulo p^h otherwise. The statement includes e=0, p=2, the zero pair, and the unique scalar residue at precision zero.",
                DescribeRole.Theorem,
                "The readings at times zero and one recover the common saturated depth of the pair. In the High case both coordinates are retained, so equality of all readings is exactly equality of the pair. For a low pair, division by its common power of p gives primitive coordinates; reduction of those coordinates to layer i vanishes exactly when the original coordinate depth is at least s+i.",
                "For NoHit records, the maximal hit layer and its unit orbit determine every lower-layer zero test. No higher-layer test occurs. These tests determine each depth below e, and hence every psi reading. Conversely the complete depth profile recovers that maximal layer and its direction, with the single empty-direction record at layer zero.",
                "For Hit records, simultaneous layer-e-s hits recover the least nonnegative phase t. The primitive zero-phase theorem also determines all lower-layer depth tests. At times t and t+r, where r=zeroRank(p^(e-s)), the readings retain complete residues. The first recovers A, and cancellation of F(r) from the second recovers B/p^s modulo p^(h-s-v_p(F(r))). The full valuation is used even when zero-rank lifting is stationary. Equality of these first two samples gives equality at every coarse-clock time by the sampling quotient theorem; t<r identifies precisely all nonnegative hit times. The remaining times are determined by the lower-layer depth tests.",
                "Prime-power Fibonacci zero ranks are treated in Wall (1960), Robinson (1963), and Bragman and Rowland, arXiv:2202.00704v2. The classification uses those zero-rank properties together with finite orbit and sampling identities, without an assumption that the rank multiplies by p at each lift."))));

    private static DocumentBlock Node(string name, string title, string statement,
        DescribeRole role, params string[] proof) => Describe.Lean(
            DescribeId.Create("graft-local-" + (name == "LocalLabel" ? "label-type"
                : name.Replace('_', '-').ToLowerInvariant())),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks([Paragraph(Text(statement)), .. proof.Select(text => Paragraph(Text(text)))]), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(Formula a, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, a, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula PhaseFormula()
    {
        Formula p = F.Id("p"), m = F.Id("m"), x = F.Id("x"), t = F.Id("t"), k = F.Id("k");
        Formula n = Pow(p, m), r = Call("zeroRank", n);
        Formula first(Formula i) => Call("fst", Call("iterate", F.Id("S"), i, x));
        Formula primitive = Seq(Call("IsUnit", Call("fst", x)), Sp, Lor, Sp,
            Call("IsUnit", Call("snd", x)));
        Formula conclusion = Seq(Par(Equal(first(k), D(0))), Sp, Iff, Sp,
            Par(Equal(Call("mod", k, r), Call("mod", t, r))));
        Formula hit = All(t, N, All(k, N,
            Seq(Equal(first(t), D(0)), Sp, Implies, Sp, Par(conclusion))));
        Formula body = All(x, Pow(Call("ZMod", n), D(2)),
            Seq(Par(primitive), Sp, Implies, Sp, hit));
        return Disp(All(p, N, All(m, N,
            Seq(Call("Prime", p), Sp, Implies, Sp, body))));
    }
}
