using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class EquicontinuousObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Map(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula All(string x, Formula t) => Seq(Forall, Sp, V(x), Colon, Sp, t, Comma);
    private static Formula Hyp(Formula a) => Seq(a, Sp, Rightarrow);
    private static Formula Inst(string c, Formula x) => Seq(OpenBracket, Call(c, x), CloseBracket);
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static Formula[] Extension(bool zero) => [
        Seq(All("X", V("Type")), Sp, Inst("UniformSpace", V("X")), Sp, Inst("TTwoSpace", V("X"))),
        Seq(All("Y", V("Type")), Sp, Inst("UniformSpace", V("Y")), Sp, Inst("CompactSpace", V("Y")),
            zero ? Seq(Inst("TTwoSpace", V("Y")), Sp, Inst("TotallyDisconnectedSpace", V("Y"))) : Seq()),
        Seq(All("p", Map(V("Y"), V("X"))), Sp, All("g", Map(V("Y"), V("Y"))), Sp, All("f", Map(V("X"), V("X")))),
        Hyp(Seq(Call("Continuous", V("p")), Sp, Land, Sp, Call("Semiconj", V("p"), V("g"), V("f")))),
        All("K", Call("Set", V("X"))), Hyp(Call("ForwardUniformEquicontinuity", V("f"), V("K"))) ];
    private static Formula[] Contraction() => [
        Seq(All("X", V("Type")), Sp, Inst("MetricSpace", V("X"))),
        Seq(All("f", Map(V("X"), V("X"))), Sp, All("q", Seq(Mathbb, Grp(V("R"))))),
        Hyp(Seq(D(0), Le, Sp, V("q"), Sp, Land, Sp, V("q"), Lt, D(1))),
        Hyp(Call("ContractionBound", V("f"), V("q"))) ];
    private static Formula[] Factor() => [
        Seq(All("X", V("Type")), Sp, Inst("UniformSpace", V("X")), Sp,
            All("B", V("Type")), Sp, Inst("MetricSpace", V("B"))),
        Seq(All("pi", Map(V("X"), V("B"))), Sp, All("f", Map(V("X"), V("X"))), Sp, All("d", Map(V("B"), V("B")))),
        Hyp(Seq(Call("UniformContinuous", V("pi")), Sp, Land, Sp, Call("Semiconj", V("pi"), V("f"), V("d")),
            Sp, Land, Sp, Call("PositivelyExpansive", V("d")))),
        All("K", Call("Set", V("X"))), Hyp(Call("ForwardUniformEquicontinuity", V("f"), V("K"))) ];
    private static DocumentBlock Doc(string id, string theorem, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + theorem),
            H(theorem.Replace('_', ' ')), StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An equicontinuous connected subset obstructs universally prescribed-source tracing; compact contractions illustrate the boundary.",
        H("Equicontinuity and Exact Fibres"), Blocks(
        Doc("orbit-lifting-clopen-image", "orbit_lifting_clopen_image", St([.. Extension(false),
            Hyp(Call("OrbitLifting", V("p"), V("g"), V("f"))), All("C", Call("Set", V("Y"))),
            Hyp(Call("IsClopen", V("C"))), Call("IsClopen", Call("RelativeImage", V("p"), V("C"), V("K")))]),
            "ForwardUniformEquicontinuity(f,K) means UniformEquicontinuous(n ↦ (x:K ↦ f^n(x.val))) with codomain X. "
            + "RelativeImage(p,C,K) is {x:K | x.val lies in p(C)}. C is compact, so its image is closed in Hausdorff X. "
            + "The two clopen cells C and its complement give one diagonal entourage. OL and equicontinuity give a neighborhood "
            + "of each point of the relative image whose lifts remain in C at time zero. No compactness or invariance of K is required here."),
        Doc("orbit-lifting-clopen-basis", "orbit_lifting_clopen_basis", St([.. Extension(true),
            Hyp(Call("Surjective", V("p"))), Hyp(Call("OrbitLifting", V("p"), V("g"), V("f"))),
            Hyp(Call("IsCompact", V("K"))), Call("ClopenBasis", V("K"))]),
            "For compact K, the clopen relative images form a neighborhood basis. Given x in an open U of K, "
            + "the image in X of K minus U is compact and closed. Separate its p-preimage from the entire closed fibre over x "
            + "by a clopen C in compact Hausdorff totally disconnected Y. Surjectivity puts x in the relative image, "
            + "and fibre avoidance puts that image inside U. This proves a basis of all clopens on K, hence zero-dimensionality."),
        Doc("connected-subset-not-source-relative", "connected_subset_not_source_relative", St([.. Extension(true),
            Hyp(Call("Surjective", V("p"))), Hyp(Call("IsCompact", V("K"))), Hyp(Call("IsPreconnected", V("K"))),
            Hyp(Call("Nondegenerate", V("K"))), new Formula.Not(Call("SourceRelativeTracing", V("p"), V("g"), V("f")))]),
            "Nondegenerate(K) means there are two distinct points of the subtype K. SR implies OL by using exact orbits "
            + "as pseudo-orbits for every control. OL would give a clopen basis, making K totally separated and totally disconnected. "
            + "Preconnectedness would force its points to agree, contradicting nondegeneracy. No f-invariance of K is introduced."),
        Doc("connected-fixed-orbit-obstruction", "connected_fixed_orbit_obstruction", St([.. Extension(true),
            Hyp(Call("Surjective", V("p"))), Hyp(Call("IsPreconnected", V("K"))), Hyp(Call("Nondegenerate", V("K"))),
            Call("FixedOrbitFailure", V("p"), V("g"), V("f"), V("K"))]),
            "FixedOrbitFailure is the exact order: there are E in the upstairs uniformity and a in Y such that, "
            + "for every D in the upstairs uniformity and every V in the downstairs uniformity, there exists x:K. "
            + "The sequence g^n(a) is a D-pseudo-orbit, (p(g^n(a)),f^n(x.val)) is in V at every n, "
            + "and there is no b with p(b)=x.val and (g^n(b),g^n(a)) in E at every n. "
            + "A clopen C contains one whole fibre and avoids another. Its relative image is nonempty, proper and closed, "
            + "hence not open on connected K. Fix a boundary point and one a in C above it, and set E to the two-cell relation. "
            + "Each V gives an equicontinuity neighborhood meeting the complement of that image. Every lift of the selected x is outside C "
            + "and fails at n=0. Compactness of K is unnecessary for this stronger fixed-witness result; compact Y supplies closed images."),
        Doc("expansive-factor-locally-constant", "expansive_factor_locally_constant_on", St([.. Factor(),
            Call("IsLocallyConstant", Call("Restriction", V("pi"), V("K")))]),
            "Pull back the positively expansive observation through the explicitly uniformly continuous pi. "
            + "Equicontinuity makes all projected forward orbits close on a neighborhood of each x:K. "
            + "Semiconjugacy and positive expansivity identify pi(y) with pi(x) throughout that neighborhood."),
        Doc("expansive-factor-constant-on-connected", "expansive_factor_constant_on_connected", St([.. Factor(),
            Hyp(Call("IsPreconnected", V("K"))), Call("ConstantOn", V("pi"), V("K"))]),
            "ConstantOn(pi,K) is ∀x,y:K, pi(x.val)=pi(y.val). Local constancy and preconnectedness imply this equality. "
            + "Surjectivity is not required. Consequently positively expansive factors cannot separate a nondegenerate connected equicontinuous subset."),
        Doc("contraction-pseudo-orbit-estimate", "contraction_pseudo_orbit_estimate", St([.. Contraction(),
            All("delta", Seq(Mathbb, Grp(V("R")))), Hyp(Seq(D(0), Le, Sp, V("delta"))),
            All("a", Map(Seq(Mathbb, Grp(V("N"))), V("X"))), Hyp(Call("WeakMetricPseudoOrbit", V("f"), V("delta"), V("a"))),
            All("n", Seq(Mathbb, Grp(V("N")))), Call("GeometricErrorBound", V("f"), V("q"), V("delta"), V("a"), V("n"))]),
            "ContractionBound is ∀x,y, dist(f(x),f(y))≤q dist(x,y). WeakMetricPseudoOrbit is "
            + "∀n, dist(f(a(n)),a(n+1))≤delta. The exact GeometricErrorBound is the conjunction "
            + "dist(f^n(a(0)),a(n))≤delta times the sum of q^j for j<n, and that finite sum times delta≤delta/(1-q). "
            + "The recurrence e(0)=0 and e(n+1)≤q e(n)+delta proves the first inequality. The geometric-sum identity proves the second. "
            + "At q=0 and n≥1 the intermediate quantities can be equal; both displayed intermediate comparisons are weak."),
        Doc("contraction-has-shadowing", "contraction_hasShadowing", St([.. Contraction(),
            Hyp(Call("CompactSpace", V("X"))), Call("HasShadowing", V("f"))]),
            "For a metric entourage choose epsilon>0, then delta=(1-q)epsilon/2. The initial point a(0) traces the pseudo-orbit. "
            + "The preceding weak geometric bounds are followed by the strict comparison delta/(1-q)<epsilon. "
            + "The cover/uniform equivalence supplies the actual finite-open-cover property, including q=0 and n=0."),
        Doc("connected-contraction-shadowing-obstruction", "connected_contraction_shadowing_obstruction", St([.. Contraction(),
            Hyp(Seq(Call("CompactSpace", V("X")), Sp, Land, Sp, Call("PreconnectedSpace", V("X")))), Hyp(Call("Nondegenerate", V("X"))),
            Seq(All("Y", V("Type")), Sp, Inst("UniformSpace", V("Y")), Sp, Inst("CompactSpace", V("Y")),
                Sp, Inst("TTwoSpace", V("Y")), Sp, Inst("TotallyDisconnectedSpace", V("Y"))),
            Seq(All("p", Map(V("Y"), V("X"))), Sp, All("g", Map(V("Y"), V("Y")))),
            Hyp(Seq(Call("Continuous", V("p")), Sp, Land, Sp, Call("Surjective", V("p")), Sp, Land, Sp,
                Call("Semiconj", V("p"), V("g"), V("f")))),
            Seq(Call("HasShadowing", V("f")), Sp, Land, Sp, new Formula.Not(Call("SourceRelativeTracing", V("p"), V("g"), V("f"))))]),
            "All iterates of a q-contraction with 0≤q<1 are nonexpansive, hence uniformly equicontinuous. "
            + "Use K=X in the connected-subset obstruction. This proves shadowing of the compact metric source and failure of SR for every supplied "
            + "continuous onto equivariant map from a compact Hausdorff zero-dimensional space. It does not disprove Peng Q5.1, "
            + "nor assert that any such extension exists or fails ordinary shadowing. The paper's metric extension existence remains an ordinary supplier, "
            + "not an automatically installed Lean instance. No originality or worldwide resolution claim is made."))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(F.Id(name))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
}
