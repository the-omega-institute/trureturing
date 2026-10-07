using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class AnchoredPhaseClassificationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/AgencyHolonomy/AnchoredPhaseClassification.anchored_phase_classification";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For finite named directed multigraphs, anchored phase coordinates give the complete compact abelian quotient and can be assigned independently in one edge field.",
        H("Complete Anchored Phase Classification"),
        Blocks(
            Paragraph(Text(
                "Fix finite types V,E, endpoint maps s,t:E to V and an arbitrary selected named spanning tree T. "
                + "Its selected edges are nonloops, their unordered endpoint pairs are distinct, "
                + "and precisely their simple support is connected and acyclic. "
                + "The original edge type retains all parallel edges, loops and separately named reverse edges. "
                + "Fix a reference subset R and a root r in R. Write n=card V, m=card E and k=card R.")),
            Paragraph(Text(
                "For u:E to Circle, let h_v(u) be the actual signed phase product along the unique simple path "
                + "in this chosen tree from r to v. Negative traversal is the inverse phase of the same original "
                + "named edge; it introduces neither another independent phase nor an execution permission. "
                + "Let C be the product of Circle indexed by E minus T and by R minus r. "
                + "The coordinate chi(u) has entries h_s(u) u_e h_t(u) inverse and h_a(u), respectively.")),
            Paragraph(Text(
                "The anchored vertex subgroup H consists exactly of functions g with g_a=1 for every a in R. "
                + "Its action is (g dot u)_e=g_t u_e g_s inverse. "
                + "The homomorphism delta:H to Circle^E sends g to g_t g_s inverse; N is its image. "
                + "The quotient is Circle^E/N with its quotient group topology, rather than treating H itself "
                + "as a literal subgroup of edge fields.")),
            Paragraph(Text(
                "Given z=(lambda,alpha) in C, extend alpha to a vertex potential H_z by setting "
                + "H_z(r)=1, H_z(a)=alpha_a at other references and H_z(v)=1 elsewhere. "
                + "Extend lambda to Lambda_z(e)=1 on T and lambda_e outside T. "
                + "The single field sigma(z)_e=H_z(t(e)) Lambda_z(e) H_z(s(e)) inverse realizes all entries.")),
            Describe.Lean(
                DescribeId.Create("anchored-phase-classification"),
                DeclarationHandle.Create(Declaration),
                H("Complete invariants, continuous section and exact quotient dimension"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Root-path covariance proves invariance under H. If two coordinate tuples agree, "
                        + "take g_v=h_v(w) h_v(u) inverse. Agreement at every reference makes this an anchored gauge. "
                        + "The selected-edge endpoint law and the non-tree coordinates then reconstruct every original named edge.")),
                    Paragraph(Text(
                        "Lambda_z is one on every selected edge, so its actual tree path products are one. "
                        + "The endpoint covariance formula therefore gives h_v(sigma(z))=H_z(v). "
                        + "Consequently chi(sigma(z))=z, with no extra equations between loops, parallel edges "
                        + "or reference coordinates. Both chi and sigma are continuous and multiplicative.")),
                    Paragraph(Text(
                        "The kernel of chi is exactly N and the coordinate fibers are exactly its cosets. "
                        + "The quotient homomorphism has inverse z mapping to the coset of sigma(z). "
                        + "The quotient map makes the forward map continuous and the continuous section makes the inverse continuous. "
                        + "The quotient is compact, Hausdorff and abelian, with continuous group operations; N is closed.")),
                    Paragraph(Text(
                        "Selected named edges are in bijection with the edges of this same tree support. "
                        + "Thus t+1=n, c+t=m and a+1=k, where t=card T, c=card(E minus T), "
                        + "and a=card(R minus r). The independent coordinate number d=c+a satisfies d+n=m+k, "
                        + "so d=m+k-n and b=c=m+1-n, with d=b+k-1. "
                        + "Only the finite index set is reindexed to Fin d; no cardinality of the underlying Circle product "
                        + "is used. Natural subtraction is justified by these additive identities.")),
                    Paragraph(Text(
                        "The quantifiers include a single vertex with no edges, arbitrary one-vertex loops, "
                        + "single or all-vertex references, tree graphs and parallel named edges. "
                        + "This classifies the declared full phase space; further physical constraints would restrict its image. "
                        + "It does not identify phases from intensity data or grant operations along formal inverse paths."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula All(string binder, Formula body)
    {
        foreach (var group in binder.Split(';').Reverse())
        {
            var pair = group.Split(':');
            var typeName = pair[1];
            Formula type = typeName switch
            {
                "E to V" => new Formula.TypeArrow(F.Id("E"), F.Id("V")),
                "E to Circle" => new Formula.TypeArrow(F.Id("E"), F.Id("Circle")),
                "V to Circle" => new Formula.TypeArrow(F.Id("V"), F.Id("Circle")),
                "subset E" => Call("Set", F.Id("E")),
                "subset V" => Call("Set", F.Id("V")),
                _ => F.Id(typeName),
            };
            foreach (var name in pair[0].Split(',').Reverse())
                body = Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
        }
        return body;
    }
    private static Formula And(params Formula[] clauses)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var clause in clauses)
        {
            if (items.Count > 0) items.AddRange([Sp, Land, Sp]);
            items.AddRange([Open, clause, Close]);
        }
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula u = F.Id("u");
        Formula w = F.Id("w");
        Formula z = F.Id("z");
        Formula g = F.Id("g");
        Formula q = F.Id("q");
        Formula chi(Formula x) => Call("chi", x);
        Formula sigma(Formula x) => Call("sigma", x);
        Formula coset(Formula x) => Call("cosetN", x);
        Formula orbit = Seq(Exists, Sp, F.Id("g"), Colon, Sp, F.Id("H"), Comma, Sp,
            Eqn(Call("gauge", g, u), w));
        Formula invariant = All("g:H;u:E to Circle", Eqn(chi(Call("gauge", g, u)), chi(u)));
        Formula fibers = All("u,w:E to Circle", Seq(Eqn(chi(u), chi(w)), Sp, Iff, Sp, orbit));
        Formula realization = All("z:C", Eqn(chi(sigma(z)), z));
        Formula sectionMul = All("z,zPrime:C", Eqn(sigma(Call("mul", z, F.Id("zPrime"))),
            Call("mul", sigma(z), sigma(F.Id("zPrime")))));
        Formula cosets = All("u,w:E to Circle", Seq(Eqn(coset(u), coset(w)), Sp, Iff, Sp, orbit));
        Formula quotient = Seq(Exists, Sp, q, Colon, Sp,
            Call("ContinuousMulEquiv", Call("QuotientGroup", new Formula.TypeArrow(F.Id("E"), F.Id("Circle")), F.Id("N")), F.Id("C")), Comma, Sp,
            And(All("u:E to Circle", Eqn(Call("q", coset(u)), chi(u))),
                All("z:C", Eqn(Call("qInverse", z), coset(sigma(z))))));
        Formula sum(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
        Formula c = F.Id("c");
        Formula a = F.Id("a");
        Formula t = F.Id("tCard");
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        Formula d = sum(c, a);
        Formula exponent = Seq(sum(m, k), Sp, Minus, Sp, n);
        Formula conclusion = And(invariant, fibers, realization,
            Call("Continuous", F.Id("sigma")), sectionMul,
            Eqn(Call("ker", F.Id("chi")), F.Id("N")), cosets, quotient,
            Call("CompactSpace", Call("QuotientGroup", new Formula.TypeArrow(F.Id("E"), F.Id("Circle")), F.Id("N"))),
            Call("T2Space", Call("QuotientGroup", new Formula.TypeArrow(F.Id("E"), F.Id("Circle")), F.Id("N"))),
            Call("IsTopologicalGroup", Call("QuotientGroup", new Formula.TypeArrow(F.Id("E"), F.Id("Circle")), F.Id("N"))), Call("IsClosed", F.Id("N")),
            Eqn(sum(t, D(1)), n), Eqn(sum(c, t), m), Eqn(sum(a, D(1)), k),
            Eqn(sum(d, n), sum(m, k)), Eqn(d, exponent),
            Eqn(c, Seq(sum(m, D(1)), Sp, Minus, Sp, n)),
            Eqn(d, Seq(sum(c, k), Sp, Minus, Sp, D(1))),
            Call("Nonempty", Call("ContinuousMulEquiv", F.Id("C"),
                Call("CirclePower", exponent))));
        return Disp(All("V,E:Type;s,t:E to V;T:subset E;R:subset V;r:V",
            Seq(Call("Fintype", F.Id("V")), Sp, Land, Sp,
                Call("Fintype", F.Id("E")), Sp, Land, Sp,
                Call("NamedSpanningTree", F.Id("s"), F.Id("t"), F.Id("T")), Sp, Land, Sp,
                Call("Member", F.Id("r"), F.Id("R")), Sp, Rightarrow, Sp, conclusion)));
    }
}
