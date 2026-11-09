using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class NorthSouthSelectorDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), Colon, Sp, t, Comma, Sp);
    private static Formula Call(string s, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(Id(s))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
    private static Formula SelectorFormula() => Seq(
        All("M", Id("CompactMetricSpace")), All("f", Call("Homeomorphism", Id("M"))),
        All("N", Id("M")), All("S", Id("M")),
        Call("Pointwise", Id("f"), Id("N"), Id("S")), Sp, Rightarrow, Sp,
        Call("LocalEquiconnection", Id("M")), Sp, Rightarrow, Sp,
        Exists, Sp, Id("delta"), Colon, Sp, Seq(Mathbb, Grp(Id("R"))), Comma, Sp,
        D(0), Sp, Lt, Sp, Id("delta"), Sp, Land, Sp,
        Exists, Sp, Id("Q"), Colon, Sp, Call("Space", Id("f"), Id("delta")), Sp, To, Sp, Id("M"), Comma, Sp,
        Call("Continuous", Id("Q")), Sp, Land, Sp,
        Open, All("p", Id("M")),
        Call("Q", Call("trueOrbit", Id("f"), Id("p"))), Sp, Eq, Sp, Id("p"), Close, Sp, Land, Sp,
        Open, All("k", Seq(Mathbb, Grp(Id("Z")))),
        All("x", Call("Space", Id("f"), Id("delta"))),
        Call("Q", Call("shift", Id("f"), Id("k"), Id("x"))), Sp, Eq, Sp,
        Call("iterate", Id("f"), Id("k"), Call("Q", Id("x"))), Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every literal pointwise north-south homeomorphism of a compact metric locally equiconnected space has a continuous exactly equivariant selector on a full closed integer pseudoorbit domain.",
        H("The Full Pointwise North-South Selector"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pointwise-north-south-selector"),
                DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/NorthSouthSelector.pointwise_north_south_selector"),
                H("A single selector on the entire closed domain"),
                StatementSource.FromAuthor(SelectorFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "M is an arbitrary compact metric space. The homeomorphism f has distinct "
                        + "fixed poles N,S, and each other point tends pointwise to S under positive "
                        + "iterates and to N under inverse iterates. A local equiconnection is explicit "
                        + "data: one open W in M×M containing the diagonal, and one continuous "
                        + "H:W×[0,1]→M with both endpoint equalities and the all-parameter diagonal "
                        + "identity. Stability, compact uniform attraction and a strict height are "
                        + "derived from the pointwise assumptions in the imported suppliers.")),
                    Paragraph(Text(
                        "There are δ>0 and Q on the entire closed set Pδ of sequences x:Z→M with "
                        + "dist(x(i+1),f(x(i)))≤δ for every integer i. Q is continuous for the "
                        + "inherited product topology, fixes every true orbit, and satisfies "
                        + "Q(shift(k,x))=f^k(Q(x)) for all integers k. The shift reads x(k+i); "
                        + "commutativity of integer addition identifies the primary x(i+k) convention. "
                        + "Errors equal to δ and infinitely many nonzero errors remain in scope.")),
                    Paragraph(Text(
                        "For the constructed strict height h, compact separation gives a positive "
                        + "closed-link tolerance, a one-way sign barrier, a uniform positive crossing "
                        + "denominator, and a compact band containing every interpolation output. "
                        + "At a weak crossing j the formula is f^(-j) applied to "
                        + "H(x(j),f^(-1)(x(j+1)), -h(x(j))/(h(x(j+1))-h(x(j)))). "
                        + "Adjacent crossings at a zero entry give exactly the same output by the "
                        + "two endpoint identities. A finite closed cover proves continuity near "
                        + "each crossing. At every all-negative or all-positive history, including "
                        + "arbitrary nonconstant histories, one far coordinate and compact uniform "
                        + "attraction prove continuity at the corresponding cap. The two-point "
                        + "space is included: the punctured clock is empty and the same proof gives "
                        + "the full selector. No finite-window replacement is made.")),
                    Paragraph(Text(
                        "For a topological sphere, transport the explicit normalized straight "
                        + "connector from the Euclidean unit sphere through the given homeomorphism. "
                        + "Its nonantipodal pair domain is open, its chord is nonzero throughout "
                        + "[0,1], and normalization supplies both endpoints and the diagonal. Thus "
                        + "the theorem applies to an arbitrary literal pointwise north-south sphere "
                        + "homeomorphism for every compatible metric. No smooth, hyperbolic, flow "
                        + "or dimension bound is introduced; compact LEC implies ANR is not claimed.")),
                    Paragraph(Text(
                        "The same Q supplies CompactSelector.global_and_limit_shadowing. For each "
                        + "ε>0 it gives 0<γ≤δ such that every x in Pγ satisfies "
                        + "dist(f^k(Q(inclusion(x))),x(k))<ε for every integer k. For every x in "
                        + "the original Pδ whose literal link errors tend to zero in the cofinite "
                        + "filter on Z, the discrepancies for Q(x) also tend to zero in that filter; "
                        + "the supplier also gives the explicit natAbs tail. Domain inclusion is "
                        + "literal sequence inclusion. The exact supplier source is reused unchanged "
                        + "from commit 5c2269ceb35eac4b8cf436d183defc9e2a1ffbc3, SHA-256 "
                        + "df66b7c5c21214ee7ba72379e228e16f19bdb386ccbec713f83fef198a30834d.")),
                    Paragraph(Text(
                        "The construction follows the supplied terminal mathematical source "
                        + "public-proof.txt SHA-256 "
                        + "9d2c8af332171841b0de2122a8a6d18d3f094b8ee563ff2b50646332144306bc "
                        + "and lean-route.txt SHA-256 "
                        + "1a51a2083580f57293ae2e0f032afb5257d891328f247d26b97b81b483360a97. "
                        + "This is a substantive open-problem-resolution assertion for the existence "
                        + "asked in Alfonso Artigue, Shadowing maps, final Question 5.19, printed "
                        + "page 52, DOI 10.2140/om.2027.4.29 (arXiv:2504.00171v1 Question 5.21). "
                        + "The primary paper's Proposition 5.18 proves non-equivariance of its "
                        + "particular bracket construction. The present selector uses a different "
                        + "formula and the literal pointwise hypotheses. Attribution and kernel "
                        + "verification do not establish literature priority, exhaustive novelty "
                        + "or official acceptance. The existing full vertical suspension theorem "
                        + "is preserved as a separate result."))),
                DescribeRole.Theorem))));
}
