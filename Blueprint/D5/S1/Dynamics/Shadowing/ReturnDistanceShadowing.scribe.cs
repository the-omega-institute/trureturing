using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class ReturnDistanceShadowingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/ReturnDistanceShadowing.";
    private static Formula Id(string s) => F.Id(s);
    private static Formula Z => Seq(Mathbb, Grp(Id("Z")));
    private static Formula SetZ => Call("Set", Z);
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), Colon, Sp, t, Comma);
    private static Formula Hyp(Formula a) => Seq(a, Sp, Rightarrow, Sp);
    private static Formula Call(string s, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(Id(s))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static DocumentBlock.Describe Thm(string key, string decl, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(key), DeclarationHandle.Create(Owner + decl), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two fixed close points trace every natural-time pseudo-orbit in an unbounded return-distance subshift.",
        H("Neighborhood Two-Shadowing by Separated Gap Repair"), Blocks(
        Paragraph(Text("NeighborhoodTwoShadowing(f) uses the existing MetricPseudoOrbit contract on sequences indexed by the natural numbers. "
            + "For every positive epsilon, one positive delta works for every such pseudo-orbit. A nonempty finite set A of at most two actual phase-space points "
            + "has initial diameter less than epsilon, and the distance from x(i) to the image f^i(A) is less than epsilon at every natural i. "
            + "The same A works for all times. The finite-set bridge uses A={a,b}, the exact identity diam({a,b})=dist(a,b), "
            + "and infDist_lt_iff with an explicit nonempty image. It does not exploit the convention for distance to the empty set.")),
        Paragraph(Text("For the compatible Mathlib countable-product metric, a sufficiently large finite signed window forces a prescribed strict distance bound. "
            + "Conversely, sufficiently small metric errors force exact agreement on any prescribed signed window. These are proved using the product uniformity "
            + "and the finite-alphabet discrete diagonal entourages. They concern actual metric distances, not a replacement cylinder-only property.")),
        Paragraph(Text("Extend negative times by the exact shifts of the initial configuration. signedDiagonal(z,j) reads coordinate zero of this extension at time j; "
            + "it equals z(j)(0) for nonnegative j, and z(0)(j) for negative j. Signed overlap propagates through both positive and negative offsets. "
            + "Only the original natural-time pseudo-orbit is quantified; the past extension introduces no assumption on it.")),
        Thm("unbounded-return-two-shadowing", "unbounded_return_neighborhood_two", "Unbounded allowed returns and distance one give two tracers", St(
            All("D", SetZ), Hyp(Seq(D(1), Sp, InMacro, Sp, Id("D"))),
            Hyp(Call("UnboundedReturnDistances", Id("D"))),
            Call("NeighborhoodTwoShadowing", Call("returnShift", Id("D")))),
            "UnboundedReturnDistances(D) means that for every natural N there is a natural h>N with the integer h in D. "
            + "Choose r so radius-r agreement implies distance less than epsilon, h in D above 2r, and K=2h. Choose delta forcing overlap on [-K,K]. "
            + "For an arbitrary delta-pseudo-orbit let c be its signed diagonal, and keep P={j at least -r : c(j)=1}. "
            + "For any original consecutive gap of length at most K, use the actual point at center p if p is nonnegative, and center zero otherwise. "
            + "Signed overlap transfers the entire pair and its intervening zeros to that point, so its distance is allowed. "
            + "Let a be the binary point on the repaired support and b the point retaining P only on [-r,r]. Both are actual legal points. "
            + "The first insertion is beyond r, so both initially agree with c. In every future radius-r window, either an original one occurs and separated repair makes a agree everywhere, "
            + "or no original one occurs and the truncated point b agrees everywhere. The metric-window bounds give the required strict pair distance and tracing. "
            + "Empty and finite original supports use the same definitions; no filler-existence assumption or infinite support enumeration is used.")
        )));

}
