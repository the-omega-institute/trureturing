using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class ProgressionTwoShadowingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/ProgressionTwoShadowing.";
    private static Formula Id(string s) => F.Id(s);
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
        "The same two genuine infinite configurations trace every natural-time pseudo-orbit, with small initial diameter.",
        H("Quadratic Progression Two-Shadowing"), Blocks(
        Paragraph(Text("Put ell(p)=p^2+3. The hereditary carrier forbids every all-one progression of that length and positive difference p. "
            + "Given epsilon>0 choose R>=1 with 2^(-(R+1))<epsilon, then M=32(R+1), alpha=sqrt(2)/M, P=256 M(M+3), D=max(R,P^3+2P) and delta=2^(-D). "
            + "These parameters are fixed before the arbitrary infinite natural-time pseudo-orbit z. The arithmetic-progression construction and explicit constants for Meddaugh--Stephens Question 5.6 are attributed to Pro.")),
        Paragraph(Text("Read c(n)=z(n)(0). Strict first-disagreement errors force edge equality through D. The existing MetricTracing.diagonal_splice_overlap gives c(i+j)=z(i)(j) for all i and j<=D+1. "
            + "For 1<=p<=P, the span p(p^2+2)<=P^3+2P fits in that overlap, so c satisfies every such progression constraint at every starting coordinate. The proof does not assume c itself is in the carrier.")),
        Thm("quarter-mask-separation", "quarter_masks_separated", "Quarter masks stay separated across wrap-around", St(
            Seq(Forall, Sp, Id("u"), Comma, Id("v"), Sp, InMacro, Sp, Mathbb, Grp(Id("R")), Comma),
            Seq(Call("fract", Id("u")), Sp, InMacro, Sp, Seq(OpenBracket, Frac, Grp(D(1)), Grp(D(8)), Comma, Frac, Grp(D(3)), Grp(D(8)), CloseBracket), Sp, Rightarrow),
            Seq(Call("fract", Id("v")), Sp, InMacro, Sp, Seq(OpenBracket, Frac, Grp(D(5)), Grp(D(8)), Comma, Frac, Grp(D(7)), Grp(D(8)), CloseBracket), Sp, Rightarrow,
                Sp, Seq(Frac, Grp(D(1)), Grp(D(8))), Sp, Le, Sp, Seq(Bar, Id("v"), Minus, Id("u"), Bar))),
            "If the real phase difference were less than 1/8, the integer difference floor(v)-floor(u) would be strictly between -1 and 0. "
            + "This contradiction handles every integer crossing. Since R alpha<1/8, no window [i,i+R] can meet both masks."),
        Paragraph(Text("Let E0 be the natural coordinates whose alpha phases lie in [1/8,3/8], and E1 those in [5/8,7/8]. Define a by deleting c on E0 and b by deleting c on E1. "
            + "For p<=P, an existing zero stays zero after deletion. For p>P, uniform quarter hitting puts a deletion in each forbidden support by index Pp<p^2+3. Thus both whole infinite branches satisfy every constraint. "
            + "Their initial phases lie in [0,1/8), so both agree initially with c. Every later R-window misses at least one deletion color, so that branch agrees throughout with the corresponding pseudo-orbit window.")),
        Thm("progression-two-shadowing", "quadratic_progression_neighborhood_two_shadowing", "The original fixed two-point tracing contract", St(
            Call("NeighborhoodTwoShadowing", Call("progressionShift", Call("quadraticProgressionLength")))),
            "For every epsilon>0 choose delta>0 before the entire pseudo-orbit. The two constructed points are in X and have distance at most 2^(-(R+1))<epsilon. "
            + "At every natural i, at least one shifted point is within the same strict epsilon of z(i). The existing neighborhood_two_of_pair packages the same nonempty finite set A={a,b}, card(A)<=2, initial diameter<epsilon and infDist(z(i),sigma^i(A))<epsilon. "
            + "The minimizer may switch with i. No all-branches tracing, coherent single tracer or all-time diameter bound is claimed.")
        )));
}
