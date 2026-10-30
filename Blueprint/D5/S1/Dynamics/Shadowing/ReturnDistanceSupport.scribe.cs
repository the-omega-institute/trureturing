using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class ReturnDistanceSupportDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/ReturnDistanceSupport.";
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
        "Separated interval repair of consecutive return distances on the integers.",
        H("Return-Distance Support Repair"), Blocks(
        Paragraph(Text("SupportAdjacent(P,p,q) means p and q belong to P, p<q, and P has no member strictly between them. "
            + "For an allowed-distance set D and a positive integer h, gapInsertions(D,P,h) is the union of all integer intervals "
            + "[p+h,q-h] over consecutive original pairs with q-p outside D. The repaired support is the union with P. "
            + "This construction is defined without choosing an enumeration, and admits empty, singleton, finite and infinite supports.")),
        Thm("separated-insertions", "insertion_separated", "Insertions stay away from every original point", St(
            All("D", SetZ), All("P", SetZ), All("h", Z), All("t", Z), All("s", Z),
            Hyp(Seq(Id("t"), Sp, InMacro, Sp, Call("gapInsertions", Id("D"), Id("P"), Id("h")))),
            Hyp(Seq(Id("s"), Sp, InMacro, Sp, Id("P"))),
            Seq(Id("t"), Sp, Le, Sp, Id("s"), Minus, Id("h"), Sp, Lor, Sp,
                Id("s"), Plus, Id("h"), Sp, Le, Sp, Id("t"))),
            "An original point lies on or beyond one of the bracketing endpoints. Each insertion is therefore at least h away from it."),
        Thm("legal-repair", "repaired_support_legal", "The interval repair has only allowed return distances", St(
            All("D", SetZ), All("P", SetZ), All("h", Z),
            Hyp(Seq(D(0), Sp, Lt, Sp, Id("h"))),
            Hyp(Seq(D(1), Sp, InMacro, Sp, Id("D"))), Hyp(Seq(Id("h"), Sp, InMacro, Sp, Id("D"))),
            Hyp(Seq(Open, All("p", Z), All("q", Z),
                Hyp(Call("SupportAdjacent", Id("P"), Id("p"), Id("q"))),
                Hyp(Seq(Id("q"), Minus, Id("p"), Sp, Le, Sp, D(2), Id("h"))),
                Id("q"), Minus, Id("p"), Sp, InMacro, Sp, Id("D"), Close)),
            All("x", Z), All("y", Z),
            Hyp(Call("SupportAdjacent", Call("repairedSupport", Id("D"), Id("P"), Id("h")), Id("x"), Id("y"))),
            Seq(Id("y"), Minus, Id("x"), Sp, InMacro, Sp, Id("D"))),
            "Assume one and h are allowed, and every original gap of length at most 2h is allowed. "
            + "An illegal original gap exceeds 2h. The filled gap has edge distances h and internal distances one. "
            + "For consecutive repaired points, the four possibilities (original/original, original/inserted, inserted/original, inserted/inserted) "
            + "give respectively an unchanged allowed gap, h, h, and one. The separation lemma excludes crossings between distinct repaired intervals."),
        Paragraph(Text("The window lemma states that if 2r<h and [i-r,i+r] contains an original support point, repair agrees with the original support throughout that window. "
            + "The truncation lemma states that retaining only P intersect [l,u] is legal whenever every original consecutive gap of length at most u-l is legal. "
            + "Neither lemma asserts that the original support is globally legal."))
        )));
}
