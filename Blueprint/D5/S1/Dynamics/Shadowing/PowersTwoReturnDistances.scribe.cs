using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class PowersTwoReturnDistancesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/PowersTwoReturnDistances.";
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
        "An explicit binary two-sided subshift with neighborhood two-shadowing and without original exact-length quasi-finite type.",
        H("Powers-of-Two Return-Distance Example"), Blocks(
        Paragraph(Text("The source is Jonathan Meddaugh and Elyssa Stephens, Shadowing with small diameter sets of bounded cardinality, "
            + "arXiv:2509.04312v1, https://arxiv.org/html/2509.04312v1, Definitions 2.1 and 3.5 and Question 5.3. "
            + "The positive return distances are 2^j for natural j. Equivalently the intervening zero-run lengths are 2^j-1, including zero. "
            + "The example uses the genuine compatible countable-product metric supplied by Mathlib, rather than the degenerate printed infimum expression in the source.")),
        Thm("powers-two-example", "powers_two_return_distance_example", "The explicit return-distance example", St(
            Seq(Call("Nonempty", Call("ReturnPoint", Call("powersTwoDistances"))), Sp, Land),
            Seq(Call("CompactSpace", Call("ReturnPoint", Call("powersTwoDistances"))), Sp, Land),
            Seq(Call("Continuous", Call("returnShift", Call("powersTwoDistances"))), Sp, Land),
            Seq(Call("NeighborhoodTwoShadowing", Call("returnShift", Call("powersTwoDistances"))), Sp, Land),
            Seq(Neg, Sp, Call("ReturnQuasiFiniteType", Call("powersTwoDistances")))),
            "A singleton-support configuration witnesses nonemptiness. The phase space is the carrier of the bundled finite-alphabet subshift on integer coordinates. All pseudo-orbit time indices remain natural numbers. "
            + "Distance one is allowed and powers of two are unbounded, so the generic gap-repair theorem supplies the original finite-set two-shadowing property. "
            + "For every n choose H=2^(n+2)>n+1. The interval (H,H+n+1] lies strictly between H and 2H and contains no power of two. "
            + "The generic first-return language obstruction therefore disproves the original exact-length QFT condition. "
            + "This theorem addresses this explicit example and the existence request of Question 5.3 only. It asserts no full hierarchy result, nonsoficity theorem, literature novelty or official acceptance.")
        )));

}
