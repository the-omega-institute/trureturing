using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciEmittedTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric emitted-event tail for the original conditional zero-reset coupling.",
        H("The full-output no-common-false event"),
        Blocks(
            Paragraph(Text(
                "Write W(n) for Fin n to Bool. C(k,n,F,x) is completions: all original "
                + "DBonacciAdmissible full words agreeing with x at every site in F. "
                + "L(F,x,h) is completionLaw on this nonempty fiber, and P(s,F,x,y,h,g) "
                + "is the original prefixCoupling defined in KBonacciConditionalBlockCoupling. "
                + "It tests resetReady before scanning and uses recursive refinement with an independent fallback. "
                + "The finite set F may include the full exterior and sampled prefix.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-prefix-coupling-emitted-tail"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciEmittedTail.prefix_coupling_emitted_tail"),
                H("Geometric tail of the original emitted no-common-false event"),
                StatementSource.FromAuthor(Disp(TailFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a full-word pair w, E(s,j,w) means that for every site i in s.take(j), "
                    + "the two emitted bits are not both false. The notation MassEvent(P,s,j) is "
                    + "mean P (fun w => if E(s,j,w) then 1 else 0). This includes (true,true), "
                    + "j=0 and the entire scan. No increasing-order or complement-cover assumption "
                    + "is needed for this event estimate. A counting induction in the original "
                    + "completion fibers bounds the all-true event by 2^(-j). This handles the "
                    + "original reset branch, whose two outputs agree at every free site. In a "
                    + "supported recursive child, the emitted head is the sampled bit pair. The "
                    + "common-false child contributes zero; the other children carry the residual "
                    + "event bound and have total mass at most one half. Impossible refinements "
                    + "have zero joint mass. The resulting induction uses the original prefixCoupling "
                    + "without modifying its fallback or initial-reset tests. Supported coalescence "
                    + "after an emitted common false is a separate assertion and is not proved here."))),
                DescribeRole.Theorem))));

    private static Formula TailFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var f = F.Id("F");
        var s = F.Id("s"); var x = F.Id("x"); var y = F.Id("y");
        var h = F.Id("h"); var g = F.Id("g"); var i = F.Id("i"); var j = F.Id("j");
        var free = All(i, Call("Fin", n), Imp(Seq(i, Sp, InMacro, Sp, s),
            Seq(Neg, Sp, Par(Seq(i, Sp, InMacro, Sp, f)))));
        var bound = All(j, Nat, Imp(Rel(j, Leq, Call("length", s)),
            Rel(Call("MassEvent", Call("P", s, f, x, y, h, g), s, j), Leq,
                new Formula.Power(Par(Seq(D(1), Slash, D(2))), j))));
        var fibers = All(Seq(x, Comma, y), Word(n),
            All(h, Call("Nonempty", Call("C", k, n, f, x)),
                All(g, Call("Nonempty", Call("C", k, n, f, y)), bound)));
        var fixedSet = All(f, Call("Finset", Call("Fin", n)), Imp(free, fibers));
        return All(Seq(k, Comma, n), Nat, Imp(Rel(D(0), Lt, k),
            All(s, Call("List", Call("Fin", n)), Imp(Call("Nodup", s), fixedSet))));
    }

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Word(Formula n) => Seq(Open, Call("Fin", n), Sp, To, Sp, Op("Bool"), Close);
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula Rel(Formula a, Formula r, Formula b) => Seq(a, Sp, r, Sp, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(Formula v, Formula t, Formula b) => Par(Seq(Forall, Sp, Open, v, Colon, t, Close, Comma, Sp, Par(b)));
    private static Formula Imp(Formula a, Formula b) => Par(Rel(Par(a), Implies, Par(b)));
}
