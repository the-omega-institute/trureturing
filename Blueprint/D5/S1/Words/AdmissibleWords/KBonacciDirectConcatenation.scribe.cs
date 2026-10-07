using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciDirectConcatenationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direct concatenation of actual Boolean words has an exact run boundary condition "
            + "and nested one-page neighborhoods.",
        H("Direct concatenation without a separator"),
        Blocks(
            Paragraph(Text(
                "A word of width m is a function from Fin m to Bool, read in increasing "
                    + "coordinate order. L(k,m,w) denotes DBonacciAdmissible k m w, "
                    + "the original scanner condition forbidding k consecutive true bits. "
                    + "The concatenation x ++ y is Fin.append x y and retains every bit. "
                    + "The natural widths may be zero. An all-true word contributes its "
                    + "entire width to its initial and terminal runs.")),
            Paragraph(Text(
                "In the theorem, p(w) is (List.ofFn w).findIdx Bool.not, and t(w) "
                    + "is p applied to i mapped to w(Fin.rev i). B(k,n,s) is the finite "
                    + "set of legal true-starting width-n words with p(w) < k-s. "
                    + "These are local definitions; natural subtraction is truncated "
                    + "at zero and head(w) is the optional first bit.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-actual-direct-concatenation"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciDirectConcatenation.actual_direct_concatenation"),
                H("The exact interface law and all neighborhood clauses"),
                StatementSource.FromAuthor(Disp(MainFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A forbidden block inside either component is excluded by that "
                        + "component's scanner. A forbidden block crossing the interface "
                        + "requires k true bits drawn from the final run of x and the "
                        + "initial run of y. Conversely, when their sum reaches k, those "
                        + "actual positions supply a forbidden crossing block. This "
                        + "argument also covers words shorter than k and all-true words. "
                        + "A true-starting word has an initial run of at least one, so "
                        + "the neighborhood at k-1 is empty. A false-starting word has "
                        + "initial run zero and therefore connects to every legal x."))),
                DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        var k = F.Id("k");
        var m = F.Id("m");
        var n = F.Id("n");
        var x = F.Id("x");
        var y = F.Id("y");
        var s = F.Id("s");
        var u = F.Id("u");
        var legal = And(Fn("L", k, m, x), Fn("L", k, n, y));
        var join = Fn("L", k, Seq(m, Plus, n), Seq(x, Plus, Plus, y));
        return All(Seq(k, Comma, m, Comma, n), Nat,
            Imp(Rel(D(2), Leq, k),
                And(
                    All(x, Word(m), All(y, Word(n), Imp(legal,
                        And(Rel(Fn("t", x), Lt, k), Rel(Fn("p", y), Lt, k),
                            Rel(join, Iff, Rel(Seq(Fn("t", x), Plus, Fn("p", y)), Lt, k)))))),
                    All(Seq(s, Comma, u), Nat,
                        Imp(Rel(s, Leq, u), Rel(Fn("B", k, n, u), Subseteq, Fn("B", k, n, s)))),
                    Rel(Fn("B", k, n, Seq(k, Minus, D(1))), Eq, Emptyset),
                    All(x, Word(m), All(y, Word(n), Imp(legal,
                        Imp(Rel(OpCall("head", y), Eq, OpCall("some", Op("false"))), join)))))));
    }

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Word(Formula width) => Seq(Open,
        OpCall("Fin", width), Sp, To, Sp, Op("Bool"), Close);
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Fn(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula OpCall(string name, params Formula[] arguments) => new Formula.Apply(Op(name), [.. arguments]);
    private static Formula Rel(Formula left, Formula relation, Formula right) => Seq(left, Sp, relation, Sp, right);
    private static Formula Par(Formula content) => Seq(Open, content, Close);
    private static Formula All(Formula variables, Formula type, Formula body) => Par(Seq(
        Forall, Sp, Open, variables, Colon, type, Close, Comma, Sp, Par(body)));
    private static Formula Imp(Formula premise, Formula conclusion) => Par(Rel(Par(premise), Implies, Par(conclusion)));
    private static Formula And(params Formula[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < parts.Length; i++)
        {
            if (i > 0) items.Add(Seq(Sp, Land, Sp));
            items.Add(Par(parts[i]));
        }
        return Par(Seq([.. items]));
    }
}
