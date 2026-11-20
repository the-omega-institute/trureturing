using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class AdjacentExcedanceSetDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet";
    private static readonly LibraryNoteRef ExcedancePaper =
        LibraryNoteRef.Create("D5/L/FiniteGroups/ehrenborgsteingrimsson2000excedance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An adjacent swap and two deletions split an exact-excedance permutation class.",
        H("Adjacent excedance and nonexcedance"),
        Blocks(
            Paragraph(Text("The bracket recurrence is due to Richard Ehrenborg and Einar "
                + "Steingrímsson, The excedance set of a permutation, Proposition 2.1, "
                + "DOI 10.1006/aama.1999.0671. The formalization uses zero-based positions.")),
            Node("has-exact-excedances", "HasExactExcedances", "Exact strict excedances", DescribeRole.Definition,
                "Every position j has p(j) greater than j exactly when j belongs to S."),
            Node("exact-permutations", "ExactPermutations", "Subtype of actual permutations", DescribeRole.Definition,
                "The subtype of permutations of Fin(n) whose exact strict excedance set is S."),
            Node("exact-count", "exactCount", "Cardinality of the prescribed subtype", DescribeRole.Definition,
                "Take the natural cardinality of the subtype of permutations with exact set S."),
            Node("swap-positions", "swapPositions", "Swap two input positions", DescribeRole.Definition,
                "Precompose the permutation by the transposition of positions a and b. "
                + "This acts on the type of permutations by an involution."),
            Node("delete-fixed-case", "deleteFixedCase", "Delete a fixed nonexcedance", DescribeRole.Definition,
                "Restrict to the complement of the fixed position b, and reindex positions "
                + "and values by the order embedding that skips b. The inverse extends the "
                + "permutation and fixes b."),
            Node("exact-swap-fixed-iff", "exact_swap_fixed_iff", "Swap the left hit into a fixed point",
                DescribeRole.Lemma, "The left position belongs to S and its right neighbor "
                + "does not. A permutation with set S that sends the left position to the "
                + "right one becomes a permutation fixing the right position after swapping "
                + "their inputs. The swap removes only the left position from S."),
            Node("delete-swap-set", "delete_swap_set", "Reindex the prescribed set after deletion",
                DescribeRole.Lemma, "The right position is outside S. Pulling back S with "
                + "the left position removed along the embedding skipping the right position "
                + "gives the same set as pulling back S along the embedding skipping the left."),
            Node("adjacent-ba", "adjacentBA", "The three-way adjacent bracket recurrence",
                DescribeRole.Theorem, "At an adjacent excedance and nonexcedance, split by "
                + "whether the right position is fixed, the left position hits the right "
                + "value, or neither does. The first two alternatives give the order-preserving "
                + "deletions. In the third, swapping the two inputs swaps their prescribed "
                + "membership and preserves the rest."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(Statement(name))),
            name is "adjacentBA" or "HasExactExcedances" or "ExactPermutations" or "exactCount"
                ? AssessedProvenance.FromLiterature(ExcedancePaper)
                : AssessedProvenance.FromRepo(ExcedancePaper),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Statement(string name)
    {
        var n = F.Id("n");
        var j = F.Id("j");
        var a = F.Id("a");
        var b = F.Id("b");
        var p = F.Id("p");
        var s = F.Id("S");
        var small = Call("Fin", Seq(n, Plus, D(1)));
        var large = Call("Fin", Seq(n, Plus, D(2)));
        var left = Call("castSucc", a);
        var right = Call("succ", a);
        var swapped = Call("swapPositions", left, right, p);
        var dropsLeft = Seq(s, Sp, Setminus, Sp, Singleton(left));
        var aType = Seq(Forall, Sp, a, Colon, Sp, small, Comma, Sp);
        var pType = Seq(Forall, Sp, p, Colon, Sp, Call("Perm", large), Comma, Sp);
        var count = Call("exactCount", s);
        var has = Call("HasExactExcedances", p, s);
        var both = Seq(left, Sp, InMacro, Sp, s, Sp, Land, Sp, Absent(right, s), Sp, Implies, Sp);
        return name switch
        {
            "HasExactExcedances" => Seq(Nat(n), SetBinder(s, Call("Fin", n)),
                Seq(Forall, Sp, p, Colon, Sp, Call("Perm", Call("Fin", n)), Comma, Sp),
                has, Sp, Iff, Sp, Parens(Seq(Forall, Sp, j, Colon, Sp, Call("Fin", n),
                    Comma, Sp, j, Sp, Lt, Sp, Call("p", j), Sp, Iff, Sp, j, Sp, InMacro, Sp, s))),
            "ExactPermutations" => Seq(Nat(n), SetBinder(s, Call("Fin", n)),
                Eqn(Call(name, s), SetOf(p, Call("Perm", Call("Fin", n)), has))),
            "exactCount" => Seq(Nat(n), SetBinder(s, Call("Fin", n)),
                Eqn(count, Call("card", Call("ExactPermutations", s)))),
            "swapPositions" => Seq(Nat(n), Forall, Sp, a, Comma, Sp, b, Colon, Sp,
                Call("Fin", n), Comma, Sp, Forall, Sp, p, Colon, Sp, Call("Perm", Call("Fin", n)),
                Comma, Sp, Eqn(Call(name, a, b, p), Seq(p, Sp, Circ, Sp, Call("swap", a, b)))),
            "deleteFixedCase" => Seq(Nat(n), Forall, Sp, b, Colon, Sp, small, Comma, Sp,
                SetBinder(s, small), Absent(b, s), Sp, Implies, Sp,
                SetOf(p, Call("ExactPermutations", s), Eqn(Call("p", b), b)), Sp, Equiv, Sp,
                Call("ExactPermutations", Call("preimage", Call("succAbove", b), s))),
            "exact_swap_fixed_iff" => Seq(Nat(n), aType, SetBinder(s, large), both, pType,
                Parens(Seq(has, Sp, Land, Sp, Eqn(Call("p", left), right))), Sp, Iff, Sp,
                Parens(Seq(Call("HasExactExcedances", swapped, dropsLeft), Sp, Land, Sp,
                    Eqn(Call("apply", swapped, right), right)))),
            "delete_swap_set" => Seq(Nat(n), aType, SetBinder(s, large), Absent(right, s), Sp, Implies, Sp,
                Eqn(Call("preimage", Call("succAbove", right), dropsLeft),
                    Call("preimage", Call("succAbove", left), s))),
            "adjacentBA" => Seq(Nat(n), aType, SetBinder(s, large), both,
                Eqn(count, Seq(Call("exactCount", Call("preimage", Call("swap", left, right), s)),
                    Plus, Call("exactCount", Call("preimage", Call("succAbove", right), s)),
                    Plus, Call("exactCount", Call("preimage", Call("succAbove", left), s))))),
            _ => throw new ArgumentOutOfRangeException(nameof(name))
        };
    }

    private static Formula Nat(Formula n) => Seq(Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
        Comma, Sp);
    private static Formula SetBinder(Formula s, Formula type) =>
        Seq(Forall, Sp, s, Colon, Sp, Call("Set", type), Comma, Sp);
    private static Formula SetOf(Formula x, Formula t, Formula pred) =>
        Seq(OpenBrace, Sp, x, Colon, Sp, t, Sp, Mid, Sp, pred, Sp, CloseBrace);
    private static Formula Singleton(Formula item) => Seq(OpenBrace, Sp, item, Sp, CloseBrace);
    private static Formula Absent(Formula x, Formula s) => Seq(Neg, Sp, Parens(Seq(x, Sp, InMacro, Sp, s)));
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(n))), [.. args]);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Parens(Formula f) => Seq(Open, f, Close);
}
