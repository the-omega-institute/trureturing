using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class RetainedDepthExactImageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite complete-bundle cuts characterize the exact retained-depth image of a single code.",
        H("Exact Images under Retained-Depth Expansion"),
        Blocks(
            Paragraph(Text(
                "Let A be any finite alphabet with at least two letters. Words are finite lists "
                + "over A, including the empty list. The relation w <=prefix g means that g is "
                + "w followed by some suffix. A code is prefix-free when comparable members are "
                + "equal. Let s be a strictly increasing sequence of natural depths starting at "
                + "zero and unbounded above. Segment j, indexed from zero, is (s(j), s(j+1)].")),
            new DocumentBlock.DisplayFormula(RetainedFormula()),
            Paragraph(Text(
                "firstDepth(s,n) is s(k), where k is the least index with n <= s(k). "
                + "D(s,F) contains every word g extending some w in F with length equal to "
                + "firstDepth(s,length(w)). Thus it retains the whole descendant bundle, rather "
                + "than one selected suffix. The original code F may be infinite. "
                + "Legal(b,F) uses the same original depths: F is prefix-free, excludes the empty "
                + "word, and has at most b(n) words of each length n, for every natural n.")),
            new DocumentBlock.DisplayFormula(ExpansionFormula()),
            new DocumentBlock.DisplayFormula(LegalFormula()),
            Paragraph(Text(
                "Fix a prefix-free target code G whose words all have positive retained lengths. "
                + "Write G(j) for its words of length s(j+1). The finite set B(j) consists of words "
                + "w in segment j such that every length s(j+1) descendant of w belongs to G(j). "
                + "The lower endpoint is excluded and the upper endpoint is allowed. "
                + "A Boolean selection x on all words represents a zero-or-one selection on B(j); "
                + "its values outside B(j) have no effect and any selection on B(j) extends to one "
                + "on all words.")),
            new DocumentBlock.DisplayFormula(AvailableFormula()),
            Paragraph(Text(
                "Equations(s,G,b,j,x) is the conjunction of the following two systems. "
                + "For every target leaf the selected ancestor count is exactly one. At every "
                + "depth strictly above the lower endpoint and at most the upper endpoint, the "
                + "selected word count respects the original budget. Here indicator(x,w) equals "
                + "one when x(w) is true and zero otherwise.")),
            new DocumentBlock.DisplayFormula(LeafFormula()),
            new DocumentBlock.DisplayFormula(BudgetFormula()),
            Describe.Lean(
                DescribeId.Create("retained-depth-exact-image"),
                DeclarationHandle.Create("D5/S0/Computability/Coding/RetainedDepthExactImage.result"),
                H("The exact image criterion"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In the forward direction take, in each segment, the words of the same "
                        + "legal F lying in that segment. Their complete bundles lie in G. "
                        + "Prefix freedom gives a unique old ancestor of every target leaf. "
                        + "The depth budget is inherited from F.")),
                    Paragraph(Text(
                        "For the reverse direction fix one feasible finite cut C(j) at every "
                        + "segment and form the single union F of these cuts. The Boolean sums "
                        + "are cardinalities of filtered finite sets. Unique leaf coverage gives "
                        + "a finite partition of G(j) into the full descendant bundles.")),
                    Paragraph(Text(
                        "Within one segment, two comparable selected ancestors would both cover "
                        + "a descendant of the deeper word, contradicting uniqueness. Across "
                        + "segments j < k, suppose an early ancestor w prefixes a later ancestor v. "
                        + "The word t obtained by truncating v to depth s(j+1) lies in G, by the "
                        + "complete bundle of w. A full extension g of v to depth s(k+1) also lies "
                        + "in G. Now t prefixes g, with strictly smaller length, contradicting "
                        + "the prefix freedom of that same G. The opposite prefix direction is "
                        + "excluded by the segment lengths.")),
                    Paragraph(Text(
                        "Each positive depth belongs to exactly one segment, so the union has "
                        + "exactly that segment's selected words at the depth and satisfies all "
                        + "budgets. It excludes the root. Full bundles give D(s,F) contained in G; "
                        + "the finite partitions cover every target leaf and give the reverse "
                        + "inclusion. Both directions therefore refer to one global F. "
                        + "Empty target levels and zero budgets are included. The existence "
                        + "statement makes no computability or running-time assertion."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/Coding/PrefixFreeCode")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality"))]));

    private static Formula RetainedFormula() => Disp(F.Seq(
        Call("Retained", F.Id("s")), Sp, Iff, Sp,
        Call("s", D(0)), Sp, Eq, Sp, D(0), Sp, Land, Sp,
        Call("StrictMono", F.Id("s")), Sp, Land, Sp,
        Open, Forall, Sp, F.Id("N"), Comma, Sp, Exists, Sp, F.Id("k"), Comma, Sp,
        F.Id("N"), Sp, Le, Sp, Call("s", F.Id("k")), Close));

    private static Formula ExpansionFormula() => Disp(F.Seq(
        F.Id("g"), Sp, InMacro, Sp, Call("D", F.Id("s"), F.Id("F")), Sp, Iff, Sp,
        Exists, Sp, F.Id("w"), Sp, InMacro, Sp, F.Id("F"), Comma, Sp,
        Call("prefix", F.Id("w"), F.Id("g")), Sp, Land, Sp,
        Call("length", F.Id("g")), Sp, Eq, Sp,
        Call("firstDepth", F.Id("s"), Call("length", F.Id("w")))));

    private static Formula AvailableFormula() => Disp(F.Seq(
        F.Id("w"), Sp, InMacro, Sp, Call("B", F.Id("j")), Sp, Iff, Sp,
        Call("s", F.Id("j")), Sp, Lt, Sp, Call("length", F.Id("w")), Sp, Le, Sp,
        Call("s", F.Seq(F.Id("j"), Plus, D(1))), Sp, Land, Sp,
        Open, Forall, Sp, F.Id("g"), Comma, Sp,
        Call("length", F.Id("g")), Sp, Eq, Sp, Call("s", F.Seq(F.Id("j"), Plus, D(1))),
        Sp, Land, Sp, Call("prefix", F.Id("w"), F.Id("g")), Sp, Rightarrow, Sp,
        F.Id("g"), Sp, InMacro, Sp, F.Id("G"), Close));

    private static Formula LegalFormula() => Disp(F.Seq(
        Call("Legal", F.Id("b"), F.Id("F")), Sp, Iff, Sp,
        Call("IsPrefixFree", F.Id("F")), Sp, Land, Sp,
        Neg, Open, Call("emptyWord"), Sp, InMacro, Sp, F.Id("F"), Close, Sp, Land, Sp,
        Open, Forall, Sp, F.Id("n"), Sp, InMacro, Sp, F.Id("Nat"), Comma, Sp,
        Call("card", F.Seq(OpenBrace, F.Id("w"), Sp, InMacro, Sp, F.Id("F"), Sp, Mid, Sp,
            Call("length", F.Id("w")), Sp, Eq, Sp, F.Id("n"), CloseBrace)),
        Sp, Le, Sp, Call("b", F.Id("n")), Close));

    private static Formula LeafFormula() => Disp(F.Seq(
        Forall, Sp, F.Id("g"), Sp, InMacro, Sp, Call("G", F.Id("j")), Comma, Sp,
        Sum, Underscore, F.Grp(Open, F.Id("w"), Sp, InMacro, Sp, Call("B", F.Id("j")), Comma,
            Sp, Call("prefix", F.Id("w"), F.Id("g")), Close), Sp,
        Call("indicator", F.Id("x"), F.Id("w")), Sp, Eq, Sp, D(1)));

    private static Formula BudgetFormula() => Disp(F.Seq(
        Forall, Sp, F.Id("n"), Comma, Sp, Call("s", F.Id("j")), Sp, Lt, Sp,
        F.Id("n"), Sp, Le, Sp, Call("s", F.Seq(F.Id("j"), Plus, D(1))), Sp, Rightarrow, Sp,
        Sum, Underscore, F.Grp(Open, F.Id("w"), Sp, InMacro, Sp, Call("B", F.Id("j")), Comma,
            Sp, Call("length", F.Id("w")), Sp, Eq, Sp, F.Id("n"), Close), Sp,
        Call("indicator", F.Id("x"), F.Id("w")), Sp, Le, Sp, Call("b", F.Id("n"))));

    private static Formula MainFormula() => Disp(F.Seq(
        Forall, Sp, F.Id("A"), Comma, Sp, Call("Finite", F.Id("A")), Sp, Land, Sp,
        D(2), Sp, Le, Sp, Call("card", F.Id("A")), Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("s"), Sp, Colon, Sp, F.Seq(F.Id("Nat"), Rightarrow, F.Id("Nat")), Comma, Sp,
        Call("Retained", F.Id("s")), Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("b"), Sp, Colon, Sp, F.Seq(F.Id("Nat"), Rightarrow, F.Id("Nat")), Comma, Sp,
        Forall, Sp, F.Id("G"), Sp, Subseteq, Sp, Call("Words", F.Id("A")), Comma, Sp,
        Call("IsPrefixFree", F.Id("G")), Sp, Land, Sp,
        Open, Forall, Sp, F.Id("g"), Sp, InMacro, Sp, F.Id("G"), Comma, Sp,
        Exists, Sp, F.Id("j"), Sp, InMacro, Sp, F.Id("Nat"), Comma, Sp,
        Call("length", F.Id("g")), Sp, Eq, Sp, Call("s", F.Seq(F.Id("j"), Plus, D(1))), Close,
        Sp, Rightarrow, Sp,
        Open, Exists, Sp, F.Id("F"), Sp, Subseteq, Sp, Call("Words", F.Id("A")), Comma, Sp,
        Call("Legal", F.Id("b"), F.Id("F")), Sp, Land, Sp,
        Call("D", F.Id("s"), F.Id("F")), Sp, Eq, Sp, F.Id("G"), Close, Sp, Iff, Sp,
        Open, Forall, Sp, F.Id("j"), Sp, InMacro, Sp, F.Id("Nat"), Comma, Sp,
        Exists, Sp, F.Id("x"), Sp, Colon, Sp, F.Seq(Call("Words", F.Id("A")), Rightarrow, F.Id("Bool")),
        Comma, Sp, Call("Equations", F.Id("s"), F.Id("G"), F.Id("b"), F.Id("j"), F.Id("x")), Close));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
