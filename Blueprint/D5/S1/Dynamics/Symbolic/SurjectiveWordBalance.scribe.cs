using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class SurjectiveWordBalanceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/SurjectiveWordBalance.";
    private static readonly LibraryNoteRef Balance =
        LibraryNoteRef.Create("D5/L/Entropy/hellouinsalotorma2025frequencies");
    private static Formula Id(string s) => F.Id(s);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Arr(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Call(string s, params Formula[] args)
    {
        var name = new List<Formula>();
        foreach (var part in s.Split('.'))
        {
            if (name.Count > 0) name.Add(Dot);
            name.Add(Id(part));
        }
        var items = new List<Formula> { Seq(Operatorname, Grp(Seq([.. name]))), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), Colon, Sp, t, Comma);
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static Formula Word(Formula n) => Arr(Call("Fin", n), Id("A"));
    private static Formula Width => Add(Id("k"), D(1));
    private static Formula Length => Add(Add(Id("n"), Id("k")), D(1));
    private static Formula Rule => Arr(Word(Add(Id("k"), D(2))), Id("A"));
    private static Formula Alphabet => Seq(All("u", Call("Universe")),
        All("A", Call("Type", Id("u"))));
    private static Formula Window => Seq(Open, Id("j"), Colon, Sp,
        Call("Fin", Add(Id("k"), D(2))), Sp, Mapsto, Sp,
        Call("p", Add(Call("val", Id("i")), Call("val", Id("j")))), Close);
    private static Formula Condition => Seq(All("i", Call("Fin", Id("n"))), Sp,
        Call("h", Window), Sp, Eq, Sp, Call("w", Id("i")));
    private static Formula Fiber => Seq(OpenBrace, Id("p"), Colon, Sp, Word(Length),
        Sp, Mid, Sp, Condition, CloseBrace);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every word has exactly card(A)^(k+1) preimages under an arbitrary surjective finite-alphabet integer block rule.",
        H("Finite-word balance"), Blocks(
        Paragraph(Text("Let A be any finite alphabet in any universe, k a natural number, and h an arbitrary rule on windows of length k+2. "
            + "The native integer code sends x to i ↦ h(j ↦ x(i+j)). Surjectivity refers to all integer configurations. "
            + "The result uses no permutation condition on either endpoint, and imposes no support or periodicity restriction.")),
        Describe.Lean(DescribeId.Create("word-map"), DeclarationHandle.Create(Owner + "wordMap"),
            H("Apply a rule to a finite word"), StatementSource.FromAuthor(St(
                Alphabet, All("k", Nat), All("h", Rule), All("n", Nat),
                All("p", Word(Length)), All("i", Call("Fin", Id("n"))),
                Seq(Call("wordMap", Id("h"), Id("p"), Id("i")), Sp, Eq, Sp, Call("h", Window)))),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("A source word has length n+k+1 and its image has length n. "
                    + "In the displayed window, p(val(i)+val(j)) means evaluation at the unique Fin(n+k+1) index with that natural value. "
                    + "The bounds i<n and j<k+2 prove that the index is in range."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("word-balance"),
            DeclarationHandle.Create(Owner + "surjective_word_balance"),
            H("Every finite output fiber has the same exact size"), StatementSource.FromAuthor(St(
                Alphabet, Seq(OpenBracket, Call("Finite", Id("A")), CloseBracket, Comma),
                All("k", Nat), All("h", Rule),
                Seq(Call("Function.Surjective", Call("BipermutativeLift.code", Id("h"))), Sp, Rightarrow),
                All("n", Nat), All("w", Word(Id("n"))),
                Seq(Call("Nat.card", Fiber), Sp, Eq, Sp,
                    Call("Nat.card", Id("A")), Caret, Grp(Width)))),
            AssessedProvenance.FromLiterature(Balance), Blocks(
                Paragraph(Text("For every universe u, every A : Type(u) with Finite(A), every natural k, every local rule h with "
                    + "Function.Surjective(BipermutativeLift.code(h)), every natural n and every word w : Fin(n) → A, "
                    + "the subtype of source words satisfying all n overlapping local equations has cardinality card(A)^(k+1). "
                    + "The telescope includes empty and singleton alphabets and n=0. There is no supplied balance or fiber certificate and no lower bound on card(A).")),
                Paragraph(Text("Write r=k+1 and L=n+r. Surjectivity gives native finite-difference preinjectivity by the Garden-of-Eden theorem. "
                    + "For a nonempty alphabet, concatenate m independently chosen source words from one fiber and insert them into a constant integer configuration. "
                    + "Each of the m length-n output blocks is the prescribed w. The remaining affected outputs form m+1 gaps, each of length r. "
                    + "Recording these gaps is injective: equal records give equal complete images, and preinjectivity identifies the inserted configurations and hence all chosen words. "
                    + "If the fiber size is t and q=card(A), this yields t^m ≤ q^(r(m+1)) for every m. "
                    + "If t>q^r, the unbounded powers of t/q^r contradict that estimate. Thus every fiber has size at most q^r. "
                    + "All q^(n+r) source words partition into q^n fibers. Their upper bounds sum to q^(n+r), so each fiber attains its bound. "
                    + "For an empty alphabet, the positive source length makes each source fiber empty; the same exact statement covers n=0.")),
                Paragraph(Text("The cited Section 2 states this classical balance property for a forward neighborhood [0,r]. "
                    + "The parameter correspondence is r=k+1. For a nonempty finite alphabet, dividing the count q^r by the q^(n+r) equally likely input words "
                    + "gives cylinder probability q^(-n), the uniform product-law preservation consequence. "
                    + "A conditional source law requires a separate probability construction. No probability assertion on an empty alphabet and no literature novelty are claimed."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/GardenOfEden"))]));
}
