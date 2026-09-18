using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class ShiehYangYuMachineConvergenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/yangshiehyu2025dotted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every permutation eventually reaches a fixed point of the 21̇-machine.",
        H("Convergence of the Shieh-Yang-Yu Machine"),
        Blocks(
            Paragraph(Text(
                "The source defines s_{21̇} through Baril's dotted patterns and PROVES the closed "
                + "form of Proposition 3.5; this module takes that proved right-hand side "
                + "(reverse each valley run) as the definition of `r`. The identification of "
                + "the dotted-pattern stack with valley-run reversal is the source's own theorem "
                + "and is NOT formalized here.")),
            Paragraph(Text(
                "Words are lists of natural numbers. List, cons, nil, map, flatten, reverse, "
                + "takeWhile, and dropWhile have their Lean list meanings. The Boolean predicate "
                + "p(v,x) is decide(v ≤ x). Perm is List.Perm, and range'(1,n) is the list "
                + "[1,...,n]. The notation Mᵗ(w) means "
                + "Function.iterate M t w, so M⁰(w)=w. "
                + "The cited paper supplies the definitions and the conjecture; the convergence "
                + "proof below is new here. Conjecture 6.1 concerns a different machine.")),
            Node("IsValley", "Valleys", ValleyFormula(),
                "Section 2 (printed p. 3): “Similarly, a valley of π is an entry πᵢ of π such "
                + "that πᵢ is less than each π₁, π₂, . . . , πᵢ₋₁.” The argument earlier is the "
                + "prefix before entry; an empty prefix makes the first entry a valley.",
                DescribeRole.Definition),
            Node("valleyRuns", "The valley-run decomposition", RunsFormula(),
                "Section 2 (printed p. 3): “Similarly, a valley run is defined as a maximal "
                + "sequence of consecutive entries such that the first entry is a valley and "
                + "no other entry is a valley.” The source example is 24315, whose valley runs "
                + "are 243 and 15. Starting with v, takeWhile retains entries at least v, and "
                + "dropWhile starts the next run at the first smaller entry. On permutations "
                + "this gives the source's unique partition; the functions also accept arbitrary lists.",
                DescribeRole.Definition),
            Node("r", "Reverse each valley run", ReversalFormula(),
                "Proposition 3.5 (printed p. 6): “Let π = V₁V₂ . . . Vₖ ∈ Sₙ. Then, "
                + "s₂₁̇(π) = rev(V₁)rev(V₂) . . . rev(Vₖ).” Here valleyRuns(w) is the list "
                + "[V₁,...,Vₖ], map reverses each member, and flatten concatenates the reversed "
                + "runs in their original order. This displayed right-hand side defines r.",
                DescribeRole.Definition),
            Node("s", "West's operational stack map", WestFormula(),
                "Section 1 (printed p. 1): “West’s stack-sorting map s processes the input "
                + "permutation through a stack in a right greedy manner such that elements "
                + "of the stack always increase from top to bottom (see for example, Figure 1).” "
                + "The auxiliary westRun has stack head as top. It pops a top a when a < x, "
                + "pushes x otherwise, and returns the remaining stack when input is empty. "
                + "The equations below give this pop/push/flush algorithm, starting from nil.",
                DescribeRole.Definition),
            Node("M", "The machine applies r before s", MachineFormula(),
                "Section 1 (printed p. 2): “Similarly, inspired by Cerbai, Claesson, and "
                + "Ferrari’s [6] σ-machines, we establish τ̇-machines, which consist of the "
                + "dotted pattern-avoiding map sτ̇ followed by s, and are to be denoted by "
                + "s ◦ sτ̇.” The displayed composition specializes this order to the 21̇-machine, "
                + "using Proposition 3.5 for its first map.", DescribeRole.Definition),
            Node("result", "Every permutation reaches a fixed point", ResultFormula(),
                "Conjecture 6.2 (printed p. 11): “All permutations in Sₙ for all n ≥ 1 are "
                + "eventually mapped to a fixed point of the 21̇-machine after a finite number "
                + "of iterations through the machine.” A permutation in Sₙ is encoded by "
                + "Perm(w,range'(1,n)); n and t are natural numbers. Equality of successive "
                + "iterates says precisely that Mᵗ(w) is fixed. Both component maps preserve "
                + "the multiset of entries. Strong induction on word length proves that "
                + "reverse(w) ≤ reverse(M(w)) in lexicographic order for every word without "
                + "repetitions. Choose a reachable word with maximal reversed word in the "
                + "finite set of permutations. The inequality is then an equality, and "
                + "injectivity of reverse gives the fixed point.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("syy-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula ValleyFormula() => Disp(All("earlier", Words(),
        All("entry", Naturals(), IffOf(Call("IsValley", Id("earlier"), Id("entry")),
            Parenthesized(All("a", Naturals(), Imp(
                Rel(Id("a"), FormulaRelationOperator.MemberOf, Id("earlier")),
                LtOf(Id("entry"), Id("a")))))))));

    private static Formula RunsFormula()
    {
        var v = Id("v");
        var tail = Id("tail");
        var predicate = Parenthesized(Seq(Id("x"), Sp, Mapsto, Sp,
            Call("decide", Parenthesized(LeOf(v, Id("x"))))));
        return Disp(new Formula.Aligned([
            EqOf(Call("valleyRuns", Nil()), Nil()),
            All("v", Naturals(), All("tail", Words(),
                EqOf(Call("valleyRuns", Cons(v, tail)),
                    Cons(Cons(v, Call("takeWhile", predicate, tail)),
                        Call("valleyRuns", Call("dropWhile", predicate, tail))))))
        ]));
    }

    private static Formula ReversalFormula() => Disp(All("w", Words(),
        EqOf(Call("r", Id("w")), Call("flatten",
            Call("map", Id("reverse"), Call("valleyRuns", Id("w")))))));

    private static Formula WestFormula()
    {
        var x = Id("x");
        var xs = Id("xs");
        var a = Id("a");
        var rest = Id("rest");
        var state = Call("westRun", Cons(a, rest), Cons(x, xs));
        Formula variables(Formula body) => All("x", Naturals(), All("xs", Words(),
            All("a", Naturals(), All("rest", Words(), body))));
        Formula[] clauses = [
            All("w", Words(), EqOf(Call("s", Id("w")), Call("westRun", Nil(), Id("w")))),
            All("stack", Words(), EqOf(Call("westRun", Id("stack"), Nil()), Id("stack"))),
            All("x", Naturals(), All("xs", Words(),
                EqOf(Call("westRun", Nil(), Cons(x, xs)), Call("westRun", Cons(x, Nil()), xs)))),
            variables(Imp(LtOf(a, x), EqOf(state, Cons(a, Call("westRun", rest, Cons(x, xs)))))),
            variables(Imp(LeOf(x, a), EqOf(state, Call("westRun", Cons(x, Cons(a, rest)), xs))))
        ];
        Formula body = Parenthesized(clauses[0]);
        foreach (var clause in clauses.Skip(1))
            body = new Formula.Logic(body, FormulaLogicOperator.And, Parenthesized(clause));
        return Disp(new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("westRun"),
            new Formula.TypeArrow(Words(), new Formula.TypeArrow(Words(), Words())), body));
    }

    private static Formula MachineFormula() => Disp(All("w", Words(),
        EqOf(Call("M", Id("w")), Call("s", Call("r", Id("w"))))));

    private static Formula ResultFormula() => Disp(All("n", Naturals(),
        Imp(LeOf(D(1), Id("n")), All("w", Words(),
            Imp(Call("Perm", Id("w"), new Formula.Apply(Seq(Id("range"), Apos), [D(1), Id("n")])),
                new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("t"),
                    Naturals(), EqOf(Iterate(new Formula.Binary(Id("t"),
                        FormulaBinaryOperator.Add, D(1))), Iterate(Id("t")))))))));

    private static Formula Iterate(Formula exponent) =>
        new Formula.Apply(new Formula.Power(Id("M"), exponent), [Id("w")]);
    private static Formula Naturals() => Seq(Mathbb, Grp(Id("N")));
    private static Formula Words() => Call("List", Naturals());
    private static Formula Nil() => Call("nil");
    private static Formula Cons(Formula head, Formula tail) => Call("cons", head, tail);
    private static Formula Id(string value) => F.Id(value);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Id(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Rel(Formula left, FormulaRelationOperator operation, Formula right) =>
        new Formula.Relation(left, operation, right);
    private static Formula EqOf(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula LtOf(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThan, right);
    private static Formula LeOf(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
}
