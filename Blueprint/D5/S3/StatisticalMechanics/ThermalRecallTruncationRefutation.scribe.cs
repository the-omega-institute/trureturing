using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class ThermalRecallTruncationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/czartowskideoliveirajuniorkorzekwa2023thermalrecall");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Removing intermediate memory resets increases the permutation approximation error in a finite reduced protocol.",
        H("A finite counterexample to improved thermal recall convergence"),
        Blocks(
            Paragraph(Text(
                "The system has d levels and the memory has n levels. Joint states are real-valued functions "
                    + "on Fin d × Fin n. The source defines the two-level thermalisation in TR.tex lines 269–275, "
                    + "the sequential rounds and truncated protocol in lines 289–296, the memory reset in lines 305–312, "
                    + "and the composed protocols in lines 315–324. At infinite temperature each elementary step "
                    + "is the average of the two selected entries, and the memory starts uniformly.")),
            Node("average", "Two-level averaging", AverageFormula(),
                "At infinite temperature, replace the values at two joint states a and b by their average and leave every other value unchanged. This is the infinite-temperature form of the source's two-level thermalisation (TR.tex lines 269–275).",
                AssessedProvenance.FromLiterature(Source)),
            Node("block", "A sequential thermalisation block", BlockFormula(),
                "For a transposition of system levels i and j, process every memory level k of i in increasing order; for each k, average it successively with every memory level l of j in increasing order. The nested list folds implement the N rounds and the N steps in each round described in TR.tex lines 289–296.",
                AssessedProvenance.FromLiterature(Source)),
            Node("joint", "A system state with uniform memory", JointFormula(),
                "Couple a system population p to a uniform memory. Each joint entry is p at its system level multiplied by the inverse of the real memory dimension, matching the infinite-temperature memory state in TR.tex lines 289–291 and 338.",
                AssessedProvenance.FromLiterature(Source)),
            Node("reset", "Memory reset", ResetFormula(),
                "Sum a joint state over the memory coordinate to obtain the system marginal, then tensor that marginal with a uniform memory. This is the full memory thermalisation from TR.tex lines 305–308.",
                AssessedProvenance.FromLiterature(Source)),
            Node("truncatedOutput", "Output without intermediate resets", TruncatedOutputFormula(),
                "Start from the joint state and apply the blocks in the word successively, with no reset between blocks. Return the system marginal, corresponding to the truncated composite protocol in TR.tex lines 293–296 and 321–322.",
                AssessedProvenance.FromLiterature(Source)),
            Node("resetOutput", "Output with intermediate resets", ResetOutputFormula(),
                "Start from the joint state and apply each block followed immediately by a memory reset. Return the final system marginal, corresponding to the reset protocol in TR.tex lines 309–322.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsReducedNeighbourWord", "Reduced neighbour word", ReducedWordFormula(),
                "A word is reduced and neighbour-admissible when every position exchanges an increasing pair of system indices that is adjacent in the current population order and whose two values remain in their original relative order. The current order is obtained by applying the preceding swaps to p. This formalizes the reduced neighbour-transposition condition in TR.tex lines 315–325.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Improved convergence for reduced words", ClaimFormula(),
                "For every positive memory dimension, nonnegative system population of total mass one, strictly decreasing population, and reduced neighbour word, the total variation distance from the ideal swapped population is no larger without intermediate resets than with them. This is the repository's formal reading of the improved-convergence conjecture stated in TR.tex lines 417–427.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("thermal-recall-truncation-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A four-level counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use four system levels, two memory levels, the strictly decreasing probability vector "
                            + "(1/2, 1/4, 2/9, 1/36), and the word ((0,1),(2,3),(0,3)). The three swaps are adjacent "
                            + "in the successive orders 0123, 1023, 1032, so the word satisfies the reduced-neighbour condition.")),
                    Paragraph(Text(
                        "The probability and strict-order hypotheses follow by checking the four coordinates. Evaluating "
                            + "the three blocks gives the ideal population (2/9, 1/2, 1/36, 1/4), the truncated output "
                            + "(31/144, 13/32, 29/288, 5/18), and the reset output (2/9, 13/32, 29/288, 13/48).")),
                    Paragraph(Text(
                        "The exact finite sums defining total variation then give the identity that the distance to the "
                            + "truncated output equals the distance to the reset output plus 1/144. Applying the claimed "
                            + "inequality to this instance contradicts that positive gap, so the universal claim is false."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(
        string declaration, string title, Formula formula, string prose,
        AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("thermal-recall-truncation-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula QCall(string owner, string name, params Formula[] arguments) =>
        At(Qualified(owner, name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula PairType(Formula left, Formula right) =>
        Seq(Fin(left), Sp, Times, Sp, Fin(right));
    private static Formula Pair(Formula left, Formula right) =>
        Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula NatToReal(Formula value) => Cast(value, Real());
    private static Formula Inverse(Formula value) =>
        new Formula.Power(Parenthesized(value), new Formula.Negate(D(1)));
    private static Formula ListOf(Formula type) => Call("List", type);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp,
            Mapsto, Sp, Parenthesized(body));
    private static Formula Let(string name, Formula value, Formula body) =>
        Seq(Named("let"), Sp, V(name), Sp, Eq, Sp, value, Semi, Sp, body);
    private static Formula Index(Formula list, Formula index) =>
        Seq(list, OpenBracket, index, CloseBracket);
    private static Formula Fst(Formula value) => Seq(value, Dot, D(1));
    private static Formula Snd(Formula value) => Seq(value, Dot, D(2));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Not(Formula value) => new Formula.Not(Parenthesized(value));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula SumOver(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Colon, Sp, domain)), Sp, Parenthesized(body));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp, yes,
            Sp, Named("else"), Sp, no);
    private static Formula App(Formula function, params Formula[] arguments) => At(function, arguments);

    private static Formula AverageFormula()
    {
        Formula d = V("d"), n = V("n"), a = V("a"), b = V("b"), v = V("v"), x = V("x");
        Formula domain = PairType(d, n);
        Formula value = If(Or(Equal(x, a), Equal(x, b)),
            new Formula.Fraction(Parenthesized(Seq(App(v, a), Sp, Plus, Sp, App(v, b))), D(2)),
            App(v, x));
        return All("d", Nat(), All("n", Nat(), All("a", domain, All("b", domain,
            All("v", Arrow(domain, Real()), All("x", domain,
                Equal(App(Call("average", a, b, v), x), value)))))));
    }

    private static Formula BlockFormula()
    {
        Formula d = V("d"), n = V("n"), i = V("i"), j = V("j"), v = V("v");
        Formula domain = PairType(d, n), state = Arrow(domain, Real());
        Formula u = V("u"), k = V("k"), l = V("l");
        Formula inner = Lambda("u", state, Lambda("l", Fin(n),
            Call("average", Pair(i, k), Pair(j, l), u)));
        Formula outer = Lambda("u", state, Lambda("k", Fin(n),
            QCall("List", "foldl", inner, u, QCall("List", "finRange", n))));
        Formula folded = QCall("List", "foldl", outer, v, QCall("List", "finRange", n));
        return All("d", Nat(), All("n", Nat(), All("i", Fin(d), All("j", Fin(d),
            All("v", state, Equal(Call("block", n, i, j, v), folded))))));
    }

    private static Formula JointFormula()
    {
        Formula d = V("d"), n = V("n"), p = V("p");
        Formula domain = PairType(d, n);
        Formula uniform = At(Qualified("Function", "const"), Fin(d),
            At(Qualified("Function", "const"), Fin(n), Inverse(NatToReal(n))));
        return All("d", Nat(), All("n", Nat(), All("p", Arrow(Fin(d), Real()),
            Equal(Call("joint", n, p), App(Call("mixtureJoint", p), uniform)))));
    }

    private static Formula ResetFormula()
    {
        Formula d = V("d"), n = V("n"), v = V("v");
        Formula domain = PairType(d, n), state = Arrow(domain, Real());
        return All("d", Nat(), All("n", Nat(), All("v", state,
            Equal(Call("reset", v), Call("joint", n, Call("marginal", v))))));
    }

    private static Formula TruncatedOutputFormula()
    {
        Formula d = V("d"), n = V("n"), p = V("p"), w = V("w"), v = V("v"), z = V("z");
        Formula pair = PairType(d, d), state = Arrow(PairType(d, n), Real());
        Formula step = Lambda("v", state, Lambda("z", pair,
            App(Call("block", n, Fst(z), Snd(z)), v)));
        Formula folded = QCall("List", "foldl", step, Call("joint", n, p), w);
        return All("d", Nat(), All("n", Nat(), All("p", Arrow(Fin(d), Real()),
            All("w", ListOf(pair), Equal(Call("truncatedOutput", n, p, w),
                Call("marginal", folded))))));
    }

    private static Formula ResetOutputFormula()
    {
        Formula d = V("d"), n = V("n"), p = V("p"), w = V("w"), v = V("v"), z = V("z");
        Formula pair = PairType(d, d), state = Arrow(PairType(d, n), Real());
        Formula step = Lambda("v", state, Lambda("z", pair,
            Call("reset", App(Call("block", n, Fst(z), Snd(z)), v))));
        Formula folded = QCall("List", "foldl", step, Call("joint", n, p), w);
        return All("d", Nat(), All("n", Nat(), All("p", Arrow(Fin(d), Real()),
            All("w", ListOf(pair), Equal(Call("resetOutput", n, p, w),
                Call("marginal", folded))))));
    }

    private static Formula ReducedWordFormula()
    {
        Formula d = V("d"), p = V("p"), w = V("w"), n = V("n"), z = V("z"), r = V("r"), c = V("c");
        Formula pair = PairType(d, d);
        Formula current = Call("applySwaps", p, QCall("List", "take", n, w));
        Formula conditions = And(Less(Fst(z), Snd(z)),
            And(Less(App(r, Snd(z)), App(r, Fst(z))),
                All("c", Fin(d), Not(And(Less(App(r, Snd(z)), App(r, c)),
                    Less(App(r, c), App(r, Fst(z))))))));
        Formula body = All("n", Nat(), Imp(Less(n, QCall("List", "length", w)),
            Let("z", Index(w, n), Let("r", current, conditions))));
        return All("d", Nat(), All("p", Arrow(Fin(d), Real()), All("w", ListOf(pair),
            Iff(Call("IsReducedNeighbourWord", p, w), body))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = V("d"), n = V("n"), p = V("p"), w = V("w"), i = V("i");
        Formula population = All("i", Fin(d), Leq(D(0), App(p, i)));
        Formula mass = Equal(SumOver("i", Fin(d), App(p, i)), Cast(D(1), Real()));
        Formula target = Call("applySwaps", p, w);
        Formula conclusion = Leq(Call("totalVariation", target, Call("truncatedOutput", n, p, w)),
            Call("totalVariation", target, Call("resetOutput", n, p, w)));
        Formula hypotheses = Imp(Less(D(0), n), Imp(population,
            Imp(mass, Imp(Call("StrictAnti", p), Imp(Call("IsReducedNeighbourWord", p, w), conclusion)))));
        return Iff(Named("claim"), All("d", Nat(), All("n", Nat(),
            All("p", Arrow(Fin(d), Real()), All("w", ListOf(PairType(d, d)), hypotheses)))));
    }
}
