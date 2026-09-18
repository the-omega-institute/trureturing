using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class ZhaoVincularPreimageRefutationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/zhao2024vincular");
    private const string Encoding =
        "The letters are natural numbers with one-based permutation entries. Stack words are read "
        + "from top to bottom. The Bool flag false denotes 1-underline(23), and true denotes "
        + "3-underline(21). Underlined entries must occupy adjacent positions. The indices i and j "
        + "in Contains are zero-based Fin values; getElem! is list indexing with default zero, "
        + "and the bounds ensure that every index used here is valid. Subtraction is natural "
        + "subtraction, truncated at zero; the conjectures' lower bounds make their exponents "
        + "ordinary nonnegative differences.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zhao's maximum and second-largest vincular-stack fibre conjectures are false.",
        H("Two Vincular-Stack Preimage Conjectures Are False"),
        Blocks(
            Paragraph(Text("The right-greedy convention reads input from left to right. It pushes "
                + "the next letter if the entire proposed stack avoids the pattern, and otherwise "
                + "pops the top letter to the output and retries. After the input ends it drains "
                + "the stack. This is the Cerbai–Claesson–Ferrari convention: the source describes "
                + "right-greedy processing without a formal stack-rule definition. Its four worked "
                + "figures send 514362 to 463215, 263415, 426315, and 632415 for the four displayed "
                + "patterns; the fourth uses 1-underline(23).")),
            Node("Contains", "Whole-stack vincular containment", ContainsFormula(),
                "On page 1, Zhao writes: “When considering whether a permutation π contains a "
                + "vincular pattern σ, some elements may be required to be adjacent in π, as "
                + "indicated by underlined terms in σ. For instance, the pattern 1423 contains "
                + "12̲3̲ and 123, but avoids 1̲2̲3 and 1̲2̲3̲.” " + Encoding,
                DescribeRole.Definition, true),
            Node("decidableContains", "Decidable containment", DecisionFormula(true),
                "Unfolding Contains leaves two quantifiers over finite position types and "
                + "decidable natural-number comparisons; inferInstance supplies the decision procedure.",
                DescribeRole.Definition),
            Node("Push", "Push or pop and retry", PushFormula(),
                "The result is the pair of emitted letters and remaining stack. In the recursive "
                + "case r is Push(d,x,s). The test examines the whole proposed stack cons(x,cons(a,s)).",
                DescribeRole.Definition, true),
            Node("Process", "Process and drain", ProcessFormula(),
                "The first list is unprocessed input and the second is the stack. Append is list "
                + "concatenation, and fst and snd are the two projections of a pair.",
                DescribeRole.Definition, true),
            Node("SC", "The right-greedy map", SCFormula(),
                "Processing starts with the empty stack nil. The map is defined on all natural-number "
                + "words, and its fibres below restrict the inputs to permutations.",
                DescribeRole.Definition, true),
            Node("IsPerm", "Permutations on one-based entries", IsPermFormula(),
                "Perm is List.Perm. The list List.range' 1 n is the entries 1 through n in increasing order.",
                DescribeRole.Definition, true),
            Node("decidableIsPerm", "Decidable permutation membership", DecisionFormula(false),
                "Unfolding IsPerm gives decidable list permutation on natural-number entries; "
                + "inferInstance supplies the decision procedure.", DescribeRole.Definition),
            Node("Sn", "Enumeration of all permutations", SnFormula(),
                "List.permutations' is the structural permutation enumerator. "
                + "Its membership is List.Perm with the original list. Because List.range' 1 n has "
                + "distinct entries, this enumeration has no repetitions.", DescribeRole.Definition),
            Node("Fibre", "The finite preimage set", FibreFormula(),
                "List.filter keeps exactly the inputs t for which SC(d,t) equals p; beq denotes "
                + "the Boolean equality test. Converting to a Finset counts each input once.",
                DescribeRole.Definition, true),
            Node("F", "Fibre cardinality", FFormula(),
                "The count includes precisely the permutations in the input fibre.",
                DescribeRole.Definition, true),
            Node("MaximumIs", "An attained maximum", MaximumFormula(),
                "The value m is attained at an output permutation and bounds every output "
                + "permutation's fibre size. Both clauses are part of the definition.",
                DescribeRole.Definition),
            Node("SecondLargestIs", "Second-largest distinct fibre size", SecondFormula(),
                "The value k is attained, a larger value m is attained, and every value above k "
                + "equals m. Thus second-largest refers to distinct values, including zero when "
                + "it occurs, rather than to a list with repetitions.", DescribeRole.Definition),
            Node("Multiplicity", "Multiplicity of a fibre size", MultiplicityFormula(),
                "This counts output permutations p with F(false,n,p)=k. It uses the same "
                + "repetition-free enumeration Sn(n), including outputs whose fibre is empty.",
                DescribeRole.Definition, true),
            Node("claimMaximum", "Zhao's Conjecture 4.14", ClaimFormula(true),
                "Conjecture 4.14 (arXiv:2410.17057v1, Section 4.1.4, printed page 17) reads: "
                + "“For n ≥ 2, it holds that max_{π∈𝔖ₙ}|SC₁₂̲₃̲⁻¹(π)| = "
                + "max_{π∈𝔖ₙ}|SC₃₂̲₁̲⁻¹(π)| = 2ⁿ⁻².” " + Encoding
                + " The chain of equalities is encoded by the two attained maxima each equalling "
                + "2^(n-2), with both conjuncts under the same quantifier and lower bound.",
                DescribeRole.Definition, true),
            Node("claimSecondLargest", "Zhao's Conjecture 5.2", ClaimFormula(false),
                "Conjecture 5.2 (arXiv:2410.17057v1, Section 5, printed page 20) reads: "
                + "“The second-largest number of preimages under SC₁₂̲₃̲ that a permutation in 𝔖ₙ "
                + "can have is 2ⁿ⁻³, for n ≥ 3. Furthermore, the number of permutations π ∈ 𝔖ₙ "
                + "satisfying |SC₁₂̲₃̲⁻¹(π)| = 2ⁿ⁻³ is 2n − 2.” " + Encoding
                + " The second-largest-value clause and the multiplicity clause are both retained "
                + "under the same universal quantifier. The carrier 𝔖ₙ is expressed by IsPerm(n,p).",
                DescribeRole.Definition, true),
            Node("resultMaximum", "The maximum claim is false", Disp(new Formula.Not(Id("claimMaximum"))),
                "At n=9, 129 explicitly listed distinct permutations map to 765432819 under the "
                + "false flag. Each mapping and permutation membership is checked separately. "
                + "The claimed maximum would bound that fibre by 2^7=128, contradicting its "
                + "cardinality lower bound. An exact maximum for n=9 is not needed.", DescribeRole.Theorem),
            Node("resultSecondLargest", "The second-largest claim is false", Disp(new Formula.Not(Id("claimSecondLargest"))),
                "Enumeration of all 120 input permutations at n=5 gives F(false,5,32415)=5 and "
                + "F(false,5,43215)=8. These are distinct fibre values greater than 2^2=4, which "
                + "contradicts the asserted uniqueness of a larger value. This refutes the "
                + "conjunction through its first clause; the multiplicity clause is not separately refuted.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, bool literature = false) => Describe.Lean(
        DescribeId.Create("zhao-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), literature
            ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula ContainsFormula()
    {
        var w = Id("w"); var i = Call("val", Id("i")); var j = Call("val", Id("j"));
        var a = new Formula.Apply(Seq(Id("getElem"), Bang), [w, i]);
        var b = new Formula.Apply(Seq(Id("getElem"), Bang), [w, j]);
        var c = new Formula.Apply(Seq(Id("getElem"), Bang), [w, Add(j, D(1))]);
        var test = Call("if", Id("d"), Parenthesized(And(Greater(a, b), Greater(b, c))),
            Parenthesized(And(Less(a, b), Less(b, c))));
        var exists = Some([Bound("i", Call("Fin", Length(w))), Bound("j", Call("Fin", Length(w)))],
            And(Less(i, j), And(Less(Add(j, D(1)), Length(w)), test)));
        return Disp(All([Bound("d", Bool()), Bound("w", Word())],
            IffOf(Call("Contains", Id("d"), w), Parenthesized(exists))));
    }

    private static Formula DecisionFormula(bool contains)
    {
        var vars = contains ? new[] { Bound("d", Bool()), Bound("w", Word()) }
            : new[] { Bound("n", Nat()), Bound("p", Word()) };
        var args = contains ? new[] { Id("d"), Id("w") } : new[] { Id("n"), Id("p") };
        return Disp(All(vars, Seq(Call(contains ? "decidableContains" : "decidableIsPerm", args),
            Colon, Sp, Call("Decidable", Call(contains ? "Contains" : "IsPerm", args)))));
    }

    private static Formula PushFormula()
    {
        var d = Id("d"); var x = Id("x"); var a = Id("a"); var s = Id("s"); var r = Id("r");
        var proposed = Cons(x, Cons(a, s));
        var popped = Let(r, Call("Push", d, x, s), Pair(Cons(a, Call("fst", r)), Call("snd", r)));
        return Disp(new Formula.Aligned([
            All([Bound("d", Bool()), Bound("x", Nat())],
                Equal(Call("Push", d, x, Nil()), Pair(Nil(), Cons(x, Nil())))),
            All([Bound("d", Bool()), Bound("x", Nat()), Bound("a", Nat()), Bound("s", Word())],
                Equal(Call("Push", d, x, Cons(a, s)),
                    Call("if", Call("Contains", d, proposed), Parenthesized(popped), Pair(Nil(), proposed))))]));
    }

    private static Formula ProcessFormula()
    {
        var d = Id("d"); var x = Id("x"); var xs = Id("xs"); var s = Id("s"); var r = Id("r");
        return Disp(new Formula.Aligned([
            All([Bound("d", Bool()), Bound("s", Word())], Equal(Call("Process", d, Nil(), s), s)),
            All([Bound("d", Bool()), Bound("x", Nat()), Bound("xs", Word()), Bound("s", Word())],
                Equal(Call("Process", d, Cons(x, xs), s),
                    Let(r, Call("Push", d, x, s),
                        Call("append", Call("fst", r), Call("Process", d, xs, Call("snd", r))))))]));
    }

    private static Formula SCFormula() => Disp(All([Bound("d", Bool()), Bound("input", Word())],
        Equal(Call("SC", Id("d"), Id("input")), Call("Process", Id("d"), Id("input"), Nil()))));
    private static Formula IsPermFormula()
    {
        var range = new Formula.Apply(Seq(Id("range"), Apos), [D(1), Id("n")]);
        return Disp(All([Bound("n", Nat()), Bound("p", Word())],
            IffOf(Call("IsPerm", Id("n"), Id("p")), Call("Perm", Id("p"), range))));
    }
    private static Formula SnFormula()
    {
        var range = new Formula.Apply(Seq(Id("range"), Apos), [D(1), Id("n")]);
        var permutations = new Formula.Apply(Seq(Id("permutations"), Apos), [range]);
        return Disp(All([Bound("n", Nat())], Equal(Call("Sn", Id("n")), permutations)));
    }
    private static Formula FibreFormula() => Disp(All(
        [Bound("d", Bool()), Bound("n", Nat()), Bound("p", Word())],
        Equal(Call("Fibre", Id("d"), Id("n"), Id("p")),
            Call("toFinset", Call("filter", LambdaOf(Id("t"),
                Call("beq", Call("SC", Id("d"), Id("t")), Id("p"))), Call("Sn", Id("n")))))));
    private static Formula FFormula() => Disp(All(
        [Bound("d", Bool()), Bound("n", Nat()), Bound("p", Word())],
        Equal(Call("F", Id("d"), Id("n"), Id("p")), Call("card", Call("Fibre", Id("d"), Id("n"), Id("p"))))));

    private static Formula Attained(Formula d, Formula n, Formula k) =>
        Some([Bound("p", Word())], And(Call("IsPerm", n, Id("p")), Equal(Call("F", d, n, Id("p")), k)));
    private static Formula MaximumFormula()
    {
        var d = Id("d"); var n = Id("n"); var m = Id("m"); var p = Id("p");
        var upper = All([Bound("p", Word())], Imp(Call("IsPerm", n, p), AtMost(Call("F", d, n, p), m)));
        return Disp(All([Bound("d", Bool()), Bound("n", Nat()), Bound("m", Nat())],
            IffOf(Call("MaximumIs", d, n, m), And(Parenthesized(Attained(d, n, m)), Parenthesized(upper)))));
    }
    private static Formula SecondFormula()
    {
        var n = Id("n"); var k = Id("k"); var m = Id("m"); var p = Id("p"); var f = Call("F", Id("false"), n, p);
        var unique = All([Bound("p", Word())], Imp(Call("IsPerm", n, p), Imp(Less(k, f), Equal(f, m))));
        var larger = Some([Bound("m", Nat())], And(Less(k, m),
            And(Parenthesized(Attained(Id("false"), n, m)), Parenthesized(unique))));
        return Disp(All([Bound("n", Nat()), Bound("k", Nat())],
            IffOf(Call("SecondLargestIs", n, k),
                And(Parenthesized(Attained(Id("false"), n, k)), Parenthesized(larger)))));
    }
    private static Formula MultiplicityFormula() => Disp(All([Bound("n", Nat()), Bound("k", Nat())],
        Equal(Call("Multiplicity", Id("n"), Id("k")), Length(Call("filter", LambdaOf(Id("p"),
            Call("beq", Call("F", Id("false"), Id("n"), Id("p")), Id("k"))), Call("Sn", Id("n")))))));
    private static Formula ClaimFormula(bool maximum)
    {
        var n = Id("n"); var power = new Formula.Power(D(2), Sub(n, maximum ? D(2) : D(3)));
        var clauses = maximum ? And(Call("MaximumIs", Id("false"), n, power), Call("MaximumIs", Id("true"), n, power))
            : And(Call("SecondLargestIs", n, power), Equal(Call("Multiplicity", n, power), Sub(Mul(D(2), n), D(2))));
        return Disp(IffOf(Id(maximum ? "claimMaximum" : "claimSecondLargest"),
            Parenthesized(All([Bound("n", Nat())], Imp(AtMost(maximum ? D(2) : D(3), n), clauses)))));
    }

    private static Formula Id(string name) => F.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Bool() => Id("Bool");
    private static Formula Word() => Call("List", Nat());
    private static Formula Nil() => Id("nil");
    private static Formula Cons(Formula x, Formula xs) => Call("cons", x, xs);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Length(Formula w) => Call("length", w);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula LambdaOf(Formula x, Formula body) => Parenthesized(Seq(x, Sp, Mapsto, Sp, body));
    private static Formula Let(Formula x, Formula value, Formula body) =>
        Seq(Operatorname, Grp(Id("let")), Sp, x, Sp, Colon, Eq, Sp, value, Comma, Sp, body);
    private static Formula.BoundVariable Bound(string name, Formula domain) => new(FormulaIdentifier.Create(name), domain);
    private static Formula All(Formula.BoundVariable[] vars, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Some(Formula.BoundVariable[] vars, Formula body) => new Formula.BindMany(FormulaQuantifier.Exists, [.. vars], body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Greater(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.GreaterThan, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
