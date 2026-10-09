using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenChronology;

internal sealed class GoldenMagnusParityRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At every fixed even length the central doubled Magnus coordinate determines a golden factor. At every odd length two distinct legal factors have center zero. Every same-length center fiber contains at most two word contents.",
        H("Magnus center, reversal and the exact length-parity boundary"),
        Blocks(
            Paragraph(Text("Write M(w) for magnusCenter(w), K(w) for scatteredTrueFalseCount(w), W(n,i) for goldenFactor(n,i), and R(i,n) for goldenWindowTrueCount(i,n). The words are finite binary lists; n and the occurrence starts are arbitrary naturals. All arithmetic in the center is integral, and integer denotes the natural-to-integer cast.")),
            Node("center-definition", "The actual represented center", "magnusCenter", DescribeRole.Definition,
                DefinitionFormula(),
                "The observation maps true to the matrix unit at (0,1) and false to that at (1,2). M is the (0,2) entry of the doubled second Magnus coordinate of this fixed chronological signature."),
            Node("center-formula", "The difference of oriented pair counts", "magnus_center_formula", DescribeRole.Theorem,
                CenterFormula(),
                "Twice the true-before-false count minus the product of both letter counts is the true-before-false count minus the false-before-true count. The doubled convention avoids a half-integral coordinate."),
            Node("reversal-pairs", "Reversal accounts for all unlike-letter pairs", "scattered_pair_reversal_sum", DescribeRole.Theorem,
                ReversalPairsFormula(),
                "Every choice of one true position and one false position has exactly one of the two orientations. Reversal interchanges those orientations, so the two scattered-pair counts sum to the product of the letter counts."),
            Node("reversal-center", "Reversal negates the center", "magnus_center_reverse", DescribeRole.Theorem,
                ReversalCenterFormula(),
                "Reversal preserves the two letter counts and replaces K by their product minus K. Substitution into the center formula changes its sign."),
            Node("palindrome-center", "A palindrome has center zero", "magnus_center_zero_of_reverse_eq", DescribeRole.Theorem,
                PalindromeFormula(),
                "A word equal to its reverse has M equal to minus M, hence M=0 over the integers. The empty word and one-letter words are included. Zero center alone does not assert that a word is a palindrome."),
            Node("count-center-recovery", "One count and center at a known length", "golden_factor_eq_of_count_and_center", DescribeRole.Theorem,
                CountRecoveryFormula(),
                "For two golden factors of the same specified length, equal true counts and equal centers force equal scattered-pair counts. Fixed-length second-order recovery then gives equal words."),
            Node("even-recovery", "Even length makes the count redundant", "even_length_center_recovers_golden_factor", DescribeRole.Theorem,
                EvenFormula(),
                "Golden balance bounds the difference of the two true counts by one. If the counts differ by one, the two products r(n-r) differ by an odd integer when n is even, whereas twice the difference of the pair counts is even. Equal centers therefore force equal true counts, and count-plus-center recovery applies."),
            Node("odd-collision", "A collision at every odd length", "odd_length_center_collision", DescribeRole.Theorem,
                OddFormula(),
                "At each odd natural length the golden language has exactly two distinct palindromic factors. Both are reversal-fixed and therefore have center zero. Choosing occurrence starts for these two words gives the displayed collision. The statement asserts distinct word contents, without a prescribed distance between the starts."),
            Node("parity-boundary", "Center recovery holds exactly at even lengths", "center_recovers_fixed_length_iff_even", DescribeRole.Theorem,
                ClassificationFormula(),
                "The recovery property quantifies over every pair of starts at the specified length. The even theorem proves one direction; the odd collision refutes the property at every odd length. Length zero is even: all its factors are empty and recovery holds. Length one is odd: the two one-letter factors both have center zero."),
            Node("two-word-fiber", "No fiber has three distinct word contents", "center_fiber_has_at_most_two_words", DescribeRole.Theorem,
                FiberFormula(),
                "Three factors of one length with a common center have pairwise true counts differing by at most one. Among three natural counts with that bound, two coincide. Their common count and center imply equal words, giving the displayed three-way disjunction. The bound holds at every length; odd zero-center fibers attain two, while every even fiber has at most one. None of these results recovers an absolute occurrence index, and this parity refers to word length.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsNat(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), F.Id("Nat"), body);
    private static Formula Nat(string name, Formula body) => All(name, F.Id("Nat"), body);
    private static Formula Three(Formula body) => Nat("n", Nat("i", Nat("j", body)));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Different(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula WordType() => Call("List", F.Id("Bool"));
    private static Formula Word(Formula n, Formula i) => Call("W", n, i);
    private static Formula Count(Formula w, string letter) => Call("count", w, F.Id(letter));
    private static Formula Integer(Formula n) => Call("integer", n);
    private static Formula Center(Formula w) => Call("M", w);
    private static Formula PairCount(Formula w) => Call("K", w);

    private static Formula DefinitionFormula()
    {
        Formula w = F.Id("w");
        Formula observation = new Formula.NamedConstant(FormulaIdentifier.Create("binaryLetterObservation"));
        Formula matrix = Call("doubledMagnusDegreeTwo", Call("chronologicalSignature", observation, w));
        return Disp(All("w", WordType(), Equal(Center(w), new Formula.Apply(matrix, [D(0), D(2)]))));
    }

    private static Formula CenterFormula()
    {
        Formula w = F.Id("w");
        return Disp(All("w", WordType(), Equal(Center(w), Sub(Mul(D(2), Integer(PairCount(w))),
            Mul(Integer(Count(w, "true")), Integer(Count(w, "false")))))));
    }

    private static Formula ReversalPairsFormula()
    {
        Formula w = F.Id("w");
        return Disp(All("w", WordType(), Equal(Add(PairCount(w), PairCount(Call("reverse", w))),
            Mul(Count(w, "true"), Count(w, "false")))));
    }

    private static Formula ReversalCenterFormula()
    {
        Formula w = F.Id("w");
        return Disp(All("w", WordType(), Equal(Center(Call("reverse", w)), new Formula.Negate(Center(w)))));
    }

    private static Formula PalindromeFormula()
    {
        Formula w = F.Id("w");
        return Disp(All("w", WordType(), Implies(Equal(Call("reverse", w), w), Equal(Center(w), D(0)))));
    }

    private static Formula CountRecoveryFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), j = F.Id("j"), a = Word(n, i), b = Word(n, j);
        return Disp(Three(Implies(Equal(Call("R", i, n), Call("R", j, n)),
            Implies(Equal(Center(a), Center(b)), Equal(a, b)))));
    }

    private static Formula EvenFormula()
    {
        Formula n = F.Id("n"), a = Word(n, F.Id("i")), b = Word(n, F.Id("j"));
        return Disp(Nat("n", Implies(Call("Even", n), Nat("i", Nat("j",
            Implies(Equal(Center(a), Center(b)), Equal(a, b)))))));
    }

    private static Formula OddFormula()
    {
        Formula n = F.Id("n"), a = Word(n, F.Id("i")), b = Word(n, F.Id("j"));
        return Disp(Nat("n", Implies(Call("Odd", n), ExistsNat("i", ExistsNat("j",
            And(Different(a, b), And(Equal(Center(a), D(0)), Equal(Center(b), D(0)))))))));
    }

    private static Formula ClassificationFormula()
    {
        Formula n = F.Id("n"), a = Word(n, F.Id("i")), b = Word(n, F.Id("j"));
        return Disp(Nat("n", Equivalent(Nat("i", Nat("j", Implies(Equal(Center(a), Center(b)), Equal(a, b)))),
            Call("Even", n))));
    }

    private static Formula FiberFormula()
    {
        Formula n = F.Id("n"), a = Word(n, F.Id("i")), b = Word(n, F.Id("j")), c = Word(n, F.Id("k"));
        return Disp(Three(Nat("k", Implies(Equal(Center(a), Center(b)), Implies(Equal(Center(a), Center(c)),
            Or(Equal(a, b), Or(Equal(a, c), Equal(b, c))))))));
    }
}
