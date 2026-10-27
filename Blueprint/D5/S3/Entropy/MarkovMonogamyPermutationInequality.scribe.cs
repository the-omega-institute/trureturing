using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class MarkovMonogamyPermutationInequalityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Entropy/MarkovMonogamyPermutationInequality";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Entropy/capelacelerichavesmodi2022markov");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The diagonal sum of mutual informations dominates every permuted sum along a finite classical Markov chain.",
        H("Classical Markov monogamy for every permutation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("composed-transition"),
                DeclarationHandle.Create(Module + ".composedTransition"),
                H("Successive transition matrices"),
                StatementSource.FromAuthor(Disp(TransitionDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For a family of finite alphabets α, the transition from position s to position t "
                    + "is the product of the successive matrices k at positions s through t − 1. "
                    + "The recursion starts with the identity matrix at s and appends one matrix by "
                    + "summing over the intermediate letter c. No positivity or normalization is "
                    + "part of this definition. The order condition supplies the implicit proof "
                    + "argument of composedTransition and Nat.leRecOn. The construction describes "
                    + "successive transitions for the Markov condition in Section II of the source "
                    + "(PRA-v1.tex, lines 119–126)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The permutation inequality"),
                StatementSource.FromAuthor(Disp(Equal(Typed(Local("claim"), Qualified("Prop")),
                    Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Choose a probability mass p at position zero and stochastic matrices k "
                    + "between the first 2n positions. Position n − 1 − i.val represents X with "
                    + "one-based index i.val + 1, and position n + i.val represents the corresponding Y. "
                    + "The first mixture transports p to the X position; mixtureJoint combines "
                    + "that law with the transition to the chosen Y position. Thus each summand "
                    + "is the mutual information, in nats, of the indicated pair. Fin.val explicitly "
                    + "converts each finite index to a natural number, and subtraction is natural "
                    + "subtraction. Order proofs in composedTransition are implicit. For positive n "
                    + "this is the finite-alphabet reading of Conjecture 1 (PRA-v1.tex, lines 153–159), "
                    + "whose mutual information is defined at line 143. The statement also includes "
                    + "n = 0, when both sums are empty. No restriction is imposed on transitions "
                    + "outside these 2n positions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The diagonal pairing maximizes the information sum"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First establish the elementary laws of successive transitions. At equal "
                        + "positions the transition is the identity matrix. Appending a step multiplies "
                        + "by the next matrix and sums over its input. Induction on the final position, "
                        + "interchange of finite sums and associativity of multiplication show that "
                        + "a transition through an intermediate position is the product of the two "
                        + "composite transitions. A second induction shows that composites of "
                        + "nonnegative matrices with unit row sums again have those properties. "
                        + "Consequently transporting p directly to a position agrees with transporting "
                        + "it first to an intermediate position, and every transported mass is a "
                        + "nonnegative probability law.")),
                    Paragraph(Text(
                        "The entropy chain rule gives the entropy of a channel joint law: it is "
                        + "the entropy of the input mass plus the input-weighted sum of the row "
                        + "entropies. Apply this to a four-position chain A to B to C to D, with "
                        + "initial law p and stochastic matrices u, v and w. Set r(b) to the sum "
                        + "of p(a)u(a,b), s(a,c) to the sum of u(a,b)v(b,c), t(b,d) to the sum "
                        + "of v(b,c)w(c,d), and z(a,d) to the sum of u(a,b)t(b,d), with each sum "
                        + "over its intermediate letter. These give the pair laws AB, BC, AC, BD "
                        + "and AD, and then the joint laws ABC, ABD, ACD and ABCD. Positivity "
                        + "and unit row sums pass to s, t and z.")),
                    Paragraph(Text(
                        "Reindex the four-variable law, whose mass is p(a)u(a,b)v(b,c)w(c,d), "
                        + "as a law q on the pair (A,D) and the pair (B,C). Summing its mass "
                        + "gives one. Its two three-variable projections are ABD and ACD, up to "
                        + "coordinate rearrangement, and its first marginal is AD. Finite bijections "
                        + "preserve entropy. Nonnegativity of conditional mutual information for q "
                        + "therefore says that H(ABD) + H(ACD) − H(ABCD) − H(AD) is nonnegative. "
                        + "Expand the first three entropies by the channel chain rule. Summing the "
                        + "AB law against a function of B gives the r-weighted sum; the weighted "
                        + "entropy of w is the same whether its weights come from AC or ABC. "
                        + "These identities cancel the common row-entropy terms, leaving "
                        + "H(AC) − H(AD) + Σ_b r(b)[H(t(b)) − H(v(b))] as the nonnegative defect.")),
                    Paragraph(Text(
                        "The C marginals of AC and BC agree, and the D marginals of AD and BD "
                        + "agree, by interchanging finite sums. Express the four pair mutual "
                        + "informations as the sum of marginal entropies minus joint entropy, "
                        + "and expand the BC and BD entropies by the same channel rule. Their "
                        + "difference is precisely the remaining nonnegative entropy defect. Hence "
                        + "I(B:C) + I(A:D) ≥ I(B:D) + I(A:C). For any ordered positions a ≤ b ≤ c ≤ d "
                        + "of the original chain, start with the transported law at a and use the "
                        + "three composite transitions from a to b, b to c and c to d. The "
                        + "composition and transport identities identify all four pair laws, so "
                        + "the same rectangle inequality holds at these positions.")),
                    Paragraph(Text(
                        "Let X_i and Y_a denote positions n − 1 − i.val and n + a.val, and set "
                        + "m(i,a) = I(X_i:Y_a). For i < j and a < b, the four positions "
                        + "n − 1 − j.val, n − 1 − i.val, n + a.val and n + b.val are ordered. "
                        + "They form the chain A = X_j to B = X_i to C = Y_a to D = Y_b. "
                        + "The entropy calculation above identifies the rectangle defect as "
                        + "I(X_i:Y_a) + I(X_j:Y_b) − I(X_i:Y_b) − I(X_j:Y_a) "
                        + "= I(B:C | A,D) ≥ 0. Every transition used precedes the last of "
                        + "these positions, which is less than 2n, so the stated stochasticity "
                        + "hypothesis suffices.")),
                    Paragraph(Text(
                        "To compare the permutation and diagonal sums for any real matrix m "
                        + "with these ordered rectangles, handle n = 0 by empty sums. For "
                        + "n = N + 1, put c = 1/(N + 1) and give each point "
                        + "e(i) = (i,f(i),i,f(i)) mass c, with zero mass elsewhere. The first "
                        + "coordinate makes e injective, so the masses sum to one. Since f "
                        + "is a permutation, all four coordinate marginals are the same uniform "
                        + "law, with mass c at every element of Fin (N + 1).")),
                    Paragraph(Text(
                        "The test Φ(x) = m(x(0),x(1)) is supermodular for coordinatewise "
                        + "minimum and maximum. Comparing the orders of the first two "
                        + "coordinates gives equality when their orders agree and the rectangle "
                        + "inequality when they are opposed; equal indices also give equality. "
                        + "Apply common_marginal_supermodular_le_diagonal to this test and "
                        + "the uniform law on the points e(i). Its expectation comparison is "
                        + "c Σ_i m(i,f(i)) ≤ c Σ_i m(i,i). Cancel the positive factor c. "
                        + "For the mutual-information matrix above, this proves that the "
                        + "identity pairing is maximal for every n and every f, as asserted "
                        + "by claim."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("capela-celeri-chaves-modi-2022-classical-markov-monogamy"),
                    ResolutionKind.Proved)))));

    private static Formula TransitionDefinition()
    {
        Formula family = LambdaOf("t", Naturals, KernelType(X("s"), X("t")));
        Formula step = LambdaOf("t", Naturals,
            LambdaOf("u", KernelType(X("s"), X("t")),
                LambdaOf("a", Alphabet(X("s")),
                    LambdaOf("b", Alphabet(Add(X("t"), D(1))),
                        SumOver("c", Alphabet(X("t")),
                            Multiply(At(X("u"), X("a"), X("c")),
                                At(X("k"), X("t"), X("c"), X("b"))))))));
        Formula initial = LambdaOf("a", Alphabet(X("s")),
            LambdaOf("b", Alphabet(X("s")),
                At(Qualified("ite"), Equal(X("a"), X("b")), RealDigit(1), RealDigit(0))));
        Formula recursion = At(Qualified("Nat", "leRecOn"),
            Parenthesized(Seq(X("C"), Colon, Eq, Sp, family)), step, initial);
        Formula definition = AlphabetBinders(At(Qualified("Type"), Universe),
            All("k", TransitionType,
                All("s", Naturals, All("t", Naturals,
                    Arrow(LE(X("s"), X("t")),
                        Equal(Typed(Transition(X("s"), X("t")), KernelType(X("s"), X("t"))),
                            recursion))))));
        return Seq(Qualified("universe"), Sp, Universe, Semi, Sp, definition);
    }

    private static Formula ClaimBody() => All("n", Naturals,
        AlphabetBinders(Qualified("Type"),
            All("p", Arrow(Alphabet(D(0)), Reals),
                All("k", TransitionType,
                    Arrow(InitialLaw,
                        Arrow(StochasticTransitions,
                            All("f", At(Qualified("Equiv", "Perm"), FinOf(X("n"))),
                                LE(InformationSum(true), InformationSum(false)))))))));

    private static Formula InitialLaw => And(
        All("a", Alphabet(D(0)), LE(RealDigit(0), At(X("p"), X("a")))),
        Equal(SumOver("a", Alphabet(D(0)), At(X("p"), X("a"))), RealDigit(1)));

    private static Formula StochasticTransitions => All("t", Naturals,
        Arrow(LT(Add(X("t"), D(1)), Multiply(D(2), X("n"))),
            And(All("a", Alphabet(X("t")),
                    All("b", Alphabet(Add(X("t"), D(1))),
                        LE(RealDigit(0), At(X("k"), X("t"), X("a"), X("b"))))),
                All("a", Alphabet(X("t")),
                    Equal(SumOver("b", Alphabet(Add(X("t"), D(1))),
                        At(X("k"), X("t"), X("a"), X("b"))), RealDigit(1))))));

    private static Formula InformationSum(bool permuted)
    {
        Formula left = Subtract(Subtract(X("n"), D(1)), NaturalIndex(X("i")));
        Formula right = Add(X("n"), NaturalIndex(permuted ? At(X("f"), X("i")) : X("i")));
        Formula mass = At(Qualified("D5", "S3", "Entropy", "Mixing", "MixtureEntropyBracket", "mixture"),
            X("p"), Transition(D(0), left));
        Formula pair = At(Qualified("D5", "S3", "Entropy", "Mixing", "MixtureEntropyBracket", "mixtureJoint"),
            mass, Transition(left, right));
        return SumOver("i", FinOf(X("n")),
            At(Qualified("D5", "S3", "Entropy", "MutualInformation", "mutualInformation"), pair));
    }

    private static Formula AlphabetBinders(Formula universe, Formula body) =>
        All("α", Arrow(Naturals, universe), Seq(OpenBracket,
            All("t", Naturals, At(Qualified("Fintype"), Alphabet(X("t")))),
            CloseBracket, Comma, Sp, Parenthesized(body)));
    private static Formula TransitionType => All("t", Naturals,
        KernelType(X("t"), Add(X("t"), D(1))));
    private static Formula KernelType(Formula s, Formula t) =>
        Arrow(Alphabet(s), Arrow(Alphabet(t), Reals));
    private static Formula Alphabet(Formula t) => At(Alpha, t);
    private static Formula Transition(Formula s, Formula t) => At(Local("composedTransition"), X("k"), s, t);
    private static Formula NaturalIndex(Formula value) => Typed(At(Qualified("Fin", "val"), value), Naturals);
    private static Formula Universe => new Formula.Subscript(X("u"), D(1));
    private static Formula Naturals => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals => Seq(Mathbb, Grp(X("R")));
    private static Formula RealDigit(byte value) => Typed(D(value), Reals);
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Local(string name) => Qualified("D5", "S3", "Entropy", "MarkovMonogamyPermutationInequality", name);
    private static Formula X(string name) => name == "α" ? Alpha : F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
