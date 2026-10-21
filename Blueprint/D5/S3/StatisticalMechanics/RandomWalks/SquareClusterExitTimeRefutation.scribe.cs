using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.RandomWalks;

internal sealed class SquareClusterExitTimeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/rognonenicosia2023clusters");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A connected lattice disk with 121 vertices has larger mean first exit time than the 11 by 11 square.",
        H("Squares do not maximize the mean first exit time"),
        Blocks(
            Node("step", "The four lattice directions", StepFormula(),
                "The directions indexed by Fin 4 are the two positive and two negative coordinate steps. "
                    + "Each direction has probability one quarter, as in the source's worked first-step system. "
                    + "The expression ite selects its second argument when its first argument holds and its third otherwise.",
                "step"),
            Node("position", "Positions along a direction word", PositionFormula(),
                "A direction word of length n is a function from Fin n to Fin 4. "
                    + "The position starts at p, follows the word in order, and stays at its final vertex after n steps. "
                    + "The function tail removes the first letter of a nonempty word.",
                "position"),
            Node("exits", "First exit at the last letter", ExitsFormula(),
                "A word exits at time n exactly when all positions with indices less than n belong to S "
                    + "and its final position does not. The map val regards a finite index as a natural number. "
                    + "For n = 0 this says that the starting point is outside S.",
                "exits"),
            Node("exit-probability", "The exit distribution", ExitProbabilityFormula(),
                "All direction words of length n have the same probability, one divided by four to the power n. "
                    + "Counting the words that first exit at their final position gives the first-exit distribution. "
                    + "The notation (a : ℝ) denotes the canonical cast from natural numbers to real numbers.",
                "exitProb"),
            Node("expected-exit", "Expected first exit time", ExpectedExitFormula(),
                "The expectation is the sum of time n multiplied by its first-exit probability. "
                    + "The primed sum denotes the real tsum, with value zero if the series is not summable; "
                    + "the rational first-step solutions used below establish summability for the two clusters. "
                    + "This follows the source's prose definition: the first visit to any vertex outside the cluster.",
                "expectedExit"),
            Node("mean-exit", "The mean over starting vertices", MeanExitFormula(),
                "Average the expected first exit time uniformly over the vertices of S. "
                    + "Real division gives zero for the empty cluster. "
                    + "The source's prose and worked first-step systems use this first-exit interpretation. "
                    + "Its displayed equation eq:eq_tau_c instead averages individual node-to-node hitting times; "
                    + "that different average is not the quantity considered here.",
                "meanExit"),
            Node("adjacent", "Nearest-neighbour adjacency within a cluster", AdjacentFormula(),
                "Two vertices are adjacent when they both belong to S and one is obtained from the other by a unit coordinate step.",
                "adjacent"),
            Node("connected", "Connected lattice clusters", ConnectedFormula(),
                "Every ordered pair of vertices of S is joined by a finite sequence of adjacent vertices in S. "
                    + "ReflTransGen is the reflexive transitive closure, so a path of length zero is allowed. "
                    + "The empty cluster satisfies this predicate vacuously.",
                "connected"),
            Node("square", "The square of side m", SquareFormula(),
                "Take the Cartesian product of two copies of range(m), the natural numbers from zero to m minus one, "
                    + "and include both coordinates in the integers. The functions fst and snd select the coordinates "
                    + "and (a : ℤ) denotes the canonical cast from natural numbers to integers. For positive m this is the square "
                    + "with m squared vertices; for m = 0 it is empty.",
                "square"),
            Node("claim", "The square-maximality conjecture", ClaimFormula(),
                "Rognone and Nicosia conjecture that the maximal exit time at each fixed number of nodes is obtained for squares. "
                    + "Here the number of nodes is m squared with m at least one, and every finite nearest-neighbour "
                    + "connected subset of the square lattice is compared with the square of side m. "
                    + "The exit time is the uniform mean of first-exit expectations.",
                "claim"),
            Describe.Lean(DescribeId.Create("square-exit-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A disk with larger mean exit time"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                ResultProse(), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("rognone-nicosia-2023-square-cluster-exit-time-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string prose, string declaration) =>
        Describe.Lean(DescribeId.Create("square-exit-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static BlockSequence ResultProse() => Blocks(
        Paragraph(Text("Let C be the lattice disk "),
            Math(Seq(OpenBrace, Pair(F.Id("x"), F.Id("y")), Sp, InMacro, Sp, Lattice(), Sp, Mid, Sp,
                AtMost(Add(new Formula.Power(F.Id("x"), D(2)), new Formula.Power(F.Id("y"), D(2))), D(3, 7)), CloseBrace)),
            Text(". It has 121 vertices and is nearest-neighbour connected: reducing the absolute value of a nonzero coordinate "
                + "preserves membership and gives a path to the origin. Let Q be square(11), the 11 by 11 square.")),
        Paragraph(Text("On C and on Q, rational functions t, extended by zero outside the cluster, satisfy the certificate identity "),
            Math(Equal(F.Id("t"), Add(D(1), Apply(F.Id("P"), F.Id("t"))))),
            Text(". Here, for a cluster S and a function f, "),
            Math(Equal(Apply(Apply(F.Id("P"), F.Id("f")), F.Id("p")),
                Call("ite", Member(F.Id("p"), F.Id("S")),
                    new Formula.Fraction(SumOver("d", Directions(), Apply(F.Id("f"),
                        Add(F.Id("p"), Call("step", F.Id("d"))))), D(4)), D(0)))),
            Text(". The identity holds at every vertex of each cluster. Both functions lie between 1 and 43 there. "
                + "Positivity of P then bounds its n-th iterate on t by (42/43) to the power n times t. "
                + "The corresponding remainder terms in the partial sums of the exit distribution tend to zero, "
                + "identifying t at each starting vertex with expectedExit for that cluster.")),
        Paragraph(Text("The exact means are "),
            Math(Equal(Call("meanExit", F.Id("C")),
                new Formula.Fraction(D(1, 9, 8, 0, 0, 8, 2, 3, 6, 1, 6, 9), D(8, 3, 3, 8, 3, 7, 7, 7, 7, 3)))),
            Text(" and "),
            Math(Equal(Call("meanExit", F.Id("Q")),
                new Formula.Fraction(D(2, 8, 1, 1, 1, 1, 8, 9, 8, 3), D(1, 1, 9, 3, 3, 3, 8, 3, 0)))),
            Text(". The first fraction is strictly greater than the second. Since both clusters have 121 vertices, "
                + "C contradicts the conjectured inequality at m = 11.")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula CastReal(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R")))));
    private static Formula CastInteger(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, Integers()));
    private static Formula Lattice() => new Formula.Power(Integers(), D(2));
    private static Formula Clusters() => Call("Finset", Lattice());
    private static Formula Directions() => Call("Fin", D(4));
    private static Formula Words(Formula n) => Parenthesized(new Formula.TypeArrow(Call("Fin", n), Directions()));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Comma, Sp, y));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula SumOver(string variable, Formula domain, Formula term) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(variable), Sp, Colon, Sp, domain)), Sp, Parenthesized(term));

    private static Formula StepFormula()
    {
        Formula d = F.Id("d");
        Formula value = Call("ite", Equal(d, D(0)), Pair(D(1), D(0)),
            Call("ite", Equal(d, D(1)), Pair(new Formula.Negate(D(1)), D(0)),
                Call("ite", Equal(d, D(2)), Pair(D(0), D(1)), Pair(D(0), new Formula.Negate(D(1))))));
        return Disp(All("d", Directions(), Equal(Call("step", d), value)));
    }

    private static Formula PositionFormula()
    {
        Formula p = F.Id("p"), n = F.Id("n"), w = F.Id("w"), j = F.Id("j");
        Formula empty = All("p", Lattice(), All("w", Words(D(0)), All("j", Naturals(),
            Equal(Call("position", p, w, j), p))));
        Formula initial = All("p", Lattice(), All("n", Naturals(), All("w", Words(Add(n, D(1))),
            Equal(Call("position", p, w, D(0)), p))));
        Formula next = All("p", Lattice(), All("n", Naturals(), All("w", Words(Add(n, D(1))), All("j", Naturals(),
            Equal(Call("position", p, w, Add(j, D(1))),
                Call("position", Add(p, Call("step", Apply(w, D(0)))), Call("tail", w), j))))));
        return Disp(new Formula.Aligned([empty, initial, next]));
    }

    private static Formula ExitsFormula()
    {
        Formula s = F.Id("S"), p = F.Id("p"), n = F.Id("n"), w = F.Id("w"), j = F.Id("j");
        Formula condition = And(All("j", Call("Fin", n), Member(Call("position", p, w, Call("val", j)), s)),
            new Formula.Not(Parenthesized(Member(Call("position", p, w, n), s))));
        return Disp(All("S", Clusters(), All("p", Lattice(), All("n", Naturals(), All("w", Words(n),
            IffOf(Call("exits", s, p, w), condition))))));
    }

    private static Formula ExitProbabilityFormula()
    {
        Formula s = F.Id("S"), p = F.Id("p"), n = F.Id("n"), w = F.Id("w");
        Formula exitingWords = Seq(OpenBrace, w, Sp, Colon, Sp, Words(n), Sp, Mid, Sp, Call("exits", s, p, w), CloseBrace);
        return Disp(All("S", Clusters(), All("p", Lattice(), All("n", Naturals(),
            Equal(Call("exitProb", s, p, n),
                new Formula.Fraction(CastReal(Call("card", exitingWords)), new Formula.Power(D(4), n)))))));
    }

    private static Formula ExpectedExitFormula()
    {
        Formula s = F.Id("S"), p = F.Id("p"), n = F.Id("n");
        Formula series = Seq(new Formula.Subscript(Seq(Sum, Apos), Seq(n, Sp, Colon, Sp, Naturals())), Sp,
            Parenthesized(new Formula.Binary(CastReal(n), FormulaBinaryOperator.Multiply, Call("exitProb", s, p, n))));
        return Disp(All("S", Clusters(), All("p", Lattice(), Equal(Call("expectedExit", s, p), series))));
    }

    private static Formula MeanExitFormula()
    {
        Formula s = F.Id("S"), p = F.Id("p");
        Formula sum = Seq(new Formula.Subscript(Sum, Member(p, s)), Sp, Parenthesized(Call("expectedExit", s, p)));
        return Disp(All("S", Clusters(), Equal(Call("meanExit", s), new Formula.Fraction(sum, CastReal(Call("card", s))))));
    }

    private static Formula AdjacentFormula()
    {
        Formula s = F.Id("S"), p = F.Id("p"), q = F.Id("q"), d = F.Id("d");
        Formula condition = And(Member(p, s), And(Member(q, s),
            Some("d", Directions(), Equal(q, Add(p, Call("step", d))))));
        return Disp(All("S", Clusters(), All("p", Lattice(), All("q", Lattice(),
            IffOf(Call("adjacent", s, p, q), condition)))));
    }

    private static Formula ConnectedFormula()
    {
        Formula s = F.Id("S"), p = F.Id("p"), q = F.Id("q");
        Formula paths = All("p", Lattice(), Implies(Member(p, s), All("q", Lattice(), Implies(Member(q, s),
            Call("ReflTransGen", Call("adjacent", s), p, q)))));
        return Disp(All("S", Clusters(), IffOf(Call("connected", s), paths)));
    }

    private static Formula SquareFormula()
    {
        Formula m = F.Id("m"), p = F.Id("p");
        Formula map = Seq(LambdaLower, Sp, p, Sp, Colon, Sp,
            Parenthesized(Seq(Naturals(), Sp, Times, Sp, Naturals())), Comma, Sp,
            Pair(CastInteger(Call("fst", p)), CastInteger(Call("snd", p))));
        Formula product = Seq(Call("range", m), Sp, Times, Sp, Call("range", m));
        return Disp(All("m", Naturals(), Equal(Call("square", m), Call("image", Parenthesized(map), Parenthesized(product)))));
    }

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("m"), s = F.Id("S");
        Formula assertion = All("m", Naturals(), Implies(AtMost(D(1), m), All("S", Clusters(),
            Implies(Equal(Call("card", s), new Formula.Power(m, D(2))),
                Implies(Call("connected", s), AtMost(Call("meanExit", s), Call("meanExit", Call("square", m))))))));
        return Disp(IffOf(F.Id("claim"), assertion));
    }
}
