using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MembraneSignatures;

internal sealed class AmendolaRiffoSchmitzRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/amendolariffoschmitz2026membranes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized two-letter array satisfies the printed membrane shuffle equations and has no piecewise bilinear realization.",
        H("The printed Chen–Chow conjecture for membranes"),
        Blocks([
            .. GridDefinitions(),
            .. ShuffleDefinitions(),
            .. SignatureDefinitions(),
            Definition("claim", "Conjecture 6.10 as printed", "claim", ClaimFormula(),
                "Conjecture 6.10, p. 32. “For every sequence s ∈ ⊕_{ℓ=0}^k ⊕_{ν∈Σ_ℓ}(ℝ^d)^{⊗ℓ} "
                    + "with entries satisfying the two-parameter shuffle identity (Theorem 2.10) there is a "
                    + "piecewise bilinear membrane such that its k-truncated signature coincides with s.” "
                    + "Equality is at every degree, word and permutation in the truncation.", fromLiterature: true),
            .. WitnessDefinitions(),
            Describe.Lean(
                DescribeId.Create("amendola-riffo-schmitz-result"),
                DeclarationHandle.Create(Prefix + "refute_conjecture_6_10_v1"),
                H("A normalized array with no membrane realization"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimFormula())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take d = 2 and k = 4. The rational array has 443 coordinates, with the "
                            + "empty coordinate equal to one and zero whenever the word uses the second letter. "
                            + "Its coefficients satisfy all 1,177 ordered equations of the printed system. "
                            + "For the input pair (1,1) and (111,231) in one-based notation, "
                            + "both the product and the printed sum equal 19/4.")),
                    Paragraph(Text(
                        "In a product of the degree-one and degree-three integrals, insert the singleton "
                            + "at one of four positions on each axis. Up to null ties, the 16 chambers "
                            + "partition the joint domain. Reindexing the axes sends old row slot j to "
                            + "π(j) and its old column slot (α ▷ β)(j) to λ((α ▷ β)(j)). "
                            + "The new row word uses π⁻¹ and the new rank is λ ∘ (α ▷ β) ∘ π⁻¹. "
                            + "For the same rational input pair this forward shuffle sum equals 7/4, "
                            + "so equality to a membrane signature is impossible.")),
                    Paragraph(Text(
                        "The same array refutes the printed conjecture with explicit degree-zero normalization. "
                            + "Realizability under the genuine shuffle equations remains open."))),
                DescribeRole.Theorem)
        ])));

    private static DocumentBlock[] GridDefinitions() =>
    [
        Definition("plane", "Ambient plane", "Plane",
            Eq(Named("Plane"), Product(R, R)),
            "A point pairs a real row coordinate with a real column coordinate."),
        Definition("unit-interval", "Unit interval", "UnitInterval",
            Eq(Named("UnitInterval"), Interval(D(0), D(1), closed: true)),
            "Both endpoints belong to the interval."),
        Definition("unit-square", "Unit square", "UnitSquare",
            Eq(Named("UnitSquare"), Product(Named("UnitInterval"), Named("UnitInterval"))),
            "The square is the product of the two closed unit intervals."),
        Definition("membrane", "Ambient membrane type", "Membrane",
            All(Eq(Membrane, Arrow(R, R, Fin(V("d")), R)), ("d", N)),
            "The function takes row coordinate, column coordinate and component, in that order."),
        Definition("grid-point", "Uniform grid point", "gridPoint",
            All(Eq(Call("gridPoint", V("m"), V("i")),
                    new Formula.Fraction(Call("cast", V("i"), R), Call("cast", V("m"), R))),
                ("m", N), ("i", N)),
            "Division uses Lean's total real division. The grid predicate below chooses positive grid sizes."),
        Definition("open-strip", "Open grid strip", "openStrip", StripFormula("openStrip", closed: false),
            "The endpoints are excluded."),
        Definition("closed-strip", "Closed grid strip", "closedStrip", StripFormula("closedStrip", closed: true),
            "The endpoints are included."),
        Definition("grid", "Piecewise bilinear membranes", "PiecewiseBilinear", GridFormula(),
            "Section 4, p. 20, uses positive uniform grid sizes and biaffinity on every closed cell. "
                + "One ambient function supplies the values on both sides of every shared boundary. "
                + "The conditions constrain its restriction to the unit square.", fromLiterature: true),
        Definition("mixed", "Native mixed partial", "mixed", MixedFormula(),
            "Differentiate the component in the column variable at the second coordinate, then in the row "
                + "variable at the first coordinate. Both occurrences of deriv denote Lean's total derivative. "
                + "On an open grid cell the result is the coefficient of the product of the two coordinates."),
        Definition("bounded-measurable", "Bounded measurable representatives", "BoundedMeasurable",
            BoundedMeasurableFormula(),
            "Each component is measurable and one nonnegative bound controls all components on the full plane.")
    ];

    private static DocumentBlock[] ShuffleDefinitions() =>
    [
        Definition("rank", "Permutation type", "Rank",
            All(Eq(Rank(V("l")), Call("Perm", Fin(V("l")))), ("l", N)),
            "The degree determines the finite set of slots."),
        Definition("insertion-rank", "Insertion permutation on four slots", "insertionRank",
            InsertionRankFormula(),
            "The permutation takes zero to p. The succAbove map enumerates the remaining slots in order, "
                + "so these two clauses determine the permutation on all four slots."),
        Definition("word", "Word type", "Word",
            All(Eq(Word(V("l")), Arrow(Fin(V("l")), Fin(V("d")))), ("d", N), ("l", N)),
            "A word assigns one letter to each slot."),
        Definition("array", "Truncated array type", "Array",
            All(Eq(Array(V("R")), Seq(new Formula.Subscript(Prod, Typed(V("l"), TruncatedDegree)), Sp,
                    Parenthesized(Arrow(Word(Val(V("l"))), Rank(Val(V("l"))), V("R"))))),
                ("R", Type), ("d", N), ("k", N)),
            "This is a dependent function type. Choosing a finite degree fixes both the word type "
                + "and the permutation type."),
        Definition("block-rank", "Block permutation", "blockRank", BlockRankFormula(),
            "castAdd and natAdd are the two Fin embeddings. The second offsets a slot by the first block's size."),
        Definition("shuffles", "Block-increasing permutations", "shuffles", ShufflesFormula(),
            "The finite set filters all permutations by strict increase on each block separately."),
        Definition("shuffle-sum", "Sum over pairs of shuffles", "shuffleSum", ShuffleSumFormula(),
            "The first shuffle reorders rows. The second reorders columns. Each pair contributes once, "
                + "including when other pairs select the same coordinate."),
        Definition("printed-rhs", "Right-hand side of the printed shuffle", "printedRhs", PrintedRhsFormula(),
            "Definition 2.6, p. 5, uses the empty pair as a two-sided unit and inverts the block rank "
                + "for nonempty inputs. The finite index in the last branch has natural value equal to "
                + "the sum of the degrees. The supplied bound h gives its strict bound via Nat.lt_succ_of_le.",
            fromLiterature: true),
        Definition("printed", "The printed truncated shuffle equations", "Printed",
            PrintedFormula(),
            "Theorem 2.10, p. 6, uses the product in Definition 2.6. Every ordered pair is tested "
                + "when its natural degrees sum to at most the cutoff. At cutoff four the pair (3,3) "
                + "is outside the domain because the natural sum is six. The unit branches apply "
                + "when either degree is zero, including when both are zero.", fromLiterature: true),
        Definition("cycle-231", "The three-cycle in the witness pair", "cycle231",
            Eq(Named("cycle231"), Compose(Call("swap", D(0), D(2)), Call("swap", D(0), D(1)))),
            "The swaps act on Fin 3, with the rightmost swap first. The one-line form in one-based notation is 231.")
    ];

    private static DocumentBlock[] SignatureDefinitions() =>
    [
        Definition("axis", "Axis coordinates", "Axis",
            All(Eq(Axis(V("l")), Arrow(Fin(V("l")), R)), ("l", N)),
            "An axis is a tuple of real coordinates of the given degree."),
        Definition("axes", "Paired axis coordinates", "Axes",
            All(Eq(Axes(V("l")), Product(Axis(V("l")), Axis(V("l")))), ("l", N)),
            "The first axis supplies row coordinates and the second supplies column coordinates."),
        Definition("cube", "Unit cube", "cube",
            All(Eq(Call("cube", V("l")),
                    new Formula.SetBuilder(V("x"), Axis(V("l")),
                        All(Member(App(V("x"), V("i")), Named("UnitInterval")), ("i", Fin(V("l")))))),
                ("l", N)),
            "Every coordinate belongs to the closed unit interval."),
        Definition("simplex", "Weakly increasing unit simplex", "simplex",
            All(Eq(Call("simplex", V("l")),
                    new Formula.SetBuilder(V("x"), Call("cube", V("l")), Call("Monotone", V("x")))),
                ("l", N)),
            "The entries are weakly increasing in slot order."),
        Definition("coordinate", "Paired coordinate evaluation", "coordinate",
            All(Eq(Call("coordinate", V("i"), V("j"), V("z")),
                    Pair(App(Projection(V("z"), D(1)), V("i")), App(Projection(V("z"), D(2)), V("j")))),
                ("l", N), ("i", Fin(V("l"))), ("j", Fin(V("l"))), ("z", Axes(V("l")))),
            "The two slot indices select coordinates on separate axes."),
        Definition("integrand", "Product of paired component evaluations", "integrand", IntegrandFormula(),
            "The word selects the component. The rank permutes the slots of the column axis."),
        Definition("simplex-integral", "Integral over the two simplices", "simplexIntegral",
            All(Eq(Call("simplexIntegral", V("f"), V("w"), V("r")),
                    Integral(V("l"), V("f"), V("w"), V("r"))),
                ("d", N), ("l", N), ("f", Components), ("w", Word(V("l"))), ("r", Rank(V("l")))),
            "The measure is Lean's volume on the product of real coordinate spaces, restricted to the two simplices."),
        Definition("signature", "Native mixed-partial signature", "signature", SignatureFormula(),
            "Definition 1.1, p. 2, uses the two weakly increasing unit simplices and assigns one to the "
                + "empty coordinate. The coordinate integrand evaluates the real mixed partial at "
                + "row slot j and column slot r(j). The integral is independent of the ambient "
                + "extension of an eligible square membrane.", fromLiterature: true),
        Definition("realizes", "Realization by a piecewise bilinear membrane", "Realizes",
            All(IffOf(Call("Realizes", V("s")), Some(
                    And(Call("PiecewiseBilinear", V("X")), Eq(Call("signature", V("X")), V("s"))),
                    ("X", Membrane))),
                ("d", N), ("k", N), ("s", Array(R))),
            "Signature equality is equality of the entire truncated array.")
    ];

    private static DocumentBlock[] WitnessDefinitions() =>
    [
        Definition("rank-code", "One-based decimal permutation code", "rankCode",
            All(Eq(Call("rankCode", V("r")),
                    Seq(new Formula.Subscript(Sum, Typed(V("i"), Fin(V("l")))), Sp,
                        Mul(Add(Val(App(V("r"), V("i"))), D(1)),
                            new Formula.Power(D(1, 0), Sub(Sub(V("l"), D(1)), Val(V("i"))))))),
                ("l", N), ("r", Rank(V("l")))),
            "Lean folds the one-based entries in slot order by multiplying the accumulator by ten and "
                + "adding the next entry, starting at zero. The exponent uses natural subtraction. "
                + "The code of the empty permutation is zero."),
        Definition("table-entry", "Rational certificate lookup", "tableEntry", TableEntryFormula(),
            "The rows give the nonzero code-to-value assignments in increasing code order. "
                + "The finite map is indexed by the requested code with default zero."),
        Definition("rational-witness", "Rational truncated array", "rationalWitness",
            All(Eq(Call("rationalWitness", V("l"), V("w"), V("r")),
                    Cases(
                        Case(Call("tableEntry", Call("rankCode", V("r"))),
                            All(Eq(App(V("w"), V("i")), D(0)), ("i", Fin(Val(V("l")))))),
                        Otherwise(D(0)))),
                ("l", Fin(D(5))), ("w", Call("Word", D(2), Val(V("l")))), ("r", Rank(Val(V("l"))))),
            "These entries form an Array over the rationals. In the empty degree the condition holds vacuously."),
        Definition("one-word", "Constant first-letter word", "oneWord",
            All(Eq(Typed(Call("oneWord", V("d"), V("l")), Call("Word", Add(V("d"), D(1)), V("l"))),
                    Abstract(V("i"), Fin(V("l")), D(0))),
                ("d", N), ("l", N)),
            "The alphabet has d+1 letters and its first letter has index zero."),
        Definition("witness", "Real truncated array", "witness",
            All(Eq(Call("witness", V("l"), V("w"), V("r")),
                    Call("cast", Call("rationalWitness", V("l"), V("w"), V("r")), R)),
                ("l", Fin(D(5))), ("w", Call("Word", D(2), Val(V("l")))), ("r", Rank(Val(V("l"))))),
            "The rational entries are cast to real numbers coordinate by coordinate.")
    ];

    private static DocumentBlock Definition(
        string id, string title, string declaration, Formula formula, string prose, bool fromLiterature = false) =>
        Describe.Lean(
            DescribeId.Create("amendola-riffo-schmitz-" + id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(Disp(formula)),
            fromLiterature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Q => Seq(Mathbb, Grp(V("Q")));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Type => Named("Type");
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Val(Formula index) => Call("val", index);
    private static Formula Rank(Formula degree) => Call("Rank", degree);
    private static Formula Word(Formula degree) => Call("Word", V("d"), degree);
    private static Formula Array(Formula coefficient) => Call("Array", coefficient, V("d"), V("k"));
    private static Formula Axis(Formula degree) => Call("Axis", degree);
    private static Formula Axes(Formula degree) => Call("Axes", degree);
    private static Formula Membrane => Call("Membrane", V("d"));
    private static Formula Components => Arrow(Fin(V("d")), Named("Plane"), R);
    private static Formula TruncatedDegree => Fin(Add(V("k"), D(1)));
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Compose(Formula a, Formula b) => Seq(a, Sp, Circ, Sp, b);
    private static Formula Projection(Formula pair, Formula slot) => Seq(pair, Dot, slot);
    private static Formula Inverse(Formula f) => new Formula.Power(f, Seq(Minus, D(1)));
    private static Formula Interval(Formula low, Formula high, bool closed) =>
        Seq(closed ? OpenBracket : Open, low, Comma, Sp, high, closed ? CloseBracket : Close);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Arrow(Formula first, Formula second, Formula third) => Arrow(first, Arrow(second, third));
    private static Formula Arrow(Formula first, Formula second, Formula third, Formula fourth) =>
        Arrow(first, Arrow(second, third, fourth));
    private static Formula Abstract(Formula value, Formula domain, Formula body) =>
        Parenthesized(Seq(Typed(value, domain), Sp, Mapsto, Sp, body));
    private static Formula All(Formula body, params (string Name, Formula Domain)[] variables) =>
        Bind(FormulaQuantifier.ForAll, body, variables);
    private static Formula Some(Formula body, params (string Name, Formula Domain)[] variables) =>
        Bind(FormulaQuantifier.Exists, body, variables);
    private static Formula Bind(FormulaQuantifier quantifier, Formula body,
        (string Name, Formula Domain)[] variables) =>
        new Formula.BindMany(quantifier,
            [.. variables.Select(variable => new Formula.BoundVariable(
                FormulaIdentifier.Create(variable.Name), variable.Domain))],
            body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LE(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LT(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula If(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Cases(params Formula[] rows) =>
        Seq(Left, OpenBrace, new Formula.Aligned([.. rows]), Right, Dot);
    private static Formula Case(Formula value, Formula condition) =>
        Seq(value, Amp, Quad, F.Text, Grp(V("if")), Sp, condition);
    private static Formula Otherwise(Formula value) =>
        Seq(value, Amp, Quad, F.Text, Grp(V("otherwise")));

    private static Formula ClaimFormula()
    {
        var arrays = All(If(Call("Printed", V("s")), Call("Realizes", V("s"))), ("s", Array(R)));
        return All(If(LE(D(2), V("d")), Parenthesized(arrays)), ("d", N), ("k", N));
    }

    private static Formula StripFormula(string name, bool closed)
    {
        var i = Val(V("i"));
        return All(Eq(Call(name, V("m"), V("i")),
                Interval(Call("gridPoint", V("m"), i), Call("gridPoint", V("m"), Add(i, D(1))), closed)),
            ("m", N), ("i", Fin(V("m"))));
    }

    private static Formula GridFormula()
    {
        var polynomial = Add(Add(Add(V("a"), Mul(V("b"), V("s"))), Mul(V("e"), V("t"))),
            Mul(Mul(V("f"), V("s")), V("t")));
        var patch = All(If(And(Member(V("s"), Call("closedStrip", V("m"), V("i"))),
                Member(V("t"), Call("closedStrip", V("n"), V("j")))),
                Eq(App(V("X"), V("s"), V("t"), V("c")), polynomial)),
            ("s", R), ("t", R));
        var coefficients = Some(patch, ("a", R), ("b", R), ("e", R), ("f", R));
        var cells = All(coefficients, ("i", Fin(V("m"))), ("j", Fin(V("n"))), ("c", Fin(V("d"))));
        var grid = Some(And(And(LT(D(0), V("m")), LT(D(0), V("n"))), Parenthesized(cells)),
            ("m", N), ("n", N));
        return All(IffOf(Call("PiecewiseBilinear", V("X")), Parenthesized(grid)), ("d", N), ("X", Membrane));
    }

    private static Formula MixedFormula()
    {
        var columnFunction = Abstract(V("t"), R, App(V("X"), V("s"), V("t"), V("c")));
        var columnDerivative = Call("deriv", columnFunction, Projection(V("z"), D(2)));
        var rowFunction = Abstract(V("s"), R, columnDerivative);
        return All(Eq(Call("mixed", V("X"), V("c"), V("z")),
                Call("deriv", rowFunction, Projection(V("z"), D(1)))),
            ("d", N), ("X", Membrane), ("c", Fin(V("d"))), ("z", Named("Plane")));
    }

    private static Formula BoundedMeasurableFormula()
    {
        var value = App(V("f"), V("c"), V("z"));
        var norm = Seq(Lvert, Lvert, Sp, value, Rvert, Rvert);
        var measurability = All(Call("Measurable", App(V("f"), V("c"))), ("c", Fin(V("d"))));
        var bound = Some(And(LE(D(0), V("M")),
                Parenthesized(All(LE(norm, V("M")), ("c", Fin(V("d"))), ("z", Named("Plane"))))), ("M", R));
        return All(IffOf(Call("BoundedMeasurable", V("f")),
                And(Parenthesized(measurability), Parenthesized(bound))),
            ("d", N), ("f", Components));
    }

    private static Formula LeftSlot(Formula i) => Call("castAdd", V("n"), i);
    private static Formula RightSlot(Formula i) => Call("natAdd", V("m"), i);

    private static Formula InsertionRankFormula()
    {
        var rank = Call("insertionRank", V("p"));
        var slot = V("i");
        var tail = All(Eq(App(rank, Call("succAbove", D(0), slot)),
            Call("succAbove", V("p"), slot)), ("i", Fin(D(3))));
        return All(And(Eq(App(rank, D(0)), V("p")), Parenthesized(tail)), ("p", Fin(D(4))));
    }

    private static Formula BlockRankFormula()
    {
        var rank = Call("blockRank", V("a"), V("b"));
        var left = All(Eq(App(rank, LeftSlot(V("i"))), LeftSlot(App(V("a"), V("i")))), ("i", Fin(V("m"))));
        var right = All(Eq(App(rank, RightSlot(V("j"))), RightSlot(App(V("b"), V("j")))), ("j", Fin(V("n"))));
        return All(And(Parenthesized(left), Parenthesized(right)),
            ("m", N), ("n", N), ("a", Rank(V("m"))), ("b", Rank(V("n"))));
    }

    private static Formula ShufflesFormula()
    {
        var i = V("i");
        var j = V("j");
        var pi = V("p");
        var left = All(If(LT(i, j), LT(App(pi, LeftSlot(i)), App(pi, LeftSlot(j)))),
            ("i", Fin(V("m"))), ("j", Fin(V("m"))));
        var right = All(If(LT(i, j), LT(App(pi, RightSlot(i)), App(pi, RightSlot(j)))),
            ("i", Fin(V("n"))), ("j", Fin(V("n"))));
        return All(Eq(Call("shuffles", V("m"), V("n")),
                new Formula.SetBuilder(pi, Rank(Add(V("m"), V("n"))),
                    And(Parenthesized(left), Parenthesized(right)))),
            ("m", N), ("n", N));
    }

    private static Formula ShuffleSumFormula()
    {
        var degree = Add(V("m"), V("n"));
        var shuffles = Call("shuffles", V("m"), V("n"));
        var pair = Pair(V("p"), V("q"));
        var inverseRow = Inverse(V("p"));
        var word = Compose(Call("append", V("u"), V("v")), inverseRow);
        var rank = Compose(V("q"), Compose(V("b"), inverseRow));
        var sum = Seq(new Formula.Subscript(Sum, Member(pair, Product(shuffles, shuffles))), Sp,
            App(V("s"), word, rank));
        return WithCoefficientStructure("AddCommMonoid", All(
            Eq(Call("shuffleSum", V("s"), V("u"), V("v"), V("b")), sum),
            ("d", N), ("m", N), ("n", N), ("s", Arrow(Word(degree), Rank(degree), V("R"))),
            ("u", Word(V("m"))), ("v", Word(V("n"))), ("b", Rank(degree))));
    }

    private static Formula AdmissibleBound => LE(Add(Val(V("m")), Val(V("n"))), V("k"));

    private static Formula PrintedInputs(Formula body) =>
        All(body, ("m", TruncatedDegree), ("n", TruncatedDegree), ("h", Parenthesized(AdmissibleBound)),
            ("u", Word(Val(V("m")))), ("v", Word(Val(V("n")))),
            ("a", Rank(Val(V("m")))), ("b", Rank(Val(V("n")))));

    private static Formula WithCoefficientStructure(string structure, Formula body) =>
        All(Seq(OpenBracket, Call(structure, V("R")), CloseBracket, Comma, SemiSpace, body), ("R", Type));

    private static Formula CoefficientContext(string structure, Formula body) =>
        WithCoefficientStructure(structure, All(body, ("d", N), ("k", N), ("s", Array(V("R")))));

    private static Formula PrintedRhsCall() =>
        Call("printedRhs", V("s"), V("m"), V("n"), V("h"), V("u"), V("v"), V("a"), V("b"));

    private static Formula PrintedRhsFormula()
    {
        var m = Val(V("m"));
        var n = Val(V("n"));
        var combined = Seq(Langle, Add(m, n), Comma, Sp, Call("ltSuccOfLe", V("h")), Rangle);
        var positive = Call("shuffleSum", App(V("s"), combined), V("u"), V("v"),
            Inverse(Call("blockRank", V("a"), V("b"))));
        var rhs = Cases(
            Case(App(V("s"), V("n"), V("v"), V("b")), Eq(m, D(0))),
            Case(App(V("s"), V("m"), V("u"), V("a")),
                And(LT(D(0), m), Eq(n, D(0)))),
            Case(positive, And(LT(D(0), m), LT(D(0), n))));
        return CoefficientContext("AddCommMonoid", PrintedInputs(Eq(PrintedRhsCall(), rhs)));
    }

    private static Formula PrintedFormula()
    {
        var lhs = Mul(App(V("s"), V("m"), V("u"), V("a")), App(V("s"), V("n"), V("v"), V("b")));
        return CoefficientContext("Semiring",
            IffOf(Call("Printed", V("s")), Parenthesized(PrintedInputs(Eq(lhs, PrintedRhsCall())))));
    }

    private static Formula IntegrandFormula()
    {
        var i = V("i");
        var degree = V("l");
        var coordinates = Call("coordinate", i, App(V("r"), i), V("z"));
        var value = App(V("f"), App(V("w"), i), coordinates);
        var product = Seq(new Formula.Subscript(Prod, Typed(i, Fin(degree))), Sp, value);
        return All(Eq(Call("integrand", V("f"), V("w"), V("r"), V("z")), product),
            ("d", N), ("l", N), ("f", Components), ("w", Word(degree)), ("r", Rank(degree)),
            ("z", Axes(degree)));
    }

    private static Formula Integral(Formula degree, Formula f, Formula w, Formula tau)
    {
        var simplex = Call("simplex", degree);
        return Seq(new Formula.Subscript(Int, Product(simplex, simplex)), Sp,
            Call("integrand", f, w, tau, V("z")), Thin, V("dz"));
    }

    private static Formula SignatureFormula()
    {
        var degree = Val(V("l"));
        var value = Call("signature", V("X"), V("l"), V("w"), V("r"));
        var rhs = Cases(
            Case(D(1), Eq(degree, D(0))),
            Case(Integral(degree, Call("mixed", V("X")), V("w"), V("r")), LT(D(0), degree)));
        return All(Eq(value, rhs), ("d", N), ("k", N), ("X", Membrane), ("l", TruncatedDegree),
            ("w", Word(degree)), ("r", Rank(degree)));
    }

    private static Formula TableEntryFormula()
    {
        (int Code, int Numerator, int Denominator)[][] entries =
        [
                [(0, 1, 1), (1, 3, 1), (12, 7, 4), (21, 11, 4)],
                [(123, 7, 12), (132, 1, 3), (213, 1, 3), (231, 19, 12)],
                [(312, 7, 12), (321, 13, 12), (1234, 71, 576), (1243, 55, 576)],
                [(1324, 35, 576), (1342, 19, 576), (1423, 19, 576), (1432, 19, 576)],
                [(2134, 55, 576), (2143, 13, 192), (2314, 19, 576), (2341, 35, 576)],
                [(2413, 1, 192), (2431, 35, 576), (3124, 19, 576), (3142, 1, 192)],
                [(3214, 19, 576), (3241, 35, 576), (3412, 73, 192), (3421, 107, 576)],
                [(4123, 323, 576), (4132, 179, 576), (4213, 179, 576), (4231, 67, 576)],
                [(4312, 251, 576), (4321, 139, 576)]
        ];
        var table = new Formula.Aligned([.. entries.Select(row => Seq(
            ListItems([.. row.Select(entry => Seq(Number(entry.Code), Sp, Mapsto, Sp,
                entry.Denominator == 1 ? Number(entry.Numerator)
                    : new Formula.Fraction(Number(entry.Numerator), Number(entry.Denominator))))])))]);
        var values = Seq(Left, OpenBrace, table, Right, CloseBrace);
        return All(Eq(Parenthesized(Typed(Call("tableEntry", V("q")), Q)),
                Call("getD", Call("lookup", V("q"), values), D(0))), ("q", N));
    }

    private static Formula ListItems(Formula[] items) =>
        Seq([.. items.SelectMany((item, index) => index == 0 ? new[] { item } : [Comma, Quad, item])]);

    private static Formula Number(int value) =>
        D([.. value.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(digit => (byte)(digit - '0'))]);
}
