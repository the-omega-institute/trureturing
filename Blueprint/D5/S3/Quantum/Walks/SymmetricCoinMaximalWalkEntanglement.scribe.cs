using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Walks;

internal sealed class SymmetricCoinMaximalWalkEntanglementDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/Entropy/donkerslootsondenheimersperling2026walks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The symmetric localized coin maximizes full-mode geometric entanglement at every time on every finite circle.",
        H("Maximal walk entanglement from the symmetric coin"),
        Blocks(
            Definition("hadamard-step", "hadamardStep", "The Hadamard step on a circle", HadamardStepFormula(),
                "The coin labels zero and one represent the left-moving and right-moving components. "
                    + "A Hadamard coin flip followed by the controlled periodic shift gives the displayed amplitudes: "
                    + "the left-moving amplitude at a position comes from the next position, "
                    + "and the right-moving amplitude comes from the preceding position. "
                    + "Positions are residues in ZMod p. The real square root of two is explicitly included in the complex scalars. "
                    + "This is the walk of arxiv-v1.tex, lines 139–166; the definition also makes sense at p equal to zero.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("walk-state", "walkState", "Evolution of a localized coin", WalkStateFormula(),
                "Initially the two coin amplitudes c are at position zero and every other position has amplitude zero. "
                    + "Iterating the Hadamard step n times gives walkState. "
                    + "The time evolution is specified in arxiv-v1.tex, lines 165–166, "
                    + "and the localized initial states in lines 423–425. The definition allows every complex coin c.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("symmetric-coin", "cStar", "The symmetric coin", CStarFormula(),
                "The entries are one over the square root of two and the imaginary unit over the square root of two. "
                    + "They give the source's angles theta and phi both equal to pi over two "
                    + "in the localized initial state, as in arxiv-v1.tex, lines 423–425 and 652–654.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("w-state", "wState", "The generalized W vector", WStateFormula(),
                "A Boolean string s records the occupation of each mode. "
                    + "For each k, updating the constantly false string to true at k gives the string with its sole excitation at k. "
                    + "The coefficient of that string is lam k; all other strings have coefficient zero. "
                    + "This is the generalized W state in arxiv-v1.tex, lines 286–293, "
                    + "expressed for an arbitrary finite mode type and without a normalization condition on lam.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("product-state", "productState", "A product of local two-component vectors", ProductStateFormula(),
                "The amplitude at a Boolean string is the product of the chosen local coordinates: "
                    + "coordinate one at an occupied mode and coordinate zero at an empty mode. "
                    + "This expresses the product states of arxiv-v1.tex, lines 227–235, for the partition into individual modes. "
                    + "The vectors z need not be normalized in this definition.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("unit-factors", "unitFactors", "Normalized local factors", UnitFactorsFormula(),
                "Each local two-component vector has the sum of its squared complex moduli equal to one. "
                    + "UnitSpinor denotes precisely this unit Hilbert norm condition. "
                    + "These are the normalized factors used in the product-state supremum of arxiv-v1.tex, lines 249–254.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("overlap", "overlap", "The product overlap", OverlapFormula(),
                "Sum over all Boolean occupation strings, conjugating the product-state amplitude and multiplying by the W-state amplitude. "
                    + "Thus overlap is the usual complex inner product with the product vector in its conjugate-linear argument. "
                    + "It is the overlap used in arxiv-v1.tex, lines 249–254, for the W states of lines 286–293.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("g-max", "gMax", "The maximum squared product overlap", GMaxFormula(),
                "Take the real supremum of the squared complex modulus of overlap over all unit local factors. "
                    + "Complex.normSq is the squared modulus, so no square root is taken in this definition. "
                    + "This is the full-partition quantity in arxiv-v1.tex, lines 249–254 and 281–290. "
                    + "The formula defines the functional for every finite amplitude family, including families that are not normalized.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("geometric-entanglement", "geometricEntanglement", "Full-mode geometric entanglement", GeometricEntanglementFormula(),
                "Subtracting the maximal squared product overlap from one gives the geometric measure in arxiv-v1.tex, lines 253–258. "
                    + "Every individual mode is a separate tensor factor. "
                    + "The definition is extended to arbitrary finite amplitude families; its interpretation as pure-state entanglement uses a normalized state.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("claim", "claim", "The symmetric coin gives maximal entanglement", ClaimFormula(),
                "For every natural p at least one, every natural time n, and every normalized coin c, "
                    + "the geometric entanglement of walkState p n c is at most that of walkState p n cStar. "
                    + "A positive p makes ZMod p a finite position type, giving two p individual modes. "
                    + "This states the expectation of arxiv-v1.tex, lines 652–654, for the circle walk and the full partition. "
                    + "Step zero and the one-position circle are included. The statement asserts maximality without asserting uniqueness.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Balancing reflection pairs proves maximality"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Expand the inner product by the single occupied mode. Its kth summand is lam k times the conjugate "
                            + "of the product of z k 1 with all z l 0 for l different from k. "
                            + "For unit local factors the squared norm of the product vector is one: "
                            + "the sum over occupation strings factors into the product of the local squared norms. "
                            + "Cauchy–Schwarz therefore bounds every squared overlap by the squared norm of the W vector. "
                            + "The local unit sets are closed and bounded, and hence compact; their finite product is compact and contains the constant family with local vector (1,0). "
                            + "The squared overlap is continuous on this product, so its supremum is attained.")),
                    Paragraph(Text(
                        "Suppose lam and mu have equal squared moduli at every mode. "
                            + "At a mode with nonzero lam k, set rho k to mu k divided by lam k; at a zero coefficient set rho k to one. "
                            + "Then rho k has squared modulus one and mu k equals rho k times lam k. "
                            + "Multiplying the occupied coordinate of each local factor by rho k preserves its norm, "
                            + "and the conjugate phase cancels the coefficient phase in each expanded summand. "
                            + "Transporting factors in both directions gives equal sets of squared overlaps and therefore equal gMax values. "
                            + "For nonnegative real coefficients, the triangle inequality bounds the modulus of every complex overlap by the overlap of the coordinatewise moduli. "
                            + "Those real nonnegative factors remain normalized and attain the bound at a maximizer. "
                            + "Thus a maximum can be chosen with every local coordinate nonnegative and real.")),
                    Paragraph(Text(
                        "The required two-dimensional optimization starts with the real quadratic form "
                            + "d times y 0 squared plus twice f times y 0 times y 1 plus e times y 1 squared, with f nonnegative. "
                            + "Let t be one half of the sum of d, e, and the square root of the sum of (d minus e) squared and four f squared. "
                            + "Then t is at least both d and e, and (t minus d)(t minus e) equals f squared. "
                            + "If t equals e, f is zero, the form is bounded by t on the unit circle, and (0,1) attains t. "
                            + "Otherwise t minus e is positive; multiplying the gap from t by t minus e expresses it as "
                            + "the square of (t minus e) times y 1 minus f times y 0. "
                            + "The nonnegative unit vector proportional to (t minus e,f) attains t.")),
                    Paragraph(Text(
                        "Apply this quadratic optimization to d equal to a squared plus b squared r squared, "
                            + "e equal to b squared s squared, and f equal to a b s, where a, b, r, s are nonnegative. "
                            + "For unit real x and y, the squared bilinear expression "
                            + "a x 0 y 0 plus b s x 0 y 1 plus b r x 1 y 0 is bounded first by Cauchy–Schwarz in x and then by that quadratic maximum in y. "
                            + "Write C for a squared plus b squared times (r squared plus s squared). "
                            + "The resulting maximum is one half of the sum of C and the square root of the difference between C squared "
                            + "and four b to the fourth times r squared s squared. "
                            + "For a maximizing y, take the vector v with coordinates a y 0 plus b s y 1 and b r y 0. "
                            + "Its squared norm is the maximum. If that norm is zero, x equal to (1,0) attains zero; "
                            + "otherwise x equal to v divided by the square root of the maximum attains the bound. "
                            + "Both maximizing vectors have nonnegative coordinates.")),
                    Paragraph(Text(
                        "Now fix two distinct modes i and j and all spectator factors. Let s be the other modes, "
                            + "d the sum of their single-excitation contributions, and e the product of their empty-mode coordinates. "
                            + "Splitting the expanded overlap into excitations in s, at j, and at i leaves "
                            + "d z i 0 z j 0 plus e a j z i 0 z j 1 plus e a i z i 1 z j 0. "
                            + "For nonnegative coefficient families a and b agreeing off i and j, suppose their sums of squares at the pair agree "
                            + "and b i squared times b j squared is at least a i squared times a j squared. "
                            + "Start with nonnegative maximizing factors for b. In the two-factor formula the trace C is unchanged, "
                            + "while the larger product for b decreases the expression under the square root. "
                            + "Replace only the two local factors by maximizing factors for a; the spectator contributions d and e stay the same. "
                            + "This gives gMax b at most gMax a. Replacing arbitrary complex coefficients by their moduli using phase invariance "
                            + "gives the same comparison whenever the squared moduli agree off the pair, "
                            + "their pair sums agree, and their pair products increase.")),
                    Paragraph(Text(
                        "For the walk, induction on n gives linearity in c: each amplitude is c 0 times the evolution from (1,0) "
                            + "plus c 1 times the evolution from (0,1). A second induction proves that these two basis-coin evolutions are real. "
                            + "At reflected positions their amplitudes satisfy the following signs: "
                            + "the first evolution at (1,−x) is minus (−1) to the power n times the second at (0,x), "
                            + "and the second at (1,−x) is (−1) to the power n times the first at (0,x). "
                            + "The zero-step identities follow from localization; the induction step follows by substituting the Hadamard recurrence, "
                            + "using −x minus one equal to minus (x plus one), and reversing the sign at each step.")),
                    Paragraph(Text(
                        "Let a and b be the real amplitudes of these two basis-coin evolutions at (0,x). "
                            + "For a unit coin c, linearity and reflection show that the two probabilities at (0,x) and (1,−x) "
                            + "are the squared moduli of c 0 times a plus c 1 times b, and c 1 times a minus c 0 times b. "
                            + "Their sum is a squared plus b squared: the mixed terms cancel and the coin squared norms sum to one. "
                            + "For cStar, each probability is half of a squared plus b squared, since the real and imaginary contributions have no mixed term. "
                            + "Consequently each reflection pair has the same total probability for both coins, and the probabilities for cStar are equal within each pair.")),
                    Paragraph(Text(
                        "For positive p the pairs (0,x),(1,−x), indexed by ZMod p, partition all modes and have distinct members. "
                            + "Induct over a finite set of positions, using the cStar amplitudes on its pairs and the c amplitudes elsewhere. "
                            + "Adding a position changes only its pair. The pair sum is preserved, and equality of the new probabilities "
                            + "makes their product at least the old product, as follows by expanding the square of the old probability difference. "
                            + "The pair comparison therefore cannot increase gMax. Starting with the empty set and ending with all positions gives "
                            + "gMax of walkState p n cStar at most gMax of walkState p n c. "
                            + "Subtracting this inequality from one proves the stated entanglement comparison for every p, n, and c under the displayed hypotheses."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("donkersloot-sondenheimer-sperling-2026-symmetric-coin-entanglement"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))),
        DescribeRole.Definition);

    private static Formula HadamardStepFormula()
    {
        var position = At(Qualified("Prod", "snd"), X("j"));
        var next = Add(position, Typed(D(1), Positions));
        var previous = Subtract(position, Typed(D(1), Positions));
        Formula Amplitude(byte coin, Formula x) => At(Psi, Pair(Typed(D(coin), Coin), x));
        return All(X("p"), Naturals, All(Psi, Amplitudes,
            Equal(At(Local("hadamardStep"), X("p"), Psi),
                LambdaOf(X("j"), Modes, If(Equal(At(Qualified("Prod", "fst"), X("j")), Typed(D(0), Coin)),
                    Divide(Add(Amplitude(0, next), Amplitude(1, next)), SqrtTwoComplex),
                    Divide(Subtract(Amplitude(0, previous), Amplitude(1, previous)), SqrtTwoComplex))))));
    }

    private static Formula WalkStateFormula() => All(X("p"), Naturals, All(X("n"), Naturals,
        All(X("c"), Arrow(Coin, Complexes), Equal(At(Local("walkState"), X("p"), X("n"), X("c")),
            At(Qualified("Nat", "iterate"), At(Local("hadamardStep"), X("p")), X("n"),
                LambdaOf(X("j"), Modes,
                    If(Equal(At(Qualified("Prod", "snd"), X("j")), Typed(D(0), Positions)),
                        At(X("c"), At(Qualified("Prod", "fst"), X("j"))), Typed(D(0), Complexes))))))));

    private static Formula CStarFormula() => Equal(Typed(Local("cStar"), Arrow(Coin, Complexes)),
        Seq(Bang, OpenBracket, Divide(Typed(D(1), Complexes), SqrtTwoComplex), Comma, Sp,
            Divide(Qualified("Complex", "I"), SqrtTwoComplex), CloseBracket));

    private static Formula WStateFormula() => OverFiniteModes(All(X("lam"), Arrow(Iota, Complexes),
        Equal(At(Local("wState"), X("lam")), LambdaOf(X("s"), Strings,
            SumOver(X("k"), Iota, If(Equal(X("s"), At(Qualified("Function", "update"),
                    At(Qualified("Function", "const"), Iota, Qualified("false")), X("k"), Qualified("true"))),
                At(X("lam"), X("k")), Typed(D(0), Complexes)))))));

    private static Formula ProductStateFormula() => OverFiniteModes(All(X("z"), Factors,
        Equal(At(Local("productState"), X("z")), LambdaOf(X("s"), Strings,
            ProductOver(X("k"), Iota, At(X("z"), X("k"),
                If(Equal(At(X("s"), X("k")), Qualified("true")), Typed(D(1), Coin), Typed(D(0), Coin))))))));

    private static Formula UnitFactorsFormula() => All(Iota, TypeStar, All(X("z"), Factors,
        Equal(At(Local("unitFactors"), X("z")), Parenthesized(All(X("k"), Iota, UnitSpinor(At(X("z"), X("k"))))))));

    private static Formula OverlapFormula() => OverFiniteModes(All(X("lam"), Arrow(Iota, Complexes),
        All(X("z"), Factors, Equal(At(Local("overlap"), X("lam"), X("z")),
            SumOver(X("s"), Strings, Multiply(
                At(At(Qualified("starRingEnd"), Complexes), At(Local("productState"), X("z"), X("s"))),
                At(Local("wState"), X("lam"), X("s"))))))));

    private static Formula GMaxFormula() => OverFiniteModes(All(X("lam"), Arrow(Iota, Complexes),
        Equal(At(Local("gMax"), X("lam")), At(Qualified("sSup"),
            Seq(OpenBrace, X("t"), Colon, Sp, Reals, Sp, Mid, Sp,
                Some(X("z"), Factors, Conjunction(At(Local("unitFactors"), X("z")),
                    Equal(X("t"), At(Qualified("Complex", "normSq"), At(Local("overlap"), X("lam"), X("z")))))),
                CloseBrace)))));

    private static Formula GeometricEntanglementFormula() => OverFiniteModes(All(X("lam"), Arrow(Iota, Complexes),
        Equal(At(Local("geometricEntanglement"), X("lam")), Subtract(Typed(D(1), Reals), At(Local("gMax"), X("lam"))))));

    private static Formula ClaimFormula() => Equal(Local("claim"), Parenthesized(ClaimBody()));
    private static Formula ClaimBody() => All(X("p"), Naturals, Implication(LE(Typed(D(1), Naturals), X("p")),
        All(X("n"), Naturals, All(X("c"), Arrow(Coin, Complexes), Implication(UnitSpinor(X("c")),
            LE(At(Local("geometricEntanglement"), At(Local("walkState"), X("p"), X("n"), X("c"))),
                At(Local("geometricEntanglement"), At(Local("walkState"), X("p"), X("n"), Local("cStar")))))))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Local(string name) => Qualified(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Naturals => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(X("C")));
    private static Formula TypeStar => Seq(Qualified("Type"), Star);
    private static Formula Coin => At(Qualified("Fin"), D(2));
    private static Formula Positions => At(Qualified("ZMod"), X("p"));
    private static Formula Modes => Seq(Parenthesized(Coin), Sp, Times, Sp, Parenthesized(Positions));
    private static Formula Amplitudes => Arrow(Modes, Complexes);
    private static Formula Strings => Arrow(Iota, Qualified("Bool"));
    private static Formula Factors => Arrow(Iota, Arrow(Coin, Complexes));
    private static Formula SqrtTwoComplex => At(Qualified("Complex", "ofReal"),
        At(Qualified("Real", "sqrt"), Typed(D(2), Reals)));
    private static Formula UnitSpinor(Formula c) => At(Qualified(
        "D5", "S3", "Quantum", "Recovery", "FiniteLocalLatitudeGeometry", "UnitSpinor"), c);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(Formula variable, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(variable, type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula OverFiniteModes(Formula body) => All(Iota, TypeStar,
        Seq(OpenBracket, At(Qualified("Fintype"), Iota), CloseBracket, Sp, body));
    private static Formula If(Formula condition, Formula yes, Formula no) => At(Qualified("ite"), condition, yes, no);
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula ProductOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(variable, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
}
