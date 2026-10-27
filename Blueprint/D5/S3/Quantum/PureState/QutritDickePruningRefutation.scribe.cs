using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class QutritDickePruningRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/PureState/QutritDickePruningRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/nepomechieraveh2024quditdicke");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pruned qutrit circuit has zero amplitude at a word required by the Dicke state with occupation (1,3,1).",
        H("A missing amplitude in the pruned qutrit Dicke circuit"),
        Blocks(
            Node("State", "Real amplitudes on qutrit words", StateFormula(),
                "An n-qutrit amplitude function assigns a real number to each word Fin n → Fin 3. "
                    + "No normalization condition is imposed on this function space.",
                AssessedProvenance.FromRepo(Source)),
            Node("Occupation", "Three occupation counts", OccupationFormula(),
                "An occupation vector assigns a natural count to each of the three letters, as in qdit_v3.tex, lines 177–178. "
                    + "The type alone imposes no condition on the sum of the counts.",
                AssessedProvenance.FromLiterature(Source)),
            Node("wire", "Reading a wire", WireFormula(),
                "Wire numbers increase from right to left. A read at r < n returns the letter at the corresponding finite index; "
                    + "a read outside the register returns the letter zero. The bound proof h supplies the finite index.",
                AssessedProvenance.FromRepo(Source)),
            Node("put", "Updating a wire", PutFormula(),
                "An update replaces the letter on wire r when r < n and otherwise leaves the word unchanged. "
                    + "The dependent conditional uses h to form the finite index; its other branch is a constant function on the negated bound.",
                AssessedProvenance.FromRepo(Source)),
            Node("controlsHold", "Testing all controls", ControlsFormula(),
                "A list of controls consists of wire and letter pairs. The Boolean test is true precisely when every listed wire lies in the register "
                    + "and carries its specified letter. An empty list passes the test.",
                AssessedProvenance.FromRepo(Source)),
            Node("controlledX", "A controlled exchange", ControlledXFormula(),
                "The controlled exchange from qdit_v3.tex, lines 485–499 and 513–527, uses the swap of letters i and j. "
                    + "At a word satisfying all controls, the amplitude is read from f at that word with its target letter swapped; otherwise it is read from f at the original word. "
                    + "For controls on wires distinct from the target, this is the inverse basis permutation. "
                    + "The displayed extension permits arbitrary control lists and target indices, using wire and put as defined above.",
                AssessedProvenance.FromLiterature(Source)),
            Node("controlledR", "A controlled real rotation", ControlledRFormula(),
                "For distinct i and j, the rotation in qdit_v3.tex, lines 501–509, has rows (c,−s) and (s,c) on the i,j coordinates. "
                    + "It leaves other target letters unchanged and acts only when every control holds. "
                    + "Here c and s are arbitrary real parameters; the later circuits choose their square-root values. "
                    + "There is no assumption i ≠ j in this definition, so the first conditional takes precedence when the two letters coincide.",
                AssessedProvenance.FromLiterature(Source)),
            Node("V", "The exchange–rotation–exchange circuit", VFormula(),
                "The V circuit is given in qdit_v3.tex, lines 598–696, with the angle specified in lines 326–332. "
                    + "The offset n − m places its local wire zero at global wire n − m. The exchange x acts first and last. "
                    + "Between them, the rotation acts on the offset wire, with cosine √(l/m) and sine −√(1−l/m). "
                    + "The predecessor control is omitted for l < 2; the control at the last local wire is included exactly when i.val > 0 and l ≤ m − 2. "
                    + "Subtractions of wire indices are natural subtraction; both l and m are cast to real numbers before division.",
                AssessedProvenance.FromLiterature(Source)),
            Node("I", "The three two-letter circuits", IFormula(),
                "The product in qdit_v3.tex, lines 612–619, applies V for the letter pairs (0,1), (0,2), then (1,2). "
                    + "Function application makes the rightmost circuit act first.",
                AssessedProvenance.FromLiterature(Source)),
            Node("II", "The circuit with two rotations", IIFormula(),
                "The two-rotation circuit and its boundary cases are given in qdit_v3.tex, lines 736–881. "
                    + "Its time order is x, r₁, x, y, r₂, y. Both rotations use the common list cs, with one additional control at off + l₁. "
                    + "The controls at off + (l₂ − 1) and off + (l₁ − 1) are omitted at the indicated boundaries. "
                    + "The two cosine squares are the real ratios l₂/m and (l₁−l₂)/(m−l₂); their sines are the negative square roots of one minus those ratios. "
                    + "In the second ratio, both differences are taken in the natural numbers before being cast to the reals.",
                AssessedProvenance.FromLiterature(Source)),
            Node("prunedTilde", "The pruned single-index product", PrunedTildeFormula(),
                "The range in qdit_v3.tex, lines 1017–1029, retains I gates from max(kt + m − n,1) through min(kt,m−1), inclusive. "
                    + "The parameter kt equals k 2 when k 0 = 0 and otherwise equals max(k 1,k 2). "
                    + "List.Ico excludes its upper endpoint, so the displayed upper bound has an added one. The left fold applies gates in increasing l.",
                AssessedProvenance.FromLiterature(Source)),
            Node("prunedTildeTilde", "The pruned double-index product", PrunedTildeTildeFormula(),
                "The range in qdit_v3.tex, lines 1008–1013, uses l₁ = k 1 + k 2 and l₂ = k 2. "
                    + "The outer index b runs from max(l₂ + m − n,1) through min(l₂,m−2). "
                    + "For each b, the inner index a runs from max(l₁ + m − n,b+1) through min(l₁,m−1). "
                    + "Both ranges are inclusive and are applied in increasing order, with a increasing inside each fixed b.",
                AssessedProvenance.FromLiterature(Source)),
            Node("prunedW", "A pruned register block", PrunedWFormula(),
                "The factorization in qdit_v3.tex, lines 1000–1004, first applies the single-index product and then the double-index product.",
                AssessedProvenance.FromLiterature(Source)),
            Node("prunedU", "The full pruned circuit", PrunedUFormula(),
                "The product in qdit_v3.tex, lines 993–997, applies the largest register block first. "
                    + "Reversing the list 2,…,n gives the time order n,n−1,…,2. Each block uses the same occupation vector k.",
                AssessedProvenance.FromLiterature(Source)),
            Node("initialWord", "The identity-permutation input word", InitialWordFormula(),
                "The input from qdit_v3.tex, lines 191–197, has its twos on the rightmost k 2 wires, followed by k 1 ones, then zeros. "
                    + "The finite index w is explicitly mapped to its natural value before either comparison. "
                    + "The definition is total for arbitrary k; it has occupation k when the three counts sum to n.",
                AssessedProvenance.FromLiterature(Source)),
            Node("dicke", "The Dicke amplitude function", DickeFormula(),
                "The state in qdit_v3.tex, lines 177–185, has a common amplitude on words with the specified letter counts and zero elsewhere. "
                    + "For counts summing to n, its number of words is n!/(k 0! k 1! k 2!). "
                    + "The displayed definition first performs this factorial division in the natural numbers, then casts the quotient to a real number before taking its square root. "
                    + "The count is the multiplicity in the multiset of letters of t; it remains a natural number.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Universal preparation by the pruned circuit", ClaimFormula(),
                "For every natural n at least two and every triple of natural counts summing to n, the pruned circuit is asserted to map "
                    + "the unit amplitude at the identity-permutation input to the Dicke amplitude function. "
                    + "This is the real-coordinate formulation of the proposed preparation identity in qdit_v3.tex, lines 987–1031, "
                    + "with the specific gate order and boundary controls defined above.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("qutrit-dicke-pruning-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The occupation (1,3,1) contradicts universal preparation"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Updating one wire leaves every distinct wire unchanged. Consequently, restriction of amplitudes to a fixed letter on an untouched wire "
                            + "commutes with a controlled exchange and with a controlled rotation. Both operations also commute with multiplication of all amplitudes by a real scalar. "
                            + "These properties pass through the compositions defining V, I and II.")),
                    Paragraph(Text(
                        "Take n = 5 and k = (1,3,1). Write words as lists of their letters on wires 0,1,2,3,4, and write δ_b for the amplitude function "
                            + "equal to one at b and zero elsewhere. Let u = [2,1,1,1,0], b = [0,2,1,1,1] and v = [0,1,1,1,2]. "
                            + "The first block is prunedW 5 5 k = II 5 5 4 1 composed with I 5 5 3. "
                            + "Evaluating the gates on all 3⁵ words shows that I 5 5 3 fixes δ_u. "
                            + "The same finite evaluation of II shows that restricting prunedW 5 5 k δ_u to wire 0 equal to zero gives δ_b/√5.")),
                    Paragraph(Text(
                        "The next block is prunedW 5 4 k = II 5 4 3 1 composed with I 5 4 3 and I 5 4 2, so I 5 4 2 acts first. "
                            + "Each of these three gates fixes δ_b, by evaluation on all 3⁵ words. Every target wire in this block is distinct from wire 0, "
                            + "so restriction to wire 0 equal to zero commutes with the block. Together with scalar multiplication, this proves that after both blocks "
                            + "the restriction is still δ_b/√5. In particular, any amplitude with wire 0 equal to zero and wire 1 different from two vanishes.")),
                    Paragraph(Text(
                        "The remaining blocks apply I 5 3 1, I 5 3 2, II 5 3 2 1, then I 5 2 1. "
                            + "They never target wires 0 or 1, and hence commute with restriction to a specified letter on either wire. "
                            + "For a function f with the preceding vanishing property, its restriction to wire 0 equal to zero is already supported on wire 1 equal to two. "
                            + "Commuting these two restrictions through the remaining composition forces its amplitude at v to be zero, since v has wire 0 equal to zero and wire 1 equal to one. "
                            + "The identity-permutation word for n = 5 and k = (1,3,1) is u, so the full pruned output has zero amplitude at v.")),
                    Paragraph(Text(
                        "The word v contains one zero, three ones and one two. Its Dicke amplitude is therefore 1/√(5!/(1!3!1!)) = 1/√20. "
                            + "This number is nonzero because 20 is positive. Applying the asserted universal identity at n = 5, k₀ = 1, k₁ = 3 and k₂ = 1, "
                            + "and evaluating both functions at v, would equate this nonzero amplitude with zero. Thus claim is false."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nepomechie-raveh-2024-qutrit-dicke-pruning-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("qutrit-dicke-pruning-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula StateFormula() => All("n", Naturals(),
        Equal(LocalCall("State", X("n")), Arrow(Word(X("n")), Reals())));

    private static Formula OccupationFormula() => Equal(Local("Occupation"), Arrow(FinOf(D(3)), Naturals()));

    private static Formula WireFormula()
    {
        Formula condition = Less(X("r"), X("n"));
        Formula index = At(Qualified("Fin", "mk"), X("r"), X("h"));
        return WordBinders(All("r", Naturals(), Equal(Typed(LocalCall("wire", X("t"), X("r")), FinOf(D(3))),
            At(Qualified("dite"), condition, LambdaOf("h", condition, At(X("t"), index)),
                Constant(new Formula.Not(Parenthesized(condition)), Typed(D(0), FinOf(D(3))))))));
    }

    private static Formula PutFormula()
    {
        Formula condition = Less(X("r"), X("n"));
        Formula index = At(Qualified("Fin", "mk"), X("r"), X("h"));
        return WordBinders(All("r", Naturals(), All("a", FinOf(D(3)),
            Equal(Typed(LocalCall("put", X("t"), X("r"), X("a")), Word(X("n"))),
                At(Qualified("dite"), condition,
                    LambdaOf("h", condition, At(Qualified("Function", "update"), X("t"), index, X("a"))),
                    Constant(new Formula.Not(Parenthesized(condition)), X("t")))))));
    }

    private static Formula ControlsFormula()
    {
        Formula first = At(Qualified("Prod", "fst"), X("p"));
        Formula second = At(Qualified("Prod", "snd"), X("p"));
        Formula test = At(Qualified("Bool", "and"), At(Qualified("Decidable", "decide"), Less(first, X("n"))),
            At(Qualified("Decidable", "decide"), Equal(LocalCall("wire", X("t"), first), second)));
        return All("n", Naturals(), All("controls", Controls(), All("t", Word(X("n")),
            Equal(Typed(LocalCall("controlsHold", X("controls"), X("t")), Qualified("Bool")),
                At(Qualified("List", "all"), X("controls"), LambdaOf("p", Control(), test))))));
    }

    private static Formula ControlledXFormula()
    {
        Formula exchanged = At(At(Qualified("Equiv", "swap"), X("i"), X("j")),
            LocalCall("wire", X("t"), X("target")));
        return GateBinders(false, All("f", State(X("n")), Equal(
            Typed(LocalCall("controlledX", X("target"), X("controls"), X("i"), X("j"), X("f")), State(X("n"))),
            LambdaOf("t", Word(X("n")), If(ControlsTrue(),
                At(X("f"), LocalCall("put", X("t"), X("target"), exchanged)), At(X("f"), X("t")))))));
    }

    private static Formula ControlledRFormula()
    {
        Formula value = At(X("f"), X("t"));
        Formula rotation = If(Equal(LocalCall("wire", X("t"), X("target")), X("i")),
            Subtract(Multiply(X("c"), value), Multiply(X("s"), At(X("f"), LocalCall("put", X("t"), X("target"), X("j"))))),
            If(Equal(LocalCall("wire", X("t"), X("target")), X("j")),
                Add(Multiply(X("s"), At(X("f"), LocalCall("put", X("t"), X("target"), X("i")))), Multiply(X("c"), value)), value));
        return GateBinders(true, All("f", State(X("n")), Equal(
            Typed(LocalCall("controlledR", X("target"), X("controls"), X("i"), X("j"), X("c"), X("s"), X("f")), State(X("n"))),
            LambdaOf("t", Word(X("n")), If(ControlsTrue(), rotation, value)))));
    }

    private static Formula VFormula()
    {
        Formula ratio = Divide(CastReal(X("l")), CastReal(X("m")));
        Formula cs = Append(Append(Singleton(Pair(Add(X("off"), X("l")), X("j"))),
            If(LE(D(2), X("l")), Singleton(Pair(Add(X("off"), Subtract(X("l"), D(1))), X("j"))), EmptyList())),
            If(Conjunction(Less(D(0), At(Qualified("Fin", "val"), X("i"))), LE(X("l"), Subtract(X("m"), D(2)))),
                Singleton(Pair(Add(X("off"), Subtract(X("m"), D(1))), X("i"))), EmptyList()));
        Formula body = Let("off", Naturals(), Subtract(X("n"), X("m")),
            Let("x", Arrow(State(X("n")), State(X("n"))),
                LocalCall("controlledX", Add(X("off"), X("l")), Singleton(Pair(X("off"), X("j"))), X("i"), X("j")),
                Let("cs", Controls(), cs, At(X("x"), LocalCall("controlledR", X("off"), X("cs"), X("i"), X("j"),
                    Root(ratio), Negative(Root(Subtract(Typed(D(1), Reals()), ratio))), At(X("x"), X("f")))))));
        return BlockIndexBinders(All("i", FinOf(D(3)), All("j", FinOf(D(3)), All("f", State(X("n")),
            Equal(Typed(LocalCall("V", X("n"), X("m"), X("l"), X("i"), X("j"), X("f")), State(X("n"))), body)))));
    }

    private static Formula IFormula() => BlockIndexBinders(All("f", State(X("n")), Equal(
        Typed(LocalCall("I", X("n"), X("m"), X("l"), X("f")), State(X("n"))),
        LocalCall("V", X("n"), X("m"), X("l"), Typed(D(1), FinOf(D(3))), Typed(D(2), FinOf(D(3))),
            LocalCall("V", X("n"), X("m"), X("l"), Typed(D(0), FinOf(D(3))), Typed(D(2), FinOf(D(3))),
                LocalCall("V", X("n"), X("m"), X("l"), Typed(D(0), FinOf(D(3))), Typed(D(1), FinOf(D(3))), X("f")))))));

    private static Formula IIFormula()
    {
        Formula off = X("off"), l1 = X("l₁"), l2 = X("l₂");
        Formula cs = Append(Append(Singleton(Pair(Add(off, l2), Typed(D(2), FinOf(D(3))))),
            If(LE(D(2), l2), Singleton(Pair(Add(off, Subtract(l2, D(1))), Typed(D(2), FinOf(D(3))))), EmptyList())),
            If(Less(l2, Subtract(l1, D(1))), Singleton(Pair(Add(off, Subtract(l1, D(1))), Typed(D(1), FinOf(D(3))))), EmptyList()));
        Formula ratio1 = Divide(CastReal(l2), CastReal(X("m")));
        Formula ratio2 = Divide(CastReal(Typed(Subtract(l1, l2), Naturals())), CastReal(Typed(Subtract(X("m"), l2), Naturals())));
        Formula body = Let("off", Naturals(), Subtract(X("n"), X("m")),
            Let("x", Arrow(State(X("n")), State(X("n"))),
                LocalCall("controlledX", Add(off, l2), Singleton(Pair(off, Typed(D(2), FinOf(D(3))))), Typed(D(1), FinOf(D(3))), Typed(D(2), FinOf(D(3)))),
                Let("y", Arrow(State(X("n")), State(X("n"))),
                    LocalCall("controlledX", Add(off, l1), Singleton(Pair(off, Typed(D(1), FinOf(D(3))))), Typed(D(0), FinOf(D(3))), Typed(D(1), FinOf(D(3)))),
                    Let("cs", Controls(), cs,
                        Let("r₁", Arrow(State(X("n")), State(X("n"))),
                            LocalCall("controlledR", off, Cons(Pair(Add(off, l1), Typed(D(0), FinOf(D(3)))), X("cs")),
                                Typed(D(1), FinOf(D(3))), Typed(D(2), FinOf(D(3))), Root(ratio1), Negative(Root(Subtract(Typed(D(1), Reals()), ratio1)))),
                            Let("r₂", Arrow(State(X("n")), State(X("n"))),
                                LocalCall("controlledR", off, Cons(Pair(Add(off, l1), Typed(D(1), FinOf(D(3)))), X("cs")),
                                    Typed(D(0), FinOf(D(3))), Typed(D(1), FinOf(D(3))), Root(ratio2), Negative(Root(Subtract(Typed(D(1), Reals()), ratio2)))),
                                At(X("y"), At(X("r₂"), At(X("y"), At(X("x"), At(X("r₁"), At(X("x"), X("f")))))))))))));
        return All("n", Naturals(), All("m", Naturals(), All("l₁", Naturals(), All("l₂", Naturals(), All("f", State(X("n")),
            Equal(Typed(LocalCall("II", X("n"), X("m"), l1, l2, X("f")), State(X("n"))), body))))));
    }

    private static Formula PrunedTildeFormula()
    {
        Formula kt = If(Equal(At(X("k"), Typed(D(0), FinOf(D(3)))), D(0)), At(X("k"), Typed(D(2), FinOf(D(3)))),
            At(Qualified("Max", "max"), At(X("k"), Typed(D(1), FinOf(D(3)))), At(X("k"), Typed(D(2), FinOf(D(3))))));
        Formula range = Range(At(Qualified("Max", "max"), Subtract(Add(X("kt"), X("m")), X("n")), D(1)),
            Add(At(Qualified("Min", "min"), X("kt"), Subtract(X("m"), D(1))), D(1)));
        Formula step = LambdaOf("g", State(X("n")), LambdaOf("l", Naturals(), LocalCall("I", X("n"), X("m"), X("l"), X("g"))));
        return OccupationBlockBinders(Equal(Typed(LocalCall("prunedTilde", X("n"), X("m"), X("k"), X("f")), State(X("n"))),
            Let("kt", Naturals(), kt, Fold(step, X("f"), range))));
    }

    private static Formula PrunedTildeTildeFormula()
    {
        Formula innerRange = Range(At(Qualified("Max", "max"), Subtract(Add(X("l₁"), X("m")), X("n")), Add(X("b"), D(1))),
            Add(At(Qualified("Min", "min"), X("l₁"), Subtract(X("m"), D(1))), D(1)));
        Formula outerRange = Range(At(Qualified("Max", "max"), Subtract(Add(X("l₂"), X("m")), X("n")), D(1)),
            Add(At(Qualified("Min", "min"), X("l₂"), Subtract(X("m"), D(2))), D(1)));
        Formula innerStep = LambdaOf("h", State(X("n")), LambdaOf("a", Naturals(), LocalCall("II", X("n"), X("m"), X("a"), X("b"), X("h"))));
        Formula outerStep = LambdaOf("g", State(X("n")), LambdaOf("b", Naturals(), Fold(innerStep, X("g"), innerRange)));
        return OccupationBlockBinders(Equal(Typed(LocalCall("prunedTildeTilde", X("n"), X("m"), X("k"), X("f")), State(X("n"))),
            Let("l₁", Naturals(), Add(At(X("k"), Typed(D(1), FinOf(D(3)))), At(X("k"), Typed(D(2), FinOf(D(3))))),
                Let("l₂", Naturals(), At(X("k"), Typed(D(2), FinOf(D(3)))), Fold(outerStep, X("f"), outerRange)))));
    }

    private static Formula PrunedWFormula() => OccupationBlockBinders(Equal(
        Typed(LocalCall("prunedW", X("n"), X("m"), X("k"), X("f")), State(X("n"))),
        LocalCall("prunedTildeTilde", X("n"), X("m"), X("k"), LocalCall("prunedTilde", X("n"), X("m"), X("k"), X("f")))));

    private static Formula PrunedUFormula() => OccupationBinders(All("f", State(X("n")), Equal(
        Typed(LocalCall("prunedU", X("n"), X("k"), X("f")), State(X("n"))),
        Fold(LambdaOf("g", State(X("n")), LambdaOf("m", Naturals(), LocalCall("prunedW", X("n"), X("m"), X("k"), X("g")))),
            X("f"), At(Qualified("List", "reverse"), Range(D(2), Add(X("n"), D(1))))))));

    private static Formula InitialWordFormula() => OccupationBinders(Equal(
        Typed(LocalCall("initialWord", X("n"), X("k")), Word(X("n"))),
        LambdaOf("w", FinOf(X("n")), If(Less(At(Qualified("Fin", "val"), X("w")), At(X("k"), Typed(D(2), FinOf(D(3))))),
            Typed(D(2), FinOf(D(3))), If(Less(At(Qualified("Fin", "val"), X("w")),
                Add(At(X("k"), Typed(D(1), FinOf(D(3)))), At(X("k"), Typed(D(2), FinOf(D(3)))))),
                Typed(D(1), FinOf(D(3))), Typed(D(0), FinOf(D(3))))))));

    private static Formula DickeFormula()
    {
        Formula occupation = At(Qualified("D5", "S3", "Quantum", "Entanglement", "OccupancyWordSectors", "occupation"), X("t"));
        Formula counts = All("s", FinOf(D(3)), Equal(At(Qualified("Multiset", "count"), X("s"), occupation), At(X("k"), X("s"))));
        Formula denominator = Multiply(Multiply(Factorial(At(X("k"), Typed(D(0), FinOf(D(3))))),
            Factorial(At(X("k"), Typed(D(1), FinOf(D(3)))))), Factorial(At(X("k"), Typed(D(2), FinOf(D(3))))));
        Formula count = Typed(At(Qualified("Nat", "div"), Factorial(X("n")), denominator), Naturals());
        return OccupationBinders(Equal(Typed(LocalCall("dicke", X("n"), X("k")), State(X("n"))),
            LambdaOf("t", Word(X("n")), If(counts, Divide(Typed(D(1), Reals()), Root(CastReal(count))), Typed(D(0), Reals())))));
    }

    private static Formula ClaimFormula()
    {
        Formula k = Typed(Seq(Bang, Parenthesized(Seq(X("k₀"), Comma, X("k₁"), Comma, X("k₂")), squareBrackets: true)), Local("Occupation"));
        Formula input = At(Qualified("D5", "S3", "Combinatorics", "Graph", "LegalWords", "SignedBoundary", "vertexDelta"),
            LocalCall("initialWord", X("n"), k));
        return Equivalence(Local("claim"), All("n", Naturals(), Arrow(LE(D(2), X("n")),
            All("k₀", Naturals(), All("k₁", Naturals(), All("k₂", Naturals(),
                Arrow(Equal(Add(Add(X("k₀"), X("k₁")), X("k₂")), X("n")),
                    Equal(LocalCall("prunedU", X("n"), k, input), LocalCall("dicke", X("n"), k)))))))));
    }

    private static Formula WordBinders(Formula body) => All("n", Naturals(), All("t", Word(X("n")), body));
    private static Formula OccupationBinders(Formula body) => All("n", Naturals(), All("k", Local("Occupation"), body));
    private static Formula BlockIndexBinders(Formula body) => All("n", Naturals(), All("m", Naturals(), All("l", Naturals(), body)));
    private static Formula OccupationBlockBinders(Formula body) => All("n", Naturals(), All("m", Naturals(),
        All("k", Local("Occupation"), All("f", State(X("n")), body))));
    private static Formula GateBinders(bool rotation, Formula body) => All("n", Naturals(), All("target", Naturals(),
        All("controls", Controls(), All("i", FinOf(D(3)), All("j", FinOf(D(3)),
            rotation ? All("c", Reals(), All("s", Reals(), body)) : body)))));
    private static Formula ControlsTrue() => Equal(LocalCall("controlsHold", X("controls"), X("t")), Qualified("Bool", "true"));
    private static Formula Control() => Seq(Naturals(), Sp, Times, Sp, FinOf(D(3)));
    private static Formula Controls() => At(Qualified("List"), Parenthesized(Control()));
    private static Formula State(Formula n) => LocalCall("State", n);
    private static Formula Word(Formula n) => At(Qualified("D5", "S3", "Quantum", "Entanglement", "OccupancyWordSectors", "Word"), FinOf(D(3)), n);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "PureState", "QutritDickePruningRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => name switch
    {
        "l₁" => new Formula.Subscript(F.Id("l"), D(1)),
        "l₂" => new Formula.Subscript(F.Id("l"), D(2)),
        "r₁" => new Formula.Subscript(F.Id("r"), D(1)),
        "r₂" => new Formula.Subscript(F.Id("r"), D(2)),
        "k₀" => new Formula.Subscript(F.Id("k"), D(0)),
        "k₁" => new Formula.Subscript(F.Id("k"), D(1)),
        "k₂" => new Formula.Subscript(F.Id("k"), D(2)),
        _ => F.Id(name),
    };
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
    private static Formula Parenthesized(Formula value, bool squareBrackets = false) =>
        squareBrackets ? Seq(OpenBracket, value, CloseBracket) : Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula CastReal(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals());
    private static Formula Factorial(Formula value) => At(Qualified("Nat", "factorial"), value);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        Seq(Qualified("let"), Sp, Typed(X(name), type), Sp, Eq, Sp, Parenthesized(value), Semi, Sp, Parenthesized(body));
    private static Formula Constant(Formula domain, Formula value) => At(Qualified("Function", "const"), Parenthesized(domain), value);
    private static Formula If(Formula condition, Formula yes, Formula no) => At(Qualified("ite"), Parenthesized(condition), yes, no);
    private static Formula Pair(Formula first, Formula second) => Parenthesized(Seq(first, Comma, Sp, second));
    private static Formula Singleton(Formula value) => Parenthesized(value, squareBrackets: true);
    private static Formula EmptyList() => Typed(Parenthesized(Seq(), squareBrackets: true), Controls());
    private static Formula Append(Formula left, Formula right) => At(Qualified("List", "append"), left, right);
    private static Formula Cons(Formula head, Formula tail) => At(Qualified("List", "cons"), head, tail);
    private static Formula Range(Formula lower, Formula upper) => At(Qualified("List", "Ico"), lower, upper);
    private static Formula Fold(Formula step, Formula initial, Formula list) => At(Qualified("List", "foldl"), step, initial, list);
    private static Formula Root(Formula value) => At(Qualified("Real", "sqrt"), value);
    private static Formula Negative(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
