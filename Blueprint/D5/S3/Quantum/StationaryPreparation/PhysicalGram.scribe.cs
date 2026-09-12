using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PhysicalGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula a = Id("a"), blank = Id("blank"), U = Id("U"), x = Id("x"), f = Id("f");
        Formula r = Id("r"), s = Id("s"), i = Id("i"), u = Id("u"), w = Id("w"), k = Id("k");
        Formula n = Id("n"), t = Id("t");
        Formula box = Call("TailBox", Counts(a));
        Formula B = Call("occupationGram", a, blank, U, x);
        Formula coefficients = FiniteTypes(
            All("blank", Id("A"), All("U", Unitary,
                All("n", N, All("t", N, All("x", Space,
                    All("w", Arrow(Call("Fin", n), Id("A")), All("k", Id("K"),
                        Eq(Circuit(n, t, x, w, k),
                            At(Call("prefixMemory", blank, U, Call("ListOfFn", w), x), k))))))))), false);
        Formula independent = Setup(All("r", Call("Multiset", Id("A")),
            Imp(Le(r, a), All("u", Call("List", Id("A")),
                Imp(Eq(Call("toMultiset", u), Sub(a, r)),
                    Eq(Call("prefixMemory", blank, U, u, Call("scaledInitial", a, x)), Residual(r)))))));
        Formula zero = Setup(Eq(Residual(D(0)), f));
        Formula legalStep = Setup(All("r", Call("Multiset", Id("A")),
            Imp(Le(r, a), All("i", Id("A"), Imp(Mem(i, r),
                Eq(Call("letter", blank, U, i, Residual(r)), Residual(Call("erase", r, i))))))));
        Formula absentStep = Setup(All("r", Call("Multiset", Id("A")),
            Imp(And(Le(r, a), Ne(r, D(0))), All("i", Id("A"), Imp(Not(Mem(i, r)),
                Eq(Call("letter", blank, U, i, Residual(r)), D(0)))))));
        Formula psd = GramContext(Call("PosSemidef", B));
        Formula rankUpper = GramContext(Le(Call("rank", B), Call("FintypeCard", Id("K"))));
        Formula gramZero = Setup(Imp(Unit(f), Eq(At(B, D(0), D(0)), D(1))));
        Formula recurrence = Setup(All("r", box, All("s", box,
            Imp(And(Ne(r, D(0)), Ne(s, D(0))), Eq(At(B, r, s),
                SumAt("i", Id("A"), Call("ite",
                    And(Lt(D(0), Call("val", At(r, i))), Lt(D(0), Call("val", At(s, i)))),
                    At(B, Call("lower", Counts(a), i, r), Call("lower", Counts(a), i, s)), D(0))))))));
        Formula lower = Setup(Le(Sub(ProdAt("i", Id("A"), Add(Call("count", a, i), D(1))),
            Call("FinsetSup", Call("univ", Id("A")), Counts(a))), Call("FintypeCard", Id("K"))), true);
        Formula dimension = Sub(ProdAt("i", Id("A"), Add(Call("count", a, i), D(1))),
            Call("FinsetSup", Call("univ", Id("A")), Counts(a)));
        Formula feasible = AlphabetContext(All("a", Call("Multiset", Id("A")),
            Eq(Call("stationaryMemoryDimensions", a), Call("setOf", LambdaAt("d", N,
                FixedWitness(Id("A"), Id("d"), Call("card", a),
                    Mul(Call("sectorVector", Call("card", a), a, w), At(f, k))))))), false);
        Formula minimum = AlphabetContext(All("a", Call("Multiset", Id("A")),
            Call("IsLeast", Call("stationaryMemoryDimensions", a), dimension)), true);
        Formula zeroMinimum = AlphabetContext(
            Call("IsLeast", Call("stationaryMemoryDimensions", D(0)), D(1)), true);
        Formula canonical = new Formula.Subscript(a, D(5, 0, 4, 0));
        Formula canonicalAlphabet = Call("Option", Call("Fin", D(3)));
        Formula canonicalAmplitude = Call("ite", Eq(Call("occupation", w), canonical),
            Seq(Frac, Grp(D(1)), Grp(Seq(Sqrt, Grp(D(8, 4, 0))))), D(0));
        Formula canonicalMinimum = And(Eq(Call("card", canonical), D(8)),
            And(Eq(Call("card", Call("sectorWords", D(8), canonical)), D(8, 4, 0)),
                And(Call("IsLeast", Call("stationaryMemoryDimensions", canonical), D(5, 6)),
                    FixedWitness(canonicalAlphabet, D(5, 6), D(8), Mul(canonicalAmplitude, At(f, k))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual fixed-unitary residual memories give the stationary memory dimension lower bound.",
            H("Physical Stationary Gram"), Blocks(
                Paragraph(Text(
                    "A and K are finite types. Space(K) is the complex Euclidean space with " +
                    "coordinate set K, and Unitary(A times K) consists of its linear isometric " +
                    "automorphisms on the joint alphabet and memory space. A fixed blank symbol " +
                    "embeds each memory into that joint space. Applying the same U after each " +
                    "embedding defines emission, a linear isometry. The coordinate slice at symbol " +
                    "i is the linear map letter(blank,U,i).")),
                Theorem("circuit-fixed-coefficients", "circuit_fixed_coefficients", coefficients,
                    "The schedule is the constant function t mapped to U. For every length and " +
                    "starting time, the circuit coefficient is obtained by applying the letter " +
                    "maps in the order of the word. This follows by induction on the word length " +
                    "and expansion in the memory coordinate basis."),
                Paragraph(Text(
                    "An occupation is a multiset a on A. Its multiplicity is the number of words " +
                    "with that occupation. sectorVector(a.card,a) has coefficient the reciprocal " +
                    "square root of this multiplicity on those words and zero elsewhere. " +
                    "The output equation below requires that every word coefficient factor through " +
                    "one common final memory f. Its schedule is explicitly constant.")),
                Paragraph(Text(
                    "scaledInitial multiplies x by the square root of the multiplicity of a. " +
                    "residualMemory(a,blank,U,x,r) applies a representative prefix of occupation " +
                    "a minus r to this scaled vector. These residuals are unnormalized. " +
                    "For legal r, every suffix of occupation r produces f and every other suffix " +
                    "of the same length produces zero. The remaining circuit is isometric and " +
                    "therefore injective.")),
                Theorem("residual-representative-independent", "residual_representative_independent", independent,
                    "Every legal prefix with the same remaining occupation gives exactly the same " +
                    "scaled residual vector. Equality is vector equality and includes its phase."),
                Theorem("residual-zero", "residual_zero", zero,
                    "With no remaining symbols, the scaled residual is precisely the common final memory."),
                Theorem("residual-letter-of-mem", "residual_letter_of_mem", legalStep,
                    "A symbol present in the remaining occupation sends its residual to the residual " +
                    "with one copy of that symbol erased."),
                Theorem("residual-letter-of-not-mem", "residual_letter_of_not_mem", absentStep,
                    "For a nonzero remaining occupation, a symbol absent from it has zero letter image."),
                Paragraph(Text(
                    "For r in TailBox(a.count), boxOccupation(a,r) is the multiset whose counts " +
                    "are the coordinate values of r. occupationGram is the Gram matrix of the " +
                    "corresponding scaled residualMemory vectors, using the complex inner product " +
                    "conjugate-linear in its first argument. Thus it is the scaled matrix B.")),
                Theorem("occupation-gram-psd", "occupation_gram_psd", psd,
                    "A Gram matrix of complex vectors is positive semidefinite, independently of " +
                    "the output equation."),
                Theorem("occupation-gram-rank-le", "occupation_gram_rank_le", rankUpper,
                    "Factoring through the memory coordinates bounds the Gram rank by the cardinality of K."),
                Theorem("occupation-gram-zero", "occupation_gram_zero", gramZero,
                    "The output equation and unit norm of f make the zero entry equal to one."),
                Theorem("occupation-gram-recurrence", "occupation_gram_recurrence", recurrence,
                    "The emission isometry preserves inner products. Summing over its letter " +
                    "coordinates and using the present and absent symbol identities gives the " +
                    "displayed recurrence on nonzero indices. The function ite chooses its " +
                    "second argument when its condition holds and its third argument otherwise."),
                Theorem("stationary-memory-dimension-lower-bound", "stationary_memory_dimension_lower_bound", lower,
                    "The PSD recurrence and unit zero entry give the product-minus-supremum rank " +
                    "bound. The Gram rank is at most the memory dimension. For zero occupation, " +
                    "the unit initial vector ensures a nonempty memory coordinate set, giving " +
                    "the same bound. Neither the common final vector nor the blank symbol is " +
                    "prescribed beyond the displayed hypotheses."),
                Theorem("stationary-memory-dimensions", "stationaryMemoryDimensions", feasible,
                    "The set consists of natural memory dimensions d for which the displayed " +
                    "physical preparation exists. setOf takes the set of arguments satisfying its " +
                    "predicate. Fin(d) supplies exactly d complex memory coordinates. One blank, " +
                    "one fixed U, and the unit memories x and f are chosen before every word and " +
                    "coordinate is quantified. No inequality or minimality condition is part of " +
                    "this definition."),
                Theorem("stationary-memory-dimension-is-least", "stationary_memory_dimension_isLeast", minimum,
                    "For every finite nonempty alphabet and every multiset a, the displayed " +
                    "dimension belongs to stationaryMemoryDimensions(a) and is no greater than " +
                    "any other member; this is the meaning of IsLeast. Counts are natural numbers, " +
                    "so zero capacities are included. The supremum over the finite alphabet is " +
                    "the maximum count. The lower bound applies to every member, and the fixed " +
                    "unitary attainment supplies a member of exactly this dimension."),
                Theorem("zero-occupation-memory-is-least", "zero_occupation_memory_isLeast", zeroMinimum,
                    "For zero occupation the minimum is one. Choose any blank, the identity " +
                    "unitary on A times Fin(1), and x and f both equal to the sole coordinate basis " +
                    "vector. The empty circuit preserves this unit vector, and the unique empty " +
                    "word has sector coefficient one. A unit vector excludes zero-dimensional " +
                    "memory. This construction has no positive-occupation hypothesis."),
                Paragraph(Text(
                    "Here a with subscript 5040 denotes CoherentHistorySchmidt.occupation5040 " +
                    "on Option(Fin(3)): its count at none is four, and its counts at some(0), " +
                    "some(1), and some(2) are two, one, and one. The count of actual occupation " +
                    "words follows from the multinomial formula: 8! divided by 4! 2! 1! 1! " +
                    "is 840. The product of count plus one is 60 and the maximum count is four. " +
                    "The square root below is the nonnegative real square root, embedded in " +
                    "the complex scalars.")),
                Theorem("occupation-stationary-minimum", "occupation_5040_stationary_minimum", canonicalMinimum,
                    "The same statement gives length eight, 840 actual legal words, least " +
                    "stationary memory dimension 56, and a physical preparation in that dimension. " +
                    "Every length-eight word and every memory coordinate satisfies the displayed " +
                    "equation. Legal words have the same positive coefficient 1/sqrt(840), " +
                    "and all other words have coefficient zero, with one common unit final memory. " +
                    "The circuit uses the same U at each emission. Its length-eight domain is " +
                    "obtained from the occupation cardinality equality."))));
    }

    private static Formula AlphabetContext(Formula body, bool nonempty)
    {
        Formula facts = And(Call("Fintype", Id("A")), Call("DecidableEq", Id("A")));
        if (nonempty) facts = And(facts, Call("Nonempty", Id("A")));
        return All("A", Id("Type"), Imp(facts, body));
    }
    private static Formula FixedWitness(Formula alphabet, Formula dimension, Formula length, Formula output)
    {
        Formula memory = Call("Fin", dimension), space = Call("Space", memory);
        Formula coefficients = All("w", Arrow(Call("Fin", length), alphabet), All("k", memory,
            Eq(Circuit(length, D(0), Id("x"), Id("w"), Id("k")), output)));
        return Some("blank", alphabet,
            Some("U", Call("Unitary", Call("Product", alphabet, memory)),
                Some("x", space, Some("f", space,
                    And(Unit(Id("x")), And(Unit(Id("f")), coefficients))))));
    }
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Setup(Formula body, bool unitEndpoints = false)
    {
        Formula hypotheses = unitEndpoints ? And(Unit(Id("x")), And(Unit(Id("f")), Output())) : Output();
        return GramContext(All("f", Space, Imp(hypotheses, body)));
    }
    private static Formula GramContext(Formula body) => FiniteTypes(
        All("a", Call("Multiset", Id("A")), All("blank", Id("A"),
            All("U", Unitary, All("x", Space, body)))), true);
    private static Formula FiniteTypes(Formula body, bool decidable)
    {
        Formula facts = And(Call("Fintype", Id("A")), Call("Fintype", Id("K")));
        if (decidable) facts = And(facts, Call("DecidableEq", Id("A")));
        return All("A", Id("Type"), All("K", Id("Type"), Imp(facts, body)));
    }
    private static Formula Output() => All("w", Arrow(Call("Fin", Call("card", Id("a"))), Id("A")),
        All("k", Id("K"), Eq(Circuit(Call("card", Id("a")), D(0), Id("x"), Id("w"), Id("k")),
            Mul(Call("sectorVector", Call("card", Id("a")), Id("a"), Id("w")), At(Id("f"), Id("k"))))));
    private static Formula Circuit(Formula n, Formula t, Formula x, Formula w, Formula k) =>
        Call("circuit", LambdaAt("t", N, Id("U")), n, t,
            Call("initialized", Id("blank"), n, x), Call("pair", w, k));
    private static Formula Residual(Formula r) => Call("residualMemory", Id("a"), Id("blank"), Id("U"), Id("x"), r);
    private static Formula Counts(Formula a) => LambdaAt("i", Id("A"), Call("count", a, Id("i")));
    private static Formula Space => Call("Space", Id("K"));
    private static Formula Unitary => Call("Unitary", Call("Product", Id("A"), Id("K")));
    private static Formula Unit(Formula x) => Eq(Call("norm", x), D(1));
    private static DocumentBlock Theorem(string id, string name, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(
            "D5/S3/Quantum/StationaryPreparation/PhysicalGram." + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))));
    private static Formula Id(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula Call(string name, params Formula[] args) => At(Id(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Arrow(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula LambdaAt(string name, Formula domain, Formula body) =>
        Seq(Id(name), Colon, domain, Sp, Mapsto, Sp, body);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Not(Formula x) => Seq(Neg, Sp, Grp(x));
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Mem(Formula x, Formula y) => Seq(x, Sp, InMacro, Sp, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula SumAt(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, domain)), Grp(body));
    private static Formula ProdAt(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(Id(name), Colon, domain)), Grp(body));
}
