using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class FiniteMemoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula A = Id("A"), Hm = Id("H"), I = Id("I"), V = Id("V"), U = Id("U");
        Formula x = Id("x"), f = Id("f"), z = Id("z"), i = Id("i"), k = Id("k");
        Formula n = Id("n"), t = Id("t"), w = Id("w"), a = Id("a"), psi = Id("psi");
        Formula blank = Id("blank"), tail = Call("tail", w), list = Call("ofFn", w);
        Formula occupation = Call("capacityOccupation", a), length = Call("card", occupation);
        Formula coeffDef = Memory(All("I", Type, Imp(Call("Fintype", I),
            Eq(Call("coefficients", I), Call("composeEquivalences",
                Call("equivFinsuppOfBasisLeft", Call("toBasis", Call("alphabetBasis", I))),
                Call("linearEquivFunOnFinite", C, Hm, I))))));
        Formula coeffPure = Memory(All("I", Type, Imp(Call("Fintype", I),
            All("z", Space(I), All("x", Hm, All("i", I,
                Eq(Coeff(I, Tmul(z, x), i), Smul(At(z, i), x))))))));
        Formula wordDef = Emission(And(
            All("x", Hm, Eq(Word(Call("nil"), x), x)),
            All("i", A, All("w", Call("List", A), All("x", Hm,
                Eq(Word(Call("cons", i, w), x), Word(w, Coeff(A, At(V, x), i))))))));
        Formula outputDef = Emission(All("n", N, All("x", Hm,
            Eq(Out(n, x), Call("inverse", Call("coefficients", Words(n)),
                Lambda("w", Words(n), Word(list, x)))))));
        Formula outputCoeff = Emission(All("n", N, All("x", Hm, All("w", Words(n),
            Eq(Coeff(Words(n), Out(n, x), w), Word(list, x))))));
        Formula zero = Emission(All("x", Hm, All("w", Words(D(0)),
            Eq(Coeff(Words(D(0)), Out(D(0), x), w), x))));
        Formula successor = Emission(All("n", N, All("x", Hm,
            All("w", Words(Add(n, D(1))), Eq(
                Coeff(Words(Add(n, D(1))), Out(Add(n, D(1)), x), w),
                Coeff(Words(n), Out(n, Coeff(A, At(V, x), At(w, D(0)))), tail))))));
        Formula tensorEquality = Emission(All("n", N, All("x", Hm, All("f", Hm,
            All("psi", Space(Words(n)), Iff(Eq(Out(n, x), Tmul(psi, f)),
                All("w", Words(n), Eq(Word(list, x), Smul(At(psi, w), f)))))))));
        Formula tensorStep = Emission(All("n", N, All("x", Hm, Eq(
            Call("tensorMap", Call("linearIdentity", Space(Words(n))), V, Out(n, x)),
            Call("inverse", Call("coefficients", Words(n)), Lambda("w", Words(n),
                Call("inverse", Call("coefficients", A), Lambda("i", A,
                    Coeff(Words(Add(n, D(1))), Out(Add(n, D(1)), x), Call("snoc", w, i))))))))));
        Formula coordinateDef = Memory(Eq(Call("coordinates", Hm),
            Call("repr", Call("stdOrthonormalBasis", C, Hm))), true);
        Formula tensorCoordinateDef = Memory(All("I", Type, Imp(Call("Fintype", I),
            Eq(Call("tensorCoordinates", Hm, I), Call("repr", Call("tensorProductBasis",
                Call("alphabetBasis", I), Call("stdOrthonormalBasis", C, Hm)))))), true);
        Formula compatibility = Memory(All("I", Type, Imp(Call("Fintype", I),
            All("z", Tensor(Space(I), Hm), All("i", I, All("k", K,
                Eq(At(Tcoord(I, z), Call("pair", i, k)),
                    At(Coord(Coeff(I, z, i)), k))))))), true);
        Formula oneStep = All("x", Hm, Eq(Call("emission", blank, U, Coord(x)),
            Tcoord(A, At(V, x))));
        Formula allWords = All("w", Call("List", A), All("x", Hm,
            Eq(Call("prefixMemory", blank, U, w, Coord(x)), Coord(Word(w, x)))));
        Formula allCircuits = All("n", N, All("t", N, All("x", Hm,
            Eq(Circuit(n, t, x), Tcoord(Words(n), Out(n, x))))));
        Formula fixedUnitary = Alphabet(Memory(All("blank", A, All("V", EmissionType,
            Exists("U", Call("Unitary", Call("Product", A, K)),
                And(oneStep, And(allWords, allCircuits))))), true));
        Formula outputNorm = Alphabet(Memory(All("blank", A, All("V", EmissionType,
            All("n", N, All("x", Hm, Eq(Call("norm", Out(n, x)), Call("norm", x)))))), true));
        Formula lower = LowerBound(Call("Multiset", A), a, Call("card", a),
            Lambda("i", A, Call("count", a, i)), Call("count", a, i));
        Formula capacityDef = Alphabet(All("a", Arrow(A, N),
            Eq(occupation, Call("toMultiset", Call("inverse", Call("equivFunOnFinite"), a)))));
        Formula counts = Alphabet(Imp(Call("DecidableEq", A), All("a", Arrow(A, N),
            All("i", A, Eq(Call("count", occupation, i), At(a, i))))));
        Formula card = Alphabet(All("a", Arrow(A, N),
            Eq(length, SumAt("i", A, At(a, i)))));
        Formula capacityLower = LowerBound(Arrow(A, N), occupation, length, a, At(a, i));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A fixed emission isometry on any finite complex memory has one fixed unitary circuit realization for every word.",
            H("Finite Hilbert Memory"), Blocks(
                Paragraph(Text(
                    "H is a complex inner product space. Space(I) is the complex Euclidean space " +
                    "on a finite type I, with its standard orthonormal alphabet basis. Tensor denotes " +
                    "the complex Hilbert tensor product; tmul is a pure tensor and smul is complex " +
                    "scalar multiplication. coefficients(I) is a linear equivalence from " +
                    "Space(I) tensor H to I-indexed H-valued coefficients. It uses no basis of H. " +
                    "Its inverse reconstructs the tensor exactly, including every complex phase.")),
                Entry("coefficients", coeffDef,
                    "Compose the tensor coefficient equivalence for the alphabet basis with the " +
                    "equivalence between finite-support functions and functions on a finite type."),
                Entry("coefficients_tmul", coeffPure,
                    "The memory coefficient of a pure tensor z tensor x at i is z(i) times x."),
                Paragraph(Text(
                    "A is a finite alphabet and V is one fixed linear isometry from H to " +
                    "Space(A) tensor H. wordMemory(V,w) is a linear map on H: the empty word " +
                    "acts as the identity, and a first symbol reads that coefficient of V before " +
                    "the rest of the word is processed. Words(n) means functions from Fin(n) to A; " +
                    "ofFn lists their symbols in order. output(V,n,x) belongs to Space(Words(n)) " +
                    "tensor H. The zero and successor identities specify repeated emission in " +
                    "this word-indexed presentation, using the same V at every step.")),
                Entry("wordMemory", wordDef,
                    "The displayed equations define the ordered iteration as a linear map."),
                Entry("output", outputDef,
                    "Reconstruct the full tensor from the memory reached at every word."),
                Entry("output_coefficients", outputCoeff,
                    "Extraction is inverse to reconstruction, so each output coefficient is its word memory."),
                Entry("output_zero", zero,
                    "Before any emission, the sole empty-word coefficient is the initial memory."),
                Entry("output_succ", successor,
                    "For a word of length n plus one, first apply V and read its first symbol, " +
                    "then emit the tail of length n. tail removes the first coordinate."),
                Entry("output_eq_tmul_iff", tensorEquality,
                    "A tensor output factors through one common f exactly when every word " +
                    "memory equals the corresponding scalar coefficient times that same f. " +
                    "There are no word-dependent phases or choices of final memory."),
                Entry("output_tensor_step", tensorStep,
                    "Applying the identity tensor V to the n-symbol output gives the next " +
                    "output, regrouped as an n-symbol word followed by one symbol. snoc(w,i) " +
                    "appends i to w. The outer coefficient inverse has values in Space(A) tensor H; " +
                    "the inner inverse has values in H. Both are exact equivalences, and every " +
                    "word has the unique split into its initial segment and last symbol. " +
                    "This identifies the word presentation with the tensor operation at every stage."),
                Paragraph(Text(
                    "Now H is finite-dimensional over the complex numbers, and K is " +
                    "Fin(finrank(C,H)). coordinates(H) is an isometric linear equivalence from H " +
                    "to Space(K). tensorCoordinates(H,I) is an isometric linear equivalence from " +
                    "Space(I) tensor H to Space(I times K), formed from the tensor product " +
                    "orthonormal basis. Thus K has exactly the dimension of H, including zero.")),
                Entry("coordinates", coordinateDef,
                    "Use the representation of the finite-dimensional orthonormal basis."),
                Entry("tensorCoordinates", tensorCoordinateDef,
                    "Use the representation of the alphabet basis tensor the memory basis."),
                Entry("tensorCoordinates_apply", compatibility,
                    "Taking a joint coordinate is the same as extracting the original H-valued " +
                    "coefficient and then taking its memory coordinate. Pure tensors give the " +
                    "identity, and linearity extends it to every tensor."),
                Entry("exists_fixed_unitary", fixedUnitary,
                    "Fix any blank symbol. The blank embedding and the coordinate form of V " +
                    "are two isometric embeddings into the same finite-dimensional joint space. " +
                    "A unitary agrees with them. Their letter maps intertwine, so induction on " +
                    "the word gives the middle equality. The actual circuit coefficient theorem " +
                    "then gives the last vector equality for every length, starting time and x. " +
                    "The schedule in circuit is the constant function with value U."),
                Entry("output_norm", outputNorm,
                    "The full circuit, initialization and coordinate equivalences preserve norms. " +
                    "Their output equality proves that the repeated emission preserves the norm of x."),
                Paragraph(Text(
                    "For the lower bound A is finite, nonempty and has decidable equality. " +
                    "sector(n,a) is the Euclidean vector with coefficients sectorVector(n,a): " +
                    "the reciprocal square root of the occupation multiplicity on words with " +
                    "occupation a, and zero elsewhere. Both initial x and final f have norm one. " +
                    "The final f is common to every word and need not be a prescribed reset. " +
                    "The subtraction in the dimension bound is natural-number subtraction; " +
                    "sup is the maximum over the finite nonempty alphabet.")),
                Entry("stationary_memory_dimension_lower_bound", lower,
                    "Transport the exact tensor output to the fixed-blank, constant-unitary " +
                    "circuit. coordinates preserves both endpoint norms and the common f. " +
                    "Applying the physical stationary bound gives the displayed dimension bound. " +
                    "Zero occupation is included; a unit initial vector excludes zero-dimensional H."),
                Entry("capacityOccupation", capacityDef,
                    "A natural-valued capacity function gives a finite-support function and hence " +
                    "a multiset. Zero capacities are retained without any positivity assumption."),
                Entry("count_capacityOccupation", counts,
                    "The multiset count at each alphabet symbol is exactly the supplied capacity."),
                Entry("card_capacityOccupation", card,
                    "The number of emissions is exactly the sum of the capacities."),
                Entry("stationary_capacity_dimension_lower_bound", capacityLower,
                    "Apply the multiset theorem to capacityOccupation(a) and substitute its counts. " +
                    "The output still uses the same fixed V, unit endpoints and exact common-memory tensor equation."))));
    }

    private static Formula LowerBound(Formula capacityType, Formula occupation, Formula n,
        Formula counts, Formula countAtIndex)
    {
        Formula a = Id("a"), x = Id("x"), f = Id("f");
        Formula output = Eq(Out(n, x), Tmul(Call("sector", n, occupation), f));
        Formula bound = Le(Sub(ProdAt("i", Id("A"), Add(countAtIndex, D(1))),
            Call("sup", Call("univ", Id("A")), counts)), Call("finrank", C, Id("H")));
        return Alphabet(Memory(Imp(And(Call("DecidableEq", Id("A")), Call("Nonempty", Id("A"))),
            All("a", capacityType, All("V", EmissionType, All("x", Id("H"), All("f", Id("H"),
                Imp(And(Unit(x), And(Unit(f), output)), bound)))))), true));
    }
    private static Formula Memory(Formula body, bool finite = false)
    {
        Formula facts = And(Call("NormedAddCommGroup", Id("H")), Call("InnerProductSpace", C, Id("H")));
        if (finite) facts = And(facts, Call("FiniteDimensional", C, Id("H")));
        return All("H", Type, Imp(facts, body));
    }
    private static Formula Alphabet(Formula body) => All("A", Type, Imp(Call("Fintype", Id("A")), body));
    private static Formula Emission(Formula body) => Alphabet(Memory(All("V", EmissionType, body)));
    private static Formula EmissionType => Call("LinearIsometry", C, Id("H"), Tensor(Space(Id("A")), Id("H")));
    private static Formula K => Call("Fin", Call("finrank", C, Id("H")));
    private static Formula Words(Formula n) => Arrow(Call("Fin", n), Id("A"));
    private static Formula Space(Formula i) => Call("Space", i);
    private static Formula Tensor(Formula x, Formula y) => Call("Tensor", C, x, y);
    private static Formula Tmul(Formula x, Formula y) => Call("tmul", x, y);
    private static Formula Smul(Formula x, Formula y) => Call("smul", x, y);
    private static Formula Coeff(Formula i, Formula z, Formula a) => Call("coefficients", i, z, a);
    private static Formula Word(Formula w, Formula x) => Call("wordMemory", Id("V"), w, x);
    private static Formula Out(Formula n, Formula x) => Call("output", Id("V"), n, x);
    private static Formula Coord(Formula x) => Call("coordinates", Id("H"), x);
    private static Formula Tcoord(Formula i, Formula x) => Call("tensorCoordinates", Id("H"), i, x);
    private static Formula Circuit(Formula n, Formula t, Formula x) => Call("circuit",
        Lambda("s", N, Id("U")), n, t, Call("initialized", Id("blank"), n, Coord(x)));
    private static Formula Unit(Formula x) => Eq(Call("norm", x), D(1));
    private static DocumentBlock Entry(string name, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(
            "D5/S3/Quantum/StationaryPreparation/FiniteMemory." + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))));
    private static Formula Id(string name) => F.Id(name);
    private static Formula Type => Id("Type");
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula C => Seq(Mathbb, Grp(Id("C")));
    private static Formula Call(string name, params Formula[] args) => At(Id(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Arrow(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula Lambda(string name, Formula domain, Formula body) => Seq(Id(name), Colon, domain, Sp, Mapsto, Sp, body);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula SumAt(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, domain)), Grp(body));
    private static Formula ProdAt(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Prod, Seq(Id(name), Colon, domain)), Grp(body));
}
