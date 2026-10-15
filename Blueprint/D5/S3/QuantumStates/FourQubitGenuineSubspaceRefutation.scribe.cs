using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class FourQubitGenuineSubspaceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/antipin2021genuinely");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four-qubit subspace obtained from Antipin's vectors (35) and substitutions (39)–(40) contains a nonzero product vector at a parameter tuple in (0,1)⁷.",
        H("Antipin's four-qubit subspace need not be genuinely entangled"), Blocks(
            Paragraph(Text(
                "The four parties, in order, are A₁, A₂, B₁ and B₂. Indices in Fin n start at zero; "
                    + "the seven entries of the real parameter function correspond to λ₁ through λ₇ "
                    + "in the source. A centered dot denotes complex scalar multiplication of a vector. "
                    + "The notation ![a₀, …, aₙ₋₁] denotes the function on Fin n with those entries. "
                    + "All coefficient functions and tensor products are over ℂ.")),
            Node("bit", "The two qubit labels", "Bit", Equal(Local("Bit"), FinOf(2)),
                "Fin 2 consists of the labels zero and one.", AssessedProvenance.FromRepo()),
            Node("party", "The four party labels", "Party", Equal(Local("Party"), FinOf(4)),
                "Labels zero through three denote A₁, A₂, B₁ and B₂, respectively.",
                AssessedProvenance.FromRepo()),
            Node("qubit", "A qubit coefficient space", "Qubit",
                Equal(Local("Qubit"), Arrow(Local("Bit"), Complexes())),
                "A qubit is a complex-valued function on its two basis labels.",
                AssessedProvenance.FromRepo()),
            Node("ququart", "A ququart coefficient space", "Ququart",
                Equal(Local("Ququart"), Arrow(FinOf(4), Complexes())),
                "A ququart is a complex-valued function on four basis labels.",
                AssessedProvenance.FromRepo()),
            Node("two-qubit", "The tensor product of two qubits", "TwoQubit",
                Equal(Local("TwoQubit"), Tensor(Local("Qubit"), Local("Qubit"))),
                "The two-qubit space is TensorProduct ℂ Qubit Qubit.",
                AssessedProvenance.FromRepo()),
            Node("config", "Four-qubit configurations", "Config",
                Equal(Local("Config"), Product(Local("Bit"),
                    Product(Local("Bit"), Product(Local("Bit"), Local("Bit"))))),
                "A configuration is the nested tuple (a,(b,(c,d))) in party order A₁,A₂,B₁,B₂.",
                AssessedProvenance.FromRepo()),
            Node("state", "Four-qubit coefficient functions", "State",
                Equal(Local("State"), Arrow(Local("Config"), Complexes())),
                "A state vector assigns a complex amplitude to each four-qubit configuration; no normalization is imposed.",
                AssessedProvenance.FromRepo()),
            Node("original", "Two-ququart coefficient functions", "Original",
                Equal(Local("Original"), Arrow(Product(FinOf(4), FinOf(4)), Complexes())),
                "The original vectors are coefficient functions on pairs of ququart labels.",
                AssessedProvenance.FromRepo()),
            Node("coordinate", "Reading the qubit of each party", "coordinate", CoordinateFormula(),
                "The four entries of a configuration give the coordinates at A₁,A₂,B₁ and B₂, in that order.",
                AssessedProvenance.FromLiterature(Source)),
            Node("product-across", "Product vectors across a chosen cut", "IsProductAcross", ProductAcrossFormula(),
                "Section II.A, equation (2), defines a product across a bipartition. Here the two factors are arbitrary complex coefficient functions on assignments to the parties in s and outside s. Subtype.val forgets the membership proof. This predicate alone permits empty parts and the zero vector; the GES condition restricts the cut and excludes zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("ges", "Genuinely entangled subspaces", "IsGES", GesFormula(),
                "Section II.A calls a subspace genuinely entangled when every nonzero vector is genuinely multipartite entangled. Every nonempty proper finite set of parties determines a bipartition, and no such cut may admit a product factorization. The seven bipartitions occur twice, once for each choice of side.",
                AssessedProvenance.FromLiterature(Source)),
            Node("ket-four-four", "The two-ququart basis vectors", "ket44", Ket44Formula(),
                "Pi.single (a,b) 1 is the coefficient function equal to one at (a,b) and zero at every other pair. It represents |a⟩ ⊗ |b⟩ in equations (35a)–(35g).",
                AssessedProvenance.FromLiterature(Source)),
            Node("ket-two-two", "The two-qubit basis tensors", "ket22", Ket22Formula(),
                "TensorProduct.tmul forms the pure tensor of the two single-qubit basis vectors. These are the |ab⟩ vectors in substitutions (39) and (40).",
                AssessedProvenance.FromLiterature(Source)),
            Node("vectors-thirty-five", "The seven vectors in equation (35)", "v35", V35Formula(),
                "These are equations (35a)–(35g), in their printed order. Real.sqrt is the real square root, and each real amplitude is cast to ℂ before acting on a vector. The definition accepts every real parameter function; the conjecture below requires every parameter to lie strictly between zero and one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("columns-thirty-nine", "The four images in substitution (39)", "columns39", Columns39Formula(),
                "These four two-qubit tensors are the images of |0⟩, |1⟩, |2⟩ and |3⟩ of the first ququart, exactly as in equation (39).",
                AssessedProvenance.FromLiterature(Source)),
            Node("columns-forty", "The four images in substitution (40)", "columns40", Columns40Formula(),
                "These are the four images of the second ququart's basis vectors, in equation (40).",
                AssessedProvenance.FromLiterature(Source)),
            Node("substitution-thirty-nine", "The linear extension of substitution (39)", "substitution39",
                SubstitutionFormula("substitution39", "columns39"),
                "Module.Basis.constr extends the prescribed columns linearly from Pi.basisFun, the standard basis of complex functions on Fin 4. Its action is the sum of each input coefficient times its column.",
                AssessedProvenance.FromLiterature(Source)),
            Node("substitution-forty", "The linear extension of substitution (40)", "substitution40",
                SubstitutionFormula("substitution40", "columns40"),
                "The second substitution is the linear extension of the four columns in equation (40), using the same standard ququart basis.",
                AssessedProvenance.FromLiterature(Source)),
            Node("two-basis", "The tensor basis of two qubits", "twoBasis", TwoBasisFormula(),
                "Module.Basis.tensorProduct assigns the tensor of the two basis vectors to a pair of labels. Pi.basisFun assigns Pi.single a 1 to label a. Thus the tensor basis has the same order as |00⟩, |01⟩, |10⟩, |11⟩.",
                AssessedProvenance.FromRepo()),
            Node("input-coordinates", "Coordinates of the two-ququart tensor product", "inputCoordinates",
                InputCoordinatesFormula(),
                "Module.Basis.equivFun gives the coefficients in the tensor product of the standard ququart bases. Its value at a label is Module.Basis.repr at that label. In particular, a pure tensor has coefficient u(a)v(b) at (a,b).",
                AssessedProvenance.FromRepo()),
            Node("output-coordinates", "Coordinates in four-qubit party order", "outputCoordinates",
                OutputCoordinatesFormula(),
                "The tensor product of two two-qubit bases first has labels ((a,b),(c,d)). Equiv.prodAssoc changes these to (a,(b,(c,d))). Module.Basis.reindex uses the inverse change on a new label, and Module.Basis.equivFun takes the coefficients in that basis. This gives exactly the configuration order A₁,A₂,B₁,B₂.",
                AssessedProvenance.FromRepo()),
            Node("factorwise", "Applying the two substitutions to their factors", "factorwise", FactorwiseFormula(),
                "Convert the input coefficient function into a two-ququart tensor, apply substitution (39) to its first factor and substitution (40) to its second, then take four-qubit coordinates. TensorProduct.map is the linear map whose value on each pure tensor is the tensor of the two images.",
                AssessedProvenance.FromLiterature(Source)),
            Node("transformed", "The seven transformed four-qubit vectors", "transformed", TransformedFormula(),
                "Each vector in (35) is transformed by the same pair of substitutions (39)–(40).",
                AssessedProvenance.FromLiterature(Source)),
            Node("span", "The parameter-dependent subspace", "S", SpanFormula(),
                "Set.range collects the seven transformed vectors, and Submodule.span takes their complex linear span. The subspace is defined for every real parameter tuple.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The universal four-qubit GES conjecture", "claim", ClaimFormula(),
                "At the end of §III.B.2, page 8, the source conjectures that equations (35), (39) and (40) determine a GES for any set of parameter values. The parameters are restricted by 0 < λᵢ < 1, as stated beside (35). This is the assertion for every such tuple, beyond the separately discussed tuple with all entries one half.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("antipin-four-qubit-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A nonzero product vector in the transformed span"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take λ = (1/2,16/25,1/2,1/2,1/17,1/2,1/2). Every entry is strictly between "
                            + "zero and one. In the source's numbering, form the linear combination "
                            + "3√2(v₁ + v₃ + v₄ + v₆ + v₇) + 5v₂ + 3√17 v₅ of the vectors (35). "
                            + "After substitutions (39)–(40), it is "
                            + "y = (1/3)(25|000⟩ + |001⟩ + |010⟩ + 13|011⟩ + 15|100⟩ "
                            + "+ 6|101⟩ + 7|110⟩ + 10|111⟩) ⊗ (|0⟩ + |1⟩).")),
                    Paragraph(Text(
                        "Thus y belongs to S at this parameter tuple. Its coefficient at |0000⟩ is "
                            + "25/3, so it is nonzero. Its first factor is on A₁,A₂,B₁ and its second "
                            + "factor is on B₂, giving a product across {A₁,A₂,B₁} | {B₂}. "
                            + "This nonzero product vector contradicts the GES condition and refutes "
                            + "the universal conjecture."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("antipin-2021-four-qubit-genuinely-entangled-subspace-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("antipin-four-qubit-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula CoordinateFormula() => All("q", Local("Config"),
        Equal(LocalCall("coordinate", V("q")), Vector(
            Projection(V("q"), 1), Projection(V("q"), 2, 1),
            Projection(V("q"), 2, 2, 1), Projection(V("q"), 2, 2, 2))));

    private static Formula ProductAcrossFormula()
    {
        Formula inside = PartySubtype(true);
        Formula outside = PartySubtype(false);
        Formula leftInput = LambdaOf("p", inside,
            LocalCall("coordinate", V("q"), Call("Subtype.val", V("p"))));
        Formula rightInput = LambdaOf("p", outside,
            LocalCall("coordinate", V("q"), Call("Subtype.val", V("p"))));
        Formula factorization = All("q", Local("Config"), Equal(At(V("z"), V("q")),
            Multiply(At(V("f"), leftInput), At(V("g"), rightInput))));
        Formula factors = Ex("f", Arrow(Arrow(inside, Local("Bit")), Complexes()),
            Ex("g", Arrow(Arrow(outside, Local("Bit")), Complexes()), factorization));
        return All("s", Call("Finset", Local("Party")), All("z", Local("State"),
            Equivalence(LocalCall("IsProductAcross", V("s"), V("z")), factors)));
    }

    private static Formula GesFormula()
    {
        Formula cuts = All("s", Call("Finset", Local("Party")),
            Imp(Call("Finset.Nonempty", V("s")),
                Imp(NotEqual(V("s"), Typed(Qualified("Finset.univ"), Call("Finset", Local("Party")))),
                    new Formula.Not(Parenthesized(LocalCall("IsProductAcross", V("s"), V("z")))))));
        Formula vectors = All("z", Local("State"),
            Imp(Member(V("z"), V("W")), Imp(NotEqual(V("z"), D(0)), cuts)));
        return All("W", Call("Submodule", Complexes(), Local("State")),
            Equivalence(LocalCall("IsGES", V("W")), vectors));
    }

    private static Formula Ket44Formula() => All("a", FinOf(4), All("b", FinOf(4),
        Equal(Typed(LocalCall("ket44", V("a"), V("b")), Local("Original")),
            Call("Pi.single", Pair(V("a"), V("b")), Typed(D(1), Complexes())))));

    private static Formula Ket22Formula() => All("a", Local("Bit"), All("b", Local("Bit"),
        Equal(LocalCall("ket22", V("a"), V("b")), Tmul(
            Single(V("a"), Local("Qubit")), Single(V("b"), Local("Qubit"))))));

    private static Formula V35Formula() => All(LambdaLower, Parameters(),
        Equal(LocalCall("v35", LambdaLower), Vector(
            WeightedVector(0, 0, 0, 2, 1),
            WeightedVector(1, 1, 2, 3, 3),
            WeightedVector(2, 0, 1, 3, 2),
            WeightedVector(3, 3, 0, 2, 2),
            WeightedVector(4, 1, 1, 0, 3),
            WeightedVector(5, 1, 0, 2, 3),
            WeightedVector(6, 2, 0, 3, 1))));

    private static Formula WeightedVector(byte i, byte a, byte b, byte c, byte d) => Add(
        Scale(Typed(Call("Real.sqrt", At(LambdaLower, D(i))), Complexes()), Ket44(a, b)),
        Scale(Typed(Call("Real.sqrt", Subtract(D(1), At(LambdaLower, D(i)))), Complexes()), Ket44(c, d)));

    private static Formula Columns39Formula() => Equal(Local("columns39"), Vector(
        Scale(ComplexFraction(1, 6), Subtract(Add(Subtract(Scale(Typed(D(5), Complexes()), Ket22(0, 0)),
            Ket22(0, 1)), Scale(Typed(D(3), Complexes()), Ket22(1, 0))), Ket22(1, 1))),
        Scale(ComplexFraction(1, 6), Subtract(Add(Add(Negate(Ket22(0, 0)),
            Scale(Typed(D(5), Complexes()), Ket22(0, 1))), Scale(Typed(D(3), Complexes()), Ket22(1, 0))), Ket22(1, 1))),
        Scale(ComplexFraction(1, 2), Add(Subtract(Add(Ket22(0, 0), Ket22(0, 1)), Ket22(1, 0)), Ket22(1, 1))),
        Scale(ComplexFraction(1, 6), Add(Add(Subtract(Negate(Ket22(0, 0)), Ket22(0, 1)),
            Scale(Typed(D(3), Complexes()), Ket22(1, 0))), Scale(Typed(D(5), Complexes()), Ket22(1, 1))))));

    private static Formula Columns40Formula() => Equal(Local("columns40"), Vector(
        Scale(ComplexFraction(1, 3), Add(Add(Negate(Ket22(0, 0)), Scale(Typed(D(2), Complexes()), Ket22(0, 1))),
            Scale(Typed(D(2), Complexes()), Ket22(1, 1)))),
        Scale(ComplexFraction(1, 3), Add(Subtract(Scale(Typed(D(2), Complexes()), Ket22(0, 0)), Ket22(0, 1)),
            Scale(Typed(D(2), Complexes()), Ket22(1, 1)))),
        Ket22(1, 0),
        Scale(ComplexFraction(1, 3), Subtract(Add(Scale(Typed(D(2), Complexes()), Ket22(0, 0)),
            Scale(Typed(D(2), Complexes()), Ket22(0, 1))), Ket22(1, 1)))));

    private static Formula SubstitutionFormula(string substitution, string columns) => new Formula.Aligned([
        Equal(Local(substitution), Call("Module.Basis.constr", StandardBasis(FinOf(4)), Complexes(), Local(columns))),
        All("a", FinOf(4), Equal(At(StandardBasis(FinOf(4)), V("a")), Single(V("a"), Local("Ququart")))),
        All("z", Local("Ququart"), Equal(
            At(Call("Module.Basis.constr", StandardBasis(FinOf(4)), Complexes(), Local(columns)), V("z")),
            SumOver("a", FinOf(4), Scale(At(V("z"), V("a")), LocalCall(columns, V("a"))))))
    ]);

    private static Formula TwoBasisFormula() => new Formula.Aligned([
        Equal(Local("twoBasis"), Call("Module.Basis.tensorProduct", StandardBasis(Local("Bit")), StandardBasis(Local("Bit")))),
        All("a", Local("Bit"), Equal(At(StandardBasis(Local("Bit")), V("a")), Single(V("a"), Local("Qubit")))),
        All("a", Local("Bit"), All("b", Local("Bit"), Equal(
            At(Call("Module.Basis.tensorProduct", StandardBasis(Local("Bit")), StandardBasis(Local("Bit"))), Pair(V("a"), V("b"))),
            Tmul(At(StandardBasis(Local("Bit")), V("a")), At(StandardBasis(Local("Bit")), V("b"))))))
    ]);

    private static Formula InputCoordinatesFormula() => new Formula.Aligned([
        Equal(Local("inputCoordinates"), Call("Module.Basis.equivFun", InputBasis())),
        All("t", Tensor(Local("Ququart"), Local("Ququart")), All("p", Product(FinOf(4), FinOf(4)),
            Equal(At(Call("Module.Basis.equivFun", InputBasis()), V("t"), V("p")),
                At(Call("Module.Basis.repr", InputBasis()), V("t"), V("p"))))),
        All("a", FinOf(4), All("b", FinOf(4), Equal(At(InputBasis(), Pair(V("a"), V("b"))),
            Tmul(Single(V("a"), Local("Ququart")), Single(V("b"), Local("Ququart")))))),
        All("u", Local("Ququart"), All("v", Local("Ququart"), All("a", FinOf(4), All("b", FinOf(4),
            Equal(LocalCall("inputCoordinates", Tmul(V("u"), V("v")), Pair(V("a"), V("b"))),
                Multiply(At(V("u"), V("a")), At(V("v"), V("b"))))))))
    ]);

    private static Formula OutputCoordinatesFormula()
    {
        Formula config = Pair(V("a"), Pair(V("b"), Pair(V("c"), V("d"))));
        Formula association = FourBitBinders(Equal(
            At(Association(), Pair(Pair(V("a"), V("b")), Pair(V("c"), V("d")))), config));
        Formula coordinates = All("u", Local("TwoQubit"), All("v", Local("TwoQubit"),
            FourBitBinders(Equal(LocalCall("outputCoordinates", Tmul(V("u"), V("v")), config),
                Multiply(At(Call("Module.Basis.equivFun", Local("twoBasis")), V("u"), Pair(V("a"), V("b"))),
                    At(Call("Module.Basis.equivFun", Local("twoBasis")), V("v"), Pair(V("c"), V("d"))))))));
        return new Formula.Aligned([
            Equal(Local("outputCoordinates"), Call("Module.Basis.equivFun", OutputBasis())),
            All("q", Local("Config"), Equal(At(OutputBasis(), V("q")),
                At(Call("Module.Basis.tensorProduct", Local("twoBasis"), Local("twoBasis")),
                    At(Call("Equiv.symm", Association()), V("q"))))),
            association,
            coordinates
        ]);
    }

    private static Formula FactorwiseFormula() => new Formula.Aligned([
        Equal(Local("factorwise"), Call("LinearMap.comp",
            Call("LinearEquiv.toLinearMap", Local("outputCoordinates")),
            Call("LinearMap.comp", Call("TensorProduct.map", Local("substitution39"), Local("substitution40")),
                Call("LinearEquiv.toLinearMap", Call("LinearEquiv.symm", Local("inputCoordinates")))))),
        All("u", Local("Ququart"), All("v", Local("Ququart"), Equal(
            At(Call("TensorProduct.map", Local("substitution39"), Local("substitution40")), Tmul(V("u"), V("v"))),
            Tmul(LocalCall("substitution39", V("u")), LocalCall("substitution40", V("v"))))))
    ]);

    private static Formula TransformedFormula() => All(LambdaLower, Parameters(), All("i", FinOf(7),
        Equal(LocalCall("transformed", LambdaLower, V("i")),
            LocalCall("factorwise", LocalCall("v35", LambdaLower, V("i"))))));

    private static Formula SpanFormula() => All(LambdaLower, Parameters(),
        Equal(LocalCall("S", LambdaLower), Call("Submodule.span", Complexes(),
            Call("Set.range", LocalCall("transformed", LambdaLower)))));

    private static Formula ClaimFormula() => Equivalence(Local("claim"), All(LambdaLower, Parameters(),
        Imp(All("i", FinOf(7), And(LessThan(D(0), At(LambdaLower, V("i"))),
                LessThan(At(LambdaLower, V("i")), D(1)))),
            LocalCall("IsGES", LocalCall("S", LambdaLower)))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(string name)
    {
        var parts = name.Split('.');
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation." + name);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Qualified(name), arguments);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Product(Formula left, Formula right) => Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula Arrow(Formula domain, Formula codomain) => Parenthesized(new Formula.TypeArrow(domain, codomain));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula FinOf(byte size) => Call("Fin", D(size));
    private static Formula Parameters() => Arrow(FinOf(7), Reals());
    private static Formula Tensor(Formula left, Formula right) => Call("TensorProduct", Complexes(), left, right);
    private static Formula Tmul(Formula left, Formula right) => Call("TensorProduct.tmul", Complexes(), left, right);
    private static Formula Single(Formula label, Formula type) => Typed(Call("Pi.single", label, Typed(D(1), Complexes())), type);
    private static Formula StandardBasis(Formula labels) => Call("Pi.basisFun", Complexes(), labels);
    private static Formula InputBasis() => Call("Module.Basis.tensorProduct", StandardBasis(FinOf(4)), StandardBasis(FinOf(4)));
    private static Formula Association() => Call("Equiv.prodAssoc", Local("Bit"), Local("Bit"), Product(Local("Bit"), Local("Bit")));
    private static Formula OutputBasis() => Call("Module.Basis.reindex",
        Call("Module.Basis.tensorProduct", Local("twoBasis"), Local("twoBasis")), Association());
    private static Formula Ket44(byte a, byte b) => LocalCall("ket44", D(a), D(b));
    private static Formula Ket22(byte a, byte b) => LocalCall("ket22", D(a), D(b));
    private static Formula ComplexFraction(byte numerator, byte denominator) =>
        Typed(new Formula.Fraction(D(numerator), D(denominator)), Complexes());
    private static Formula Vector(params Formula[] entries)
    {
        var items = new System.Collections.Generic.List<Formula> { Bang, OpenBracket };
        foreach (var entry in entries)
        {
            if (items.Count > 2) items.AddRange([Comma, Sp]);
            items.Add(entry);
        }
        items.Add(CloseBracket);
        return Seq([.. items]);
    }
    private static Formula Projection(Formula value, params byte[] fields)
    {
        var items = new System.Collections.Generic.List<Formula> { value };
        foreach (var field in fields) items.AddRange([Dot, D(field)]);
        return Seq([.. items]);
    }
    private static Formula PartySubtype(bool inside) => Seq(OpenBrace, V("p"), Colon, Sp, Local("Party"), Sp,
        Slash, Slash, Sp, inside ? Member(V("p"), V("s")) : new Formula.Not(Parenthesized(Member(V("p"), V("s")))), CloseBrace);
    private static Formula All(string name, Formula type, Formula body) => All(V(name), type, body);
    private static Formula FourBitBinders(Formula body) => All("a", Local("Bit"), All("b", Local("Bit"),
        All("c", Local("Bit"), All("d", Local("Bit"), body))));
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), type)), Sp, Parenthesized(body));
    private static Formula Scale(Formula scalar, Formula vector) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula Negate(Formula vector) => Seq(Minus, Parenthesized(vector));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LessThan(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
