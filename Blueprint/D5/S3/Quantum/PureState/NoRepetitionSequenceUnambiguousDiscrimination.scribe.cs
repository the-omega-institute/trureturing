using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class NoRepetitionSequenceUnambiguousDiscriminationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/murshidguptarussobandyopadhyay2026nonlocality");
    private static LibraryNoteRef Sequences => LibraryNoteRef.Create(
        "D5/L/QuantumContext/guptamurshidbandyopadhyay2024sequences");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent local measurements attain the global unambiguous optimum for sequences of distinct equal-overlap states.",
        H("Unambiguous discrimination without repeated labels"),
        Blocks(
            Definition("label", "Label", "Sequences of distinct labels", LabelFormula(),
                "Label N k is the type of injective functions from the k positions to the N labels. "
                    + "An element x consists of its function x.val and a proof of injectivity. "
                    + "These are the ordered sequences in revised_02.tex, lines 828–835.", true),
            Definition("is-equiangular", "IsEquiangular", "Normalized states with equal real overlap", EquiangularFormula(),
                "Each vector ψ i has squared norm one, and every inner product between different vectors equals the real number s included in the complex numbers. "
                    + "The predicate itself places no restriction on s; the theorem assumes 0 < s < 1. "
                    + "This is the equal-overlap family in revised_02.tex, lines 822–826.", true),
            Definition("product-state", "productState", "Product-state coordinates", ProductStateFormula(),
                "The coordinate a of the product state labelled by x is the product, over positions j, of the coordinate a j of ψ (x.val j). "
                    + "Subtype.val explicitly extracts the function from the injective label. "
                    + "This expresses the tensor products in revised_02.tex, lines 828–832, in the coordinate basis.", true),
            Definition("is-unambiguous-measurement", "IsUnambiguousMeasurement", "Measurements with no erroneous output", MeasurementFormula(),
                "Every conclusive effect E x and the inconclusive effect E₀ is positive semidefinite. "
                    + "Their sum is the identity, and the effect for x has zero probability on every different input y. "
                    + "The success probabilities may depend on the input. This is the unambiguous condition of revised_02.tex, lines 652–672.", true),
            Definition("average-success", "averageSuccess", "Uniform average success", AverageFormula(),
                "The finite expectation averages the real readout of E x on φ x over all injective labels x, as in the uniform ensemble of revised_02.tex, lines 834–840. "
                    + "The displayed quotient expands that expectation and readout. Nat.cast explicitly includes the natural cardinality in the reals. "
                    + "If there are no labels the finite expectation is zero; k ≤ N ensures that labels exist in the theorem.", true),
            Definition("induced-effect", "inducedEffect", "Effects after classical processing", InducedFormula(),
                "For each output z, sum the tensor-product effects of exactly those outcome tuples o for which d o = z. "
                    + "Option.none denotes an inconclusive output, while Option.some carries a label. "
                    + "The single-system effects are the same at every position.", false),
            Definition("is-product-protocol", "IsProductProtocol", "Independent measurements and a decision rule", ProtocolFormula(),
                "The family F is one positive operator-valued measurement with outcomes Option (Fin N). "
                    + "Each position uses F independently, and d assigns an output to every tuple of local outcomes. "
                    + "The conclusive and inconclusive effects are precisely the effects induced by d. "
                    + "This predicate specifies the measurement and its processing; the separate unambiguous predicate imposes the no-error condition.", false),
            Definition("value", "value", "The two branches of the optimum", ValueFormula(),
                "The first branch is (1 − s) to the power k. The other branch is (1 − s) to the power N − 1 times 1 + (N − 1)s. "
                    + "In the latter coefficient, N − 1 is first computed in the natural numbers and then cast to a real number. "
                    + "The formula agrees with revised_02.tex, lines 976–982, on k ≤ N; its second branch also defines a value when k > N.", true),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The global bound and product attainment"),
                StatementSource.FromAuthor(Disp(Equal(Local("claim"), Parenthesized(ClaimFormula())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every N ≥ 3, 2 ≤ k ≤ N, real 0 < s < 1 and normalized equal-overlap family ψ, "
                            + "every unambiguous measurement has average success at most value N k s, and one independent product protocol is unambiguous and attains that value. "
                            + "This expresses the unambiguous clauses of the conjecture in revised_02.tex, lines 970–984. "
                            + "The minimum-error clause is not claimed.")),
                    Paragraph(Text(
                        "For k < N this also answers the no-repetition question in the 2024 paper, source.tex, lines 883–903: collective measurements give no improvement under these hypotheses. See "),
                        Ref(Sequences.Value), Text("."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Optimal unambiguous discrimination by local product measurements"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First form the Gram matrix K of the product states φ x = productState ψ x. "
                            + "Its (x,y) entry is the product over positions of 1 when x.val j = y.val j and s otherwise. "
                            + "For an unambiguous measurement put q x = Re⟨φ x, E x φ x⟩. "
                            + "Positivity and zero erroneous probability imply E x φ y = 0 whenever y ≠ x. "
                            + "Writing A for the matrix whose columns are φ x, compression of the conclusive effects therefore gives "
                            + "A* (Σx E x) A = diag(q). The inconclusive effect is positive, so K − diag(q) is positive semidefinite.")),
                    Paragraph(Text(
                        "Permutations of the N labels preserve K and act transitively on the injective labels: any bijection between the images of two injections extends to a permutation. "
                            + "Average the permuted positive matrices K − diag(q). Transitivity makes every averaged diagonal entry equal to the uniform mean of q. "
                            + "After division by the positive number of permutations, K − averageSuccess φ E times the identity is positive semidefinite.")),
                    Paragraph(Text(
                        "To find an eigenvalue of K, let G = (1 − s)I + sJ, where J has every entry one. "
                            + "If u i are eigenvectors of G with eigenvalues ev i, expand the determinant det(u i (y j)) by multilinearity in its rows. "
                            + "Summing over all tuples y shows that the tensor power of G multiplies this determinant by the product of the ev i. "
                            + "The determinant vanishes whenever y repeats a label, because two rows coincide. "
                            + "Thus the same eigenvector equation restricts to the injective labels and K.")),
                    Paragraph(Text(
                        "When k < N, use the k difference vectors eᵢ − eₖ for i in Fin k, with Fin k embedded in Fin N. "
                            + "Each has eigenvalue 1 − s. On the injection listing the first k labels, their evaluation matrix is the identity, so the determinant vector is nonzero. "
                            + "Its eigenvalue is (1 − s)^k. When k = N, write N = n + 1 and use the n differences eᵢ − eₙ together with the constant-one vector. "
                            + "The latter has eigenvalue 1 + ns. The evaluation matrix is invertible: summing coordinates in a vector in its nullspace first forces the coefficient of the constant column to vanish, "
                            + "and the other coordinates then force every remaining coefficient to vanish. "
                            + "Its nonzero determinant supplies an eigenvector with eigenvalue (1 − s)^(N − 1)(1 + (N − 1)s).")),
                    Paragraph(Text(
                        "Apply the positive matrix K − averageSuccess φ E times the identity to the nonzero determinant vector w. "
                            + "Its quadratic form is (value N k s − averageSuccess φ E) times the strictly positive squared norm of w. "
                            + "Nonnegativity proves the required upper bound for every unambiguous measurement.")),
                    Paragraph(Text(
                        "For attainment, let A now be the square matrix whose columns are the single-system vectors ψ i. "
                            + "Its Gram matrix is G. Since 1 − s > 0 and sJ is positive semidefinite, G is positive definite, so A is invertible. "
                            + "Put B = A⁻¹. On the label-coordinate space take H none = sJ and H (some i) = (1 − s)eᵢeᵢ*. "
                            + "These positive effects sum to G. The effects F o = B* H o B are positive and sum to the identity. "
                            + "The identity A* F o A = H o shows that on ψ j the outcome some j has probability 1 − s, none has probability s, and every other conclusive outcome has probability zero.")),
                    Paragraph(Text(
                        "A product effect is positive: each coordinate effect pulled back to the tuple indices is positive, and successive Hadamard products preserve positivity. "
                            + "Distributing the finite sums shows that all product effects sum to the identity. "
                            + "Distributing the coordinate sums in the quadratic form shows that each outcome probability is the product of its single-system probabilities. "
                            + "Summing product effects over the fibers of any decision rule preserves positivity and completeness. "
                            + "An injective map from pairs (x,r) to accepted outcome patterns defines a rule that returns x on these patterns and none elsewhere; "
                            + "the effect for x is then the sum over its patterns r. "
                            + "If its probability on y is p for x = y and zero otherwise, these effects form an unambiguous measurement with uniform average p.")),
                    Paragraph(Text(
                        "For full sequences, two injective maps Fin N → Fin N agreeing away from one position also agree at that position, since both use every label. "
                            + "Consequently the patterns obtained from x by retaining all outcomes, or replacing exactly one position by none, identify both x and the erased position uniquely. "
                            + "For k < N accept only the fully conclusive pattern listing x. Its probability is (1 − s)^k on x and zero on every other sequence. "
                            + "For k = N accept the fully conclusive pattern and all N patterns with exactly one inconclusive position. "
                            + "Their probabilities on x are (1 − s)^N and s(1 − s)^(N − 1) respectively. "
                            + "On a different sequence every accepted pattern contains a mismatched conclusive label, so its probability is zero. "
                            + "The total correct probability is (1 − s)^N + Ns(1 − s)^(N − 1) = (1 − s)^(N − 1)(1 + (N − 1)s). "
                            + "The two cases provide the required attaining protocol.")),
                    Paragraph(Text(
                        "Together the global upper bound and this attained value prove the unambiguous clauses of the conjecture. "
                            + "Independent local measurements followed by classical processing form an LOCC protocol. "
                            + "Thus the local and global unambiguous optima defined in revised_02.tex, lines 213–221, both equal value N k s. "
                            + "The same conclusion answers the 2024 no-repetition question for k < N under the stated hypotheses. "
                            + "The minimum-error clause is not claimed."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("murshid-gupta-russo-bandyopadhyay-2026-no-repetition-unambiguous-discrimination"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula LabelFormula() => Dimensions(Equal(LocalCall("Label", X("N"), X("k")),
        Seq(OpenBrace, Typed(X("x"), TupleType()), Sp, Slash, Slash, Sp,
            At(Qualified("Function", "Injective"), X("x")), CloseBrace)));

    private static Formula EquiangularFormula()
    {
        Formula normalized = All("i", FinOf(X("N")),
            Equal(Inner(At(X("ψ"), X("i")), At(X("ψ"), X("i"))), Typed(D(1), Complexes())));
        Formula overlap = All("i", FinOf(X("N")), All("j", FinOf(X("N")),
            ImpliesFormula(NotEqual(X("i"), X("j")),
                Equal(Inner(At(X("ψ"), X("i")), At(X("ψ"), X("j"))), ComplexCast(X("s"))))));
        return All("N", Naturals(), All("ψ", States(), All("s", Reals(),
            IffFormula(LocalCall("IsEquiangular", X("ψ"), X("s")), And(normalized, overlap)))));
    }

    private static Formula ProductStateFormula() => Dimensions(All("ψ", States(), All("x", Labels(),
        All("a", TupleType(), Equal(LocalCall("productState", X("ψ"), X("x"), X("a")),
            Product("j", FinOf(X("k")), At(X("ψ"), At(At(Qualified("Subtype", "val"), X("x")), X("j")),
                At(X("a"), X("j")))))))));

    private static Formula MeasurementFormula()
    {
        Formula positive = All("x", Labels(), Positive(At(X("E"), X("x"))));
        Formula complete = Equal(Add(SumOver("x", Labels(), At(X("E"), X("x"))), X("E₀")), Typed(D(1), ProductMatrix()));
        Formula noError = All("x", Labels(), All("y", Labels(), ImpliesFormula(NotEqual(X("y"), X("x")),
            Equal(Inner(At(X("φ"), X("y")), MulVec(At(X("E"), X("x")), At(X("φ"), X("y")))), Typed(D(0), Complexes())))));
        Formula body = And(positive, And(Positive(X("E₀")), And(complete, noError)));
        return Dimensions(All("φ", ProductStates(), All("E", Effects(), All("E₀", ProductMatrix(),
            IffFormula(LocalCall("IsUnambiguousMeasurement", X("φ"), X("E"), X("E₀")), body)))));
    }

    private static Formula AverageFormula() => Dimensions(All("φ", ProductStates(), All("E", Effects(),
        Equal(LocalCall("averageSuccess", X("φ"), X("E")), new Formula.Fraction(
            SumOver("x", Labels(), At(Qualified("Complex", "re"),
                Inner(At(X("φ"), X("x")), MulVec(At(X("E"), X("x")), At(X("φ"), X("x")))))),
            RealCast(At(Qualified("Fintype", "card"), Labels())))))));

    private static Formula InducedFormula() => Dimensions(All("F", SingleMeasurement(), All("d", Decision(),
        All("z", OptionOf(Labels()), Equal(LocalCall("inducedEffect", X("F"), X("d"), X("z")),
            SumOver("o", Outcomes(), If(Equal(At(X("d"), X("o")), X("z")),
                At(Qualified("D5", "S3", "Quantum", "Recovery", "ProductPrefixRigidity", "productMap"),
                    At(Qualified("Function", "const"), FinOf(X("k")), FinOf(X("N"))),
                    LambdaOf("j", FinOf(X("k")), At(X("F"), At(X("o"), X("j"))))),
                Typed(D(0), ProductMatrix()))))))));

    private static Formula ProtocolFormula() => Dimensions(All("F", SingleMeasurement(), All("d", Decision(),
        All("E", Effects(), All("E₀", ProductMatrix(), IffFormula(
            LocalCall("IsProductProtocol", X("F"), X("d"), X("E"), X("E₀")),
            And(All("o", OptionOf(FinOf(X("N"))), Positive(At(X("F"), X("o")))),
                And(Equal(SumOver("o", OptionOf(FinOf(X("N"))), At(X("F"), X("o"))), Typed(D(1), SingleMatrix())),
                    And(All("x", Labels(), Equal(At(X("E"), X("x")),
                            LocalCall("inducedEffect", X("F"), X("d"), At(Qualified("Option", "some"), X("x"))))),
                        Equal(X("E₀"), LocalCall("inducedEffect", X("F"), X("d"),
                            Typed(Qualified("Option", "none"), OptionOf(Labels())))))))))))));

    private static Formula ValueFormula() => Dimensions(All("s", Reals(),
        Equal(LocalCall("value", X("N"), X("k"), X("s")), If(Less(X("k"), X("N")),
            Power(Subtract(Typed(D(1), Reals()), X("s")), X("k")),
            Multiply(Power(Subtract(Typed(D(1), Reals()), X("s")), NatPredecessor()),
                Add(Typed(D(1), Reals()), Multiply(RealCast(NatPredecessor()), X("s"))))))));

    private static Formula ClaimFormula()
    {
        Formula product = LocalCall("productState", X("ψ"));
        Formula unambiguous = LocalCall("IsUnambiguousMeasurement", product, X("E"), X("E₀"));
        Formula success = LocalCall("averageSuccess", product, X("E"));
        Formula optimum = LocalCall("value", X("N"), X("k"), X("s"));
        Formula bound = All("E", Effects(), All("E₀", ProductMatrix(), ImpliesFormula(unambiguous, LE(success, optimum))));
        Formula attained = Some("F", SingleMeasurement(), Some("d", Decision(), Some("E", Effects(),
            Some("E₀", ProductMatrix(), And(LocalCall("IsProductProtocol", X("F"), X("d"), X("E"), X("E₀")),
                And(unambiguous, Equal(success, optimum)))))));
        Formula states = All("ψ", States(), ImpliesFormula(LocalCall("IsEquiangular", X("ψ"), X("s")), And(bound, attained)));
        Formula overlap = All("s", Reals(), ImpliesFormula(Less(Typed(D(0), Reals()), X("s")),
            ImpliesFormula(Less(X("s"), Typed(D(1), Reals())), states)));
        return Dimensions(ImpliesFormula(LE(Typed(D(3), Naturals()), X("N")),
            ImpliesFormula(LE(Typed(D(2), Naturals()), X("k")), ImpliesFormula(LE(X("k"), X("N")), overlap))));
    }

    private static Formula X(string name) => name switch
    {
        "ψ" => new Formula.Psi(),
        "φ" => new Formula.Phi(),
        "E₀" => new Formula.Subscript(F.Id("E"), D(0)),
        _ => F.Id(name),
    };
    private static Formula Local(string name) => Qualified(name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula OptionOf(Formula type) => At(Qualified("Option"), type);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula TupleType() => Arrow(FinOf(X("k")), FinOf(X("N")));
    private static Formula Labels() => LocalCall("Label", X("N"), X("k"));
    private static Formula States() => Arrow(FinOf(X("N")), Arrow(FinOf(X("N")), Complexes()));
    private static Formula ProductStates() => Arrow(Labels(), Arrow(TupleType(), Complexes()));
    private static Formula ProductMatrix() => At(Qualified("Matrix"), TupleType(), TupleType(), Complexes());
    private static Formula SingleMatrix() => At(Qualified("Matrix"), FinOf(X("N")), FinOf(X("N")), Complexes());
    private static Formula Effects() => Arrow(Labels(), ProductMatrix());
    private static Formula SingleMeasurement() => Arrow(OptionOf(FinOf(X("N"))), SingleMatrix());
    private static Formula Outcomes() => Arrow(FinOf(X("k")), OptionOf(FinOf(X("N"))));
    private static Formula Decision() => Arrow(Outcomes(), OptionOf(Labels()));
    private static Formula Dimensions(Formula body) => All("N", Naturals(), All("k", Naturals(), body));
    private static Formula NatPredecessor() => Typed(Subtract(X("N"), Typed(D(1), Naturals())), Naturals());
    private static Formula RealCast(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals());
    private static Formula ComplexCast(Formula value) => Typed(At(Qualified("Complex", "ofReal"), value), Complexes());
    private static Formula Positive(Formula matrix) => At(Qualified("Matrix", "PosSemidef"), matrix);
    private static Formula Inner(Formula left, Formula right) => At(Qualified("dotProduct"), At(Qualified("star"), left), right);
    private static Formula MulVec(Formula matrix, Formula vector) => At(Qualified("Matrix", "mulVec"), matrix, vector);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Product(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Prod, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), Parenthesized(exponent));
    private static Formula If(Formula condition, Formula yes, Formula no) => At(Qualified("ite"), condition, yes, no);
}
