using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class KvashchukMulticopyDesignRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/kvashchuk2026multicopy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven qubit states with three copies outperform every minimal weighted design with the maximally mixed state appended.",
        H("Weighted multicopy designs need not be optimal"), Blocks(
            Node("oct-vec", "Six qubit preparation vectors", "octVec", OctVecFormula(),
                "The six vectors are the computational basis vectors and the two eigenvectors of each of the Pauli X and Y matrices. They are unnormalized; their squared norms are 1, 1, 2, 2, 2 and 2, respectively.",
                AssessedProvenance.FromRepo()),
            Node("tensor-pow", "Tensor powers in digit coordinates", "tensorPow", TensorPowFormula(),
                "The equivalence finFunctionFinEquiv identifies a function Fin k → Fin d with an index in Fin (d^k). Each matrix entry is the product of the k entries selected by the inverse equivalence. This gives tensor powers also when k=0, using the empty product.",
                AssessedProvenance.FromRepo()),
            Node("perm-op", "Permutation of tensor factors", "permOp", PermOpFormula(),
                "A permutation of Fin k induces a permutation matrix on the tensor coordinates. Its row i and column j entry is one precisely when the digit function of i equals the digit function of j composed with the permutation, and zero otherwise.",
                AssessedProvenance.FromRepo()),
            Node("pi-sym", "The symmetric projector", "PiSym", PiSymFormula(),
                "Equation (8) expresses the symmetric projector as the average of all tensor-factor permutation matrices. The normalization is the inverse of Nat.factorial k cast to the complex numbers; the sum ranges over Equiv.Perm (Fin k).",
                AssessedProvenance.FromLiterature(Source)),
            Node("weighted-design", "Weighted state designs", "IsWeightedDesign", WeightedDesignFormula(),
                "Definition 6 requires nonnegative real weights summing to one. A state must be pure whenever its weight is strictly positive; zero-weight states need not be pure. The weighted tensor moment equals the symmetric projector multiplied by the inverse of its complex trace. D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState consists of positive CStarMatrix values of trace one, and D5.S3.Quantum.Foundation.FiniteDiamondDistance.IsPure requires an outer-product representation of the underlying value.",
                AssessedProvenance.FromLiterature(Source)),
            Node("design-exists", "Existence of a weighted design", "DesignExists", DesignExistsFormula(),
                "The existence condition in §3.3 asks for an N-state family and real weights satisfying Definition 6. Both the family and the weights are existentially quantified.",
                AssessedProvenance.FromLiterature(Source)),
            Node("n-prime", "The least design size", "Nprime", NprimeFormula(),
                "Section 3.3 defines N′(d,k) as the smallest size admitting a weighted state k-design. Here sInf is taken in the natural numbers. Nat.sInf_def identifies it with the least member of a nonempty set, and Nat.sInf_empty gives zero for the empty set.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("max-mixed"), DeclarationHandle.Create(Prefix + "maxMixed"),
                H("The maximally mixed density state"), StatementSource.FromAuthor(Disp(MaxMixedFormula())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For positive dimension d, maxMixed is D5.S3.Quantum.Divergence.GibbsVariationalIdentity.gibbsState at the zero Hamiltonian, with self-adjointness supplied by IsSelfAdjoint.zero. The index ⟨0,hd⟩ supplies the Nonempty (Fin d) instance. D5.S3.Quantum.Divergence.GibbsVariationalIdentity.gibbs_state_zero identifies its underlying value with the identity scaled by the inverse of the real cast of d, as displayed below.")),
                    new DocumentBlock.DisplayFormula(MaxMixedValueFormula())), DescribeRole.Definition),
            Node("adjoin", "Append the maximally mixed state", "adjoin", AdjoinFormula(),
                "Fin.lastCases retains the original states at the first N indices and places the maximally mixed state at the last index of Fin (N+1). The positive-dimension argument supplies the appended density state.",
                AssessedProvenance.FromRepo()),
            Describe.Lean(DescribeId.Create("discr"), DeclarationHandle.Create(Prefix + "Discr"),
                H("Multicopy discriminability"), StatementSource.FromAuthor(Disp(DiscrFormula())),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Definition 1 in §2 optimizes the equiprobable discrimination success over all N-outcome POVMs on the k-copy space. The definition here uses the real supremum sSup. D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM requires positive semidefinite effects summing to the identity. D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation.success includes the complex scalar 1/(N:ℂ) before taking the real part of each trace, as the following equality shows.")),
                    new DocumentBlock.DisplayFormula(SuccessFormula())), DescribeRole.Definition),
            Node("claim", "Optimality of a minimal design with one extra state", "claim", ClaimFormula(),
                "Section 11.2 and §12, question 4, ask whether a minimal weighted design combined with the maximally mixed state is optimal. The assertion quantifies over positive dimensions and positive copy counts, every weighted design on N′(d,k) states, and every competing density-state family on N′(d,k)+1 states. The probabilities of the discrimination task are uniform even when the design weights are not.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("A seven-state qubit counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "In dimension 2 with three copies, the six octahedral pure states with equal weights form a weighted design. The third-factor partial transpose of the normalized symmetric projector has rank six, whereas each positive-weight pure summand has rank at most one. Thus N′(2,3)=6, and every six-state weighted design has positive weights and pure states. The symmetric projector has trace four. Adding one eighth of its orthogonal complement gives an operator of trace 9/2 that dominates the three-copy state of every pure qubit and the three-copy maximally mixed state. Every six-state weighted design with the maximally mixed state appended therefore has discriminability at most 9/14. A competing family consists of the two computational basis states, the three pure states with normalized vectors (1,ω^j)/√2 for j=0,1,2 and ω=(−1+i√3)/2, and the two diagonal density matrices with diagonals (2/3,1/3) and (1/3,2/3). An explicit seven-outcome POVM has individual success probabilities 51/64, 51/64, 25/32, 25/32, 25/32, 8/27 and 8/27. Their uniform average is 1957/3024, exceeding 9/14 by 13/3024. This gives a negative answer to Kvashchuk and coauthors' question 4 already for qubits."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kvashchuk-2026-multicopy-design-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Vec(params Formula[] entries)
    {
        Formula result = Qualified("Matrix", "vecEmpty");
        for (int i = entries.Length - 1; i >= 0; i--)
            result = At(Qualified("Matrix", "vecCons"), entries[i], result);
        return result;
    }
    private static Formula OctVecFormula() => Equal(Local("octVec"), Vec(
        Vec(Typed(Num(1), Complexes()), Num(0)), Vec(Num(0), Num(1)),
        Vec(Num(1), Num(1)), Vec(Num(1), new Formula.Negate(Num(1))),
        Vec(Num(1), Qualified("Complex", "I")),
        Vec(Num(1), new Formula.Negate(Qualified("Complex", "I")))));

    private static Formula TensorPowFormula() => Dimensions(All("A", Matrix(Fin(X("d"))),
        All("i", TensorIndex(), All("j", TensorIndex(), Equal(
            At(LocalCall("tensorPow", X("k"), X("A")), X("i"), X("j")),
            ProductOver("t", Fin(X("k")), At(X("A"),
                At(Digits(X("i")), X("t")), At(Digits(X("j")), X("t")))))))));

    private static Formula PermOpFormula() => Dimensions(All("sigma", Permutations(),
        All("i", TensorIndex(), All("j", TensorIndex(), Equal(
            At(LocalCall("permOp", X("d"), X("k"), X("sigma")), X("i"), X("j")),
            At(Qualified("ite"), Equal(Digits(X("i")),
                    At(Qualified("Function", "comp"), Digits(X("j")), X("sigma"))),
                Typed(Num(1), Complexes()), Typed(Num(0), Complexes())))))));

    private static Formula PiSymFormula() => Dimensions(Equal(
        LocalCall("PiSym", X("d"), X("k")), Smul(
            Inverse(Typed(At(Qualified("Nat", "cast"),
                At(Qualified("Nat", "factorial"), X("k"))), Complexes())),
            SumOver("sigma", Permutations(), LocalCall("permOp", X("d"), X("k"), X("sigma"))))));

    private static Formula WeightedDesignFormula()
    {
        Formula nonnegative = All("i", Fin(X("N")), LE(Num(0), At(X("p"), X("i"))));
        Formula normalized = Equal(SumOver("i", Fin(X("N")), At(X("p"), X("i"))),
            Typed(Num(1), Reals()));
        Formula pure = All("i", Fin(X("N")), Implication(LT(Num(0), At(X("p"), X("i"))),
            At(Qualified("D5", "S3", "Quantum", "Foundation", "FiniteDiamondDistance", "IsPure"),
                At(X("rho"), X("i")))));
        Formula projector = LocalCall("PiSym", X("d"), X("k"));
        Formula moment = Equal(SumOver("i", Fin(X("N")), Smul(
                At(Qualified("Complex", "ofReal"), At(X("p"), X("i"))), TensorState(X("i")))),
            Smul(Inverse(At(Qualified("Matrix", "trace"), projector)), projector));
        return EnsembleParameters(All("p", Arrow(Fin(X("N")), Reals()), Equivalence(
            LocalCall("IsWeightedDesign", X("k"), X("rho"), X("p")),
            And(nonnegative, And(normalized, And(pure, moment))))));
    }

    private static Formula DesignExistsFormula() => Dimensions(All("N", Naturals(), Equivalence(
        LocalCall("DesignExists", X("d"), X("k"), X("N")),
        Some("rho", StateFamily(X("N")), Some("p", Arrow(Fin(X("N")), Reals()),
            LocalCall("IsWeightedDesign", X("k"), X("rho"), X("p")))))));

    private static Formula NprimeFormula() => Dimensions(Equal(
        LocalCall("Nprime", X("d"), X("k")), At(Qualified("sInf"),
            Typed(SetWhere("N", Naturals(), LocalCall("DesignExists", X("d"), X("k"), X("N"))),
                At(Qualified("Set"), Naturals())))));

    private static Formula MaxMixedFormula() => All("d", Naturals(), All("hd", LT(Num(0), X("d")),
        Equal(LocalCall("maxMixed", X("d"), X("hd")),
            At(Qualified("D5", "S3", "Quantum", "Divergence", "GibbsVariationalIdentity", "gibbsState"),
                Typed(Num(0), At(Qualified("CStarMatrix"), Fin(X("d")), Fin(X("d")), Complexes())),
                At(Qualified("IsSelfAdjoint", "zero"),
                    At(Qualified("CStarMatrix"), Fin(X("d")), Fin(X("d")), Complexes()))))));

    private static Formula MaxMixedValueFormula() => All("d", Naturals(), All("hd", LT(Num(0), X("d")),
        Equal(Projection(LocalCall("maxMixed", X("d"), X("hd")), 1),
            At(Qualified("CStarMatrix", "ofMatrix"), Smul(
                Inverse(Typed(At(Qualified("Nat", "cast"), X("d")), Reals())),
                Typed(Num(1), Matrix(Fin(X("d")))))))));

    private static Formula AdjoinFormula() => All("d", Naturals(), All("N", Naturals(),
        All("rho", StateFamily(X("N")), All("hd", LT(Num(0), X("d")), Equal(
            LocalCall("adjoin", X("rho"), X("hd")),
            At(Qualified("Fin", "lastCases"), LocalCall("maxMixed", X("d"), X("hd")), X("rho")))))));

    private static Formula DiscrFormula() => EnsembleParameters(Equal(
        LocalCall("Discr", X("k"), X("rho")), At(Qualified("sSup"),
            Typed(SetWhere("r", Reals(), Some("E", Effects(), And(
                At(Qualified("D5", "S3", "Quantum", "QuantumChannels",
                    "ConcealmentKernelNecessityRefutation", "IsPOVM"), X("E")),
                Equal(X("r"), Success())))), At(Qualified("Set"), Reals())))));

    private static Formula SuccessFormula() => EnsembleParameters(All("E", Effects(), Equal(
        Success(), SumOver("i", Fin(X("N")), At(Qualified("Complex", "re"),
            At(Qualified("Matrix", "trace"), Multiply(
                Smul(new Formula.Fraction(Typed(Num(1), Complexes()),
                    Typed(At(Qualified("Nat", "cast"), X("N")), Complexes())), TensorState(X("i"))),
                At(X("E"), X("i")))))))));

    private static Formula ClaimFormula()
    {
        Formula size = LocalCall("Nprime", X("d"), X("k"));
        return Equivalence(Local("claim"), Dimensions(All("hd", LT(Num(0), X("d")),
            Implication(LT(Num(0), X("k")), All("rho", StateFamily(size),
                All("p", Arrow(Fin(size), Reals()), Implication(
                    LocalCall("IsWeightedDesign", X("k"), X("rho"), X("p")),
                    All("E", StateFamily(Add(size, Num(1))), LE(
                        LocalCall("Discr", X("k"), X("E")),
                        LocalCall("Discr", X("k"), LocalCall("adjoin", X("rho"), X("hd"))))))))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Measurement", "KvashchukMulticopyDesignRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(Formula size) => At(Qualified("Fin"), size);
    private static Formula Matrix(Formula index) => At(Qualified("Matrix"), index, index, Complexes());
    private static Formula StateFamily(Formula size) => Arrow(Fin(size), At(Qualified(
        "D5", "S3", "Quantum", "Foundation", "FiniteStateChannel", "DensityState"), Fin(X("d"))));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula TensorIndex() => Fin(new Formula.Power(X("d"), X("k")));
    private static Formula Permutations() => At(Qualified("Equiv", "Perm"), Fin(X("k")));
    private static Formula Digits(Formula index) => At(At(Qualified("Equiv", "symm"),
        Typed(Qualified("finFunctionFinEquiv"), At(Qualified("Equiv"),
            Arrow(Fin(X("k")), Fin(X("d"))), TensorIndex()))), index);
    private static Formula Projection(Formula value, byte field) => Seq(Parenthesized(value), Dot, D(field));
    private static Formula TensorState(Formula index) =>
        LocalCall("tensorPow", X("k"), Projection(At(X("rho"), index), 1));
    private static Formula Effects() => Arrow(Fin(X("N")), Matrix(TensorIndex()));
    private static Formula Success() => At(Qualified("D5", "S3", "Quantum", "Measurement",
        "EquiprobablePgmActiveSetRefutation", "success"), LambdaOf("i", Fin(X("N")), TensorState(X("i"))), X("E"));
    private static Formula Dimensions(Formula body) => All("d", Naturals(), All("k", Naturals(), body));
    private static Formula EnsembleParameters(Formula body) => All("d", Naturals(), All("N", Naturals(),
        All("k", Naturals(), All("rho", StateFamily(X("N")), body))));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula SetWhere(string name, Formula type, Formula condition) =>
        Seq(OpenBrace, Typed(X(name), type), Sp, Mid, Sp, condition, Sp, CloseBrace);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula ProductOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula Inverse(Formula value) => new Formula.Power(Parenthesized(value), new Formula.Negate(Num(1)));
    private static Formula Smul(Formula scalar, Formula value) => At(Qualified("HSMul", "hSMul"), scalar, value);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
