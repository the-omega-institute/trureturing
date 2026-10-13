using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class PassiveMemoryNonclassicalRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/salazar2025dephasing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In dimension 3, a passive memory implementation exists whose Gram matrix is not classical.",
        H("Passive memory with a nonclassical Gram matrix"), Blocks(
            Node("mat", "Complex square matrices", "Mat", MatFormula(),
                "The operators in Equation (9) are complex matrices. The coordinate type ι is arbitrary; finite coordinate types are specified when sums and channels are used."),
            Node("kraus-channel", "Finite Kraus channels", "KrausChannel", KrausChannelFormula(),
                "The channels in Equation (9) have finite Kraus families. The dependent pair records the number n of Kraus operators, and the subtype requires their conjugate-transpose products to sum to the identity matrix."),
            Node("act", "Action of a Kraus channel", "act", ActFormula(),
                "Equation (9) uses the channel action. D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus applies the family on the left and its conjugate transpose on the right; the two family arguments here are both E.2.1."),
            Node("state-matrix", "The matrix of a density state", "stateMatrix", StateMatrixFormula(),
                "The states in Equation (9) are positive matrices of trace one. D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState uses CStarMatrix coordinates. Applying Equiv.symm to CStarMatrix.ofMatrix converts the underlying value ρ.1 to an ordinary complex matrix."),
            Node("append-memory", "Append the initial memory", "appendMemory", AppendMemoryFormula(),
                "Equation (9) begins by tensoring an input matrix with the fixed memory state τ. Matrix.kronecker puts the system coordinate first and the memory coordinate second."),
            Node("discard-memory", "Discard the final memory", "discardMemory", DiscardMemoryFormula(),
                "Equation (9) ends by tracing out the memory. D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight sums the diagonal entries in the second coordinate and retains the system matrix."),
            Node("implemented", "The implemented channel", "implemented", ImplementedFormula(),
                "Equation (9) first appends τ, applies the encoding channel Nen, applies E to the system while leaving the memory unchanged, applies the decoding channel Nde, and traces out the memory. D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron is the tensor product of the two linear maps."),
            Node("choi", "Normalized output-first Choi matrix", "choi", ChoiFormula(),
                "Equation (2) uses a normalized maximally entangled input. The definition scales D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.choi_matrix F by the inverse of the complex cast of d. Accordingly, the entry at row (i,j) and column (k,l) is the (i,k) entry of F applied to Matrix.single j l 1, multiplied by that inverse. The first coordinate is the output coordinate. The definition also accepts d=0."),
            Node("gram", "Gram matrices", "Gram", GramFormula(),
                "The Gram matrices in Equations (13) and (19) are positive semidefinite complex matrices with every diagonal entry equal to one."),
            Node("dephasing-gram", "Equal diagonal blocks", "DephasingGram", DephasingGramFormula(),
                "Equation (13) requires all diagonal blocks of the Gram matrix to agree: for every i,k,j,l, the entry C((i,j),(i,l)) equals C((k,j),(k,l))."),
            Node("passive", "Passive memory", "Passive", PassiveFormula(),
                "Definition 2 and Equation (29) require the memory marginal after encoding to be independent of the input state. Equality for every pair of density inputs ρ and σ expresses that independence. D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft traces out the system coordinate."),
            Node("classical-gram", "Classical Gram matrices", "ClassicalGram", ClassicalGramFormula(),
                "Proposition 1(ii) describes classical memory by a finite convex combination of Kronecker products of Gram matrices. The weights q are real and nonnegative, sum to one, and act by scalar multiplication on the complex matrices. Each P(a) and Q(a) has unit diagonal and is positive semidefinite."),
            Node("implements", "Implementation of a dephasing Gram matrix", "Implements", ImplementsFormula(),
                "Equations (13) and (19) combine the equal diagonal-block condition with the channel identity: for every Kraus channel E, the normalized Choi matrix of the implementation is Matrix.hadamard C applied to the normalized Choi matrix of E. Matrix.hadamard is entrywise multiplication."),
            Node("claim", "Passive memory and classical simulation", "claim", ClaimFormula(),
                "Section V.C asks whether the equivalence with classical memory proved for qubits extends to every dimension. The assertion here quantifies over positive system and finite memory dimensions, every memory density state, every encoding and decoding Kraus channel, and every Gram matrix implemented as in Equations (9), (13) and (19). It asserts that a passive memory always gives the classical decomposition of Proposition 1(ii)."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("A passive memory need not give a classical Gram matrix"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "For a system of dimension 3 and a memory of dimension 2, take the memory state to be one half of the identity. Use the same block diagonal unitary for encoding and decoding, with diagonal blocks the identity, D5.S3.Quantum.FiniteDimensional.qubitX and D5.S3.Quantum.FiniteDimensional.qubitZ. The memory marginal remains equal to its initial state for every density input. The resulting Gram matrix has equal diagonal blocks and gives the required Choi identity for every Kraus channel. Every classical Gram matrix has a positive semidefinite partial transpose in the second coordinate. Here its principal block on (0,0), (1,1), (2,2) has rows (1,1,1), (1,1,−1), (1,−1,1). Its quadratic form at (−1,1,1) equals −3, so the Gram matrix is not classical. This gives a negative answer to Salazar and Shahbeigi's question in §V.C."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("salazar-shahbeigi-2025-passive-memory-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula MatFormula() => For(Iota, TypeStar(),
        Equal(LocalCall("Mat", Iota), Call("Matrix", Iota, Iota, Complexes())));

    private static Formula KrausChannelFormula()
    {
        Formula family = Arrow(Fin(X("n")), Mat(Iota));
        Formula completeness = Equal(SumOver(X("a"), Fin(X("n")),
            Multiply(At(Qualified("Matrix", "conjTranspose"), At(X("K"), X("a"))),
                At(X("K"), X("a")))), Typed(Num(1), Mat(Iota)));
        Formula subtype = Seq(OpenBrace, Sp, X("K"), Sp, Colon, Sp, family,
            Sp, Slash, Slash, Sp, completeness, Sp, CloseBrace);
        Formula sigma = Seq(Sigma, Sp, Typed(X("n"), Naturals()), Comma, Sp, subtype);
        return FiniteCoordinates(Equal(LocalCall("KrausChannel", Iota), sigma));
    }

    private static Formula ActFormula() => FiniteCoordinates(For(X("E"), Channel(Iota),
        Equal(LocalCall("act", X("E")), At(KrausMap(),
            Projection(Projection(X("E"), 2), 1), Projection(Projection(X("E"), 2), 1)))));

    private static Formula StateMatrixFormula() => FiniteCoordinates(For(Rho, State(Iota),
        Equal(LocalCall("stateMatrix", Rho), At(
            At(Qualified("Equiv", "symm"), Qualified("CStarMatrix", "ofMatrix")),
            Typed(Projection(Rho, 1), Call("CStarMatrix", Iota, Iota, Complexes()))))));

    private static Formula AppendMemoryFormula() => Dimensions(For(Tau, State(Fin(X("r"))),
        For(X("A"), Mat(Fin(X("d"))), Equal(
            At(Typed(LocalCall("appendMemory", Tau), Map(Fin(X("d")), SystemMemory())), X("A")),
            At(Qualified("Matrix", "kronecker"), X("A"), LocalCall("stateMatrix", Tau))))));

    private static Formula DiscardMemoryFormula() => Dimensions(
        For(X("A"), Mat(SystemMemory()), Equal(
            At(Typed(Local("discardMemory"), Map(SystemMemory(), Fin(X("d")))), X("A")),
            At(PartialTrace("partialTraceRight"), X("A")))));

    private static Formula ImplementedFormula() => Dimensions(For(Tau, State(Fin(X("r"))),
        For(X("Nen"), Channel(SystemMemory()), For(X("Nde"), Channel(SystemMemory()),
            For(X("E"), Channel(Fin(X("d"))), For(X("A"), Mat(Fin(X("d"))),
                Equal(At(LocalCall("implemented", Tau, X("Nen"), X("Nde"), X("E")), X("A")),
                    At(PartialTrace("partialTraceRight"),
                        At(LocalCall("act", X("Nde")),
                            At(At(MatrixMapName("kron"), LocalCall("act", X("E")),
                                    Typed(Qualified("LinearMap", "id"), Map(Fin(X("r")), Fin(X("r"))))),
                                At(LocalCall("act", X("Nen")),
                                    At(Qualified("Matrix", "kronecker"), X("A"),
                                        LocalCall("stateMatrix", Tau)))))))))))));

    private static Formula ChoiFormula() => For(X("d"), Naturals(),
        For(X("F"), Map(Fin(X("d")), Fin(X("d"))), Equal(
            LocalCall("choi", X("d"), X("F")),
            At(Qualified("HSMul", "hSMul"),
                new Formula.Power(Typed(At(Qualified("Nat", "cast"), X("d")), Complexes()),
                    new Formula.Negate(Num(1))),
                At(Seq(MatrixMapName("choi"), Underscore, Grp(X("matrix"))), X("F"))))));

    private static Formula GramFormula() => For(Iota, TypeStar(), For(X("C"), Mat(Iota),
        Equivalence(LocalCall("Gram", X("C")), And(
            At(Qualified("Matrix", "PosSemidef"), X("C")),
            For(X("i"), Iota, Equal(At(X("C"), X("i"), X("i")), Typed(Num(1), Complexes())))))));

    private static Formula DephasingGramFormula() => For(X("d"), Naturals(),
        For(X("C"), Mat(Product(Fin(X("d")), Fin(X("d")))),
            Equivalence(LocalCall("DephasingGram", X("C")), And(LocalCall("Gram", X("C")),
                For(X("i"), Fin(X("d")), For(X("k"), Fin(X("d")),
                    For(X("j"), Fin(X("d")), For(X("l"), Fin(X("d")), Equal(
                        At(X("C"), Pair(X("i"), X("j")), Pair(X("i"), X("l"))),
                        At(X("C"), Pair(X("k"), X("j")), Pair(X("k"), X("l"))))))))))));

    private static Formula PassiveFormula()
    {
        Formula Marginal(Formula input) => At(PartialTrace("partialTraceLeft"),
            At(LocalCall("act", X("Nen")), At(Qualified("Matrix", "kronecker"),
                LocalCall("stateMatrix", input), LocalCall("stateMatrix", Tau))));
        return Dimensions(For(Tau, State(Fin(X("r"))), For(X("Nen"), Channel(SystemMemory()),
            Equivalence(LocalCall("Passive", Tau, X("Nen")),
                For(Rho, State(Fin(X("d"))), For(SigmaLower, State(Fin(X("d"))),
                    Equal(Marginal(Rho), Marginal(SigmaLower))))))));
    }

    private static Formula ClassicalGramFormula()
    {
        Formula gramFamily = Arrow(Fin(X("n")), Mat(Fin(X("d"))));
        Formula conditions = And(For(X("a"), Fin(X("n")), LE(Num(0), At(X("q"), X("a")))),
            And(Equal(SumOver(X("a"), Fin(X("n")), At(X("q"), X("a"))), Typed(Num(1), Reals())),
                And(For(X("a"), Fin(X("n")), And(
                        LocalCall("Gram", At(X("P"), X("a"))),
                        LocalCall("Gram", At(X("Q"), X("a"))))),
                    Equal(X("C"), SumOver(X("a"), Fin(X("n")),
                        At(Qualified("HSMul", "hSMul"), At(X("q"), X("a")),
                            At(Qualified("Matrix", "kronecker"),
                                At(X("P"), X("a")), At(X("Q"), X("a")))))))));
        return For(X("d"), Naturals(), For(X("C"), Mat(Product(Fin(X("d")), Fin(X("d")))),
            Equivalence(LocalCall("ClassicalGram", X("C")),
                Some(X("n"), Naturals(), Some(X("q"), Arrow(Fin(X("n")), Reals()),
                    Some(X("P"), gramFamily, Some(X("Q"), gramFamily, conditions)))))));
    }

    private static Formula ImplementsFormula() => Dimensions(For(Tau, State(Fin(X("r"))),
        For(X("Nen"), Channel(SystemMemory()), For(X("Nde"), Channel(SystemMemory()),
            For(X("C"), Mat(Product(Fin(X("d")), Fin(X("d")))),
                Equivalence(LocalCall("Implements", Tau, X("Nen"), X("Nde"), X("C")),
                    And(LocalCall("DephasingGram", X("C")),
                        For(X("E"), Channel(Fin(X("d"))), Equal(
                            LocalCall("choi", X("d"), LocalCall("implemented", Tau, X("Nen"), X("Nde"), X("E"))),
                            At(Qualified("Matrix", "hadamard"), X("C"),
                                LocalCall("choi", X("d"), LocalCall("act", X("E")))))))))))));

    private static Formula ClaimFormula() => Equivalence(Local("claim"), Dimensions(
        Implication(LT(Num(0), X("d")), Implication(LT(Num(0), X("r")),
            For(Tau, State(Fin(X("r"))), For(X("Nen"), Channel(SystemMemory()),
                For(X("Nde"), Channel(SystemMemory()),
                    For(X("C"), Mat(Product(Fin(X("d")), Fin(X("d")))),
                        Implication(LocalCall("Implements", Tau, X("Nen"), X("Nde"), X("C")),
                            Implication(LocalCall("Passive", Tau, X("Nen")),
                                LocalCall("ClassicalGram", X("C"))))))))))));

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
        Qualified("D5", "S3", "QuantumChannels", "PassiveMemoryNonclassicalRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula MatrixMapName(string name) => Qualified(
        "D5", "S3", "Quantum", "Foundation", "FiniteKrausChannel", "PhyslibLeaf", "MatrixMap", name);
    private static Formula KrausMap() => Seq(MatrixMapName("of"), Underscore, Grp(X("kraus")));
    private static Formula Map(Formula input, Formula output) => At(Qualified(
        "D5", "S3", "Quantum", "Foundation", "FiniteKrausChannel", "PhyslibLeaf", "MatrixMap"),
        input, output, Complexes());
    private static Formula PartialTrace(string name) => Qualified(
        "D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula TypeStar() => Seq(X("Type"), Star);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Mat(Formula index) => LocalCall("Mat", index);
    private static Formula Channel(Formula index) => LocalCall("KrausChannel", index);
    private static Formula State(Formula index) => At(Qualified(
        "D5", "S3", "Quantum", "Foundation", "FiniteStateChannel", "DensityState"), index);
    private static Formula Product(Formula left, Formula right) => Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula SystemMemory() => Product(Fin(X("d")), Fin(X("r")));
    private static Formula Arrow(Formula input, Formula output) => new Formula.TypeArrow(input, output);
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Projection(Formula value, byte field) => Seq(Parenthesized(value), Dot, D(field));
    private static Formula For(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula FiniteCoordinates(Formula body) => For(Iota, TypeStar(),
        Inst(Call("Fintype", Iota), Inst(Call("DecidableEq", Iota), body)));
    private static Formula Dimensions(Formula body) => For(X("d"), Naturals(), For(X("r"), Naturals(), body));
    private static Formula SumOver(Formula name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(name, type)), Sp, Parenthesized(body));
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
