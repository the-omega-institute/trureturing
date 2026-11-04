using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class RenyiCMILocalChannelRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/seshadreesan2015renyi");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete dephasing of A increases the Rényi conditional quantum mutual information of equation (3.18) for a faithful three-qubit state at alpha = 2.",
        H("Rényi CMI local-channel monotonicity"),
        Blocks(
            Node("mpow", "Real matrix powers", PowerFormula(),
                "Real powers use the continuous functional calculus on complex square matrices. Nonzero negative powers give generalized inverses on the support. Every matrix in the counterexample whose inverse power is used is positive definite.", DescribeRole.Definition),
            Node("margAE", "Marginal on AE", MarginalFormula("margAE", "ReorderBAE"),
                "The input carrier is (A times B) times E. ReorderBAE maps (b,(a,e)) to ((a,b),e), so partialTraceLeft traces B and retains AE.", DescribeRole.Definition),
            Node("margE", "Marginal on E", MarginalFormula("margE", null),
                "The frozen partialTraceLeft traces the whole AB factor and retains E.", DescribeRole.Definition),
            Node("traceA", "Partial trace over A", MarginalFormula("traceA", "ReorderABE"),
                "ReorderABE maps (a,(b,e)) to ((a,b),e). The partial trace then retains BE.", DescribeRole.Definition),
            Node("extAE", "Identity extension of AE", ExtensionAEFormula(),
                "At indices ((a,b),e), ((aPrime,bPrime),ePrime), the entry is S((a,e),(aPrime,ePrime)) if b = bPrime and zero otherwise. BIndex and AEIndex are the corresponding coordinate projections. This is the identity extension of S on B in the input index order.", DescribeRole.Definition),
            Node("extE", "Identity extension of E", ExtensionEFormula(),
                "The identity is on B; the output carrier is B times E.", DescribeRole.Definition),
            Node("renyiCMI", "Equation (3.18)", RenyiFormula(),
                "Section 3, equation (3.18), verbatim: Throughout this paper, we take our definition of Rényi conditional quantum mutual information for α ∈ (0, 1) ∪ (1, ∞) to be as follows [BSW15a, Definition 7]: The formula uses the AE and E marginals, their identity extensions, partial trace over A, real matrix powers and the real part of the final trace. The logarithm is natural.", DescribeRole.Definition),
            Node("applyA", "A finite Kraus channel acting on A", ChannelFormula(),
                "L_j = (K_j tensor 1_B) tensor 1_E. Each K_j maps A to APrime. The finite sum is a channel when sum_j K_j adjoint K_j = 1.", DescribeRole.Definition),
            Node("claim", "Conjecture 1", ClaimFormula(),
                "Section 3, verbatim: Some results in this paper rely on the following conjecture: Conjecture 1 The Rényi conditional quantum mutual information obeys monotonicity with respect to CPTP maps on system A, i.e., for ρABE ∈ S(HABE) and α ∈ (0, 1) ∪ (1, 2], Iα(A; B|E)ρ ≥ Iα(A′; B|E)τ, where τA′BE ≡ MA→A′(ρABE) and MA→A′ is a CPTP map acting on system A alone. Section 2, verbatim: it was left as an open question to determine if the property holds for local quantum operations on the other system (with numerical evidence supporting a positive answer). Here, we assume the latter to hold. The Lean claim quantifies over all natural dimensions and finite Kraus counts, a positive semidefinite trace-one state, a complete Kraus family and the stated alpha range.", DescribeRole.Definition),
            Node("result", "A faithful state refutes local monotonicity", Disp(new Formula.Not(F.Id("claim"))),
                "A, B and E are qubits and B is classical. The two AE blocks are M(13,8,7;13,39)/144 and M(7,8,13;39,13)/144, where M has corner entries p,q,q,s and middle diagonal entries u,v. Rational triangular conjugation certificates prove positivity and the trace is one. The Kraus matrices diagonal(1,0) and diagonal(0,1) completely dephase A. The input AE marginal is M(5,4,5;13,13)/36, whose positive square root is M(2,1,2;sqrt(13),sqrt(13))/6 and inverse square root is M(4,-2,4;6/sqrt(13),6/sqrt(13)). E is identity/2. The matrix under the last square root is diagonal(9,1,1,9)/64 before dephasing and diagonal(377,57,57,377)/2880 after it. The input square-root trace is one and the output trace is strictly greater than one. Thus the CMI goes from zero to a positive value, equivalently log((217+sqrt(21489))/360), contradicting the claim at alpha = 2.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("seshadreesan-berta-wilde-2015-renyi-cmi-local-channel"), ResolutionKind.Refuted,
                    additionalMembers: [
                        DeclarationHandle.Create("D5/S3/Quantum/Information/RenyiCMILowAlphaRefutation.result")
                    ]))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("renyi-cmi-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula),
            role == DescribeRole.Theorem ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name)
    {
        string[] words = name.Split('.');
        Formula[] items = new Formula[words.Length * 2 - 1];
        for (int i = 0; i < words.Length; i++)
        {
            items[2 * i] = F.Id(words[i]);
            if (i + 1 < words.Length) items[2 * i + 1] = Dot;
        }
        return Seq(Operatorname, Grp(items));
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id(name), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula MatrixOf(Formula n, Formula m) =>
        Call("Matrix", n, m, Seq(Mathbb, Grp(F.Id("C"))));
    private static Formula Finite(string name, Formula body) => All(name, Named("Type"),
        Seq(OpenBracket, Call("Fintype", F.Id(name)), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", F.Id(name)), CloseBracket, Sp, body));
    private static Formula InputIndex => Product(Product(F.Id("A"), F.Id("B")), F.Id("E"));
    private static Formula Systems(Formula body) => Finite("A", Finite("B", Finite("E", body)));
    private static Formula PowerFormula()
    {
        Formula n = F.Id("n"), x = F.Id("X"), p = F.Id("p");
        return Disp(Finite("n", All("X", MatrixOf(n, n), All("p", Reals,
            Equal(Call("mpow", x, p), Call("cfc",
                Lambda("t", Reals, new Formula.Power(F.Id("t"), p)), x))))));
    }
    private static Formula MarginalFormula(string name, string? reorder)
    {
        Formula rho = F.Id("rho");
        Formula matrix = reorder is null ? rho : Call("Matrix.submatrix", rho, Named(reorder), Named(reorder));
        return Disp(Systems(All("rho", MatrixOf(InputIndex, InputIndex),
            Equal(Call(name, rho), Call("partialTraceLeft", matrix)))));
    }
    private static Formula ExtensionAEFormula()
    {
        Formula ae = Product(F.Id("A"), F.Id("E")), x = F.Id("x"), y = F.Id("y");
        Formula value = Lambda("x", InputIndex, Lambda("y", InputIndex,
            Call("ite", Equal(Call("BIndex", x), Call("BIndex", y)),
                Call("S", Call("AEIndex", x), Call("AEIndex", y)), D(0))));
        return Disp(Systems(All("S", MatrixOf(ae, ae),
            Equal(Call("extAE", F.Id("A"), F.Id("B"), F.Id("E"), F.Id("S")), value))));
    }
    private static Formula ExtensionEFormula() => Disp(Finite("B", Finite("E",
        All("W", MatrixOf(F.Id("E"), F.Id("E")), Equal(
            Call("extE", F.Id("B"), F.Id("E"), F.Id("W")),
            Call("Matrix.kronecker", Call("Identity", F.Id("B")), F.Id("W")))))));
    private static Formula ChannelFormula()
    {
        Formula k = F.Id("K"), rho = F.Id("rho"), j = F.Id("j");
        Formula l = Call("Matrix.kronecker", Call("Matrix.kronecker", Seq(k, Sp, j),
            Call("Identity", F.Id("B"))), Call("Identity", F.Id("E")));
        Formula sum = Seq(Sum, Underscore, Grp(j), Sp, Mul(Mul(l, rho), Call("conjTranspose", l)));
        return Disp(Systems(Finite("APrime", All("r", Naturals,
            All("K", new Formula.TypeArrow(Call("Fin", F.Id("r")), MatrixOf(F.Id("APrime"), F.Id("A"))),
            All("rho", MatrixOf(InputIndex, InputIndex), Equal(Call("applyA", k, rho), sum)))))));
    }

    private static Formula RenyiFormula()
    {
        Formula alpha = F.Id("alpha"), rho = F.Id("rho");
        Formula q = Div(Sub(D(1), alpha), D(2));
        Formula s = Call("mpow", Call("extAE", Call("margAE", rho)), q);
        Formula w = Call("mpow", Call("extE", Call("margE", rho)), Div(Sub(alpha, D(1)), D(2)));
        Formula inner = Mul(Mul(w, Call("traceA", Mul(Mul(s, Call("mpow", rho, alpha)), s))), w);
        Formula value = Mul(Div(alpha, Sub(alpha, D(1))), Call("Real.log",
            Call("Complex.re", Call("Matrix.trace", Call("mpow", inner, Div(D(1), alpha))))));
        return Disp(Systems(All("alpha", Reals, All("rho", MatrixOf(InputIndex, InputIndex),
            Equal(Call("renyiCMI", alpha, rho), value)))));
    }

    private static Formula ClaimFormula()
    {
        Formula alpha = F.Id("alpha"), rho = F.Id("rho"), k = F.Id("K");
        Formula range = Or(And(Less(D(0), alpha), Less(alpha, D(1))), And(Less(D(1), alpha), LeqTo(alpha, D(2))));
        Formula complete = Equal(Seq(Sum, Underscore, Grp(F.Id("j")), Sp,
            Mul(Call("conjTranspose", Seq(k, Sp, F.Id("j"))), Seq(k, Sp, F.Id("j")))), D(1));
        Formula body = Imp(Call("Matrix.PosSemidef", rho), Imp(Equal(Call("Matrix.trace", rho), D(1)),
            Imp(complete, Imp(range, LeqTo(Call("renyiCMI", alpha, Call("applyA", k, rho)), Call("renyiCMI", alpha, rho))))));
        Formula a = Call("Fin", F.Id("dA")), ap = Call("Fin", F.Id("dAPrime")),
            b = Call("Fin", F.Id("dB")), e = Call("Fin", F.Id("dE"));
        Formula input = Product(Product(a, b), e);
        Formula matrix = Call("Matrix", input, input, Seq(Mathbb, Grp(F.Id("C"))));
        Formula kraus = new Formula.TypeArrow(Call("Fin", F.Id("r")),
            Call("Matrix", ap, a, Seq(Mathbb, Grp(F.Id("C")))));
        Formula quantified = All("dA", Naturals, All("dAPrime", Naturals, All("dB", Naturals,
            All("dE", Naturals, All("r", Naturals, All("rho", matrix,
            All("K", kraus, All("alpha", Reals, body))))))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(quantified)));
    }
}
