using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class ConcealmentKernelNecessityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/siddiquiwang2026concealment");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete dephasing and complete depolarization on a qubit conceal every pair of finite POVMs, although their adjoint kernels on Hermitian operators are different.",
        H("Concealment does not determine the adjoint kernel"),
        Blocks(
            Node("povm", "Finite POVMs", PovmFormula(), "IsPOVM",
                "For a finite outcome type Omega, a POVM consists of positive semidefinite complex d by d matrices whose sum is the identity. Zero effects are allowed. Positivity includes Hermitian symmetry."),
            Node("compatible", "Joint measurements", CompatibleFormula(), "Compatible",
                "Two POVMs with outcome types Omega and Lambda are compatible if a positive normalized family on Omega times Lambda has the two given marginal sums."),
            Node("concealed", "Operational concealment", ConcealedFormula(), "Concealed",
                "Let E map input matrices of dimension din to output matrices of dimension dout, and let T be a set of input density matrices. Concealment requires compatible output POVMs F and G with the same outcome types as M and N. Each simulated outcome has the same trace probability as the corresponding original outcome on E(rho), for every rho in T. For a Kraus family K the channel is E(rho)=sum over j of K(j) rho K(j) adjoint."),
            Node("tomographic", "Tomographic completeness", TomographicFormula(), "TomographicallyComplete",
                "Every member of T is positive semidefinite and has trace one. Its span over the real numbers equals the real vector space of Hermitian matrices. The set of all density matrices has this property: a Hermitian matrix is the difference of two positive semidefinite matrices; each nonzero positive semidefinite matrix is its positive real trace times a density matrix. A positive semidefinite matrix of trace zero is zero."),
            Node("kernel", "The Hermitian adjoint kernel", KernelFormula(), "AdjointKernel",
                "The trace dual is characterized by tr(E(X)A)=tr(X E adjoint(A)) for every input matrix X and output matrix A. Nondegeneracy and cyclicity of the trace pairing identify the dual of a finite Kraus map with the Heisenberg sum over j of K(j) adjoint A K(j). The kernel here consists only of Hermitian output operators."),
            Node("claim", "Kernel necessity for concealment equivalence", ClaimFormula(), "claim",
                "The assertion quantifies over all finite input and output dimensions, all finite Kraus index types kappa and eta, and all trace-preserving Kraus families K and L with those common dimensions. For every tomographically complete density set T, equality of concealment for every pair of finite outcome types and every pair of POVMs would imply equality of the two Hermitian adjoint kernels. The finite-type hypotheses specify the sums; the Kraus completeness equalities specify trace preservation."),
            Describe.Lean(DescribeId.Create("concealment-kernel-result"),
                DeclarationHandle.Create(Prefix + "result"), H("A qubit counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take din=dout=2 and T to be all density matrices. The complete dephasing channel D has Kraus operators |0><0| and |1><1|, so D(A)=diag(A00,A11). For arbitrary finite POVMs M and N, put F(a)=diag(M(a)00,M(a)11), G(b)=diag(N(b)00,N(b)11), and J(a,b)=diag(M(a)00 N(b)00,M(a)11 N(b)11). Positive semidefinite effects have nonnegative real diagonal entries. Thus J is positive; normalization of M and N gives normalization of J and both marginal identities. Diagonal outputs give identical trace probabilities for F and M, and for G and N.")),
                    Paragraph(Text("The complete depolarization channel R has Kraus operators I/2, X/2, Y/2, Z/2, where Y=iXZ and X,Z are the Pauli matrices. The Kraus completeness sum is I, and R(A)=tr(A)I/2. Put F(a)=tr(M(a))I/2, G(b)=tr(N(b))I/2, and J(a,b)=tr(M(a))tr(N(b))I/4. The traces are nonnegative real numbers and sum to two. These scalar effects and their joint family are positive, normalized, and have the stated marginals. Scalar outputs give the same outcome probabilities as the original effects.")),
                    Paragraph(Text("Both constructions hold for arbitrary finite outcome types, so both channels conceal every pair. Yet D adjoint(Z)=Z is nonzero, whereas R adjoint(Z)=0. Their concealment relations coincide and their Hermitian adjoint kernels differ. Each output range is commutative and allows a classical joint simulation; concealment therefore loses the distinction between these two kernels."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("siddiqui-wang-2026-concealment-kernel-necessity"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string declaration, string prose) =>
        Describe.Lean(DescribeId.Create("concealment-kernel-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Field(string name) => Seq(Mathbb, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Ex(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, body);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Mem(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Iff(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, Par(y));
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(Par(x), FormulaBinaryOperator.Multiply, Par(y));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Mat(Formula d) => Call("Matrix", Fin(d), Fin(d), Field("C"));
    private static Formula Rect(Formula dout, Formula din) =>
        Call("Matrix", Fin(dout), Fin(din), Field("C"));
    private static Formula Map(Formula din, Formula dout) =>
        Call("MatrixMap", Fin(din), Fin(dout), Field("C"));
    private static Formula Fun(Formula domain, Formula range) => new Formula.TypeArrow(domain, range);
    private static Formula Set(Formula type) => Call("Set", type);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula SumOver(string x, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(x), Sp, Colon, Sp, type), Sp, Par(body));
    private static Formula Finite(string x, Formula body) =>
        All(x, V("Type"), Seq(OpenBracket, Call("Fintype", V(x)), CloseBracket, Sp, body));
    private static Formula Measurements(Formula d, Formula body) =>
        Finite("Omega", Finite("Lambda",
            All("M", Fun(V("Omega"), Mat(d)), All("N", Fun(V("Lambda"), Mat(d)), body))));
    private static Formula Kraus(Formula k) => Call("ofKraus", k, k);
    private static Formula Trace(Formula a) => Call("tr", a);
    private static Formula Adjoint(Formula a) => Call("adjoint", a);
    private static Formula Probability(Formula m, Formula e, Formula rho) => Trace(Mul(m, At(e, rho)));
    private static Formula Normalized(Formula type, Formula k) =>
        Eq(SumOver("j", type, Mul(Adjoint(At(k, V("j"))), At(k, V("j")))), D(1));

    private static Formula PovmFormula()
    {
        Formula d = V("d"), omega = V("Omega"), m = V("M");
        return All("d", Field("N"), Finite("Omega", All("M", Fun(omega, Mat(d)),
            Iff(Call("IsPOVM", m), And(All("a", omega, Call("PosSemidef", At(m, V("a")))),
                Eq(SumOver("a", omega, At(m, V("a"))), D(1)))))));
    }

    private static Formula CompatibleFormula()
    {
        Formula d = V("d"), m = V("M"), n = V("N"), j = V("J");
        Formula marginals = And(All("a", V("Omega"),
            Eq(SumOver("b", V("Lambda"), At(j, Pair(V("a"), V("b")))), At(m, V("a")))),
            All("b", V("Lambda"),
                Eq(SumOver("a", V("Omega"), At(j, Pair(V("a"), V("b")))), At(n, V("b")))));
        return All("d", Field("N"), Measurements(d, Iff(Call("Compatible", m, n),
            And(Call("IsPOVM", m), And(Call("IsPOVM", n),
                Ex("J", Fun(Product(V("Omega"), V("Lambda")), Mat(d)),
                    And(Call("IsPOVM", j), marginals)))))));
    }

    private static Formula ConcealedFormula()
    {
        Formula din = V("din"), dout = V("dout"), e = V("E"), t = V("T");
        Formula rho = V("rho"), f = V("F"), g = V("G");
        Formula statistics = And(All("rho", Mat(din), Imp(Mem(rho, t),
            All("a", V("Omega"), Eq(Probability(At(f, V("a")), e, rho),
                Probability(At(V("M"), V("a")), e, rho))))),
            All("rho", Mat(din), Imp(Mem(rho, t),
                All("b", V("Lambda"), Eq(Probability(At(g, V("b")), e, rho),
                    Probability(At(V("N"), V("b")), e, rho))))));
        return All("din", Field("N"), All("dout", Field("N"), All("E", Map(din, dout),
            All("T", Set(Mat(din)), Measurements(dout,
                Iff(Call("Concealed", e, t, V("M"), V("N")),
                    Ex("F", Fun(V("Omega"), Mat(dout)), Ex("G", Fun(V("Lambda"), Mat(dout)),
                        And(Call("Compatible", f, g), statistics)))))))));
    }

    private static Formula TomographicFormula()
    {
        Formula d = V("d"), t = V("T"), rho = V("rho");
        return All("d", Field("N"), All("T", Set(Mat(d)),
            Iff(Call("TomographicallyComplete", t),
                And(All("rho", Mat(d), Imp(Mem(rho, t),
                    And(Call("PosSemidef", rho), Eq(Trace(rho), D(1))))),
                    Eq(Call("span", Field("R"), t), Call("HermitianSpace", d))))));
    }

    private static Formula KernelFormula()
    {
        Formula din = V("din"), dout = V("dout"), e = V("E"), a = V("A");
        return All("din", Field("N"), All("dout", Field("N"), All("E", Map(din, dout),
            All("A", Mat(dout), Iff(Mem(a, Call("AdjointKernel", e)),
                And(Call("IsHermitian", a), Eq(At(Call("dual", e), a), D(0))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula din = V("din"), dout = V("dout"), k = V("K"), l = V("L"), t = V("T");
        Formula equivalence = Measurements(dout,
            Imp(Call("IsPOVM", V("M")), Imp(Call("IsPOVM", V("N")),
                Iff(Call("Concealed", Kraus(k), t, V("M"), V("N")),
                    Call("Concealed", Kraus(l), t, V("M"), V("N"))))));
        Formula body = All("din", Field("N"), All("dout", Field("N"),
            Finite("kappa", Finite("eta", All("K", Fun(V("kappa"), Rect(dout, din)),
                All("L", Fun(V("eta"), Rect(dout, din)),
                    Imp(Normalized(V("kappa"), k), Imp(Normalized(V("eta"), l),
                        All("T", Set(Mat(din)), Imp(Call("TomographicallyComplete", t),
                            Imp(equivalence, Eq(Call("AdjointKernel", Kraus(k)),
                                Call("AdjointKernel", Kraus(l))))))))))))));
        return Iff(V("claim"), body);
    }
}
