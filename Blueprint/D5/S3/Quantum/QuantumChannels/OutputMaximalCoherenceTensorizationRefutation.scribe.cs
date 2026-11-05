using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class OutputMaximalCoherenceTensorizationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/leebaekparkkimnha2022tensorizedresources");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A qubit Pauli channel has output maximal coherence 3/4, while two copies on a Bell input give maximal coherence 225/272, contradicting Conjecture 1 of Lee, Baek, Park, Kim and Nha.",
        H("Entangled inputs violate output maximal coherence tensorization"),
        Blocks(
            Paragraph(Text(
                "All matrices use a fixed basis; tensor products use the corresponding product basis. "
                    + "Matrix(b,a,C) denotes complex matrices with rows indexed by b and columns indexed by a. "
                    + "The superscript H denotes conjugate transpose, re denotes real part, and the norm of "
                    + "a complex entry is its modulus. Anonymous bracketed assumptions supply finite "
                    + "enumerations and decidable equality on the indicated index types.")),
            Node("maxcoherence", "Maximal coherence in a fixed basis", MaxCoherenceFormula(),
                "Equation (15) compares each off-diagonal modulus with the geometric mean of its diagonal "
                    + "populations. The displayed supremum includes zero and every ordered pair of indices. "
                    + "A pair contributes zero when its indices agree or its diagonal product is not positive. "
                    + "Thus a matrix with no supported off-diagonal pair has value zero, including the "
                    + "one-dimensional case. On a density matrix this is the maximal coherence of Eq. (15), "
                    + "with the zero convention made explicit.", "maxCoherence"),
            Node("krausapply", "The action of a finite Kraus family", KrausApplyFormula(),
                "A finite family K of matrices from a to b acts by the sum of K(r) R K(r)^H. "
                    + "This is MatrixMap.of_kraus K K applied to R, the Kraus representation of the "
                    + "completely positive maps considered in Section IV. No normalization is imposed "
                    + "by the action itself.", "krausApply"),
            Describe.Lean(
                DescribeId.Create("kraus-psd"),
                DeclarationHandle.Create(Prefix + "kraus_psd"),
                H("Kraus actions preserve positivity"),
                StatementSource.FromAuthor(Disp(KrausPsdFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite Kraus family sends positive semidefinite input matrices to positive semidefinite output matrices."))),
                DescribeRole.Theorem),
            Node("iskrauschannel", "Kraus normalization", KrausChannelFormula(),
                "The finite Kraus family represents a trace-preserving channel precisely when the sum "
                    + "of K(r)^H K(r) is the identity on a. Together with the Kraus action, this is the "
                    + "finite-dimensional completely positive trace-preserving channel setting of Section IV.",
                "IsKrausChannel"),
            Node("outputmaxcoherence", "Output maximal coherence", OutputFormula(),
                "Equation (28), specializing the output resource of Eq. (19), optimizes maximal coherence "
                    + "over all density inputs. The maximum is expressed as a real supremum. "
                    + "The density inputs are exactly the positive semidefinite complex matrices of trace one; "
                    + "the displayed set expands this condition. There is no restriction to product inputs "
                    + "when a is itself a product type, so entangled inputs are included. The definition "
                    + "is meaningful for any finite Kraus family, before imposing channel normalization.",
                "outputMaxCoherence"),
            Node("kraustensor", "Kraus operators of the product channel", KrausTensorFormula(),
                "A pair of Kraus families gives the family K(r) tensor L(s), indexed by the Cartesian "
                    + "product of their index types. The rows are indexed by b times d and the columns "
                    + "by a times c. These are the Kraus operators of the tensor product channel in Eq. (29). "
                    + "The family itself does not require finiteness or decidable equality assumptions.",
                "krausTensor"),
            Node("claim", "The proposed tensorization equality", ClaimFormula(),
                "Conjecture 1, Eq. (29), asserts that for every pair of finite-dimensional Kraus channels "
                    + "the output maximal coherence of their tensor product equals the larger of the two "
                    + "individual values. Input and output dimensions may differ. Every finite index type "
                    + "and every normalized Kraus family is quantified, and the product-channel supremum "
                    + "ranges over all density matrices in the product input space.", "claim"),
            Describe.Lean(
                DescribeId.Create("output-max-coherence-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A Pauli channel and a Bell input contradict the equality"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let I = [[1,0],[0,1]], X = [[0,1],[1,0]], "
                            + "Y = [[0,-i],[i,0]] and Z = [[1,0],[0,-1]], where i is the imaginary unit. "
                            + "Take the Pauli channel Phi(A) = (31/40) I A I + (1/10) X A X "
                            + "+ (1/10) Y A Y + (1/40) Z A Z. Its Kraus operators are "
                            + "sqrt(31/40) I, sqrt(1/10) X, sqrt(1/10) Y and sqrt(1/40) Z. "
                            + "The four probabilities are nonnegative and sum to one, and each Pauli "
                            + "matrix is a self-adjoint involution, so the Kraus normalization holds.")),
                    Paragraph(Text(
                        "For a density matrix R = [[a,z],[conj(z),1-a]], the output is "
                            + "[[1/5 + 3a/5,3z/4],[3conj(z)/4,4/5 - 3a/5]]. Its diagonal product "
                            + "is 4/25 + (9/25)a(1-a), exceeding a(1-a) by (4/25)(2a-1)^2. "
                            + "Positivity gives |z|^2 <= a(1-a), hence every such output has maximal "
                            + "coherence at most 3/4. At R = (1/2)[[1,1],[1,1]], the output is "
                            + "[[1/2,3/8],[3/8,1/2]], with maximal coherence 3/4, so the "
                            + "single-channel output supremum equals 3/4. The upper bound suffices "
                            + "for the contradiction.")),
                    Paragraph(Text(
                        "Use the Bell input (1/2)[[1,0,0,1],[0,0,0,0],[0,0,0,0],[1,0,0,1]], "
                            + "the density matrix of (|00> + |11>)/sqrt(2). In the ordered product "
                            + "basis (00,01,10,11), applying Phi tensor Phi gives "
                            + "[[17/50,0,0,9/32],[0,4/25,0,0],[0,0,4/25,0],[9/32,0,0,17/50]]. "
                            + "Its only nonzero off-diagonal entries are the two corners, each with "
                            + "normalized modulus (9/32)/(17/50) = 225/272. Thus the product-channel "
                            + "output supremum is at least 225/272, exceeding 3/4 by 21/272. "
                            + "This contradicts Eq. (29) for two copies of the same qubit channel."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lee-baek-park-kim-nha-2022-output-coherence-tensorization-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string prose, string declaration) => Describe.Lean(
            DescribeId.Create("output-max-coherence-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Types(string[] names, Formula body)
    {
        for (var index = names.Length - 1; index >= 0; index--)
            body = All(names[index], V("Type"), body);
        return body;
    }
    private static Formula Instance(string name, string type, Formula body) =>
        Seq(OpenBracket, Call(name, V(type)), CloseBracket, Sp, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Pair(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Mat(Formula rows, Formula columns) => Call("Matrix", rows, columns, Complexes());
    private static Formula Family(string index, string rows, string columns) =>
        new Formula.TypeArrow(V(index), Mat(V(rows), V(columns)));
    private static Formula Adjoint(Formula matrix) => new Formula.Power(Parenthesized(matrix), V("H"));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), type)), Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula condition) =>
        Seq(OpenBrace, Typed(V(name), type), Sp, Mid, Sp, condition, CloseBrace);
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp,
            Parenthesized(yes), Sp, Named("else"), Sp, Parenthesized(no));

    private static Formula MaxCoherenceFormula()
    {
        Formula n = V("n"), r = V("R"), p = V("p");
        Formula i = Seq(p, Dot, D(1)), j = Seq(p, Dot, D(2));
        Formula populations = Multiply(Call("re", At(r, i, i)), Call("re", At(r, j, j)));
        Formula condition = And(NotEqual(i, j), LT(D(0), populations));
        Formula ratio = new Formula.Fraction(new Formula.Norm(At(r, i, j)),
            Seq(Sqrt, Grp(populations)));
        Formula pairValue = Seq(LambdaLower, Sp, Typed(p, Pair(n, n)), Sp, Mapsto, Sp,
            Parenthesized(Conditional(condition, ratio, D(0))));
        Formula values = Call("insert", D(0), Call("range", pairValue));
        return Types(["n"], Instance("Fintype", "n", All("R", Mat(n, n),
            Equal(Call("maxCoherence", r), Call("sSup", values)))));
    }

    private static Formula ChannelBinders(Formula body, bool outputFinite) => Types(["a", "b", "k"],
        Instance("Fintype", "a", Instance("DecidableEq", "a",
            outputFinite ? Instance("Fintype", "b", Instance("Fintype", "k", body))
                : Instance("Fintype", "k", body))));

    private static Formula KrausApplyFormula()
    {
        Formula k = V("K"), r = V("R"), kr = At(k, V("r"));
        Formula action = SumOver("r", V("k"), Multiply(Multiply(kr, r), Adjoint(kr)));
        return ChannelBinders(All("K", Family("k", "b", "a"),
            All("R", Mat(V("a"), V("a")), Equal(Call("krausApply", k, r), action))), false);
    }

    private static Formula KrausChannelFormula()
    {
        Formula k = V("K"), kr = At(k, V("r"));
        Formula normalization = Equal(SumOver("r", V("k"), Multiply(Adjoint(kr), kr)), D(1));
        return ChannelBinders(All("K", Family("k", "b", "a"),
            IffOf(Call("IsKrausChannel", k), normalization)), true);
    }

    private static Formula KrausPsdFormula()
    {
        Formula positive = Call("PosSemidef", Call("krausApply", V("K"), V("R")));
        Formula body = All("K", Family("k", "b", "a"), All("R", Mat(V("a"), V("a")),
            Imp(Call("PosSemidef", V("R")), positive)));
        body = Instance("Fintype", "k", body);
        body = Instance("Finite", "b", body);
        body = Instance("DecidableEq", "a", body);
        body = Instance("Fintype", "a", body);
        return Types(["a", "b", "k"], body);
    }

    private static Formula OutputFormula()
    {
        Formula k = V("K"), r = V("R");
        Formula density = And(Call("PosSemidef", r), Equal(Call("trace", r), D(1)));
        Formula value = Equal(V("x"), Call("maxCoherence", Call("krausApply", k, r)));
        Formula values = SetOf("x", Reals(), Some("R", Mat(V("a"), V("a")), And(density, value)));
        return ChannelBinders(All("K", Family("k", "b", "a"),
            Equal(Call("outputMaxCoherence", k), Call("sSup", values))), true);
    }

    private static Formula KrausTensorFormula()
    {
        Formula p = V("p");
        Formula first = At(V("K"), Seq(p, Dot, D(1)));
        Formula second = At(V("L"), Seq(p, Dot, D(2)));
        Formula family = Seq(LambdaLower, Sp, Typed(p, Pair(V("k"), V("l"))), Sp, Mapsto, Sp,
            Call("kronecker", first, second));
        return Types(["a", "b", "c", "d", "k", "l"],
            All("K", Family("k", "b", "a"), All("L", Family("l", "d", "c"),
                Equal(Call("krausTensor", V("K"), V("L")), Parenthesized(family)))));
    }

    private static Formula ClaimFormula()
    {
        Formula k = V("K"), l = V("L");
        Formula equality = Equal(Call("outputMaxCoherence", Call("krausTensor", k, l)),
            Call("max", Call("outputMaxCoherence", k), Call("outputMaxCoherence", l)));
        Formula body = All("K", Family("k", "b", "a"), All("L", Family("l", "d", "c"),
            Imp(Call("IsKrausChannel", k), Imp(Call("IsKrausChannel", l), equality))));
        body = Instance("Fintype", "a", Instance("DecidableEq", "a", Instance("Fintype", "b",
            Instance("DecidableEq", "b", Instance("Fintype", "c", Instance("DecidableEq", "c",
                Instance("Fintype", "d", Instance("DecidableEq", "d", Instance("Fintype", "k",
                    Instance("Fintype", "l", body))))))))));
        return IffOf(Named("claim"), Types(["a", "b", "c", "d", "k", "l"], body));
    }
}
