using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class ConicalDesignConcurrenceComparabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.";
    private static readonly LibraryNoteRef Wzcf = LibraryNoteRef.Create("D5/L/QuantumStates/wangzhouchenfei2026conical");
    private static readonly LibraryNoteRef Siudzinska = LibraryNoteRef.Create("D5/L/QuantumStates/siudzinska2025twoconstants");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conical two-design concurrence bounds have a uniform ratio ordering.",
        H("Comparability of conical-design concurrence bounds"),
        Blocks(
            Node("traceNorm_smul_nonneg", "Nonnegative homogeneity of the trace norm", TraceNormSmulFormula(),
                "Multiplication of a complex matrix by a nonnegative real scalar multiplies its trace norm by the same scalar. This includes zero and allows convex trace-norm estimates to pass from pure states to mixtures.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("traceNorm_isometry", "Rectangular isometries preserve the trace norm", TraceNormIsometryFormula(),
                "For finite index types M and N, a complex rectangular matrix V with adjoint times V equal to the identity preserves the trace norm under X mapped to V X V adjoint. The square matrix X is arbitrary. This invariance is used in the normal form of the concurrence bound and in the projection dilation.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("swap", "The literal tensor swap", SwapFormula(),
                "The flip F in Siudzinska's Section 2, Eq. (9), p. 2, sends the computational-basis pair (a,b) to (b,a). The identity matrix is reindexed in its columns by Prod.swap, so its (p,q) entry is 1 exactly when p=(q.2,q.1). Scalars are complex.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Siudzinska)),
            Node("Design", "A finite conical two-design", DesignFormula(),
                @"Section 2, Eq. (9), p. 2: ""By definition, `\mathcal{P}` is a conical 2-design if"" the displayed identity is `\sum_{\alpha=1}^N\sum_{k=1}^{M_\alpha}P_{\alpha,k}\otimes P_{\alpha,k}=\kappa_+I_d\otimes I_d+\kappa_-F_d`, ""where `\kappa_+\geq\kappa_->0`"". The constructor below lists all data and proof fields: the positive effects, real alpha and beta, positivity of beta, beta at most alpha, and the tensor identity. Measurement labels are flattened to Fin m. No POVM normalization or fixed number of outcomes is added. The complex casts of alpha and beta are explicit.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Siudzinska)),
            Node("P_E", "The measurement correlation matrix", CorrelationFormula(),
                @"Section 6, Eq. (59), p. 9: ""The elements of `\mathcal{B}(\rho)` in the basis of `\omega_{\alpha,k}` form the correlation matrix `\mathcal{B}_{\alpha,k;\beta,\ell}=\operatorname{Tr}[\rho(P_{\alpha,k}\otimes P_{\beta,\ell})]`."" P_E is this complex square matrix, with flattened labels and the same design on both tensor factors. Its input is any bipartite complex matrix; the final claim restricts it to density states. Theorem 6 refers to Eq. (60); the defining operator expression is Eq. (59).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Siudzinska)),
            Node("c", "The dimension factor", CoefficientFormula(),
                @"Section 7, Theorem 6, Eq. (74), p. 10: `\eta=\frac{1}{S}\sqrt{\frac{2}{d(d-1)}},\qquad\xi=\mathcal{C}_{\max}`. The factor c isolates the square root. Both appearances of d are real casts, and the division is real division. The final comparison assumes d at least 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Siudzinska)),
            Node("B_E", "The concurrence lower bound", BoundFormula(),
                @"Section 7, Theorem 6, Eq. (73), p. 10: ""The concurrence of a mixed bipartite state `\rho` is lower bounded by"" `\mathcal{N}_{\min}(\rho)=\eta\Big[\|\mathcal{B}(\rho)\|_{\tr}-\xi\Big]`. Here S=beta and C_max=alpha+beta. The frozen traceNorm is the real trace of the positive square root of X.conjTranspose times X, equivalently the sum of singular values. The expression is not truncated at zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Siudzinska)),
            Node("claim", "The Wang–Zhou–Chen–Fei conjecture", ClaimFormula(),
                "Section IV, p. 8, after Theorem 2, verbatim: \"The lower bounds of concurrence induced by arbitrary two distinct conical 2-designs are comparable.\" For each d at least 2 and each pair of finite designs, one ordering holds for every bipartite state. DensityState is the canonical positive semidefinite trace-one CStarMatrix; CStarMatrix.ofMatrix.symm takes its underlying Matrix. Equal designs are also included. The state quantifier lies inside each branch, so the choice of ordering is independent of the state.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Wzcf)),
            Node("result", "Uniform comparison by the ratio alpha over beta", Disp(F.Id("claim")),
                "Vectorize each effect as A_ip=(E_i)_(p.2,p.1). The tensor identity gives A.conjTranspose times A=beta I+alpha vv.conjTranspose, where v=Matrix.vec I. With Q=vv.conjTranspose/d and t=sqrt(1+d alpha/beta), a rectangular isometry factors A as sqrt(beta) U (I+(t-1)Q). The trace norm is unchanged by that isometry, so the bound depends only on t. For s at most t, the projection dilation gives a trace-norm gain of at least (t squared minus s squared)/d, cancelling the change of the offset. Consequently alpha_E/beta_E at least alpha_G/beta_G gives B_E at least B_G for every state. Equal ratios give equal bounds. The total order on real ratios proves claim.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Wzcf),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wang-zhou-chen-fei-2026-conical-design-concurrence-comparability"),
                    ResolutionKind.Proved)),
            PhysicalApplication()),
        []));

    private static DocumentBlock PhysicalApplication()
    {
        Formula l = LambdaLower, t = F.Id("t"), x = F.Id("X"), a = F.Id("A"), h = F.Id("H");
        Formula phi = new Formula.Subscript(Phi, D(2));
        Formula rho = new Formula.Subscript(Rho, Star);
        Formula mt = new Formula.Subscript(F.Id("M"), t);
        Formula bound = Call("B_E", Call("E", l), rho);
        Formula answer = new Formula.Fraction(Sub(Mul(t, Root(Add(Square(t), D(1)))), Square(t)), D(2));
        Formula q = F.Id("Q"), i2 = new Formula.Subscript(F.Id("I"), D(2)), i4 = new Formula.Subscript(F.Id("I"), D(4));
        return new DocumentBlock.Section(H("A physical six-effect family with a strict comparison"), Blocks(
            Paragraph(Text("This analytical application uses the existing bound_normal_form and ratio ordering in this module. "
                + "The physical realization and singular-value calculation below are mathematical exposition, not additional kernel-checked declarations. "
                + "The cited Wang–Zhou–Chen–Fei and Siudzinska sources supply the conjecture and bound conventions; no priority claim for this example is made.")),
            new DocumentBlock.Section(H("Six complex effects and their design constants"), Blocks(
                Paragraph(Text("Work on the complex two-qubit space, in computational order 00, 01, 10, 11. "
                    + "For every real parameter in the following interval, take both signs for each of the three ordinary Pauli matrices (i denotes the complex imaginary unit):")),
                Display(Seq(D(0), F.Lt, l, Leq, new Formula.Fraction(D(1), Root(D(2))))),
                Display(Seq(new Formula.Subscript(SigmaLower, F.Id("x")), Eq,
                    SmallMatrix([D(0), D(1)], [D(1), D(0)]), Comma, Quad, Sp,
                    new Formula.Subscript(SigmaLower, F.Id("y")), Eq,
                    SmallMatrix([D(0), new Formula.Negate(F.Id("i"))], [F.Id("i"), D(0)]), Comma, Quad, Sp,
                    new Formula.Subscript(SigmaLower, F.Id("z")), Eq,
                    SmallMatrix([D(1), D(0)], [D(0), new Formula.Negate(D(1))]))),
                Display(Seq(new Formula.Apply(new Formula.Subscript(F.Id("E"), Seq(F.Id("k"), Comma, Pm)), [l]), Eq,
                    new Formula.Fraction(i2, D(2)), Pm, new Formula.Fraction(l, Root(D(2))),
                    new Formula.Subscript(SigmaLower, F.Id("k")), Comma, Quad, Sp,
                    F.Id("k"), InMacro, OpenBrace, F.Id("x"), Comma, F.Id("y"), Comma, F.Id("z"), CloseBrace)),
                Paragraph(Text("Each Pauli matrix is Hermitian with eigenvalues +1 and -1, so every effect has eigenvalues "),
                    Math(Seq(Rational(1, 2), Pm, new Formula.Fraction(l, Root(D(2))))),
                    Text(". They lie between zero and one on the whole interval. Every effect has trace one and is nonzero. "
                        + "At the included upper endpoint its eigenvalues are zero and one, so it is rank one; positive definiteness is not required. "
                        + "Each plus/minus pair sums to the identity. The six effects sum to three times the identity: they are three binary POVMs, "
                        + "not one globally normalized six-outcome POVM, and no rescaling is applied.")),
                Paragraph(Text("Suppress the common argument lambda in the effects below. The cross terms cancel within each pair, giving")),
                Display(Seq(new Formula.Subscript(Sum, Seq(F.Id("s"), Eq, Pm)),
                    Tensor(new Formula.Subscript(F.Id("E"), Seq(F.Id("k"), Comma, F.Id("s"))),
                        new Formula.Subscript(F.Id("E"), Seq(F.Id("k"), Comma, F.Id("s")))), Eq,
                    new Formula.Fraction(i4, D(2)), Plus, Square(l),
                    Tensor(new Formula.Subscript(SigmaLower, F.Id("k")), new Formula.Subscript(SigmaLower, F.Id("k"))))),
                Paragraph(Text("Here kronecker denotes the tensor product. For the literal tensor swap F, entrywise evaluation of the displayed Pauli matrices gives the first identity below, and summing the three pair identities gives the second:")),
                Display(Seq(new Formula.Subscript(Sum, F.Id("k")), Tensor(new Formula.Subscript(SigmaLower, F.Id("k")),
                        new Formula.Subscript(SigmaLower, F.Id("k"))), Eq, D(2), F.Id("F"), Minus, i4)),
                Display(Seq(new Formula.Subscript(Sum, Seq(F.Id("k"), Comma, F.Id("s"))),
                    Tensor(new Formula.Subscript(F.Id("E"), Seq(F.Id("k"), Comma, F.Id("s"))),
                        new Formula.Subscript(F.Id("E"), Seq(F.Id("k"), Comma, F.Id("s")))), Eq,
                    Parenthesized(Sub(Rational(3, 2), Square(l))), i4, Plus, D(2), Square(l), F.Id("F"))),
                Display(Seq(Alpha, Eq, Sub(Rational(3, 2), Square(l)), Comma, Quad, Sp,
                    Beta, Eq, D(2), Square(l), Comma, Quad, Sp,
                    Alpha, Minus, Beta, Eq, D(3), Parenthesized(Sub(Rational(1, 2), Square(l))), Geq, D(0))),
                Paragraph(Text("Thus alpha is at least beta and beta is strictly positive, exactly as required by Design. "
                    + "The value lambda = 0 is excluded: it would give beta = 0 and leave the bound undefined.")))),
            new DocumentBlock.Section(H("A mixed density state and the same-design convention"), Blocks(
                Display(Seq(phi, Eq, new Formula.Fraction(Add(Ket(D(0, 0)), Ket(D(1, 1))), Root(D(2))), Comma, Quad, Sp,
                    rho, Eq, Rational(1, 2), Projector(phi), Plus, Rational(1, 2), Projector(D(0, 1)))),
                Paragraph(Text("Both displayed vectors have norm one and are orthogonal. Each projector is positive semidefinite with trace one; "
                    + "their equal mixture is therefore positive semidefinite with trace one and has rank two. It is an actual mixed density state. "
                    + "Use the six effects in the order x+, x-, y+, y-, z+, z- on both subsystems. In particular, the second effect is not complex-conjugated, "
                    + "which matters for the imaginary entries of the y Pauli matrix:")),
                Display(Seq(new Formula.Subscript(Call("P_E", rho), Seq(F.Id("i"), Comma, F.Id("j"))), Eq,
                    Call("tr", Mul(rho, Tensor(new Formula.Subscript(F.Id("E"), F.Id("i")),
                        new Formula.Subscript(F.Id("E"), F.Id("j"))))))),
                Paragraph(Text("The trace norm is the sum of singular values. For this dimension c(2) = 1, and the untruncated bound is")),
                Display(Eqn(bound, new Formula.Fraction(Sub(Sub(NormOne(Call("P_E", rho)), Alpha), Beta), Beta))),
                Paragraph(Text("Apply the owner's realignedFlip convention, "),
                    Math(Seq(new Formula.Subscript(x, Seq(Parenthesized(Seq(F.Id("a"), Comma, F.Id("b"))), Comma,
                        Parenthesized(Seq(F.Id("c"), Comma, F.Id("e"))))), Eq,
                        new Formula.Subscript(rho, Seq(Parenthesized(Seq(F.Id("a"), Comma, F.Id("e"))), Comma,
                            Parenthesized(Seq(F.Id("b"), Comma, F.Id("c"))))))),
                    Text(". In computational order this gives")),
                Display(Seq(rho, Eq, SmallMatrix(
                    [Rational(1, 4), D(0), D(0), Rational(1, 4)],
                    [D(0), Rational(1, 2), D(0), D(0)], [D(0), D(0), D(0), D(0)],
                    [Rational(1, 4), D(0), D(0), Rational(1, 4)]), Comma, Quad, Sp,
                    x, Eq, SmallMatrix([Rational(1, 4), D(0), D(0), Rational(1, 2)],
                        [D(0), D(0), Rational(1, 4), D(0)], [D(0), Rational(1, 4), D(0), D(0)],
                        [D(0), D(0), D(0), Rational(1, 4)]))))),
            new DocumentBlock.Section(H("The entire parameter interval in the normal form"), Blocks(
                Paragraph(Text("The owner's Q(2) is the projector onto the maximally entangled vector above. Set")),
                Display(Seq(q, Eq, Projector(phi), Comma, Quad, Sp, mt, Eq,
                    i4, Plus, Parenthesized(Sub(t, D(1))), q, Comma, Quad, Sp,
                    t, Eq, Root(Add(D(1), new Formula.Fraction(Mul(D(2), Alpha), Beta))), Eq,
                    Root(new Formula.Fraction(D(3), Mul(D(2), Square(l)))), Geq, Root(D(3)))),
                Paragraph(Text("Use the orthonormal basis consisting, in order, of "), Math(phi),
                    Text(", "), Math(new Formula.Fraction(Sub(Ket(D(0, 0)), Ket(D(1, 1))), Root(D(2)))),
                    Text(", |01>, and |10>. The last two coordinates do not couple to the first two, and M_t acts as diag(t,1,1,1). "
                        + "Consequently the transformed matrix has the following two diagonal blocks:")),
                Display(Seq(mt, x, mt, Eq, SmallMatrix(
                    [new Formula.Fraction(Square(t), D(2)), new Formula.Negate(new Formula.Fraction(t, D(4))), D(0), D(0)],
                    [new Formula.Fraction(t, D(4)), D(0), D(0), D(0)],
                    [D(0), D(0), D(0), Rational(1, 4)], [D(0), D(0), Rational(1, 4), D(0)]))),
                Display(Seq(a, Eq, SmallMatrix([new Formula.Fraction(Square(t), D(2)), new Formula.Negate(new Formula.Fraction(t, D(4)))],
                    [new Formula.Fraction(t, D(4)), D(0)]), Comma, Quad, Sp,
                    h, Eq, SmallMatrix([D(0), Rational(1, 4)], [Rational(1, 4), D(0)]))),
                Paragraph(Text("The off-diagonal signs in A are opposite. This block is not Hermitian, so its eigenvalues cannot be substituted for singular values. "
                    + "For the two singular values s1 and s2 of any complex 2-by-2 matrix A, the sum of their squares is tr(A* A) and their product is |det A|. Hence")),
                Display(Seq(Square(Parenthesized(Add(new Formula.Subscript(F.Id("s"), D(1)), new Formula.Subscript(F.Id("s"), D(2))))), Eq,
                    Call("tr", Mul(new Formula.Power(a, Star), a)), Plus, D(2), new Formula.Absolute(Call("det", a)))),
                Display(Seq(Call("tr", Mul(new Formula.Power(a, Star), a)), Eq,
                    new Formula.Fraction(new Formula.Power(t, D(4)), D(4)), Plus,
                    new Formula.Fraction(Square(t), D(8)), Comma, Quad, Sp,
                    Call("det", a), Eq, new Formula.Fraction(Square(t), new Formula.Number(16)))),
                Paragraph(Text("Since t is positive, taking the nonnegative square root yields the first block's trace norm. "
                    + "The second block has two singular values equal to one quarter. Unitary invariance for the basis change and additivity over the two blocks give")),
                Display(Seq(NormOne(a), Eq, new Formula.Fraction(Mul(t, Root(Add(Square(t), D(1)))), D(2)), Comma, Quad, Sp,
                    NormOne(h), Eq, Rational(1, 2))),
                Display(Seq(NormOne(Mul(Mul(mt, x), mt)), Eq,
                    new Formula.Fraction(Add(Mul(t, Root(Add(Square(t), D(1)))), D(1)), D(2)))),
                Paragraph(Text("The existing bound_normal_form subtracts (t squared minus one)/2 and then one. "
                    + "Equivalently its offset is (t squared plus one)/2. Therefore the exact formulas throughout the stated interval are")),
                Display(Seq(NormOne(Call("P_E", rho)), Eq,
                    Beta, new Formula.Fraction(Add(Mul(t, Root(Add(Square(t), D(1)))), D(1)), D(2)))),
                Display(Seq(bound, Eq, NormOne(Mul(Mul(mt, x), mt)), Minus,
                    new Formula.Fraction(Add(Square(t), D(1)), D(2)), Eq, answer)))),
            new DocumentBlock.Section(H("Positive bounds with an exact strict comparison"), Blocks(
                Paragraph(Text("For every allowed parameter, t is positive and sqrt(t squared plus one) is strictly larger than t. "
                    + "The displayed bound is thus strictly positive on the entire interval. At the included upper endpoint and at a second interior parameter it becomes")),
                Display(Seq(l, Eq, new Formula.Fraction(D(1), Root(D(2))), Colon, Quad, Sp,
                    Alpha, Eq, Beta, Eq, D(1), Comma, Quad, Sp,
                    new Formula.Fraction(Alpha, Beta), Eq, D(1), Comma, Quad, Sp,
                    t, Eq, Root(D(3)), Comma, Quad, Sp, bound, Eq, Sub(Root(D(3)), Rational(3, 2)), F.Gt, D(0))),
                Display(Seq(l, Eq, new Formula.Fraction(D(1), Root(D(6))), Colon, Quad, Sp,
                    Alpha, Eq, Rational(4, 3), Comma, Quad, Sp, Beta, Eq, Rational(1, 3), Comma, Quad, Sp,
                    new Formula.Fraction(Alpha, Beta), Eq, D(4), Comma, Quad, Sp, t, Eq, D(3), Comma, Quad, Sp,
                    bound, Eq, new Formula.Fraction(Sub(Mul(D(3), Root(new Formula.Number(10))), D(9)), D(2)))),
                Paragraph(Text("The strict comparison reduces to 3 sqrt(10) > 6 + 2 sqrt(3). "
                    + "Both sides are positive, so squaring preserves and reflects the inequality: it becomes 42 > 24 sqrt(3), "
                    + "or 7 > 4 sqrt(3). Squaring these positive quantities gives 49 > 48. Thus")),
                Display(Seq(new Formula.Fraction(Sub(Mul(D(3), Root(new Formula.Number(10))), D(9)), D(2)), F.Gt,
                    Sub(Root(D(3)), Rational(3, 2)), F.Gt, D(0))),
                Paragraph(Text("Because both bounds are positive, replacing each B by max(0,B) preserves this strict improvement for the same mixed state. "
                    + "This example does not settle strictness for every distinct ratio pair or identify concurrence for arbitrary states. "
                    + "The arbitrary pure-state formula and mixed-state convex-roof obligations are separate from this application."))))));
    }

    private static DocumentBlock Display(Formula value) => new DocumentBlock.DisplayFormula(Disp(value));
    private static Formula Tensor(Formula left, Formula right) => Call("kronecker", left, right);
    private static Formula Rational(long numerator, long denominator) =>
        new Formula.Fraction(new Formula.Number(numerator), new Formula.Number(denominator));
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Ket(Formula value) => Seq(Bar, value, Rangle);
    private static Formula Projector(Formula value) => Seq(Ket(value), Langle, value, Bar);
    private static Formula NormOne(Formula value) => new Formula.Subscript(new Formula.Norm(value), D(1));
    private static Formula SmallMatrix(params Formula[][] rows)
    {
        var entries = new System.Collections.Generic.List<Formula> { Begin, Grp(F.Id("bmatrix")) };
        for (var r = 0; r < rows.Length; r++)
        {
            if (r > 0) entries.Add(RowBreak);
            for (var c = 0; c < rows[r].Length; c++)
            {
                if (c > 0) entries.Add(Amp);
                entries.Add(rows[r][c]);
            }
        }
        entries.Add(End);
        entries.Add(Grp(F.Id("bmatrix")));
        return Seq([.. entries]);
    }

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("wzcf-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] args) => name is "P_E" or "B_E"
        ? new Formula.Apply(new Formula.Subscript(F.Id(name == "P_E" ? "P" : "B"), F.Id("E")), [.. args])
        : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args)
    {
        Formula function = Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
        return args.Length == 0 ? function : new Formula.Apply(function, [.. args]);
    }
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Sp, Colon, Sp, type));
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Pairs(Formula d) => Parenthesized(Seq(Fin(d), Sp, F.Times, Sp, Fin(d)));
    private static Formula MatrixType(Formula i) => Call("Matrix", i, i, ComplexType());
    private static Formula Field(Formula x, string name) => Seq(x, Dot, name == "1" ? D(1) : F.Id(name));
    private static Formula Dim(Formula body) => All("d", NatType(), body);
    private static Formula DesignInputs(Formula body) => Dim(All("m", NatType(), All("E", Call("Design", F.Id("d"), F.Id("m")), body)));
    private static Formula MatrixInputs(Formula body) => DesignInputs(All("rho", MatrixType(Pairs(F.Id("d"))), body));
    private static Formula SumOver(Formula i, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, type)), Sp, body);

    private static Formula TraceNormSmulFormula()
    {
        Formula n = F.Id("n"), x = F.Id("X"), c = F.Id("c");
        Formula instances = Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", n), CloseBracket, Sp);
        return Disp(All("n", Seq(F.Id("Type"), Star), Seq(instances,
            All("X", MatrixType(n), All("c", RealType(), Imp(Le(D(0), c),
                Eqn(Call("traceNorm", Call("smul", Cast(c, ComplexType()), x)),
                    Mul(c, Call("traceNorm", x)))))))));
    }

    private static Formula TraceNormIsometryFormula()
    {
        Formula m = F.Id("M"), n = F.Id("N"), v = F.Id("V"), x = F.Id("X");
        Formula adjoint = Qualified("Matrix", "conjTranspose", v);
        Formula matrix = Call("Matrix", m, n, ComplexType());
        Formula identity = Cast(D(1), MatrixType(n));
        Formula type = Seq(F.Id("Type"), Star);
        Formula instances = Seq(
            OpenBracket, Call("Fintype", m), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", m), CloseBracket, Sp,
            OpenBracket, Call("Fintype", n), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", n), CloseBracket, Comma, Sp);
        return Disp(All("M", type, All("N", type, Seq(instances,
            All("V", matrix, Imp(Eqn(Mul(adjoint, v), identity),
                All("X", MatrixType(n), Eqn(Call("traceNorm", Mul(Mul(v, x), adjoint)),
                    Call("traceNorm", x)))))))));
    }

    private static Formula SwapFormula()
    {
        Formula d = F.Id("d");
        return Disp(Dim(Eqn(Call("swap", d), Qualified("Matrix", "submatrix",
            Cast(D(1), MatrixType(Pairs(d))), F.Id("id"), Qualified("Prod", "swap")))));
    }

    private static Formula DesignFormula()
    {
        Formula d = F.Id("d"), m = F.Id("m"), effects = F.Id("E"), alpha = F.Id("alpha"), beta = F.Id("beta"), i = F.Id("i");
        Formula effectType = Parenthesized(Seq(Fin(m), Sp, To, Sp, MatrixType(Fin(d))));
        Formula positiveType = All("i", Fin(m), Seq(Parenthesized(Apply(effects, i)), Dot, F.Id("PosSemidef")));
        Formula identity = Eqn(SumOver(i, Fin(m), Qualified("Matrix", "kronecker", Apply(effects, i), Apply(effects, i))),
            Add(Mul(Cast(alpha, ComplexType()), Cast(D(1), MatrixType(Pairs(d)))), Mul(Cast(beta, ComplexType()), Call("swap", d))));
        Formula constructor = Cast(Qualified("Design", "mk", effects, alpha, beta, F.Id("positive"), F.Id("betaPos"), F.Id("betaLeAlpha"), F.Id("tensorIdentity")), Call("Design", d, m));
        return Disp(Dim(All("m", NatType(), All("E", effectType, All("alpha", RealType(), All("beta", RealType(),
            All("positive", Parenthesized(positiveType), All("betaPos", Lt(D(0), beta),
                All("betaLeAlpha", Le(beta, alpha), All("tensorIdentity", Parenthesized(identity), constructor))))))))));
    }

    private static Formula CorrelationFormula()
    {
        Formula e = F.Id("E"), rho = F.Id("rho"), i = F.Id("i"), j = F.Id("j");
        Formula effect = Field(e, "E");
        Formula value = Qualified("Matrix", "trace",
            Mul(rho, Qualified("Matrix", "kronecker", Apply(effect, i), Apply(effect, j))));
        Formula equation = Eqn(Apply(Call("P_E", e, rho), i, j), value);
        return Disp(MatrixInputs(All("i", Fin(F.Id("m")), All("j", Fin(F.Id("m")), equation))));
    }

    private static Formula CoefficientFormula()
    {
        Formula d = F.Id("d"), realD = Cast(d, RealType());
        return Disp(Dim(Eqn(Call("c", d), Qualified("Real", "sqrt",
            new Formula.Fraction(D(2), Mul(realD, Parenthesized(Sub(realD, D(1)))))))));
    }

    private static Formula BoundFormula()
    {
        Formula e = F.Id("E"), rho = F.Id("rho");
        Formula excess = Sub(Sub(Call("traceNorm", Call("P_E", e, rho)), Field(e, "alpha")), Field(e, "beta"));
        return Disp(MatrixInputs(Eqn(Call("B_E", e, rho), new Formula.Fraction(
            Mul(Call("c", F.Id("d")), Parenthesized(excess)), Field(e, "beta")))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), e = F.Id("E"), g = F.Id("G"), rho = F.Id("rho");
        Formula matrix = Apply(Seq(Qualified("CStarMatrix", "ofMatrix"), Dot, F.Id("symm")), Field(rho, "1"));
        Formula states = Call("DensityState", Pairs(d));
        Formula order = new Formula.Logic(Parenthesized(All("rho", states, Le(Call("B_E", g, matrix), Call("B_E", e, matrix)))),
            FormulaLogicOperator.Or, Parenthesized(All("rho", states, Le(Call("B_E", e, matrix), Call("B_E", g, matrix)))));
        Formula body = Dim(Imp(Le(D(2), d), All("m", NatType(), All("n", NatType(),
            All("E", Call("Design", d, F.Id("m")), All("G", Call("Design", d, F.Id("n")), order))))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(body)));
    }
}
