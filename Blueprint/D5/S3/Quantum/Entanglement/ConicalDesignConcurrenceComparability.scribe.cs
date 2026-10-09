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
                    ResolutionKind.Proved))),
        []));

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
