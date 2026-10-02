using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class RenyiOptimalStateDependenceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/abdelkhalek2015optimality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A qutrit basis projector is Pareto optimal for the Shannon dual pair (1,1), but ceases to be optimal for the dual pair (3/5,3). Thus the optimal states for two projective measurements can depend on their Renyi orders.",
        H("Optimal quantum states depend on the Renyi orders"),
        Blocks(
            Node("pX", "Standard-basis probabilities", PXFormula(),
                "The standard basis X gives the real diagonal entries of CStarMatrix.ofMatrix.symm(val(rho)); CStarMatrix.ofMatrix.symm is the inverse identity equivalence from CStarMatrix to Matrix, and val exposes the subtype value. Positivity and trace one make these a probability distribution. Indices run from 0 to d - 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pY", "Probabilities in the columns of the overlap matrix", PYFormula(),
                "The overlap matrix has entries U_ij = <x_i|y_j>. Thus Y is the column basis of U, and its probabilities are the real diagonal entries of U* CStarMatrix.ofMatrix.symm(val(rho)) U. The star denotes conjugate transpose and val(U) exposes the matrix of the bundled unitary.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("H", "Finite-order Renyi entropy", EntropyFormula(),
                "Section II, equation (6), p. 4 defines Renyi entropy by log(sum_i p_i^alpha)/(1-alpha) away from order one, and by the Shannon entropy at order one. Here shannonEntropy(p) = sum_i -p_i log(p_i) is the frozen finite Shannon entropy. All logarithms are natural: the paper states, verbatim, 'The logarithms can be taken in any base (as long as it is always the same base).' The explicit zero-mass branch implements 0^alpha = 0 for the positive orders in the conjecture. Orders are finite real numbers; infinity is outside this encoding.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Below", "Entropy-coordinate order", BelowFormula(),
                "Section II, p. 4: 'For any choice we can define the order relation ⊑ on the state space, so that ρ⊑ρ′ stands for “f₁(ρ)≤f₁(ρ′) and f₂(ρ)≤f₂(ρ′)”.' Here f(rho) = (H(alpha,pX(rho)), H(beta,pY(U,rho))); Below(U,alpha,beta,rho,sigma) encodes rho ⊑ sigma.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Optimal", "Pareto optimality over every density state", OptimalFormula(),
                "Section II, p. 4, verbatim: 'We call a state ρ optimal if ρ′⊑ρ implies ρ⊑ρ′, and hence f(ρ)=f(ρ′).' The quantified competitor sigma ranges over all complex density states in the same dimension, with the same U and entropy orders.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Independence conjecture", ClaimFormula(),
                "Conjecture V.8, section V.E, p. 21, '(Independence of the optimal states of (α,β))': 'If ρ is an optimal state for any unitary operator and any α,β>½ satisfying the duality relation (2), then ρ is also an optimal state for all other dual pairs.' The optimality definition is, verbatim (section II, p. 4): 'We call a state ρ optimal if ρ′⊑ρ implies ρ⊑ρ′, and hence f(ρ)=f(ρ′).' Encoding: d is a natural dimension, U is any complex unitary, rho is any density state, alpha and beta are the first finite dual pair, and alphaPrime and betaPrime are the second. Both pairs obey 1/alpha + 1/beta = 2 and every order exceeds 1/2. The source excludes the extremal pair {1/2,infinity}. Zero-based Fin(d) indices relabel its d basis outcomes.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A qutrit refutes order independence", Disp(new Formula.Not(F.Id("claim"))),
                "Use the real orthogonal overlap matrix with rows (sqrt(2)/2,sqrt(2)/2,0), (sqrt(2)/4,-sqrt(2)/4,sqrt(3)/2), and (sqrt(2)sqrt(3)/4,-sqrt(2)sqrt(3)/4,-1/2). The X basis projectors are OrthogonalRecordEntropy.pointerState specialized to Fin(3). The Y laws of these projectors are p0 = (1/2,1/2,0), p1 = (1/8,1/8,3/4), and p2 = (3/8,3/8,1/4). At orders (1,1), zero X entropy forces any dominating density state to be an X basis projector: the Shannon zero-entropy characterization forces a point mass, and positivity eliminates the off-diagonal entries. The Y entropies are log(2), (9/4)log(2)-(3/4)log(3), and (11/4)log(2)-(3/4)log(3); 27 < 32 makes the last two strictly larger than the first. Hence the first projector is optimal. At orders (3/5,3), the second projector has the same zero X entropy and Y entropy -(1/2)log(109/256) < log(2), since 1/4 < 109/256. It strictly dominates the first projector, so the latter is not optimal. Both pairs satisfy duality and have orders strictly above 1/2.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("renyi-optimal-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => name == "CStarMatrix.ofMatrix.symm"
        ? Seq(Operatorname, Grp(F.Id("CStarMatrix"), Dot, F.Id("ofMatrix"), Dot, F.Id("symm")))
        : Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula d) => Call("Fin", d);
    private static Formula DensityOf(Formula d) => Call("DensityState", FinOf(d));
    private static Formula UnitaryOf(Formula d) => Call("unitaryGroup", FinOf(d), Complexes);
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp,
            Parenthesized(yes), Sp, Named("else"), Sp, Parenthesized(no));
    private static Formula SumOver(Formula i, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(i, Colon, domain), Sp, Parenthesized(body));

    private static Formula PXFormula()
    {
        Formula d = F.Id("d"), rho = F.Id("rho"), i = F.Id("i");
        return Disp(All("d", Naturals, All("rho", DensityOf(d), All("i", FinOf(d),
            Equal(Call("pX", rho, i), Call("Re", Apply(Call("CStarMatrix.ofMatrix.symm", Call("val", rho)), i, i)))))));
    }

    private static Formula PYFormula()
    {
        Formula d = F.Id("d"), u = F.Id("U"), rho = F.Id("rho"), j = F.Id("j");
        Formula matrix = Parenthesized(Mul(Mul(Call("conjTranspose", Call("val", u)),
            Call("CStarMatrix.ofMatrix.symm", Call("val", rho))), Call("val", u)));
        return Disp(All("d", Naturals, All("U", UnitaryOf(d), All("rho", DensityOf(d),
            All("j", FinOf(d), Equal(Call("pY", u, rho, j), Call("Re", Apply(matrix, j, j))))))));
    }

    private static Formula EntropyFormula()
    {
        Formula d = F.Id("d"), alpha = F.Id("alpha"), p = F.Id("p"), i = F.Id("i");
        Formula pi = Apply(p, i);
        Formula powers = SumOver(i, FinOf(d), IfThenElse(Equal(pi, D(0)), D(0),
            new Formula.Power(Parenthesized(pi), alpha)));
        Formula value = IfThenElse(Equal(alpha, D(1)), Call("shannonEntropy", p),
            Fr(Call("log", powers), Sub(D(1), alpha)));
        return Disp(All("d", Naturals, All("alpha", Reals,
            All("p", new Formula.TypeArrow(FinOf(d), Reals), Equal(Call("H", alpha, p), value)))));
    }

    private static Formula BelowFormula()
    {
        Formula d = F.Id("d"), u = F.Id("U"), alpha = F.Id("alpha"), beta = F.Id("beta"),
            rho = F.Id("rho"), sigma = F.Id("sigma");
        Formula body = And(LeqTo(Call("H", alpha, Call("pX", rho)), Call("H", alpha, Call("pX", sigma))),
            LeqTo(Call("H", beta, Call("pY", u, rho)), Call("H", beta, Call("pY", u, sigma))));
        return Disp(All("d", Naturals, All("U", UnitaryOf(d), All("alpha", Reals,
            All("beta", Reals, All("rho", DensityOf(d), All("sigma", DensityOf(d),
                IffTo(Call("Below", u, alpha, beta, rho, sigma), body))))))));
    }

    private static Formula OptimalFormula()
    {
        Formula d = F.Id("d"), u = F.Id("U"), alpha = F.Id("alpha"), beta = F.Id("beta"),
            rho = F.Id("rho"), sigma = F.Id("sigma");
        Formula body = All("sigma", DensityOf(d), Imp(Call("Below", u, alpha, beta, sigma, rho),
            Call("Below", u, alpha, beta, rho, sigma)));
        return Disp(All("d", Naturals, All("U", UnitaryOf(d), All("alpha", Reals,
            All("beta", Reals, All("rho", DensityOf(d), IffTo(Call("Optimal", u, alpha, beta, rho), body)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), u = F.Id("U"), alpha = F.Id("alpha"), beta = F.Id("beta"),
            ap = F.Id("alphaPrime"), bp = F.Id("betaPrime"), rho = F.Id("rho");
        Formula body = All("rho", DensityOf(d), Imp(Call("Optimal", u, alpha, beta, rho),
            Call("Optimal", u, ap, bp, rho)));
        body = Imp(Equal(Add(Fr(D(1), ap), Fr(D(1), bp)), D(2)), body);
        body = Imp(Equal(Add(Fr(D(1), alpha), Fr(D(1), beta)), D(2)), body);
        foreach (Formula order in new[] { bp, ap, beta, alpha })
            body = Imp(Less(Fr(D(1), D(2)), order), body);
        body = All("d", Naturals, All("U", UnitaryOf(d), All("alpha", Reals,
            All("beta", Reals, All("alphaPrime", Reals, All("betaPrime", Reals, body))))));
        return Disp(IffTo(F.Id("claim"), body));
    }
}
