using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class OriginalDataQuantitativeDetectorRankHorizonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Short-time density observations bound the spectral tail of an effect under an arbitrary complex subunital completely positive map.",
        H("A quantitative detector-rank horizon"),
        Blocks(Describe.Lean(DescribeId.Create("original-data-quantitative-detector-rank-horizon"),
            DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/OriginalDataQuantitativeDetectorRankHorizon.detector_rank_horizon"),
            H("The universal bound from the original matrices"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The matrices act on complex Euclidean space of dimension D. T is completely positive and T(I) is at most I. B is an effect and sigma is a positive matrix of trace one. The eigenvalues of B are ordered decreasingly, with repetitions and zero eigenvalues retained; eigenvalueszero(B,r-1) denotes the r-th eigenvalue. Iteration at zero is the identity. All matrix norms below are Euclidean operator norms.")),
                Paragraph(Text("Put s=lambda_r(B). Nonnegativity settles s=0. For s>0 set t=p s/4, delta=p/(8 n D sqrt(D)), and C=(D/delta)^(D-r). Since s is at most one, t is positive and at most p/4. The threshold delta is positive and less than one. Start with every eigenvector whose eigenvalue is at least t. These vectors form an orthonormal seed of size q at least r. For each seed vector eta, t times its rank-one projection is at most B. Every larger subspace W containing this seed satisfies B at most P_W+t I: on the selected eigenspaces B is at most I, and on the complement every eigenvalue is below t. This construction does not require a spectral gap.")),
                Paragraph(Text("Take the finite Kraus representation of the actual map T, indexed by D squared operators, allowing zero operators. Subunitality makes each Kraus operator a contraction. Apply quantitative_word_orthonormal_extension to this family and the chosen seed. It supplies an orthonormal family e of size m at most D, its projection P, residuals norm((I-P) A_a e_j) at most delta, and expansions of e_j in chronological Kraus words of length at most D-r. The sum of absolute coefficients in each expansion is at most C.")),
                Paragraph(Text("Positivity of individual summands in the same Kraus representation gives t times the rank-one projection onto A_w eta at most T^k(B), where k is the length of w. Trace against sigma and use the early inequalities. The identity Tr(sigma |v><v|)=norm(sqrt(sigma) v) squared yields norm(sqrt(sigma) A_w eta) at most sqrt(epsilon/t). The finite expansions and the triangle inequality then give norm(sqrt(sigma) e_j) at most C sqrt(epsilon/t). Summing over the orthonormal family proves Tr(sigma P) at most D C squared epsilon/t.")),
                Paragraph(Text("Let Q=I-P. Decompose P into its orthonormal rank-one projections and apply the same Kraus representation. Then Q T(P) Q is the sum, over a and j, of rank-one operators on Q A_a e_j. The operator norm of each is at most delta squared. There are at most D cubed terms, so norm(Q T(P) Q) is at most D cubed delta squared. Its square root alpha is therefore at most p/(8 n). This controls the full complex operator, including all off-diagonal coherences.")),
                Paragraph(Text("The spectral cutoff gives X=B-t I at most P. Apply coherent_compression_trace_transfer to T, this P, X and sigma. It gives Re Tr(sigma T^n(X)) at most Tr(sigma P)+2 n alpha. Subunitality implies T^n(I) at most I. Linearity thus gives Re Tr(sigma T^n(B)) at most Tr(sigma P)+2 n alpha+t. The late hypothesis implies p at most D C squared epsilon/t+p/4+p/4. Multiplication by the positive t and substitution t=p s/4 give s at most 8 D C squared epsilon/p squared. Finally D/delta=8 n D^(5/2)/p, giving the displayed constant.")),
                Paragraph(Text("The argument never divides by epsilon and includes epsilon=0. It also includes repeated eigenvalues, singular mixed densities, arbitrary complex coherences, and a late index lying in the early window. No commutation, diagonalizability, conditioning or single-Kraus condition is used. The stronger late-free smallest-eigenvalue endpoint is a separate statement."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Statement()
    {
        Formula d=F.Id("D"), r=F.Id("r"), n=F.Id("n"), t=F.Id("T"), b=F.Id("B"),
            s=F.Id("sigma"), eps=F.Id("epsilon"), p=F.Id("p"), k=F.Id("k");
        var nat=Seq(Mathbb, Grp(F.Id("N")));
        var real=Seq(Mathbb, Grp(F.Id("R")));
        var mat=Call("ComplexEuclideanMatrix",d);
        Formula Obs(Formula j) => Call("re",Call("trace",Mul(s,Call("iterate",t,j,b))));
        var early=All("k",nat,Imp(Le(k,Sub(d,r)),Le(Obs(k),eps)));
        var hypotheses=And(Le(Num(2),d),And(Le(Num(2),r),And(Le(r,d),And(Le(Num(1),n),
            And(Le(Call("apply",t,Num(1)),Num(1)),And(Le(Num(0),b),And(Le(b,Num(1)),
            And(Le(Num(0),s),And(Eq(Call("trace",s),Num(1)),And(Le(Num(0),eps),
            And(Lt(Num(0),p),And(Le(p,Num(1)),And(early,Le(p,Obs(n))))))))))))))));
        var constant=Mul(Div(Mul(Num(8),d),Pow(p,Num(2))),
            Pow(Div(Mul(Mul(Num(8),n),Pow(d,Div(Num(5),Num(2)))),p),Mul(Num(2),Sub(d,r))));
        var conclusion=Le(Call("eigenvalueszero",b,Sub(r,Num(1))),Mul(constant,eps));
        return Disp(All("D",nat,All("r",nat,All("n",nat,
            All("T",Call("CompletelyPositiveMap",mat,mat),All("B",mat,All("sigma",mat,
            All("epsilon",real,All("p",real,Imp(hypotheses,conclusion))))))))));
    }
}
