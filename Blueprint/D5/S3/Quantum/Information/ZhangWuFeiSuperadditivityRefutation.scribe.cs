using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ZhangWuFeiSuperadditivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Divergence/zhangwufei2013superadditivity");
    private const string SourceSentence =
        "Based on the above result, we propose the following conjecture: There exist unitary operators "
        + "U_A ∈ U(H_A), U_B ∈ U(H_B) and U_AB ∈ U(H_A ⊗ H_B) such that "
        + "S(U_AB ρ_AB U_AB† ‖ σ_AB) ⩾ S(U_A ρ_A U_A† ‖ σ_A) + S(U_B ρ_B U_B† ‖ σ_B), "
        + "(4.2) where the reference state σ_AB is required to be full-ranked state. "
        + "Indeed, our numerical calculations show that inequality (4.2) is true.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A maximally mixed two-qubit input and a full-rank correlated diagonal reference contradict relative-entropy superadditivity.",
        H("A counterexample to Zhang–Wu–Fei superadditivity"),
        Blocks(
            Describe.Lean(DescribeId.Create("zwf-claim"), DeclarationHandle.Create(Module + "claim"),
                H("The unitary superadditivity conjecture"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(Named("claim"),
                    FormulaLogicOperator.Iff, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Zhang, Wu and Fei, arXiv:1210.4720v4, p. 6, §4: “" + SourceSentence + "”")),
                    Paragraph(Text("The dimensions a and b range over natural numbers. DensityState means a positive semidefinite complex matrix of trace one. The first subsystem is Fin a and the second is Fin b. marginalRight retains A, while marginalLeft retains B. PosDef expresses full rank of the reference. quantumRelativeEntropy is Re Tr(ρ(log ρ − log σ)), with natural logarithms. The three matrices and their membership proofs express independent joint and local unitaries."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zwf-result"), DeclarationHandle.Create(Module + "result"),
                H("The conjecture fails for two qubits"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take a = b = 2, ρ = I/4 and σ = diag(61,1,1,1)/64 in product order (0,0), (0,1), (1,0), (1,1). All four reference eigenvalues are positive. The two input marginals equal I/2, and the two reference marginals equal diag(31,1)/32. Every unitary fixes the input and its marginals.")),
                    Paragraph(Text("The joint relative entropy is log(1/4) − log(61/64)/4 − 3 log(1/64)/4. Each marginal relative entropy is log(1/2) − log(31/32)/2 − log(1/32)/2. Four times the difference between the joint value and twice the marginal value is log(923521/3997696), which is negative. Thus no choice of the three unitaries satisfies the displayed inequality."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhang-wu-fei-2012-relative-entropy-superadditivity-conjecture-4-2"),
                    ResolutionKind.Refuted)))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula variable, Formula type) => Parenthesized(Seq(variable, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula dimension) => Call("Fin", dimension);
    private static Formula Mat(Formula index) => Call("Matrix", index, index, Complexes());
    private static Formula Membership(Formula unitary, Formula index) =>
        Seq(unitary, InMacro, Sp, App(Qualified("Matrix", "unitaryGroup"), index, Complexes()));

    private static Formula ClaimBody()
    {
        Formula a = F.Id("a"), b = F.Id("b"), rho = F.Id("rho"), sigma = F.Id("sigma");
        Formula uab = F.Id("UAB"), ua = F.Id("UA"), ub = F.Id("UB");
        Formula hab = F.Id("hAB"), ha = F.Id("hA"), hb = F.Id("hB");
        Formula joint = Parenthesized(Seq(Fin(a), Times, Sp, Fin(b)));
        Formula sigmaValue = Call("val", sigma);
        Formula ofMatrixSymm = Seq(Qualified("CStarMatrix", "ofMatrix"), Dot, Named("symm"));
        Formula positive = Seq(Parenthesized(App(ofMatrixSymm, sigmaValue)), Dot, Named("PosDef"));
        Formula lhs = new Formula.Binary(
            Call("quantumRelativeEntropy", Call("unitaryConjugateState", ua, ha, Call("marginalRight", rho)),
                Call("marginalRight", sigma)), FormulaBinaryOperator.Add,
            Call("quantumRelativeEntropy", Call("unitaryConjugateState", ub, hb, Call("marginalLeft", rho)),
                Call("marginalLeft", sigma)));
        Formula rhs = Call("quantumRelativeEntropy", Call("unitaryConjugateState", uab, hab, rho), sigma);
        Formula inequality = new Formula.Relation(lhs, FormulaRelationOperator.LessThanOrEqual, rhs);
        Formula existence = Some(uab, Mat(joint), Some(hab, Membership(uab, joint),
            Some(ua, Mat(Fin(a)), Some(ha, Membership(ua, Fin(a)),
                Some(ub, Mat(Fin(b)), Some(hb, Membership(ub, Fin(b)), inequality))))));
        Formula implication = new Formula.Logic(Parenthesized(positive), FormulaLogicOperator.Implies,
            Parenthesized(existence));
        return All(a, Seq(Mathbb, Grp(F.Id("N"))), All(b, Seq(Mathbb, Grp(F.Id("N"))),
            All(rho, Call("DensityState", joint), All(sigma, Call("DensityState", joint), implication))));
    }
}
