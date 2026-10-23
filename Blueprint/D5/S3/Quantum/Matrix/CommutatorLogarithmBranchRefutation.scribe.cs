using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CommutatorLogarithmBranchRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/bathory2025commutator");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exponential of a complex matrix does not determine its halved commutator operator.",
        H("An obstruction to exponential-dependent logarithm branches"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Recovering the commutator from the exponential"),
                StatementSource.FromAuthor(Disp(ClaimDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For a complex two-by-two matrix G, LinearMap.mulLeft ℂ G sends X to GX, "
                        + "and LinearMap.mulRight ℂ G sends X to XG. Half their difference is the "
                        + "halved commutator operator. The claim asks for two functions ΛL and ΛR "
                        + "from complex two-by-two matrices to complex-linear endomorphisms of "
                        + "that matrix space, whose half-difference at exp G equals this operator "
                        + "for every G. Both functions depend only on the exponential, and no "
                        + "further conditions are imposed on them.")),
                    Paragraph(Text(
                        "Bathory defines the multiplication and halved commutator operators in "
                        + "equation (1.1), cc_arxiv_1_.tex line 38. Lemma 3.4 states the logarithm "
                        + "identity (3.42) for real symmetric matrices at lines 377–387, with the "
                        + "identity itself at line 385. Conjecture 3.7 at lines 505–507 proposes "
                        + "extending these identities to all complex square matrices. The claim "
                        + "is the dimension-two reading of (3.42) in which the generalized logarithm "
                        + "operators are determined by A = exp G."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Equal exponentials with different commutators"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(LocalClaim)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Suppose such functions ΛL and ΛR exist. The diagonal matrix "
                        + "diag(0, 2πi) has exponential equal to the identity: exponentiating a "
                        + "diagonal matrix exponentiates its diagonal entries, and exp 0 = 1 "
                        + "and exp(2πi) = 1. Here π is the real number Real.pi included in ℂ, "
                        + "and i is Complex.I.")),
                    Paragraph(Text(
                        "Apply the asserted identity first to the zero matrix and then to "
                        + "diag(0, 2πi). The exponential of the zero matrix is also the identity. "
                        + "Thus both right sides are the same linear map, namely half of "
                        + "ΛL(1) − ΛR(1), so the two halved commutator operators must agree.")),
                    Paragraph(Text(
                        "Evaluate this equality on Matrix.single 0 1 1 and take its entry at "
                        + "row 0, column 1. This matrix has complex entry one at that position "
                        + "and zero elsewhere. The zero matrix gives entry zero. Left "
                        + "multiplication by diag(0, 2πi) gives entry zero, while right "
                        + "multiplication gives entry 2πi. Subtracting and multiplying by the "
                        + "complex scalar one half therefore gives −πi. Equality would force "
                        + "0 = −πi, contradicting π > 0 and i ≠ 0. Hence no such pair of "
                        + "functions exists. The obstruction concerns the exponential-dependent "
                        + "complex extension; the real symmetric identity retains its stated scope."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bathory-2025-commutator-logarithm-branch-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula LocalClaim => Seq(Operatorname, Grp(F.Id("claim")));
    private static Formula LambdaL => Seq(Lambda, Sp, F.Id("L"));
    private static Formula LambdaR => Seq(Lambda, Sp, F.Id("R"));
    private static Formula G => F.Id("G");
    private static Formula FinTwo => Call("Fin", Typed(D(2), Naturals));
    private static Formula Matrices => Call("Matrix", FinTwo, FinTwo, Complexes);
    private static Formula Endomorphisms => Seq(
        Parenthesized(Matrices), Sp, new Formula.Subscript(To, Ell),
        OpenBracket, Complexes, CloseBracket, Sp, Parenthesized(Matrices));
    private static Formula LogarithmFunctions =>
        new Formula.TypeArrow(Parenthesized(Matrices), Parenthesized(Endomorphisms));
    private static Formula Half =>
        new Formula.Fraction(Typed(D(1), Complexes), Typed(D(2), Complexes));
    private static Formula Exponential => QualifiedCall("NormedSpace", "exp", G);
    private static Formula ClaimDefinition => Equal(LocalClaim,
        Parenthesized(Some(LambdaL, LogarithmFunctions,
            Some(LambdaR, LogarithmFunctions, All(G, Matrices,
                Equal(Scale(Half, Subtract(
                        QualifiedCall("LinearMap", "mulLeft", Complexes, G),
                        QualifiedCall("LinearMap", "mulRight", Complexes, G))),
                    Scale(Half, Subtract(App(LambdaL, Parenthesized(Exponential)),
                        App(LambdaR, Parenthesized(Exponential))))))))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula QualifiedCall(string owner, string name, params Formula[] arguments) =>
        App(Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))), arguments);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Scale(Formula scalar, Formula value) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
}
