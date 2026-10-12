using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetQuadraticGaussianCokernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetQuadraticGaussianCokernel.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Ex(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Q => Call("add", Call("mul", Num(4), I("m")), Num(3));
    private static Formula M => Call("VertexModule", I("Sign"), Q);
    private static Formula C => Call("resetGaussianCharacter", I("m"));
    private static Formula D => Call("resetTwoStepDefect", Q);
    private static Formula Apply(Formula f, Formula x) => Call("apply", f, x);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two primitive integer residual characters classify the full two-step cokernel at q=4m+3.",
        H("Reset quadratic Gaussian cokernel"), Blocks(
            Paragraph(Text("Sign=Multiplicative Bool, tau=ofAdd true, and each original suffix coordinate "
                + "is an element of Int[C2] with both integer coefficients retained. M=VertexModule Sign q "
                + "is the original right-row module, T=transition(resetMatrix q) its original integer "
                + "transition, and J=resetFlip is right multiplication by [tau]. J squares to identity. "
                + "The result concerns the ordinary integer cokernel of id+T^2 for every q=4m+3; "
                + "it imposes neither an order-cone equivalence nor a realization by a full reset "
                + "automorphism. Other residue classes modulo four are not classified here.")),
            Describe.Lean(DescribeId.Create("actual-two-step-integer-defect"),
                DeclarationHandle.Create(Prefix + "resetTwoStepDefect"), H("Two genuine integer time steps"),
                StatementSource.FromAuthor(Disp(All(Equal(Call("resetTwoStepDefect", I("q")),
                    Call("endSum", I("linearIdentity"), Call("power",
                        Call("transition", Call("resetMatrix", I("q"))), Num(2)))), B("q", I("Nat"))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The endomorphism is exactly "
                    + "LinearMap.id + (transition(resetMatrix q))^2 on the original full integer row. "
                    + "The square is composition of the genuine transition with itself, not the "
                    + "separate complement-group action."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primitive-two-head-character"),
                DeclarationHandle.Create(Prefix + "resetGaussianCharacter"), H("A primitive pair of integer characters"),
                StatementSource.FromAuthor(Disp(All(Call("hasType", C,
                    Call("IntLinearMap", M, Call("Prod", I("Int"), I("Int")))), B("m", I("Nat"))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Let z be the independently constructed "
                    + "quadratic companion codomain shear applied to y. The character is "
                    + "(coeff_1(z.head0)-coeff_tau(z.head0), coeff_1(z.head1)-coeff_tau(z.head1)). "
                    + "The shear incorporates the entire inhomogeneous skip-one tail recurrence. "
                    + "The pair is onto Int x Int: place single 1 k and single 1 l in the residual "
                    + "heads, zero in the residual tails, and use the inverse shear. This uses no half "
                    + "eigenvector and does not discard sign coefficients."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exact-three-mod-four-integral-image"),
                DeclarationHandle.Create(Prefix + "reset_two_step_three_mod_four_image"),
                H("The complete integral solvability criterion"),
                StatementSource.FromAuthor(Disp(All(Iff(Ex(Equal(Apply(D, I("v")), I("y")), B("v", M)),
                    Equal(Apply(C, I("y")), Num(0))), B("m", I("Nat")), B("y", M)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The actual T^2 coordinate formulas "
                    + "identify this defect with the quadratic additive companion. At q=4m+3 the "
                    + "integral normal form is ((id+J)(a+b),(id+J)(b),identity on tails). On Int[C2], "
                    + "the image of id+J consists exactly of rows whose two coefficients are equal; "
                    + "an integral preimage is single 1 k. Thus character zero is necessary and sufficient. "
                    + "For sufficiency, solve the two residual heads as (id+J)(a) and (id+J)(b), "
                    + "then reconstruct with free values a-b,b and the original residual tails. "
                    + "This is a full image criterion, not only a mod-two obstruction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("free-rank-two-ordinary-cokernel"),
                DeclarationHandle.Create(Prefix + "resetGaussianCokernelEquiv"), H("The exact cokernel is Int x Int"),
                StatementSource.FromAuthor(Disp(All(Call("hasType", Call("resetGaussianCokernelEquiv", I("m")),
                    Call("IntLinearEquiv", Call("quotient", M, Call("range", D)),
                        Call("Prod", I("Int"), I("Int")))), B("m", I("Nat"))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The complete image criterion identifies "
                    + "range(id+T^2) with the kernel of the surjective primitive pair character. "
                    + "The first isomorphism theorem constructs the displayed integer-linear equivalence. "
                    + "In particular the ordinary cokernel is free of rank two, with no additional "
                    + "order-two torsion. Gaussian denotes the period-four recurrence a,b,-a,-b; "
                    + "the displayed target is its integer coordinate pair, not a separately proved "
                    + "Gaussian-ring module equivalence."))), DescribeRole.Definition),
            Paragraph(Text("Native applicability. The existing resetNativeEquiv q hq identifies the "
                + "original stationary dimension group with stage-zero integer rows, and "
                + "resetNativeEquiv_theta states F Theta=T F. Applying it twice gives "
                + "F(id+Theta^2)=(id+T^2)F. Therefore the same exact image and ordinary cokernel "
                + "transport to genuine native time. This paragraph describes that application of "
                + "the existing equivalence; it asserts no full reset-group classification or RH result.")))));
}
