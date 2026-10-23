using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetNativeIntegralDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Ex(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Scope(Formula body, params Formula.BoundVariable[] extra) => All(body,
        [B("q", I("Nat")), B("hq", Call("NatPositive", I("q"))), .. extra]);
    private static Formula OddScope(Formula body, params Formula.BoundVariable[] extra) => Scope(body,
        [B("ho", Call("Odd", I("q"))), .. extra]);
    private static Formula Unique(System.Func<Formula, Formula> predicate) =>
        Ex(And(predicate(I("k")), All(Imp(predicate(I("l")), Equal(I("l"), I("k"))),
            B("l", I("Int")))), B("k", I("Int")));
    private static Formula M => Call("VertexModule", I("Sign"), I("q"));
    private static Formula G => Call("DimensionGroup", Call("resetMatrix", I("q")));
    private static Formula T => Call("transition", Call("resetMatrix", I("q")));
    private static Formula P => Call("resetInverse", I("q"), I("hq"));
    private static Formula E => Call("resetNativeEquiv", I("q"), I("hq"));
    private static Formula D => Call("resetNativeDefect", I("q"));
    private static Formula C => Call("resetOddClass", I("q"));
    private static Formula Char => Call("resetNativeCharacter", I("q"), I("hq"));
    private static Formula Lambda(Formula x) => Call("apply", Char, x);
    private static Formula L(Formula x) => Call("apply", D, x);
    private static Formula Row(Formula x) => Call("apply", E, x);
    private static Formula Part(Formula y) => Call("resetNativePreimage", I("q"), I("hq"), y);
    private static Formula Range => Call("range", D);
    private static Formula Kernel => Call("kernel", D);
    private static Formula Combined => Call("submoduleSup", Range, Kernel);
    private static Formula Stage(Formula n, Formula v) =>
        Call("ModuleDirectLimitOf", I("Int"), I("Nat"), M, Call("stationaryTransition", T), n, v);
    private static Formula Fibre(Formula y, Formula x) =>
        Unique(k => Equal(x, Call("add", Part(y), Call("integerScale", k, C))));
    private static DocumentBlock Theorem(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static DocumentBlock Definition(string name, string title, Formula type, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(Scope(Call("hasType", Call(name, I("q"), I("hq")), type)))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral reset dynamics, a signed primitive character and the arithmetic index of image plus kernel.",
        H("Native integral reset defect"),
        Blocks(
            Paragraph(Text("M=VertexModule Sign q is the original Fin q -> Int[C2] right-row module. "
                + "G=DimensionGroup(resetMatrix q) is its original stationary Module.DirectLimit, "
                + "with forward maps T raised to the stage difference. Sign=Multiplicative Bool and "
                + "tau=ofAdd true. T is the original transition, whose head is (sum v)[tau] and "
                + "whose successor coordinates read their predecessors. Theta=resetTheta is genuine "
                + "time induced by T; the complement group action is a separate operator. "
                + "NatPositive(q) means 0<q. Every assertion includes q=1 when its parity permits it.")),
            Definition("resetInverse", "An integral inverse of the actual transition", Call("IntEnd", M),
                "For q=n+1, P(y)=Fin.snoc (j maps to y(j.succ)) "
                + "(resetFlip(y(0))-sum over Fin n of y(j.succ)). resetFlip is actual right multiplication "
                + "by [tau]. It is involutive on both coefficients. The formula uses integer subtraction, "
                + "so it need not preserve the coordinatewise nonnegative cone."),
            Theorem("reset_transition_inverse", "Two exact inverse identities at every positive length",
                Scope(And(Equal(Call("endMultiply", P, T), Num(1)),
                    Equal(Call("endMultiply", T, P), Num(1)))),
                "endMultiply is multiplication in Module.End Int M, that is composition. "
                + "The row sum of P(y) is resetFlip(y(0)), so the head of T(P(y)) is y(0); its tails "
                + "recover y. In P(T(v)), the prefix is recovered, and subtraction of that prefix "
                + "from the total sum recovers the last coordinate. The original transition_zero and "
                + "transition_succ facts supply the coordinate equations."),
            Definition("resetTransitionEquiv", "The original transition is an integer-linear equivalence",
                Call("IntLinearEquiv", M, M), "The forward map is exactly T and its inverse is exactly P."),
            Definition("resetNativeEquiv", "Faithful identification with stage zero",
                Call("IntLinearEquiv", G, M),
                "F=resetNativeEquiv lifts the compatible family P raised to n. The identity "
                + "P raised to j times T raised to j-i equals P raised to i proves compatibility "
                + "in the endomorphism ring. Its inverse is the original stage-zero linear map. "
                + "The direct-limit transition relation and T raised to n times P raised to n equals "
                + "identity prove both sides. This module equivalence makes no order-cone assertion."),
            Theorem("resetNativeEquiv_stage", "The exact stage formula",
                Scope(Equal(Row(Stage(I("n"), I("v"))),
                    Call("apply", Call("power", P, I("n")), I("v"))), B("n", I("Nat")), B("v", M)),
                "At stage zero F(of_0(v))=v. At any later natural stage, F(of_n(v))=P raised to n applied "
                + "to v. This retains the original forward directed system."),
            Theorem("resetNativeEquiv_theta", "Stage-zero coordinates preserve genuine time",
                Scope(Equal(Row(Call("apply", Call("resetTheta", I("q")), I("x"))),
                    Call("apply", T, Row(I("x")))), B("x", G)),
                "The original resetTheta_apply_of describes the induced map on each stage. P and T commute because "
                + "both compositions are identity; their powers therefore give F Theta=T F."),
            Definition("resetNativeCharacter", "The primitive integer character on the native group",
                Call("IntLinearMap", G, I("Int")),
                "Lambda=resetCharacter q composed with F. The finite character sums coeff_1 minus "
                + "coeff_tau over even suffix indices. Its transport reads the entire original group, "
                + "rather than a rational quotient or a sign-only replacement."),
            Theorem("reset_native_character_stage", "The character changes sign between stages",
                OddScope(Equal(Lambda(Stage(I("n"), I("v"))),
                    Call("mul", Call("power", new Formula.Negate(Num(1)), I("n")),
                        Call("apply", Call("resetCharacter", I("q")), I("v")))),
                    B("n", I("Nat")), B("v", M)),
                "The finite image criterion applied to v+Tv gives ell(Tv)=-ell(v). Applying this to Pv "
                + "gives ell(Pv)=-ell(v); induction yields the signed stage formula. The unsigned "
                + "prescription ell(v) at every stage does not descend, already for the q=1 swap."),
            Theorem("reset_native_character_theta", "Time negates the character",
                OddScope(Equal(Lambda(Call("apply", Call("resetTheta", I("q")), I("x"))),
                    new Formula.Negate(Lambda(I("x")))), B("x", G)),
                "This follows from F Theta=T F and the finite image criterion, without a second suffix-parity calculation."),
            Theorem("reset_native_character_surjective", "Every integer is attained",
                Scope(Call("Surjective", Char)),
                "The finite character is surjective by the suffix-zero identity basis row. F is "
                + "surjective, so the primitive character on G is surjective."),
            Theorem("reset_native_odd_kernel", "The full native odd kernel is primitive cyclic",
                OddScope(Iff(Equal(L(I("x")), Num(0)),
                    Unique(k => Equal(I("x"), Call("integerScale", k, C)))), B("x", G)),
                "c=resetOddClass q is the existing stage-zero class of w_i=(-1)^i([1]-[tau]). "
                + "The intertwining transports the finite reset_odd_kernel classification, "
                + "and F(c)=w preserves its unique integer coefficient."),
            Theorem("reset_native_odd_image", "Exact native solvability",
                OddScope(Iff(Ex(Equal(L(I("x")), I("y")), B("x", G)), Equal(Lambda(I("y")), Num(0))),
                    B("y", G)),
                "F(id+Theta)=(id+T)F transports reset_odd_image on the full two-coefficient lattice. "
                + "A finite integer preimage returns through F inverse to an actual native class."),
            Theorem("reset_native_odd_all_solutions", "All odd solution fibres",
                OddScope(All(Imp(Equal(Lambda(I("y")), Num(0)),
                    All(Iff(Equal(L(I("x")), I("y")), Fibre(I("y"), I("x"))), B("x", G))), B("y", G))),
                "The particular native solution is F inverse applied to resetPreimage q hq (F y). "
                + "Transport of reset_odd_all_solutions gives every solution with a unique integer parameter."),
            Theorem("reset_native_odd_range", "The exact native image submodule",
                OddScope(Equal(Range, Call("kernel", Char))),
                "The image is precisely the kernel of the primitive signed character."),
            Describe.Lean(DescribeId.Create("native-odd-integer-cokernel"),
                DeclarationHandle.Create(Prefix + "resetNativeOddCokernelEquiv"), H("The ordinary cokernel is Int"),
                StatementSource.FromAuthor(Disp(OddScope(Call("hasType",
                    Call("resetNativeOddCokernelEquiv", I("q"), I("hq"), I("ho")),
                    Call("IntLinearEquiv", Call("quotient", G, Range), I("Int")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The first isomorphism theorem for Lambda "
                    + "gives G/range(id+Theta) isomorphic to Int. This ordinary cokernel is free cyclic and "
                    + "has no hidden order-two torsion."))), DescribeRole.Definition),
            Theorem("reset_native_pairing", "The kernel pairs with the character by q+1",
                OddScope(Equal(Lambda(C), Call("intCast", Call("add", I("q"), Num(1))))),
                "On w the even-index character summand is 1+(-1)^i. Summing gives q plus the alternating "
                + "sum, which is one for odd q by Fin.sum_neg_one_pow. Thus Lambda(c)=q+1, "
                + "although Lambda itself is onto all integers."),
            Theorem("reset_native_kernel_inf_range", "The kernel and image meet only at zero",
                OddScope(Equal(Call("submoduleInf", Kernel, Range), I("bottomSubmodule"))),
                "If x=kc belongs to the image, then 0=Lambda(x)=k(q+1). The positive integer q+1 "
                + "is nonzero, forcing k=0. submoduleInf denotes intersection."),
            Theorem("reset_native_sum_criterion", "Exact arithmetic membership in image plus kernel",
                OddScope(Iff(Call("member", I("x"), Combined),
                    Call("Divides", Call("intCast", Call("add", I("q"), Num(1))), Lambda(I("x")))), B("x", G)),
                "If x=a+kc with a in the image, its character is k(q+1). Conversely, if Lambda(x)="
                + "k(q+1), subtract kc: the difference has zero character and hence lies in the image. "
                + "submoduleSup is the actual sum of integer submodules."),
            Describe.Lean(DescribeId.Create("native-combined-cyclic-quotient"),
                DeclarationHandle.Create(Prefix + "resetNativeCombinedQuotientEquiv"), H("The combined quotient is ZMod(q+1)"),
                StatementSource.FromAuthor(Disp(OddScope(Call("hasType",
                    Call("resetNativeCombinedQuotientEquiv", I("q"), I("hq"), I("ho")),
                    Call("IntLinearEquiv", Call("quotient", G, Combined), Call("ZMod", Call("add", I("q"), Num(1)))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Reduce Lambda modulo q+1. "
                    + "The exact divisibility criterion identifies its kernel with range(id+Theta) plus "
                    + "ker(id+Theta). Integer-cast surjectivity and Lambda surjectivity give the displayed "
                    + "integer-linear equivalence. At q=1 this quotient is ZMod 2 while the ordinary "
                    + "cokernel remains Int."))), DescribeRole.Definition),
            Theorem("reset_native_no_equivariant_linear_section", "No integer-linear equivariant section",
                OddScope(new Formula.Not(Ex(And(Equal(Call("compose", Char, I("s")), I("linearIdentity")),
                    All(Equal(Call("apply", Call("resetTheta", I("q")), Call("apply", I("s"), I("n"))),
                        Call("apply", I("s"), new Formula.Negate(I("n")))), B("n", I("Int")))),
                    B("s", Call("IntLinearMap", I("Int"), G))))),
                "Equivariance forces s(1) into the kernel, hence s(1)=kc. The section equation gives "
                + "1=k(q+1), impossible for positive q. The obstruction concerns additive or integer-linear "
                + "sections. It does not forbid set sections: at q=1 the nonadditive map "
                + "n maps to (max(n,0),max(-n,0)) is equivariant for coordinate swap. The underlying "
                + "integer-linear surjection splits after forgetting the time action."),
            Theorem("reset_native_all_solutions", "Complete fibres for every positive length",
                Scope(And(Imp(Call("Even", I("q")), Iff(Equal(L(I("x")), I("y")), Equal(I("x"), Part(I("y"))))),
                    Imp(Call("Odd", I("q")), Iff(Equal(L(I("x")), I("y")),
                        And(Equal(Lambda(I("y")), Num(0)), Fibre(I("y"), I("x")))))), B("y", G), B("x", G)),
                "For positive even q the transported finite solver gives the unique solution, "
                + "so the native kernel and cokernel vanish. For positive odd q, vanishing of Lambda "
                + "is exactly solvability and the full fibre is the particular solution plus Zc. "
                + "Both cases use the original integer transition and the original stationary colimit."))));
}
