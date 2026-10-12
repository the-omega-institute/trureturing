using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetFiniteIntegralDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Ex(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Unique(System.Func<Formula, Formula> predicate) =>
        Ex(And(predicate(I("k")), All(new Formula.Logic(predicate(I("l")),
            FormulaLogicOperator.Implies, Equal(I("l"), I("k"))), B("l", I("Int")))), B("k", I("Int")));
    private static Formula M => Call("VertexModule", I("Sign"), I("q"));
    private static Formula L(Formula v) => Call("apply", Call("resetDefect", I("q")), v);
    private static Formula Char(Formula y) => Call("apply", Call("resetCharacter", I("q")), y);
    private static Formula W => Call("resetOddVector", I("q"));
    private static Formula P(Formula y) => Call("resetPreimage", I("q"), I("hq"), y);
    private static Formula OddScope(Formula body, params Formula.BoundVariable[] extra) => All(body,
        [B("q", I("Nat")), B("hq", Call("NatPositive", I("q"))),
            B("ho", Call("Odd", I("q"))), .. extra]);
    private static Formula OddTheoremScope(Formula body, params Formula.BoundVariable[] extra) =>
        All(Imp(And(Call("NatPositive", I("q")), Call("Odd", I("q"))),
            extra.Length == 0 ? body : All(body, extra)), B("q", I("Nat")));
    private static DocumentBlock Theorem(string name, string id, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete finite integral reset defect on the original right-row lattice.",
        H("Finite integral reset defect"),
        Blocks(
            Paragraph(Text("Sign=Multiplicative Bool is the original two-element group, "
                + "tau=ofAdd true, and VertexModule Sign q is Fin q -> MonoidAlgebra Int Sign. "
                + "Each coordinate retains its identity and tau coefficients. T is the existing "
                + "transition(resetMatrix q), using integerMatrix and right-row multiplication. "
                + "At suffix zero it is right multiplication of the full row sum by tau; at each "
                + "successor it reads the preceding coordinate. resetDefect q=L=id+T. "
                + "NatPositive(q) means 0<q; Int denotes the integers. All positive q, including one, "
                + "are covered. No rational replacement, positivity, mixing or geometric conjugacy "
                + "hypothesis is used.")),
            Paragraph(Text("resetCharacter q is ell(y)=sum over even i<q of "
                + "coeff_1(y_i)-coeff_tau(y_i). It is an Int-linear map. "
                + "resetPreimage first applies the finite-companion codomain shear to y. "
                + "For even q its initial value is the entire residual z. For odd q its initial "
                + "value is single 1 (coeff_1(z)). It then uses the inverse adjacent-sum recurrence. "
                + "The odd choice solves the residual precisely when its two coefficients agree. "
                + "No division by two appears.")),
            Theorem("reset_defect_companion", "original-reset-companion-identification",
                "The additive companion is the actual original right-row operator",
                All(Equal(Call("apply", Call("resetDefect", Call("succ", I("n"))), I("v")),
                    Call("companion", I("resetFlip"), I("n"), I("v"))),
                    B("n", I("Nat")), B("v", Call("VertexModule", I("Sign"), Call("succ", I("n"))))),
                "resetFlip is right multiplication by single tau 1, and companion is the finite "
                + "additive map with head v(0)+resetFlip(sum v) and adjacent-sum tails. "
                + "The equality directly reuses the original transition_zero and transition_succ coordinate facts. "
                + "It identifies the actual operator without replacing either integer coefficient, "
                + "and supplies the finite elimination and subsequent transition calculations."),
            Theorem("reset_even_unique_solution", "even-reset-explicit-unique-solution",
                "Unique integral solution at every positive even length",
                All(Imp(Call("Even", I("q")),
                    All(And(Equal(L(P(I("y"))), I("y")),
                        All(Iff(Equal(L(I("v")), I("y")), Equal(I("v"), P(I("y")))), B("v", M))),
                        B("y", M))),
                    B("q", I("Nat")), B("hq", Call("NatPositive", I("q")))),
                "The separately defined domain and codomain equivalences reduce the even operator to identity "
                + "on the entire integral carrier. The displayed solver is its unique inverse value. "
                + "This is a finite lattice statement about the actual right-row map."),
            Theorem("reset_character_surjective", "primitive-reset-integer-character",
                "The character is onto Int",
                All(Imp(Call("NatPositive", I("q")), Call("Surjective", Call("resetCharacter", I("q")))),
                    B("q", I("Nat"))),
                "Surjective means every integer is attained. Put single 1 k in the zero suffix "
                + "and zero in all other suffixes; ell of this row is k. Thus the character is primitive, "
                + "rather than an even-valued character obtained by using an anti-vector basis."),
            Theorem("reset_odd_image", "odd-reset-exact-integral-image",
                "Solvability is exactly vanishing of the primitive character",
                OddTheoremScope(Iff(Ex(Equal(L(I("v")), I("y")), B("v", M)), Equal(Char(I("y")), Num(0))),
                    B("y", M)),
                "After the codomain shear, the residual coefficient difference equals ell(y). "
                + "When it is zero the residual is d(1+tau), and the initial value d[1] solves "
                + "(id+rightTau)a=d(1+tau). The tail recurrence supplies an explicit integral preimage. "
                + "Conversely the residual of L(v) has equal coefficients, so ell annihilates the whole image."),
            Theorem("reset_odd_kernel", "odd-reset-full-primitive-kernel",
                "The entire odd kernel has a unique integer generator coefficient",
                OddTheoremScope(Iff(Equal(L(I("v")), Num(0)),
                    Unique(k => Equal(I("v"), Call("integerScale", k, W)))),
                    B("v", M)),
                "existsUnique means there exists exactly one integer k satisfying the equation. "
                + "resetOddVector is the existing original row w_i=(-1)^i([1]-[tau]). "
                + "Zero adjacent sums determine every coordinate from v_0; the residual equation "
                + "forces v_0 to be k([1]-[tau]). Its identity coefficient recovers k uniquely. "
                + "The earlier transition equation T(w)=-w supplies the reverse direction."),
            Theorem("reset_odd_all_solutions", "odd-reset-complete-affine-solutions",
                "All solutions differ by a unique multiple of the odd row",
                All(Imp(Call("Odd", I("q")),
                    All(Imp(Equal(Char(I("y")), Num(0)),
                        All(Iff(Equal(L(I("v")), I("y")),
                            Unique(k => Equal(I("v"), Call("add", P(I("y")), Call("integerScale", k, W))))),
                            B("v", M))), B("y", M))),
                    B("q", I("Nat")), B("hq", Call("NatPositive", I("q")))),
                "Subtract the explicit particular solution. The difference lies in the full kernel, "
                + "so the unique coefficient in the kernel theorem classifies every solution. "
                + "Nonvanishing ell excludes any solution by the image theorem."),
            Theorem("reset_odd_range", "odd-reset-range-equals-character-kernel",
                "The exact sequence on the full integer lattice",
                OddTheoremScope(Equal(Call("range", Call("resetDefect", I("q"))),
                    Call("kernel", Call("resetCharacter", I("q"))))),
                "range and kernel are the Int-linear submodules of the displayed maps. "
                + "Together with the surjective character, this equality gives exactness on the "
                + "original lattice. It is used to identify its cokernel."),
            Describe.Lean(DescribeId.Create("odd-reset-integer-cokernel-equivalence"),
                DeclarationHandle.Create(Prefix + "resetOddCokernelEquiv"),
                H("The full odd cokernel is Int"),
                StatementSource.FromAuthor(Disp(OddScope(Call("hasType",
                    Call("resetOddCokernelEquiv", I("q"), I("hq"), I("ho")),
                    Call("IntLinearEquiv", Call("quotient", M,
                        Call("range", Call("resetDefect", I("q")))), I("Int")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("hasType displays the definition's exact result type. "
                    + "IntLinearEquiv is a linear equivalence over Int, and quotient is the whole "
                    + "module modulo the displayed image. The equivalence is the first isomorphism "
                    + "theorem for ell after replacing its kernel by range(L). The cokernel is free "
                    + "cyclic and has no order-two torsion. At q=1, T(a,b)=(b,a), L(a,b)=(a+b,a+b), "
                    + "the kernel is the anti-diagonal and the image is the primitive diagonal. "
                    + "The vectors (1,1),(1,-1) have determinant -2 and do not form an integral basis. "
                    + "The generic scalar specialization A=Int,J=id instead leaves multiplication "
                    + "by two, so involution alone does not justify the free-cokernel conclusion. "
                    + "These results concern the finite carrier; transport to the stationary colimit "
                    + "requires a separate identification with the genuine shift action."))),
                DescribeRole.Definition))));
}
