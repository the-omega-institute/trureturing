using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHWeightedRelationLimsupDocument : IScribeDocumentDefinition
{
    private const string Path = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Disjoint integer relations can lower the normalized RH left-window upper limit.",
        H("A quantitative left-window gap from disjoint relations"),
        Blocks(
            Paragraph(Text("Assume the Riemann hypothesis. Let J(T) be the positive zeta zeros "
                + "with ordinate γ at most T. The real part is fixed by RH, so each ordinate "
                + "in the cutoff identifies one zero. With analytic multiplicity mγ the "
                + "weight is wγ = mγ γ/(1/4 + γ²), which is strictly positive. "
                + "Use these weights both in the total mass W(T) and in the finite sine "
                + "polynomial with frequencies γ. Its deficit D(T) is one minus the real "
                + "supremum of the polynomial divided by W(T). "),
                Ref(Path + "RHRootWeightedSine"), Text(" "), Ref(Path + "RHWeightedPhaseLimsup")),
            Paragraph(Text("At any cutoff of positive mass, let δₐ be the norm of the difference "
                + "between 1 and i raised to the sum of the integer coefficients in row a. "
                + "For arbitrary overlapping integer relations and nonnegative multipliers, "
                + "the squared sum of the multiplied defects divided by twice the mass times "
                + "the column energy bounds D(T) from below, provided the column energy is "
                + "positive. For disjoint nonzero relation rows, the lower bound is the sum "
                + "of the squared row defects divided by their row energies, all divided by "
                + "twice W(T). These are the finite character inequalities with ordinates "
                + "and weights taken from J(T). "),
                Ref("D5/S3/Fourier/WeightedIntegerRelations")),
            Describe.Lean(DescribeId.Create("signed-window-limsup-disjoint-relations"),
                DeclarationHandle.Create(Path + "RHWeightedRelationLimsup"
                    + ".signed_window_limsup_le_of_eventually_disjoint_relations"),
                H("An eventual packing gives a strict coefficient gap"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix natural m and r satisfying m ≥ 2 and m + 1 = 2r. "
                        + "Set s = orderRate(m) and cₘ = μ(m+1)(m+1)/(ms). At each positive "
                        + "width L and left endpoint exp(u), divide signedWindowResidual at "
                        + "exp(u), exp(u+L) by powerGap at rate s at those endpoints. Add cₘ "
                        + "and μ(r) times rootSignal(r,u), and take the absolute value. "
                        + "Write Q(m,r,L) for the limsup of this absolute value as u tends to "
                        + "positive infinity, divided by L log²(1/L). The full coefficient "
                        + "κ(m,r) is |μ(r)|/(4πs).")),
                    Paragraph(Text("For a finite set R of row indices and integer coefficients "
                        + "k(a,j) on positive zeta zeros, P(T,R,k) is the sum over rows of δₐ² "
                        + "divided by the energy Σⱼ k(a,j)²/w(j), divided by 2W(T). Each sum "
                        + "over j is restricted to J(T). The formula requires at each sufficiently "
                        + "large T a choice of rows and coefficients giving P(T,R,k) ≥ ε. "
                        + "Each row is an integer relation among the ordinates, is nonzero on J(T), "
                        + "and shares no nonzero column with a distinct row.")),
                    Paragraph(Text("The mass is eventually positive. The disjoint bound therefore "
                        + "gives D(T) ≥ ε on a tail. Since 2r/L tends to positive infinity as "
                        + "L tends to zero from above, the moving-coefficient formula bounds "
                        + "Q(m,r,L) by κ(m,r)(1 − ε) plus an error tending to zero on the same "
                        + "one-sided filter. Q is eventually nonnegative, so the resulting "
                        + "upper bound passes to its real limsup. The Möbius assumption makes "
                        + "κ(m,r) positive and the upper limit strictly smaller than κ(m,r). "
                        + "Whether such relation families exist for the zeta ordinates remains open. "),
                        Ref(Path + "RHWeightedPhaseLimsup"))),
                DescribeRole.Theorem))));

    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Naturals => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Integers => F.Seq(F.Mathbb, F.Grp(F.Id("Z")));
    private static Formula Zeros => Id("PositiveZetaZero");

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);
    private static Formula Rel(Formula a, FormulaRelationOperator rel, Formula b) =>
        new Formula.Relation(a, rel, b);
    private static Formula Le(Formula a, Formula b) =>
        Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Ne(Formula a, Formula b) =>
        Rel(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Mem(Formula a, Formula b) =>
        Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Function(string name, Formula body) =>
        F.Seq(F.Open, F.LambdaLower, F.Sp, F.Id(name), F.Sp, F.Mapsto, F.Sp, body, F.Close);
    private static Formula AllMember(string name, Formula type, Formula set, Formula body) =>
        All(name, type, Imp(Mem(Id(name), set), body));
    private static Formula Coefficient(string row) => Call("k", Id(row), Id("j"));

    private static Formula EventuallyPacked(Formula epsilon)
    {
        var type = Id("A");
        var height = Id("T");
        var rows = Id("R");
        var columns = Call("J", height);
        var relation = AllMember("a", type, rows, Equal(
            F.Seq(F.Sum, F.Underscore, F.Grp(F.Id("j"), F.InMacro, F.Sp, columns), F.Sp,
                Multiply(Coefficient("a"), Call("gamma", Id("j")))), Num(0)));
        var nonzero = AllMember("a", type, rows, Exists("j", Zeros,
            And(Mem(Id("j"), columns), Ne(Coefficient("a"), Num(0)))));
        var disjoint = AllMember("a", type, rows, AllMember("b", type, rows,
            Imp(Ne(Id("a"), Id("b")), AllMember("j", Zeros, columns,
                Or(Equal(Coefficient("a"), Num(0)), Equal(Coefficient("b"), Num(0))))));
        var bound = Le(epsilon, Call("P", height, rows, Id("k")));
        var choice = Exists("R", Call("Finset", type),
            Exists("k", Arrow(type, Arrow(Zeros, Integers)),
                And(relation, And(nonzero, And(disjoint, bound)))));
        return Call("Eventually", Function("T", choice), Id("atTop"));
    }

    private static Formula Statement()
    {
        var m = Id("m");
        var r = Id("r");
        var epsilon = Id("epsilon");
        var coeff = Call("kappa", m, r);
        var limsup = Call("limsup", Function("L", Call("Q", m, r, Id("L"))), Call("nhdsGT", Num(0)));
        var bound = And(Le(limsup, Multiply(coeff, Subtract(Num(1), epsilon))), Lt(limsup, coeff));
        var premise = And(Le(Num(2), m), And(Equal(Add(m, Num(1)), Multiply(Num(2), r)),
            And(Ne(Call("mu", r), Num(0)), And(Lt(Num(0), epsilon), EventuallyPacked(epsilon)))));
        return F.Disp(Imp(Id("RH"), All("A", Id("Type"), All("m", Naturals,
            All("r", Naturals, All("epsilon", Reals, Imp(premise, bound)))))));
    }
}
