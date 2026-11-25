using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class FejerCollisionLimitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/FejerCollisionLimit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A differentiable limit of normalized triangular collision moments determines the normalized closed-band mass.",
        H("Hard collision limits from differentiable ramp profiles"),
        Blocks(
            Paragraph(Text(
                "Let the data vary over an arbitrary filter ell on an index type. At each index n, let S(n) be a finite set of real-frequency data with frequencies x(n,i) and real weights c(n,i). Write L_n(r) for the finite weighted collision ramp and E_n(r) for the ordered closed-band mass. Let B and eta be real-valued normalizing factors and radius scales. " +
                "EventualPairNonnegative(ell,c) means eventually all pair products c(n,i)c(n,j) are nonnegative for i,j in S(n). EventuallyNonnegative(ell,B) and EventuallyPositive(ell,eta) mean eventually B(n)>=0 and eta(n)>0, respectively. " +
                "Set F(t) to the function n -> B(n)L_n(t eta(n)) and H(a) to the function n -> B(n)eta(n)E_n(a eta(n)). Let f be a real profile, a and d real numbers and R a positive neighborhood radius. HasDerivAt(f,d,a) means that f is differentiable at a with derivative d.")),
            Describe.Lean(DescribeId.Create("hard-band-limit"),
                DeclarationHandle.Create(Owner + ".collision_ramp_tendsto_hard"),
                H("Recovery at a differentiable limiting profile"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For fixed 0<delta<R, apply the finite collision secants at radius a eta(n) with spacing delta eta(n) and multiply by B(n). Eventually the resulting left and right differences of F bracket delta H(a). Differentiability provides, for each lower or upper comparison with d, a fixed spacing for which the corresponding limiting secant is strictly beyond that comparison. Pointwise convergence at the two endpoints transfers this strict bound to the finite data eventually. These bounds characterize convergence of H(a) to d. The spacings are chosen independently of n.")),
                    Paragraph(Text(
                        "For varying degree-n frequency families with nonnegative original weights, positive eta(n) eventually and B(n)>=0 eventually, the Fourier identity identifies L_n(r) for r>0 with r times the whole-line angular Fejer moment. If for every fixed t>0 the normalized ramp at radius t eta(n) tends to k t², take a=1, R=1 and f(t)=k t². Then B(n)eta(n)E_n(eta(n)) tends to 2k. In particular, with B(n)=sqrt(n V(n))/(eta(n)^2 W(n)^(2n)) where the total mass W(n), resolution and variance budget are positive eventually, k=1/(2 sqrt(pi)) yields the normalized hard-band coefficient 1/sqrt(pi). The actual zeta-tail upper estimate and control of noncentral contributions at neighboring radii are additional arithmetic obligations."))),
                DescribeRole.Theorem))));

    private static Formula I(string name) => F.Id(name);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Tends(Formula x, Formula d) => Call("Tendsto", x, I("ell"), Call("nhds", d));

    private static Formula Statement()
    {
        Formula t = I("t"), a = I("a"), R = I("R"), ell = I("ell");
        Formula real = F.Seq(F.Mathbb, F.Grp(I("R")));
        Formula pointwise = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("t"), real)],
            Imp(Lt(Call("Abs", Subtract(t, a)), R), Tends(Call("F", t), Call("f", t))));
        Formula assumptions = And(Call("EventualPairNonnegative", ell, I("c")),
            And(Call("EventuallyNonnegative", ell, I("B")),
            And(Call("EventuallyPositive", ell, I("eta")),
            And(Lt(F.D(0), R), And(Call("HasDerivAt", I("f"), I("d"), a), pointwise)))));
        return F.Disp(Imp(assumptions, Tends(Call("H", a), I("d"))));
    }
}
