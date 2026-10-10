using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class HeterogeneousTeacherSeparationDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        Seq(Par(premise), Sp, Implies, Sp, Par(conclusion));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every independent heterogeneous whole-window law with all five symbol masses "
            + "at least rho separates different increasing priority teachers by the same sharp "
            + "squared-distance constant, attained within the common-law subclass.",
        H("Sharp Heterogeneous Whole-Window Teacher Separation"),
        Blocks(
            Paragraph(Text("Window is the five-symbol alphabet 000,100,010,101,001 in low-to-high "
                + "bit order. Its first and last bits are the low and high endpoints. "
                + "Input(n) contains all words of n whole windows, including every zero window. "
                + "Positions in Fin(n) start at zero. Roles(n) is the existing type of triples "
                + "p<q<r. No global seam condition is imposed.")),
            Paragraph(Text("Laws(n) is Fin(n) to Window to the real numbers. "
                + "Admissible(rho,mu) requires each of the five masses mu(i,a) to be at least rho "
                + "and each position's total mass to equal one. The input mass is the product "
                + "of mu(i,w(i)) over all positions. Positions are independent; their laws need "
                + "not agree. Within one window, the joint high-and-low mass is mu(i,101), "
                + "rather than the product of the two endpoint marginals.")),
            Paragraph(Text("classValue(t,w) is the real value of the existing priority teacher: "
                + "it returns 1 when high(w(p)) and low(w(q)) both hold, otherwise 2 when "
                + "high(w(q)) and low(w(r)) both hold, and 0 otherwise. "
                + "distance(mu,t,u) is the sum over all complete words of the product input "
                + "mass times the squared class-value difference. "
                + "gamma(rho) is 8 times rho squared times (1 minus 2 times rho).")),
            Paragraph(Text("Product expectation productExpectation(mu,f) sums the actual product input mass "
                + "times f. The functions highIndicator and lowIndicator are the real zero-one endpoint indicators, "
                + "highMarginal and lowMarginal are their marginal means, and firstGate(t,w)=highIndicator(w(p)) lowIndicator(w(q)) is the first "
                + "gate. The product formulas for two, three and four positions apply at distinct positions; "
                + "product_expectation_linear_combination distributes three-term linear combinations. The endpoint and joint "
                + "means, binary indicators, class formula, marginal interval and Bernoulli discrepancy estimate "
                + "give the same identities for every actual heterogeneous law.")),
            Describe.Lean(DescribeId.Create("heterogeneous-first-gate-separation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation.first_gate_discrepancy_lower"),
                H("Separation of different first pairs"),
                StatementSource.FromAuthor(GateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A shared first position, a shared second position, a "
                    + "crossed position, and disjoint first pairs exhaust the overlaps. The same "
                    + "window joint mass is preserved in the crossed case. In all four cases "
                    + "the squared discrepancy of the binary first gates is at least gamma."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("heterogeneous-teacher-sharp-separation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation.result"),
                H("A uniform lower bound and an attaining law"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Finite product factorization integrates every unselected "
                        + "coordinate using its total mass one. These product identities and the "
                        + "Bernoulli discrepancy s+t-2st are standard probability algebra. "
                        + "Both endpoint marginals lie between 2 rho and 1 minus 3 rho. "
                        + "The bilinear discrepancy is minimized at the lower-lower corner "
                        + "on this rectangle.")),
                    Paragraph(Text("The uniform estimate treats shared first positions, shared "
                        + "second positions, a crossed middle position, and disjoint first pairs. "
                        + "The crossed case retains the same middle window's low-only, high-only, "
                        + "and joint endpoint masses simultaneously. A first-gate disagreement "
                        + "forces a squared class difference of one, regardless of the third "
                        + "positions. For identical first pairs and different third positions, "
                        + "restricting the middle window to 001 gives a sufficient bound: "
                        + "the first gate vanishes, the second gate is open to either third "
                        + "low bit, and the squared difference is four times their discrepancy.")),
                    Paragraph(Text("The public equality clause fixes the admissible common law "
                        + "mu(i,a)=extremal(rho)(a), with masses "
                        + "((1-3 rho)/2, rho, (1-3 rho)/2, rho, rho) in alphabet order. "
                        + "The triples (0,n-2,n-1) and (1,n-2,n-1) share the last two positions. "
                        + "Their squared class difference equals their first-gate discrepancy, "
                        + "whose expectation is exactly gamma(rho). All five masses satisfy "
                        + "the required lower bound. The universal lower bound and attained "
                        + "equality identify the infimum over all admissible heterogeneous laws "
                        + "and distinct triples. No label channel or sampling guarantee is asserted."))),
                DescribeRole.Theorem))));

    private static Formula GateFormula()
    {
        var n = V("n"); var rho = V("rho"); var mu = V("mu");
        var t = V("t"); var u = V("u"); var w = V("w");
        var discrepancy = new Formula.Power(Par(Seq(Call("firstGate", t, w), Sp, Minus, Sp,
            Call("firstGate", u, w))), D(2));
        var integrand = Par(Seq(w, Sp, Mapsto, Sp, discrepancy));
        var pairs = Seq(Call("p", t), Sp, Neq, Sp, Call("p", u), Sp, Lor, Sp,
            Call("q", t), Sp, Neq, Sp, Call("q", u));
        var premises = Seq(D(0), Sp, Lt, Sp, rho, Sp, Land, Sp, rho, Sp, Le, Sp,
            new Formula.Fraction(D(1), D(8)), Sp, Land, Sp, Call("Admissible", rho, mu),
            Sp, Land, Sp, Par(pairs));
        return All(n, Seq(Mathbb, Grp(V("N"))), All(rho, Seq(Mathbb, Grp(V("R"))),
            All(mu, Call("Laws", n), All(t, Call("Roles", n), All(u, Call("Roles", n),
                Imp(premises, Seq(Call("gamma", rho), Sp, Le, Sp, Call("productExpectation", mu, integrand))))))));
    }

    private static Formula ResultFormula()
    {
        var n = V("n");
        var rho = V("rho");
        var mu = V("mu");
        var t = V("t");
        var u = V("u");
        var laws = Call("Laws", n);
        var roles = Call("Roles", n);
        var admissible = Call("Admissible", rho, mu);
        var different = Seq(t, Sp, Neq, Sp, u);
        var distance = Call("distance", mu, t, u);
        var gamma = Call("gamma", rho);
        var lower = All(mu, laws, Imp(admissible,
            All(t, roles, All(u, roles, Imp(different, Seq(gamma, Sp, Le, Sp, distance))))));
        var common = Call("extremal", rho);
        var commonLaw = Par(Seq(V("i"), Sp, Mapsto, Sp, common));
        var attained = Seq(Call("Admissible", rho, commonLaw), Sp, Land, Sp,
            Ex(t, roles, Ex(u, roles, Seq(different, Sp, Land, Sp,
                Call("distance", commonLaw, t, u), Sp, Eq, Sp, gamma))));
        var premises = Seq(D(4), Sp, Le, Sp, n, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, rho, Sp, Land, Sp, rho, Sp, Le, Sp, new Formula.Fraction(D(1), D(8)));
        return All(n, Seq(Mathbb, Grp(V("N"))),
            All(rho, Seq(Mathbb, Grp(V("R"))),
                Imp(premises, Seq(Par(lower), Sp, Land, Sp, Par(attained)))));
    }
}
