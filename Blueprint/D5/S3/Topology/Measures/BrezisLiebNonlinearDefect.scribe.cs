using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class BrezisLiebNonlinearDefectDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula At(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Lam(string name, Formula body) =>
        Seq(Open, V(name), Sp, Mapsto, Sp, body, Close);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Norm(Formula a) => Seq(Vert, Sp, a, Vert, Sp);
    private static Formula Function => Arrow(V("Omega"), V("Complex"));
    private static Formula Family => Arrow(V("Real"), Arrow(V("Complex"), V("Real")));
    private static Formula Vn => At(V("v"), V("n"));
    private static Formula An => At(V("A"), V("n"));
    private static Formula Dn => At(V("D"), V("n"));
    private static Formula Jg => Lam("x", At(V("j"), At(V("g"), V("x"))));
    private static Formula Phi => At(V("phi"), V("epsilon"));
    private static Formula Psi => At(V("psi"), V("epsilon"));
    private static Formula Admissible => Call("admissible", V("epsilon"));
    private static Formula I(Formula h) => Call("integral", V("mu"), h);
    private static Formula Mass(Formula h) => Call("mass", h);
    private static Formula Integrable(Formula h) => Call("Integrable", h, V("mu"));
    private static Formula Tendsto(Formula h, Formula value) =>
        Call("Tendsto", h, V("atTop"), Call("nhds", value));
    private static Formula Nonnegative(Formula h) => Seq(Open, All("z", V("Complex")),
        Le(D(0), At(h, V("z"))), Close);

    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("Omega", Seq(V("Type"), Underscore, Grp(V("u")))),
            OpenBracket, Call("MeasurableSpace", V("Omega")), CloseBracket),
        Seq(All("mu", Call("Measure", V("Omega"))), All("j", Arrow(V("Complex"), V("Complex")))),
        Seq(Open, Call("Continuous", V("j")), Sp, Land, Sp,
            At(V("j"), D(0)), Sp, Eq, Sp, D(0), Close, Sp, Rightarrow),
        Seq(All("epsilon0", V("Real")), D(0), Sp, F.Lt, Sp, V("epsilon0"), Sp, Rightarrow),
        Seq(All("phi", Family), All("psi", Family)),
        Seq(Open, All("epsilon", V("Real")), Admissible, Sp, Rightarrow,
            Call("Continuous", Phi), Sp, Land, Sp, Nonnegative(Phi), Close, Sp, Rightarrow),
        Seq(Open, All("epsilon", V("Real")), Admissible, Sp, Rightarrow,
            Nonnegative(Psi), Close, Sp, Rightarrow),
        Seq(Open, All("epsilon", V("Real")), Admissible, Sp, Rightarrow,
            All("a", V("Complex")), All("b", V("Complex"))),
        Seq(Le(Norm(Sub(At(V("j"), Add(V("a"), V("b"))), At(V("j"), V("a")))),
            Add(Seq(V("epsilon"), Sp, At(Phi, V("a"))), At(Psi, V("b")))), Close, Sp, Rightarrow),
        Seq(All("M", V("NNReal")), All("g", Function), All("v", Arrow(V("Nat"), Function))),
        Seq(Call("AEStronglyMeasurable", V("g"), V("mu")), Sp, Rightarrow),
        Seq(Open, All("n", V("Nat")), Call("AEStronglyMeasurable", Vn, V("mu")), Close, Sp, Rightarrow),
        Seq(Call("AE", V("mu"), Lam("x", Tendsto(Lam("n", At(Vn, V("x"))), D(0)))), Sp, Rightarrow),
        Seq(Integrable(Jg), Sp, Rightarrow),
        Seq(Open, All("epsilon", V("Real")), Admissible, Sp, Rightarrow,
            Integrable(Lam("x", At(Psi, At(V("g"), V("x"))))), Close, Sp, Rightarrow),
        Seq(Open, All("epsilon", V("Real")), Admissible, Sp, Rightarrow,
            All("n", V("Nat")), Le(Mass(Lam("x", At(Phi, At(Vn, V("x"))))),
                Call("ofNNReal", V("M"))), Close, Sp, Rightarrow),
        Seq(Open, All("n", V("Nat")), Integrable(An), Sp, Land, Sp, Integrable(Dn), Close),
        Seq(Land, Sp, Tendsto(Lam("n", I(Lam("x", Norm(At(Dn, V("x")))))), D(0))),
        Seq(Land, Sp, Tendsto(Lam("n", I(An)), I(Jg)))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full nonlinear cancellation on arbitrary measure spaces, without separate integrability of the two terms.",
        H("Nonlinear Brézis–Lieb defect"),
        Blocks(
            Paragraph(Text("The universe u, measurable space Omega and measure mu are arbitrary. "
                + "The nonlinearity j maps Complex to Complex. The families phi and psi have type Real -> Complex -> Real. "
                + "The predicate admissible(epsilon) means 0 < epsilon and epsilon < epsilon0. "
                + "The function g has type Omega -> Complex, v has type Nat -> Omega -> Complex, and M is a finite NNReal bound. "
                + "Write A(n)(x) = j(g(x)+v(n)(x)) - j(v(n)(x)) and D(n)(x) = A(n)(x) - j(g(x)). "
                + "For a real function h on Omega, mass(h) = lintegral mu (x maps to ENNReal.ofReal(h(x))). "
                + "The coercion ofNNReal embeds M into ENNReal. Integral and Integrable use Bochner integration in the stated value space. "
                + "AE(mu,P) means that P holds mu-almost everywhere.")),
            Describe.Lean(DescribeId.Create("full-nonlinear-brezis-lieb-cancellation"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/BrezisLiebNonlinearDefect.brezis_lieb_nonlinear_defect"),
                H("Integrable cancellation and full L1 decay"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/brezislieb1983pointwise")),
                Blocks(
                    Paragraph(Text("The function j is continuous and vanishes at zero. For every admissible epsilon, "
                        + "phi(epsilon) is continuous and nonnegative, psi(epsilon) is nonnegative, and their increment inequality "
                        + "holds for every pair of complex a and b. The same finite M bounds the nonnegative integrals "
                        + "of phi(epsilon,v(n)) for every admitted epsilon and every n. The function j(g) is integrable, "
                        + "as is each psi(epsilon,g). Both g and every v(n) are almost-everywhere strongly measurable, "
                        + "and v(n) tends almost everywhere to zero.")),
                    Paragraph(Text("Every A(n) and D(n) is integrable. The integrals of norm(D(n)) tend to zero, "
                        + "and the complex integrals of A(n) tend to the integral of j(g). Individual integrability of "
                        + "j(g+v(n)) and j(v(n)) is absent. No finite or sigma-finite measure, common integrable dominator, "
                        + "uniform integrability, separate energy convergence or subsequence is assumed.")),
                    Paragraph(Text("A fixed admitted epsilon first gives integrability of A(n) through its increment bound. "
                        + "Continuity and j(0)=0 give almost-everywhere cancellation. For an arbitrary positive error coefficient, "
                        + "choose an admitted smaller coefficient. The nonnegative error is bounded by that coefficient times "
                        + "phi applied to v(n), plus psi applied to g and norm(j(g)). The common epsilon-domination theorem "
                        + "therefore yields full L1 decay. The integral norm inequality then gives the complex integral limit. "
                        + "Only fixed-epsilon integrability of the compensation term is required; it need not tend to zero with epsilon.")),
                    Paragraph(Text("This is the complex arbitrary-measure statement of Brézis–Lieb Theorem 2, "
                        + "including the separate-integrability boundary in Remark (i) and strong L1 conclusion in Remark (ii). "
                        + "The existing positive-power theorem uses the same extracted integral-control inference. "
                        + "The growth estimate and mass hypotheses still have to be established for any new integrand or application; "
                        + "the theorem supplies no additional compactness, nonvanishing or PDE existence premise."))),
                DescribeRole.Theorem))));
}
