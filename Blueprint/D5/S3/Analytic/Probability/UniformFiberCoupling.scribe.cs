using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class UniformFiberCouplingDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Analytic/Probability/UniformFiberCoupling.displacement_iff";

    private static Formula V(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Membership(string name, string carrier) =>
        Seq(V(name), Sp, InMacro, Sp, V(carrier));
    private static Formula All(string name, string carrier) =>
        Seq(Forall, Sp, Membership(name, carrier), Comma, Sp);
    private static Formula SumOver(string name, string carrier) =>
        Seq(Sum, Underscore, Grp(Membership(name, carrier)), Sp);
    private static Formula ReciprocalCardinality(string carrier) =>
        Seq(Frac, Grp(D(1)), Grp(Bar, V(carrier), Bar));
    private static Formula W => At(V("w"), V("x"), V("y"));

    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, V("G"), Comma, Sp, V("H"), Colon, Sp,
            Operatorname, Grp(V("Group")), Comma, Sp, Forall, Sp,
            Phi, Colon, Sp, At(Seq(Operatorname, Grp(V("Hom"))), V("G"), V("H")),
            Comma, Sp, All("t", "H")),
        Seq(Bar, V("K"), Bar, Sp, Lt, Sp, Infty, Sp, Implies, Sp,
            Forall, Sp, Rho, Colon, Sp, V("T"), Sp, To, Sp, Real, Comma),
        Seq(Open, All("d", "T"), D(0), Sp, Leq, Sp, At(Rho, V("d")), Close,
            Sp, Land, Sp, SumOver("d", "T"), At(Rho, V("d")), Sp, Eq, Sp, D(1)),
        Seq(Iff, Sp, Exists, Sp, V("w"), Colon, Sp, V("K"), Sp, Times, Sp,
            V("T"), Sp, To, Sp, Real, Comma, Sp,
            Open, All("x", "K"), All("y", "T"), D(0), Sp, Leq, Sp, W, Close),
        Seq(Land, Sp, Open, All("x", "K"), SumOver("y", "T"), W,
            Sp, Eq, Sp, ReciprocalCardinality("K"), Close),
        Seq(Land, Sp, Open, All("y", "T"), SumOver("x", "K"), W,
            Sp, Eq, Sp, ReciprocalCardinality("T"), Close),
        Seq(Land, Sp, Open, All("d", "T"), Sum, Underscore,
            Grp(Membership("x", "K"), Comma, Sp, Membership("y", "T"), Comma, Sp,
                V("x"), Caret, Grp(Minus, D(1)), V("y"), Sp, Eq, Sp, V("d")),
            Sp, W, Sp, Eq, Sp, At(Rho, V("d")), Close)
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every law on a group homomorphism fiber arises as the displacement of a uniform coupling.",
        H("Displacements of uniform couplings on group fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-fiber-coupling"),
                DeclarationHandle.Create(Result),
                H("Exact displacement laws for a uniform fiber coupling"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let G and H be groups, and take a homomorphism from G to " +
                        "H and an element t of H. Assume its kernel K is finite. Write T for " +
                        "the fiber over t. If T is empty, neither assertion can hold. There " +
                        "is no probability law on T, and the row at the identity cannot " +
                        "have its prescribed positive mass.")),
                    Paragraph(Text("To construct the coupling, give a pair the weight of its " +
                        "displacement divided by the size of K. With the first entry fixed, " +
                        "left translation permutes T. With the second entry fixed, varying " +
                        "the first entry gives a bijection from K to T. These two bijections " +
                        "give the marginals. The first bijection also gives one occurrence " +
                        "of each prescribed displacement in every row. In reverse, the " +
                        "displacement weights are sums of nonnegative entries. Their sum " +
                        "gives the total mass of the coupling."))),
                DescribeRole.Theorem))));
}
