using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class JensenSimpleRealStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simple real roots persist under uniform complex polynomial approximation.",
        H("Simple real polynomial stability"),
        Blocks(Describe.Lean(
            DescribeId.Create("simple-real-polynomial-stability"),
            DeclarationHandle.Create("D5/S3/Zeros/Jensen/JensenSimpleRealStability.simple_real_polynomial_stability"),
            H("All roots and a common derivative margin"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let p be a monic real polynomial of degree m. Assume every complex root of p is real and its derivative is nonzero. Let Q(n) be complex polynomials taking real values on the real line. For every q>=2 assume positive C and a natural N exist such that, for every n>=N, n>=1 and |Q(n)(z)-p(z)|<=C/sqrt(n) whenever |z|<=q.")),
                Paragraph(Text("Then R>=1, chi>0 and a natural N exist such that every n>=N has m distinct real zeros u(i) of Q(n), indexed injectively by Fin(m), with |u(i)|<=R and |Q(n)'(u(i))|>=chi for every i. The constants are common to all roots and all later n.")),
                Paragraph(Text("The fundamental theorem of algebra supplies the complete root multiset of p. Nonvanishing derivatives make this multiset simple. Small disjoint real intervals around all roots have opposite endpoint signs and a common derivative margin. Complex approximation on a larger disk controls derivatives on contained unit disks by the Cauchy estimate. The intermediate value theorem supplies one real zero in each interval, while separation proves injectivity.")),
                Paragraph(Text("This is the classical persistence of simple real polynomial roots, with a common quantitative derivative margin supplied by the Cauchy estimate and the intermediate value theorem. Every root is retained, including a root at zero, and m=0 is allowed. The statement constructs m simple real zeros of each approximating polynomial; a separate boundary comparison is needed to exclude additional roots in a specified disk."))),
            DescribeRole.Theorem))));

    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, F.Id("p"), Comma, Sp, F.Id("m"), Comma, Sp, F.Id("Q"), Comma,
            Sp, Call("Monic", F.Id("p")), Sp, Land, Sp,
            Call("degree", F.Id("p")), Eq, F.Id("m")),
        Seq(Sp, Land, Sp, Call("AllRootsRealSimple", F.Id("p")),
            Sp, Land, Sp, Call("RealOnReal", F.Id("Q")),
            Sp, Land, Sp, Call("ComplexApproximation", F.Id("Q"), F.Id("p")), Implies),
        Seq(Exists, Sp, F.Id("R"), Ge, Sp, D(1), Comma, Sp, Exists, Sp, F.Id("chi"), Gt, D(0),
            Comma, Sp, Exists, Sp, F.Id("N"), Comma, Sp, Forall, Sp, F.Id("n"), Ge, Sp, F.Id("N"), Comma),
        Seq(F.Id("n"), Ge, Sp, D(1), Sp, Land, Sp, Exists, Sp, F.Id("u"), Comma,
            Sp, Call("Injective", F.Id("u")), Sp, Land, Sp, Forall, Sp, F.Id("i"), Comma),
        Seq(Call("Q", F.Id("n"), Call("u", F.Id("i"))), Eq, D(0),
            Sp, Land, Sp, Call("abs", Call("u", F.Id("i"))), Le, Sp, F.Id("R"),
            Sp, Land, Sp, Call("absDerivative", F.Id("Q"), F.Id("n"), Call("u", F.Id("i"))), Ge, Sp, F.Id("chi"))
    ]));
}
