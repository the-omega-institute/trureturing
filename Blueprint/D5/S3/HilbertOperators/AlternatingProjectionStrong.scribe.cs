using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class AlternatingProjectionStrongDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HilbertOperators/AlternatingProjectionStrong.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/HilbertOperators/bauschkedeutschhundal2007alternating");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual powers of two orthogonal projections converge in norm on every vector to the projection onto the intersection, in an arbitrary complete real or complex Hilbert space.",
        H("Strong convergence of alternating orthogonal projections"), Blocks(
            Paragraph(Text("For a closed k-linear subspace U of H, P(U) denotes the actual orthogonal projection onto U from H to H. Comp(A,B) applies B first and then A. Inf(U,V) denotes the closed linear intersection. Powers are powers of bounded endomorphisms: the zeroth power is the identity, and applying the nth power agrees with n iterations of the same map.")),
            Describe.Lean(DescribeId.Create("alternating-projection-strong-convergence"),
                DeclarationHandle.Create(Prefix + "tendsto_alternating_projection_pow"),
                H("Actual nonaveraged powers"), StatementSource.FromAuthor(Disp(EndpointFormula())),
                AssessedProvenance.FromLiterature(Background), Blocks(
                    Paragraph(Text("The universes u and v, the RCLike scalar k, and the complete inner product space H are arbitrary. For all closed k-linear subspaces U and V and every x in H, set T=P(U) composed with P(V). Then the sequence T to the power n applied to x converges in the norm topology to P(Inf(U,V)) applied to x. The displayed epsilon statement is precisely this pointwise norm convergence; N can depend on the vector, both subspaces and epsilon.")),
                    Paragraph(Text("For the same actual orbit x_n=T^n x, apply the orthogonal-projection Pythagorean identity at x_n and at P(V)x_n. The triangle inequality bounds the squared full-step displacement by twice the drop in squared orbit norm. The squared norms are nonnegative and antitone, so the monotone convergence theorem gives their limit and their successive drops tend to zero. Squeezing the squared increments and taking square roots proves x_(n+1)-x_n tends to zero.")),
                    Paragraph(Text("For each fixed positive m, telescope finitely many increments to obtain x_(n+i)-x_n tending to zero for every i below m. Linearity identifies T^n applied to the m-term Cesàro average, minus x_n, with the average of these finitely many shifted differences. This error tends to zero with m fixed. Contractivity bounds the distance of the transported average from a fixed vector by its original average error, uniformly in n. Given epsilon, choose m from Cesàro convergence first, then choose n from the fixed-window error. No interchange of two limits or Cauchy conclusion from square summability is used.")),
                    Paragraph(Text("The product is a contraction. Its fixed vectors are exactly U intersect V: a fixed vector lies in U, and equality through the two projection norm bounds forces it into V by the characterization of equality in the orthogonal-projection norm bound. Conversely, each vector in both subspaces is fixed. The Hilbert space mean ergodic theorem supplies Cesàro convergence to the fixed-locus projection. Uniqueness of orthogonal projection identifies that projection with the actual intersection projection, giving the endpoint used in the fixed-window estimate.")),
                    Paragraph(Text("The statement includes zero ambient space, zero or whole subspaces, coincident subspaces, arbitrary infinite dimension, nonseparability and zero Friedrichs angle. It assumes no closed sum, positive angle, finite dimension, separability, convergence rate, prior convergence or supplied decomposition. It asserts convergence for each vector in the norm topology, and supplies no operator-norm convergence or uniform rate.")),
                    Paragraph(Text("The classical result is von Neumann's alternating-projection theorem, stated in Theorem 1.1 of Bauschke, Deutsch and Hundal, arXiv:0710.2387v1. Badea, Grivaux and Müller, arXiv:1006.2047v1, equation (1.1), gives the same strong-convergence formula and discusses the separate operator-norm question."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => StrataLint.Scribe.FormulaDsl.Id(name);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);
    private static Formula Imp(Formula left, Formula right) =>
        Seq(Par(left), Sp, Rightarrow, Sp, right);
    private static Formula TypeAt(string level) =>
        Seq(Operatorname, Grp(V("Type")), Underscore, Grp(V(level)));
    private static Formula EndpointFormula()
    {
        var real = Seq(Mathbb, Grp(V("R")));
        var nat = Seq(Mathbb, Grp(V("N")));
        var pU = Call("P", V("U"));
        var pV = Call("P", V("V"));
        var powerAtX = Seq(Par(Call("Comp", pU, pV)), Caret, Grp(V("n")), Par(V("x")));
        var target = Seq(Call("P", Call("Inf", V("U"), V("V"))), Par(V("x")));
        var error = new Formula.Norm(Seq(powerAtX, Sp, Minus, Sp, target));
        var convergence = All("epsilon", real,
            Imp(Seq(D(0), Sp, Lt, Sp, V("epsilon")),
                Some("N", nat, All("n", nat,
                    Imp(Seq(V("N"), Sp, Leq, Sp, V("n")),
                        Seq(error, Sp, Lt, Sp, V("epsilon")))))));
        var body = All("U", Call("ClosedSubmodule", V("k"), V("H")),
            All("V", Call("ClosedSubmodule", V("k"), V("H")), All("x", V("H"), convergence)));
        body = Seq(Inst(Call("RCLike", V("k"))),
            Inst(Call("NormedAddCommGroup", V("H"))),
            Inst(Call("InnerProductSpace", V("k"), V("H"))),
            Inst(Call("CompleteSpace", V("H"))), body);
        return All("u", Call("UniverseLevel"), All("v", Call("UniverseLevel"),
            All("k", TypeAt("u"), All("H", TypeAt("v"), body))));
    }
}
