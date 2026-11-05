using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class FiniteCyclicProjectionStrongDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HilbertOperators/FiniteCyclicProjectionStrong.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/HilbertOperators/ginat2018alternating");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The powers of each fixed finite ordered product of actual orthogonal projections converge in norm on every vector to the actual projection onto the common intersection.",
        H("Strong convergence of finite cyclic orthogonal projections"), Blocks(
            Describe.Lean(DescribeId.Create("finite-cyclic-projection-product"),
                DeclarationHandle.Create(Prefix + "cycle"), H("Ordered projection product"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For a finite ordered list Us of closed k-linear subspaces of H, Cycle(Us) is a bounded k-linear endomorphism. Cycle([]) is the identity. For a head U and tail Vs, Cycle(U::Vs) is Cycle(Vs) composed with the actual orthogonal projection P(U). Thus the first listed projection acts first, and the last listed projection acts last. The order is part of the list and remains fixed throughout iteration."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-cyclic-projection-strong-convergence"),
                DeclarationHandle.Create(Prefix + "tendsto_cycle_pow"),
                H("Convergence to the common intersection"), StatementSource.FromAuthor(Disp(EndpointFormula())),
                AssessedProvenance.FromLiterature(Background), Blocks(
                    Paragraph(Text("The universes u and v are independent. The scalar k is any RCLike field, and H is any complete inner product space over k. The list Us and initial vector x are arbitrary. Inter(Us) is the infimum of the set of subspaces occurring in Us, so membership means membership in every listed subspace. P(Inter(Us)) is its actual orthogonal projection. For every positive real epsilon there is a natural N such that every n at least N satisfies the displayed strict norm bound. N may depend on k, H, Us, x and epsilon.")),
                    Paragraph(Text("For every finite list and vector z, the squared displacement of one complete cycle is at most 2 to the power length(Us) times the drop in squared norm. Inductively split a cycle into its first projection and the remaining cycle. The projection Pythagorean identity gives the first loss; the inductive bound gives the remaining loss. The triangle inequality combines the two displacements. The factor 2 to the power length(Us) is sufficient and is not asserted sharp.")),
                    Paragraph(Text("The cycle is a contraction. A vector fixed by the cycle has equal norms through the initial projection and the remaining contraction. Equality in the projection norm bound puts the vector in the first subspace, and induction puts it in every subsequent subspace. Conversely, a vector in every subspace is fixed by every factor. Thus the fixed locus is exactly Inter(Us).")),
                    Paragraph(Text("Along the actual orbit, squared norms are nonnegative and antitone. Their successive drops tend to zero. The complete-cycle energy inequality then gives asymptotic regularity. The Hilbert space mean ergodic theorem gives convergence of the averages to the fixed-locus projection. The fixed-window convergence theorem for contractive powers transfers these averages and asymptotic regularity to convergence of the actual nonaveraged powers. Uniqueness of orthogonal projection identifies the limit with P(Inter(Us))x.")),
                    Paragraph(Text("The empty list has identity cycle and whole-space intersection. A singleton gives its orthogonal projection. Arbitrary repetitions, the zero or whole subspace, and the zero ambient space are included. There is no dimension, separability, positive-angle, closed-sum, nonzero or distinct-subspace assumption. The conclusion gives pointwise norm convergence, with no rate and no operator-norm convergence assertion.")),
                    Paragraph(Text("Ginat, arXiv:1809.05858v1, Section 4.2, Theorem 4.2 on printed page 21, states Halperin's finite-family theorem for real or complex Hilbert spaces and J at least 2, with T=P_J ... P_1. The empty and singleton cases are included in the present formal statement. The source is an exposition; Halperin's original paper is cited there but is not the directly consulted source."))),
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
        var product = Call("Cycle", V("Us"));
        var powerAtX = Seq(Par(product), Caret, Grp(V("n")), Par(V("x")));
        var target = Seq(Call("P", Call("Inter", V("Us"))), Par(V("x")));
        var error = new Formula.Norm(Seq(powerAtX, Sp, Minus, Sp, target));
        var convergence = All("epsilon", real,
            Imp(Seq(D(0), Sp, Lt, Sp, V("epsilon")),
                Some("N", nat, All("n", nat,
                    Imp(Seq(V("N"), Sp, Leq, Sp, V("n")),
                        Seq(error, Sp, Lt, Sp, V("epsilon")))))));
        var body = All("Us", Call("List", Call("ClosedSubmodule", V("k"), V("H"))),
            All("x", V("H"), convergence));
        body = Seq(Inst(Call("RCLike", V("k"))),
            Inst(Call("NormedAddCommGroup", V("H"))),
            Inst(Call("InnerProductSpace", V("k"), V("H"))),
            Inst(Call("CompleteSpace", V("H"))), body);
        return All("u", Call("UniverseLevel"), All("v", Call("UniverseLevel"),
            All("k", TypeAt("u"), All("H", TypeAt("v"), body))));
    }
}
