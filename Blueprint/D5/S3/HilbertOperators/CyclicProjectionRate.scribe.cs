using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class CyclicProjectionRateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HilbertOperators/CyclicProjectionRate.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/badeagrivauxmuller2010alternating");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear regularity exactly characterizes uniform geometric convergence of a finite cyclic product, with the inclination energy rate.",
        H("Linear regularity and cyclic projection rates"), Blocks(
            Describe.Lean(DescribeId.Create("cyclic-linear-regularity"),
                DeclarationHandle.Create(Prefix + "LinearRegular"), H("Same-family residual observation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let k be an RCLike field and H a complete inner product space over k, with independent universes. Let Us be a nonempty finite ordered list of closed subspaces, m its length, M the infimum of its members, P the actual orthogonal projection onto M, and T the existing cycle of Us, whose first listed factor acts first. R(Us,ell) means that for every x in H there is a member U of Us such that ell times the norm of x-Px is at most the norm of x-P_U x. The witnessing member can depend on x. Every projection refers to this same actual family."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cyclic-inclination-energy-rate"),
                DeclarationHandle.Create(Prefix + "geometric_rate"), H("Inclination energy rate"),
                StatementSource.FromAuthor(Disp(RateFormula())),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("The displayed estimate holds for every natural n, including zero, and every x in H whenever zero is less than ell, ell is at most one, and R(Us,ell) holds. The scalar ell is any admissible lower bound, without an infimum or an angle parameter.")),
                    Paragraph(Text("For one cycle starting at z, write E for the drop in squared norm. Projection Pythagoras makes E nonnegative and bounds each successive step by the square root of E. Induction along the actual list, using contractivity of complementary projections, bounds each member residual at the initial z by m times the square root of E. Squaring yields the member residual bound by m squared times E.")),
                    Paragraph(Text("The common projection p=Px belongs to every listed subspace and is fixed by the cycle. Apply the member estimate to x-p. The regularity witness then forces a loss of at least ell squared divided by m squared of the squared distance to M. Nested orthogonal projections show PTx=Px. Induction on n gives the displayed rate with the same P and T."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclic-uniform-rate-classification"),
                DeclarationHandle.Create(Prefix + "linear_regular_iff_uniform_geometric"),
                H("Exact uniform geometric classification"), StatementSource.FromAuthor(Disp(ClassificationFormula())),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("For this fixed actual family, a positive regularity constant at most one exists if and only if a real q with zero at most q and q less than one gives the squared-error estimate for every natural n and every vector. The forward direction chooses q=1-ell squared divided by m squared.")),
                    Paragraph(Text("Conversely, put a=sqrt(q) and ell=(1-a)/m. The n=1 estimate bounds the norm of Tx-Px by a times the norm of x-Px. A member U maximizing the initial residual exists because the actual list is finite and nonempty. Contractivity and telescoping bound the complete displacement by m times this maximal member residual. The triangle inequality therefore proves R(Us,ell), and zero is less than ell and ell is at most one.")),
                    Paragraph(Text("There is no dimension, separability, angle, closed-sum or additional contraction hypothesis. Repeated subspaces, singleton lists, top and bottom subspaces, the zero Hilbert space, ell=1 and q=0 are included. The list remains nonempty.")),
                    Paragraph(Text("Badea, Grivaux and Müller, arXiv:1006.2047, Section 4.1, give the qualitative inclination criterion for complex Hilbert spaces and at least two subspaces. The quantitative remark in Section 4.2 gives the factor sqrt(1-ell squared divided by m squared). The elementary energy and displacement proofs also cover real scalars and the listed degenerate cases."))),
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
    private static Formula Imp(Formula left, Formula right) =>
        Seq(Par(left), Sp, Rightarrow, Sp, right);

    private static Formula Error(Formula n) => new Formula.Norm(
        Seq(Call("Iterate", Call("Cycle", V("Us")), n, V("x")), Minus,
            Call("P", Call("Inter", V("Us")), V("x"))));
    private static Formula Sq(Formula a) => Seq(Par(a), Caret, Grp(D(2)));
    private static Formula Bound(Formula q) => All("n", Seq(Mathbb, Grp(V("N"))),
        All("x", V("H"), Seq(Sq(Error(V("n"))), Sp, Leq, Sp,
            Par(q), Caret, Grp(V("n")), Sp, Sq(Error(D(0))))));
    private static Formula Regular() => Call("R", V("Us"), V("ell"));
    private static Formula EllCondition() => Seq(D(0), Sp, Lt, Sp, V("ell"), Sp, Leq, Sp, D(1));
    private static Formula RateFormula() => All("ell", Seq(Mathbb, Grp(V("R"))),
        Imp(Seq(EllCondition(), Sp, Land, Sp, Regular()),
            Bound(Seq(D(1), Minus, new Formula.Fraction(Sq(V("ell")), Sq(Call("length", V("Us"))))))));
    private static Formula ClassificationFormula() => Seq(
        Par(Some("ell", Seq(Mathbb, Grp(V("R"))),
            Seq(EllCondition(), Sp, Land, Sp, Regular()))), Sp, Leftrightarrow, Sp,
        Par(Some("q", Seq(Mathbb, Grp(V("R"))),
            Seq(D(0), Sp, Leq, Sp, V("q"), Sp, Lt, Sp, D(1), Sp, Land, Sp, Bound(V("q"))))));
}
