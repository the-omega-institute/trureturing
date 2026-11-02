using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FiniteOrientedAnchorRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite oriented anchors determine an arbitrary complete actual output.",
        H("Finite oriented anchor rigidity"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-oriented-anchor-rigidity"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteOrientedAnchorRigidity.finite_oriented_anchor_rigidity"),
            H("Complete intensity and one-sided anchor comparisons force linear isometry"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let H be a complex Hilbert space of dimension d at least one, with a specified orthonormal basis a indexed by Fin d. Let E be the finite complete outcome menu, and let W_e be finite-dimensional complex Hilbert spaces. The output PiLp 2 W is their Hilbert direct sum, so its squared norm is the sum of the squared channel norms. Write F_e(x)=(F(x))_e for a single arbitrary function F on all of H. No additivity, homogeneity, continuity, linearity, output-anchor orthogonality or input-dependent phase convention is assumed.")),
                Paragraph(Text("For every x in H, require sum_e ||F_e(x)||^2=||x||^2. For each basis index j and k in {0,1,2,3}, require F_e(i^k a_j)=i^k F_e(a_j) in every channel, and sum_e ||F_e(x)-F_e(i^k a_j)||^2 <= ||x-i^k a_j||^2 for every input x. The k=0 calibration is the identity. Thus the calibration is exactly the three nonzero orientations in Definition 3.1, and the comparisons use exactly the four anchors in Definition 3.2 of AURIC v80. Neither condition is extended to arbitrary phase rotations or arbitrary comparison pairs.")),
                Paragraph(Text("The inner product is conjugate linear in its first slot and linear in its second slot. Expanding the two squared distances with equal diagonal norms bounds the real part of <F(x),i^k F(a_j)> from below by that of <x,i^k a_j>. The opposite orientations give both inequalities for the real coordinate, and the two quarter turns give both inequalities for the imaginary coordinate. Consequently <F(x),F(a_j)>=<x,a_j> for every x and j. Conjugation gives the source convention <F(a_j),F(x)>=<a_j,x>. Taking x=a_i proves orthonormality of the output anchors.")),
                Paragraph(Text("Define L by sending a_j to F(a_j), using basis extension. The orthonormality just proved makes L a complex linear isometry V. Basis reconstruction and the anchor-coordinate equalities give <F(x),V(x)>=<x,x>. Together with the two equal norms this gives ||F(x)-V(x)||^2=0. Hence F(x)=V(x) on all inputs, including zero and arbitrary unnormalized vectors. Pointwise agreement makes V unique. The finite Hilbert adjoint satisfies V* V=I.")),
                Paragraph(Text("This is Theorem 5.1 with the complete-record interpretation of Definitions 2.1 through 3.2. The Hilbert-space and shared-reference interface is a premise; the theorem supplies no construction of that interface from physical history. Every outcome, including failure and stopping records, must be included in E. A Hilbert direct sum represents the complete record mathematically and does not grant actual coherent control between different outcome labels. The same F is used throughout, without postselection or separate phase choices for different inputs.")),
                Paragraph(Text("Full pairwise complex inner products and distances, complex linearity and continuity follow from F=V and the standard linear-isometry properties. The conclusion is on all of H, rather than only the unit sphere of Proposition 5.3. The dimension d is a natural number with the literal premise 1<=d; no dimension truncation is used. The norm expansion, basis reconstruction, orthonormal-basis isometry constructor and adjoint identity use Mathlib's existing results. The finite-anchor argument supplies their geometric hypotheses; no separate novelty claim is made for those general results."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula h = V("H"), e = V("E"), w = V("W"), a = V("a"), f = V("F");
        Formula x = V("x"), j = V("j"), k = V("k"), channel = V("e");
        Formula output = Call("PiLp", D(2), w);
        Formula anchor = Smul(new Formula.Power(V("i"), Call("val", k)), Apply(a, j));
        Formula image = Apply(f, x);
        Formula mass = All("x", h, Equal(
            SumOver("e", e, NormSq(Apply(image, channel))), NormSq(x)));
        Formula phase = All("j", Call("Fin", V("d")), All("k", Call("Fin", D(4)),
            All("e", e, Equal(Apply(Apply(f, anchor), channel),
                Smul(new Formula.Power(V("i"), Call("val", k)),
                    Apply(Apply(f, Apply(a, j)), channel))))));
        Formula comparisons = All("x", h, All("j", Call("Fin", V("d")),
            All("k", Call("Fin", D(4)), Le(
                SumOver("e", e, NormSq(Subtract(Apply(image, channel),
                    Apply(Apply(f, anchor), channel)))), NormSq(Subtract(x, anchor))))));
        Formula isometries = Call("LinearIsometry", Complexes(), h, output);
        Formula Property(Formula v) => And(
            All("x", h, Equal(Apply(f, x), Apply(v, x))),
            Equal(Call("comp", Call("adjoint", v), Call("toLinearMap", v)),
                Call("id", h)));
        Formula unique = ExistsQ("V", isometries, And(Property(V("V")),
            All("U", isometries, Imp(Property(V("U")), Equal(V("U"), V("V"))))));
        Formula result = Imp(And(mass, And(phase, comparisons)), unique);
        result = All("F", Arrow(h, output), result);
        result = All("a", Call("OrthonormalBasis", Call("Fin", V("d")), Complexes(), h), result);
        result = All("W", Arrow(e, V("Type")), Imp(All("e", e, Space(Apply(w, channel))), result));
        result = All("E", V("Type"), Imp(Call("Fintype", e), result));
        result = All("H", V("Type"), Imp(Space(h), result));
        return All("d", Naturals(), Imp(Le(D(1), V("d")), result));
    }

    private static Formula Space(Formula h) => And(Call("NormedAddCommGroup", h),
        And(Call("InnerProductSpace", Complexes(), h), Call("FiniteDimensional", Complexes(), h)));
    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsQ(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Smul(Formula a, Formula b) => Call("smul", a, b);
    private static Formula NormSq(Formula x) => new Formula.Power(Seq(Vert, Sp, x, Sp, Vert), D(2));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(V(name), Colon, type)), Sp, body);
}
