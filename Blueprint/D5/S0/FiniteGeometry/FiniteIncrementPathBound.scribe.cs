using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.FiniteGeometry;

internal sealed class FiniteIncrementPathBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed finite increment set bounds every finite admissible path uniformly in its length and schedule.",
        H("Uniform Bounds for Finite Increment Paths"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-finite-increment-path-bound"),
            DeclarationHandle.Create("D5/S0/FiniteGeometry/FiniteIncrementPathBound.exists_uniform_bound"),
            H("A bound chosen before the path"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let E be any finite-dimensional real inner-product space and V a finite set of vectors. "
                    + "There is a nonnegative constant C, depending only on V and the fixed space, such that "
                    + "every path from zero whose first N increments lie in V and have nonpositive inner "
                    + "product with the current state has norm at most C at every index through N. "
                    + "The values after N are arbitrary. The increment rule allows equality, including the "
                    + "first step from zero. Empty sets, zero vectors and zero-dimensional spaces are included.")),
                Paragraph(Text(
                    "For each point u of the ambient unit sphere, finiteness of V gives a radius "
                    + "0 < delta <= 1/2 such that a direction within delta of u can use only increments "
                    + "with nonpositive projection onto u. Indeed every increment with positive projection "
                    + "at u retains positive projection in a sufficiently small neighborhood. Compactness "
                    + "selects finitely many open caps of radius delta/2 covering the ambient sphere. "
                    + "These caps and M = 1 + sum of the increment norms are fixed before the path.")),
                Paragraph(Text(
                    "For a finite path let R be its maximum norm. If R is positive, select a cap containing "
                    + "the direction of a maximizing state y. For its center u and radius delta put "
                    + "a = 1 - delta^2/2 and b = 1 - delta^2/8. The cap gives <u,y> > bR. "
                    + "Any state x with <u,x> >= aR has direction within delta of u, since its norm is at "
                    + "most R. Its next projection cannot increase. Below aR, one increment changes the "
                    + "projection by at most M. Induction from zero therefore gives <u,w(k)> <= aR + M "
                    + "throughout the path, including after repeated exits and returns. At y this implies "
                    + "(3 delta^2/8) R < M. Summing the positive per-cap bounds 8M/(3 delta^2) and "
                    + "adding one gives a single C for every length and every schedule. If R is zero "
                    + "the conclusion is immediate; an empty cap cover excludes R > 0.")),
                Paragraph(Text(
                    "For a fixed finite step set in an integer lattice with a fixed positive-definite quadratic form, an isometric "
                    + "change of coordinates turns the nonpositive quadratic pairing rule into this inner "
                    + "product rule. The resulting bounded ellipsoid contains only finitely many integer "
                    + "states. This is an application conditional on that change of coordinates and lattice "
                    + "discreteness; no matrix specialization or conclusion about oscillator generation is "
                    + "asserted by the theorem here."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula At(Formula w, Formula k) => new Formula.Apply(w, [k]);

    private static Formula TheoremFormula()
    {
        Formula e = F.Id("E"), v = F.Id("V"), c = F.Id("C"),
            n = F.Id("N"), w = F.Id("w"), k = F.Id("k");
        Formula wk = At(w, k);
        Formula increment = Seq(At(w, Seq(k, Sp, Plus, Sp, D(1))), Sp, Minus, Sp, wk);
        Formula step = Seq(Forall, Sp, k, Colon, Sp, Naturals, Comma, Sp,
            k, Sp, Lt, Sp, n, Sp, Rightarrow, Sp,
            Paren(Seq(increment, Sp, InMacro, Sp, v, Sp, Land, Sp,
                Langle, Sp, wk, Comma, Sp, increment, Rangle, Sp, Leq, Sp, D(0))));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, e, Colon, Sp, Seq(Operatorname, Grp(F.Id("Type"))), Comma, Sp,
                Seq(OpenBracket, Call("NormedAddCommGroup", e), CloseBracket), Comma, Sp,
                Seq(OpenBracket, Call("InnerProductSpace", Reals, e), CloseBracket), Comma, Sp,
                Seq(OpenBracket, Call("FiniteDimensional", Reals, e), CloseBracket), Comma),
            Seq(Forall, Sp, v, Colon, Sp, Call("Finset", e), Comma, Sp,
                Exists, Sp, c, Colon, Sp, Reals, Comma, Sp,
                D(0), Sp, Leq, Sp, c, Sp, Land),
            Seq(Forall, Sp, n, Colon, Sp, Naturals, Comma, Sp,
                w, Colon, Sp, Naturals, Sp, To, Sp, e, Comma, Sp,
                At(w, D(0)), Sp, Eq, Sp, D(0), Sp, Rightarrow),
            Seq(Paren(step), Sp, Rightarrow),
            Seq(Forall, Sp, k, Colon, Sp, Naturals, Comma, Sp,
                k, Sp, Leq, Sp, n, Sp, Rightarrow, Sp,
                Call("norm", wk), Sp, Leq, Sp, c, Dot),
        ]));
    }
}
