using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class UnitaryPowerDilationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/leanpool2026unitarypowerdilation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every contraction on a complete complex Hilbert space admits a unitary dilation in which every natural power of the contraction is the compression of the corresponding power of that same unitary operator.",
        H("Common unitary dilation of all natural powers"),
        Blocks(Describe.Lean(DescribeId.Create("unitary-power-dilation"),
            DeclarationHandle.Create("D5/S3/HilbertOperators/UnitaryPowerDilation.exists_unitary_power_dilation"),
            H("Arbitrary complex Hilbert-space power dilation"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("Fix any universe u and any E in Type u with a normed additive commutative group structure, a complex inner product and completeness. Let T be a continuous complex-linear endomorphism of E with operator norm at most one. C denotes the complex numbers, N the natural numbers, and CLM(C,E,H) the continuous complex-linear maps from E to H. Norm, Inner and Adjoint denote the operator norm, complex inner product and Hilbert-space adjoint, respectively.")),
                Paragraph(Text("There exist H in the SAME Type u, its normed additive group, complex inner product and completeness structures, and continuous complex-linear maps V from E to H and U from H to H. The map V preserves the inner product of every pair x,y in E. U belongs to the unitary elements of the star algebra of bounded operators on H. For these SAME H, structures, V and U, every natural n and every x in E satisfy adjoint(V)((U^n)(V(x))) = (T^n)(x). The witnesses are chosen before n and x; there is one dilation for all natural powers, including n = 0.")),
                Paragraph(Text("The Hilbert space used in the construction is the square-summable family over the integers of pairs E plus E equipped with the Hilbert direct-sum norm: H = lp(fun i : Z => WithLp 2 (E times E)) 2. V inserts x into the first coordinate at site zero and puts zero in every other coordinate. Its adjoint extracts the first coordinate at site zero. No dimension, separability, basis or nontriviality assumption is used, so zero spaces are included.")),
                Paragraph(Text("First construct a Halmos unitary J on E plus E whose first coordinate on (x,0) is T(x). For the self-adjoint off-diagonal operator a(x,y) = (T(y),adjoint(T)(x)), the contraction bound allows continuous functional calculus to form the unitary a + I times sqrt(1-a^2). Its product with the coordinate flip has the required compression. The grading (x,y) maps to (x,-y) commutes with 1-a^2 and its square root; applying this relation to (0,x) makes the square root's first coordinate zero.")),
                Paragraph(Text("Apply this same J at every integer site and then shift only the second, environment coordinate one site to the right, leaving the system coordinates at their sites. The pointwise interaction and the routing map are linear isometry equivalences, hence their composition U is unitary. Square summability and equality of norms follow from the sum of the two coordinate norm squares and reindexing the integer sum.")),
                Paragraph(Text("For the orbit U^n(V(x)), prove one joint invariant by induction on n: the first coordinate at site zero is T^n(x), the second coordinate at site zero is zero, and every negative site is zero. At the successor step the zero second coordinate allows the local compression rule for J to advance the system to T^(n+1)(x). The site minus one is zero and supplies a zero environment input to site zero. The negative sites remain zero because both a negative site and its predecessor are zero. Thus both auxiliary parts of the invariant are needed to propagate the first part. Applying adjoint(V) extracts that first part and yields the compression identity for every n.")),
                Paragraph(Text("This is the classical unitary power-dilation existence theorem, using the cited formal source's repeated-interaction construction. The source construction uses the complex scalar I; an arbitrary RCLike scalar extension is outside this statement. No minimality, uniqueness, effective construction, finite environment or finite-dimensional witness is asserted. The larger Hilbert space may be infinite dimensional even when E is finite dimensional.")),
                Paragraph(Text("A finite total dilation space has an obstruction when a nonzero vector decays under the contraction powers. Fix complete complex Hilbert spaces E,H, bounded linear maps T:E to E and V:E to H, and a unitary U on H. Suppose the same U,V satisfy adjoint(V)(U^n(V(x)))=T^n(x) for every natural n along some x distinct from zero. If H is finite dimensional, the norms of T^n(x) cannot tend to zero. This implication uses only the stated compression along x: the n=0 identity already gives adjoint(V)(V(x))=x, so a separate isometry or contraction assumption is unnecessary for this obstruction.")),
                Paragraph(Text("The supplier is the compact-group recurrence result mapClusterPt_one_atTop_pow in Mathlib.Topology.Algebra.Group.SubmonoidClosure. Finite dimensionality makes the bounded-operator space on H proper, and its unitary group is closed and bounded, hence compact. The cited recurrence gives a strictly increasing sequence n_j tending to infinity with U^n_j tending to the identity. Apply the continuous compressed observable f(W)=||adjoint(V)(W(V(x)))||. Its value at the identity is ||x|| by the n=0 compression, whereas its value at U^n is ||T^n(x)||. The recurrent subsequence therefore tends to the positive value ||x||; it cannot also tend to zero as decay of the full sequence would require.")),
                Paragraph(Text("Thus, whenever T has a nonzero decaying vector, an exact common compression of all its powers requires infinite total dimension H. This applies existing compactness, recurrence and continuity results; it adds no frozen theorem to the displayed existence result. It provides no quantitative return time and excludes neither finite-horizon constructions nor finite-horizon approximations. The relevant premise is finite dimension of the entire dilation space. A finite environment with an infinite-dimensional system does not make the total space finite dimensional, so this argument supplies no obstruction from environment dimension alone."))),
            DescribeRole.Theorem))));

    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] xs)
    {
        var a = new List<Formula> { Operatorname, Grp(V(n)), Open };
        for (int i = 0; i < xs.Length; i++) { if (i > 0) a.AddRange([Comma, Sp]); a.Add(xs[i]); }
        a.Add(Close); return Seq([.. a]);
    }
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, Par(Seq(V(n), Colon, Sp, t)), Comma, Sp, b);
    private static Formula Some(string n, Formula t, Formula b) => Seq(Exists, Sp, Par(Seq(V(n), Colon, Sp, t)), Comma, Sp, b);
    private static Formula Inst(string n, Formula b, params Formula[] xs) => Seq(OpenBracket, Call(n, xs), CloseBracket, Sp, b);
    private static Formula Statement()
    {
        Formula compression = Call("Apply", Call("Adjoint", V("V")),
            Call("Apply", Seq(V("U"), Caret, Grp(V("n"))), Call("V", V("x"))));
        Formula powers = All("n", V("N"), All("x", V("E"), Seq(compression, Sp, Eq, Sp,
            Call("Apply", Seq(V("T"), Caret, Grp(V("n"))), V("x")))));
        Formula inner = All("x", V("E"), All("y", V("E"), Seq(
            Call("Inner", Call("V", V("x")), Call("V", V("y"))), Sp, Eq, Sp,
            Call("Inner", V("x"), V("y")))));
        Formula result = Seq(Par(inner), Sp, Land, Sp,
            Call("Unitary", V("U")), Sp, Land, Sp, Par(powers));
        result = Some("U", Call("CLM", V("C"), V("H"), V("H")), result);
        result = Some("V", Call("CLM", V("C"), V("E"), V("H")), result);
        result = Some("completeH", Call("CompleteSpace", V("H")), result);
        result = Some("innerH", Call("InnerProductSpace", V("C"), V("H")), result);
        result = Some("normedH", Call("NormedAddCommGroup", V("H")), result);
        result = Some("H", Call("Type", V("u")), result);
        result = Seq(Call("Norm", V("T")), Sp, Le, Sp, Num(1), Sp, Implies, Sp, result);
        result = All("T", Call("CLM", V("C"), V("E"), V("E")), result);
        result = Inst("CompleteSpace", result, V("E"));
        result = Inst("InnerProductSpace", result, V("C"), V("E"));
        result = Inst("NormedAddCommGroup", result, V("E"));
        return All("u", V("Universe"), All("E", Call("Type", V("u")), result));
    }
}
