using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Selection;

internal sealed class ContinuousMatrixOrbitCounterexampleDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(V(s), [.. xs]);
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Both(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Grp(a), Sp, Cdot, Sp, Grp(b));
    private static Formula Z(bool first, Formula x) => C(first ? "Zfirst" : "Zsecond", V("n"), x);
    private static Formula StarOf(Formula a) => C("star", a);
    private static Formula Gram(Formula a) => Mul(StarOf(a), a);
    private static Formula Identity => C("identity", V("n"));
    private static Formula Sign(Formula k) => Seq(Open, Minus, D(1), Close, Caret, Grp(k));
    private static Formula NoMultiplier(bool polar)
    {
        Formula factor = polar ? C("abs", Z(false, V("x"))) : Z(true, V("x"));
        Formula equation = Equal(Z(false, V("x")), Mul(C("U", V("x")), factor));
        Formula law = Both(C("Continuous", V("U")), Seq(All("x", V("X")), equation));
        return Seq(Neg, Sp, Exists, Sp, V("U"), Colon, Sp,
            V("X"), Sp, To, Sp, C("Mat", V("n")), Comma, Sp, law);
    }

    private static Formula Statement()
    {
        Formula n = V("n"), k = V("k"), x = V("x"), cutoff = V("N");
        Formula radius = C("radius", k), point = C("point", k);
        Formula positive = C("positivePoint", k), approximation = C("approximant", n, cutoff, x);
        Formula unitary = Both(Equal(Gram(approximation), Identity),
            Equal(Mul(approximation, StarOf(approximation)), Identity));
        Formula error = Seq(C("norm", Seq(Z(false, x), Sp, Minus, Sp, Mul(approximation, Z(true, x)))),
            Sp, Le, Sp, Seq(Frac, Grp(D(2)), Grp(Seq(cutoff, Sp, Plus, Sp, D(1)))));
        Formula pointValues = Seq(All("k", V("Nat")), Both(
            Equal(Z(true, point), Mul(radius, Identity)),
            Equal(Z(false, point), Mul(Mul(Sign(Seq(k, Plus, D(1))), radius), Identity))));
        Formula positiveValues = Seq(All("k", V("Nat")), D(1), Sp, Le, Sp, k, Sp, Implies, Sp,
            Both(Equal(Z(true, positive), Mul(Seq(Frac, Grp(D(1)), Grp(k)), Identity)),
                Equal(Z(false, positive), Mul(Seq(Frac, Grp(Sign(k)), Grp(k)), Identity))));
        Formula approximationLaw = Seq(All("N", V("Nat")), C("IsClopen", C("finiteHead", cutoff)),
            Sp, Land, Sp, C("Continuous", C("approximant", n, cutoff)), Sp, Land, Sp,
            Par(Seq(All("x", V("X")), unitary)), Sp, Land, Sp,
            Par(Seq(All("x", V("X")), error)));
        Formula gramLaw = Seq(All("x", V("X")), Equal(Gram(Z(true, x)), Gram(Z(false, x))));
        Formula modulusLaw = Seq(All("x", V("X")), Both(Seq(D(0), Sp, Le, Sp, Z(true, x)),
            Equal(C("abs", Z(false, x)), Z(true, x))));
        return Disp(new Formula.Aligned([
            Seq(All("n", V("Nat")), D(1), Sp, Le, Sp, n, Sp, Implies),
            Seq(C("IsCompact", V("literalSet")), Sp, Land, Sp, C("Nonempty", V("X")), Sp, Land, Sp,
                C("CompactSpace", V("X")), Sp, Land, Sp, C("TTwoSpace", V("X")), Sp, Land, Sp,
                C("ZeroDimensionalSpace", V("X")), Sp, Land),
            Seq(C("Continuous", C("Zfirst", n)), Sp, Land, Sp,
                C("Continuous", C("Zsecond", n)), Sp, Land),
            Seq(Both(Equal(Z(true, V("origin")), D(0)), Equal(Z(false, V("origin")), D(0))), Sp, Land),
            Seq(Par(pointValues), Sp, Land),
            Seq(Par(positiveValues), Sp, Land),
            Seq(Par(approximationLaw), Sp, Land),
            Seq(Par(gramLaw), Sp, Land),
            Seq(Par(modulusLaw), Sp, Land),
            Seq(Par(NoMultiplier(true)), Sp, Land),
            NoMultiplier(false)
        ]));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous equal-Gram matrix fields on the inverse-natural real compactum have explicit unitary approximants but no continuous multiplier or unitary polar factor.",
        H("Equal Gram fields outside one exact unitary orbit"),
        Blocks(
            Paragraph(Text("The space X is the actual subspace of the real line consisting of zero and 1/k for positive natural k. "
                + "Its inherited topology is used throughout. Mat(n) is Matrix (Fin n) (Fin n) Complex, with conjugate transpose star and the complex Euclidean operator norm. "
                + "The matrix norm is the L2Operator norm: Matrix.cstar_norm_def identifies it with the norm of Matrix.toEuclideanCLM. "
                + "Mathlib's matrix C-star construction preserves the product topology and uniformity, so continuity is continuity of every complex entry.")),
            Paragraph(Text("Write S=OnePoint Nat, radius(k)=1/(k+1), point(k)=radius(k) in X, origin=0, and positivePoint(k)=1/k for k at least one. "
                + "The map S to X sends infinity to origin and k to point(k). Its bijectivity follows from positivity and injectivity of radius; "
                + "its continuity follows from tendsto_inv_atTop_nhds_zero_nat and OnePoint.continuous_iff_from_nat. Compactness and Hausdorffness give the proved homeomorphism literalHomeomorph. "
                + "Countability and complete regularity give ZeroDimensionalSpace X through Mathlib's existing instance. No proxy space is assumed equivalent to X.")),
            Paragraph(Text("Zfirst and Zsecond in the display denote Z1 and Z2 in Lean. On S their diagonal entries are respectively zero at infinity and "
                + "radius(k), (-1)^(k+1) radius(k) at k; the fields on X are transported by literalHomeomorph.symm. "
                + "finiteHead(N) consists of point(k) with k<N, equivalently the positive points 1/k with 1<=k<=N. "
                + "approximant(n,N) has phase (-1)^k times the identity at those positive points, and the identity on the complementary tail and at origin. "
                + "The symbols identity, star, abs and norm denote the matrix identity, conjugate transpose, CFC.abs and that operator norm; scalar multiplication and matrix multiplication use the same displayed dot with their respective types. "
                + "Natural denominators and radius are cast to the complex scalars in matrix formulas and to the reals in the error bound.")),
            Describe.Lean(DescribeId.Create("equal-gram-no-continuous-multiplier"),
                DeclarationHandle.Create("D5/S3/Topology/Selection/ContinuousMatrixOrbitCounterexample.proposition10_3"),
                H("The inverse-natural counterexample in every positive dimension"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The theorem holds for every n>=1, hence for every finite n>=3. Both fields vanish at origin, are continuous, and have the stated values at every nonzero point. "
                        + "Their Gram matrices agree pointwise. The positive first field is exactly the CFC modulus of the second. "
                        + "The two nonexistence clauses quantify over all continuous matrix-valued multipliers, with no unitary assumption, and therefore also exclude continuous unitary multipliers and unitary polar factors.")),
                    Paragraph(Text("For a hypothetical multiplier U, inspect its (0,0) entry after composing with literalHomeomorph. "
                        + "The equality at point(k), followed by cancellation of the nonzero radius(k), forces this entry to equal (-1)^(k+1). "
                        + "Continuity would give a limit at infinity. Along k=2j the entry is -1 and along k=2j+1 it is +1; both index maps tend to infinity. "
                        + "Uniqueness of limits in the complex numbers would identify -1 and +1, a contradiction. "
                        + "This is the obstruction to exact alignment, even though both original fields converge to zero.")),
                    Paragraph(Text("Each finite head is clopen: its preimage in OnePoint Nat is finite, closed and open away from infinity. "
                        + "The phase of each approximant is eventually one, so it is continuous; its conjugate times itself in either order is one. "
                        + "On the head the error is zero. On the tail the scalar error is at most twice radius(k), bounded by 2/(N+1). "
                        + "The identity matrix has operator norm one in positive dimension, yielding the displayed uniform pointwise operator bound. "
                        + "The bound tends to zero independently of x and explains approximation in the uniform topology on these fields. "
                        + "A separate theorem packaged in the continuous-function-algebra supremum norm is not supplied.")),
                    Paragraph(Text("The construction is the repository's inverse-natural counterexample, using the pinned Mathlib OnePoint, matrix, norm, positivity and CFC suppliers. "
                        + "It establishes this boundary between exact alignment and approximation. The general square-fiber orbit-closure theorem and the exact original PB classification are separate results and are not established here. "
                        + "No conclusion about the broader semifinite response classification or an arbitrary incomplete Jordan domain follows from this example."))),
                DescribeRole.Theorem))));
}
