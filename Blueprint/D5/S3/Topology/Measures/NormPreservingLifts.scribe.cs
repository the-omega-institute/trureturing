using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class NormPreservingLiftsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/NormPreservingLifts.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Real => Call("Real");
    private static Formula Fun(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula At(string name, string arg) => Call(name, V(arg));
    private static Formula Mass(string name) => Call("totalVariationMass", At(name, "i"));
    private static Formula Lift(string name) => Seq(
        Call("map", At(name, "i"), V("p")), Sp, Eq, Sp, At("nu", "i"), Sp, Land, Sp,
        Mass(name), Sp, Eq, Sp, Mass("nu"));
    private static Formula Limit(string name) =>
        Call("Tendsto", Call("weakSignedFunctional", V(name)), V("l"), Call("nhds", V("F")));
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("K", Call("Type", V("u"))), All("L", Call("Type", V("v"))), All("I", Call("Type", V("w")))),
        Seq(Call("CompactHausdorffTotallyDisconnected", V("K")), Sp, Land, Sp,
            Call("Hausdorff", V("L")), Sp, Land, Sp, Call("BorelSpaces", V("K"), V("L")), Sp, Rightarrow),
        Seq(All("l", Call("Filter", V("I"))), All("p", Fun(V("K"), V("L"))),
            Call("Continuous", V("p")), Sp, Rightarrow),
        Seq(All("V", Fun(V("I"), Call("Set", V("L")))),
            All("nu", Fun(V("I"), Call("SignedMeasure", V("L"))))),
        Seq(All("s", Fun(V("I"), Call("SignedMeasure", V("K")))),
            All("t", Fun(V("I"), Call("SignedMeasure", V("K")))), All("C", Real),
            All("F", Call("WeakDual", Real, Call("ContinuousMap", V("K"), Real)))),
        Seq(V("C"), Sp, Ge, Sp, Num(0), Sp, Land, Sp, Grp(Seq(All("i", V("I")),
            Call("IsClopen", At("V", "i")), Sp, Land, Sp, Grp(Lift("s")), Sp, Land, Sp, Grp(Lift("t")))), Sp, Rightarrow),
        Seq(Grp(Seq(All("i", V("I")), Call("totalVariation", At("nu", "i"), Call("compl", At("V", "i"))),
            Sp, Eq, Sp, Num(0), Sp, Land, Sp, Call("toReal", Mass("nu")), Sp, Le, Sp, V("C"))), Sp, Rightarrow),
        Seq(Grp(Seq(All("f", Call("LocallyConstant", V("K"), Real)),
            Call("Eventually", V("l"), Call("FibreConstantOn", V("f"), V("p"), V("V"))))), Sp, Rightarrow),
        Seq(Limit("s"), Sp, Rightarrow, Sp, Limit("t"))
    ]));

    private static Formula VariationMapStatement() => Disp(new Formula.Aligned([
        Seq(All("X", Call("Type", V("u"))), All("Y", Call("Type", V("v"))),
            Call("MeasurableSpaces", V("X"), V("Y")), Sp, Rightarrow),
        Seq(All("s", Call("SignedMeasure", V("X"))), All("p", Fun(V("X"), V("Y"))),
            Call("Measurable", V("p")), Sp, Rightarrow),
        Seq(Call("totalVariation", Call("map", V("s"), V("p")), Call("univ")),
            Sp, Eq, Sp, Call("totalVariation", V("s"), Call("univ")), Sp, Rightarrow),
        Seq(Call("totalVariation", Call("map", V("s"), V("p"))), Sp, Eq, Sp,
            Call("map", Call("totalVariation", V("s")), V("p")))
    ]));

    private static Formula SupportedClopenStatement() => Disp(new Formula.Aligned([
        Seq(All("K", Call("Type", V("u"))), All("L", Call("Type", V("v"))),
            Call("CompactBorel", V("K")), Sp, Land, Sp,
            Call("HausdorffBorel", V("L")), Sp, Rightarrow),
        Seq(All("p", Fun(V("K"), V("L"))), Call("Continuous", V("p")), Sp, Rightarrow),
        Seq(All("V", Call("Set", V("L"))), All("A", Call("Set", V("K"))),
            Call("IsClopen", V("V")), Sp, Land, Sp, Call("IsClopen", V("A")), Sp, Rightarrow),
        Seq(All("s", Call("SignedMeasure", V("K"))), All("t", Call("SignedMeasure", V("K"))),
            Call("map", V("s"), V("p")), Sp, Eq, Sp, Call("map", V("t"), V("p")), Sp, Rightarrow),
        Seq(Call("totalVariation", V("s"), Call("compl", Call("preimage", V("p"), V("V")))),
            Sp, Eq, Sp, Num(0), Sp, Land, Sp,
            Call("totalVariation", V("t"), Call("compl", Call("preimage", V("p"), V("V")))),
            Sp, Eq, Sp, Num(0), Sp, Rightarrow),
        Seq(Call("FibreConstantOn", Call("indicator", V("A")), V("p"), V("V")), Sp, Rightarrow,
            Call("s", V("A")), Sp, Eq, Sp, Call("t", V("A")))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Norm-preserving signed lifts on compact spaces inherit a reference weak-star limit when each fixed locally constant test is eventually constant on supported projection fibres.",
        H("Arbitrary signed lifts and weak-star stability"),
        Blocks(
            Paragraph(Text(
                "K is compact Hausdorff and totally disconnected, with its Borel measurable structure. L is Hausdorff with its Borel structure. "
                + "The carrier universes u and v and index universe w are independent. The index filter l is arbitrary: neither a sequence nor a nontrivial-filter assumption is needed. "
                + "A continuous p from K to L is used as an actual measurable pushforward. The proof works without surjectivity or compactness of L, so continuous compact quotient maps are included.")),
            Paragraph(Text(
                "signedFunctional(s) is the continuous linear map from C(K,Real) to Real given by the actual vector-measure signed integral of f against s, with scalar multiplication as its bilinear pairing. "
                + "Its operator norm is bounded by the real total mass of the Hahn–Jordan totalVariation of s. SignedMeasure itself is not assigned a normed-space instance. "
                + "weakSignedFunctional(s) means pointwise application of StrongDual.toWeakDual to this functional. totalVariationMass(s) means totalVariation(s)(univ), an extended nonnegative real; toReal is used only for its finite total mass.")),
            Describe.Lean(
                DescribeId.Create("total-variation-map-of-mass"),
                DeclarationHandle.Create(Owner + "totalVariation_map_of_mass"),
                H("Preserved mass makes variation commute with pushforward"),
                StatementSource.FromAuthor(VariationMapStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "X and Y carry measurable spaces, s is an actual signed measure on X, and p is measurable. "
                    + "If pushing s forward preserves its entire total variation mass, then the positive measures totalVariation(map(s,p)) and map(totalVariation(s),p) are equal. "
                    + "The proof combines Mathlib's variation_map_le with equality of finite measures from domination and equal total mass. "
                    + "No topology, surjectivity, mass-one normalization or regularity premise is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("apply-eq-of-supported-clopen"),
                DeclarationHandle.Create(Owner + "apply_eq_of_supported_clopen"),
                H("Supported lifts agree on a fibre-constant clopen"),
                StatementSource.FromAuthor(SupportedClopenStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "K is compact with its Borel structure; L is Hausdorff with its Borel structure. The map p is continuous. "
                        + "V in L and A in K are clopen. The signed measures s and t have the same pushforward and give zero total variation to the complement of p-preimage(V). "
                        + "FibreConstantOn(indicator(A),p,V) means that p(x),p(y) in V and p(x)=p(y) imply x in A if and only if y in A. "
                        + "Then s(A)=t(A). Neither Hausdorffness of K nor surjectivity of p is needed.")),
                    Paragraph(Text(
                        "The compact image p[A intersect p-preimage(V)] is closed in L. Its preimage differs from A only off the common support. "
                        + "Zero variation on both set differences identifies each signed evaluation with its pushforward evaluation on that image.")),
                    Paragraph(Text(
                        "For a fixed finite coordinate test, each clopen atom is an A of this kind once the supported fibres are constant on those coordinates. "
                        + "Norm-preserving lifts first obtain their common positive pushforward and support from totalVariation_map_of_mass. Applying this clopen comparison gives equality of their signed atom values. "
                        + "For positive-variation atom values, convert the finite measures totalVariation(s) and totalVariation(t) with Measure.toSignedMeasure. "
                        + "Their signed pushforwards agree by the common positive pushforward; Measure.variation_toSignedMeasure preserves the same concentration hypotheses. "
                        + "The same clopen comparison then gives equality of real positive evaluations, hence equality of the finite measure values. "
                        + "This argument does not claim that variation commutes with the finite coordinate map.")),
                    Paragraph(Text(
                        "A finite sum of the reference atom errors consequently bounds every lift at once, provided that the finitely many reference evaluations converge. "
                        + "Signed weak-star convergence gives signed clopen evaluation convergence by the continuous clopen indicator. "
                        + "For positive evaluations, extract a separate probability-measure limit of the mass-one variations on a compact metric carrier and use clopen convergence for that probability limit. "
                        + "The probability limit is not identified with the variation of a signed weak-star limit. "
                        + "A finite coordinate family is fixed before choosing its tail; moving families require a new finite-stage choice. "
                        + "These are applications of the existing comparison, not a construction of the successor space, its split traces, the transfinite recursion or the final analytic endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("arbitrary-lifts-tendsto"),
                DeclarationHandle.Create(Owner + "arbitrary_lifts_tendsto"),
                H("Every norm-preserving choice has the reference limit"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each index i, s(i) and t(i) push forward to the same signed measure nu(i), and both retain exactly nu(i)'s total variation mass. "
                        + "The variation of nu(i) gives zero mass to the complement of the clopen support V(i). Its real total variation mass is at most C, where C is nonnegative. "
                        + "FibreConstantOn(f,p,V) at i means literally: for all x,y in K, p(x) and p(y) belong to V(i) and p(x)=p(y) imply f(x)=f(y). "
                        + "For each fixed locally constant real f this condition holds eventually in l; no one stage works for every f. If the s functionals converge to F in the actual weak-star topology, the t functionals converge to the same F.")),
                    Paragraph(Text(
                        "Mathlib's variation_map_le, SignedMeasure.totalVariation_eq_variation and finite-measure equality from domination and equal total mass give totalVariation(map(s,p))=map(totalVariation(s),p). "
                        + "This identity pulls the support concentration back to K. For a clopen test A, the compact image p[A intersect p-preimage(V)] is closed and hence measurable. "
                        + "Fibre constancy makes its pullback agree with A on the support. Both set differences have zero variation, so the two lifts give the same value on A. "
                        + "Applying this to all inverse images of a locally constant f makes the actual signed pushforwards along f equal. Mathlib's signed vector integral_map then gives equality of the f integrals.")),
                    Paragraph(Text(
                        "The locally constant algebra separates points on K. The existing real Stone–Weierstrass theorem supplies a locally constant g within epsilon/(2C+2) of an arbitrary continuous f. "
                        + "Once the two g integrals agree, the integral difference for f is at most 2C times the uniform approximation error. This tends to zero, including C=0. "
                        + "Adding the vanishing difference to the reference evaluation limit proves convergence on every continuous test; the existing weak-dual evaluation criterion gives the conclusion.")),
                    Paragraph(Text(
                        "Repository search found no exact all-lifts signed-measure convergence theorem in the topology or total-variation owners. The pinned Mathlib suppliers are reused directly rather than reproved. "
                        + "The new synthesis supplies the all-choices quantifier needed in the ordinary signed-measure condition (F) of the Talagrand candidate. "
                        + "It proves stability for any already given norm-preserving lifts; it does not construct lifts or prove their existence by Hahn–Banach or Riesz representation. "
                        + "It does not formalize the transfinite recursion, CH bookkeeping, Banach-space preservation theorem or Problem 8.2. No literature novelty or official acceptance of that problem is asserted."))),
                DescribeRole.Theorem))));
}
