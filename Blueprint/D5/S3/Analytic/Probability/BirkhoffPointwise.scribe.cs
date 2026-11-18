using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class BirkhoffPointwiseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real integrable time averages of an ergodic probability transformation converge almost everywhere to their integral.",
        H("Birkhoff pointwise ergodic theorem"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("birkhoff-pointwise-ergodic"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BirkhoffPointwise.birkhoff_pointwise_ergodic"),
                H("Almost-everywhere convergence to the mean"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/durrett2019probability")),
                Blocks(
                    Paragraph(Text("The carrier alpha ranges over every universe u and has an arbitrary measurable-space structure. The measure mu is any probability measure. Ergodic(T,mu) is the native conjunction of measure preservation and pre-ergodicity: every null-measurable almost-invariant set is null or conull. The real observable g is only assumed integrable. No pointwise measurability, boundedness, square integrability, countability, standard Borel structure, or invertibility is required.")),
                    Paragraph(Text("For each fixed g, the conclusion holds for mu-almost every x along the complete sequence of natural times. The average at n=0 is canonically zero; for positive n it is the sum of g(T^j x) over j<n divided by n. The theorem retains empty-carrier quantification and all integrable constants, including zero. It asserts neither a common exceptional set for every g nor uniform, vector-valued, nonergodic conditional-expectation, or L1 convergence.")),
                    Paragraph(Text("For a measurable integrable f, take the finite maximum of its initial orbit sums, including the zeroth sum. Positivity of that maximum gives a one-step inequality. Integrating over its positive set, measure preservation cancels the full integrals of the maximum and its composition with T. An increasing-set limit yields the nonnegative integral of f over the set where some orbit sum is positive.")),
                    Paragraph(Text("For each level c above the mean of g, form the invariant set where orbit sums exceed n times a rational level above c arbitrarily late. Apply the maximal integral inequality to the indicator of this set times g-c. Ergodicity makes the set null or conull; the conull case contradicts the negative integral of g-c. Countably many rational levels for g and -g give the upper and lower eventual bounds, hence order convergence. Finally, an almost-everywhere equal measurable representative has the same integral, and quasi-measure preservation identifies every finite-time average almost everywhere.")),
                    Paragraph(Text("Durrett, Probability: Theory and Examples, fifth edition, Section 6.2, Theorem 6.2.1 and Lemma 6.2.2, printed pages 335–337, provide the classical mathematical reference. The Lean proof is an attributed adaptation of facebookresearch/atlas-lean, MathlibExt/Dynamics/Ergodic/Birkhoff.lean, revision a60759060b5616df0d5775b42da4d337719feb32. Its Meta Platforms copyright and complete supplier license are retained. The adaptation makes auxiliary declarations private and uses pinned Mathlib fixed-set iteration and almost-everywhere transport; the literature note separates the book citation from the code provenance.")),
                    Paragraph(Text("Symbolic frequencies, joint-product moments, context-dependent compositions and entropy-production rates require an actual probability law, ergodicity, an integrable observable, identification of its integral and the relevant orbit or boundary correspondence. This autonomous theorem supplies the convergence step once those mathematical bridges are established.")),
                    Paragraph(Text("For the literal doubling-map application, put I = [0,1), mu = volume.restrict I on the real line, and F(x) = Int.fract(2*x). Here volume is real Lebesgue measure, mu(univ) = volume(I) = 1, and F maps every real number into I. In particular F(0) = 0 and F(1/2) = 0. The interval carrier X is the actual subtype of reals belonging to I; its measure nu is Measure.comap Subtype.val volume, and its lifted dynamics is U(x) = the subtype element with real value F(x). The real inclusion iota = Subtype.val pushes nu forward to mu, by map_comap_subtype_coe. Thus the subtype presentation and the restricted real measure describe the same measured interval.")),
                    Paragraph(Text("Use the additive circle C = AddCircle 1 with its native volume of total mass one, the quotient pi(x) = (x : C), and d(y) = (2 : Nat) • y. The measurable equivalence e = AddCircle.measurableEquivIco 1 0 takes C to X; its inverse is the quotient restricted to X. Write r(y) = iota(e(y)) for the representative in [0,1). AddCircle.coe_equivIco_mk_apply gives r(pi(x)) = Int.fract(x) for every real x, while the equivalence gives pi(r(y)) = y for every circle point. On I the first identity is r(pi(x)) = x, including x = 0.")),
                    Paragraph(Text("The upstream AddCircle.measurePreserving_mk 1 0 uses volume.restrict (0,1], rather than the requested volume.restrict [0,1). The real Lebesgue measure has null singletons, so restrict_Ico_eq_restrict_Ioc identifies these two measures and makes pi measure preserving from mu to circle volume. This equality is used only for measures. To obtain the reverse transport, r composed with pi equals the identity mu-almost everywhere because mu is concentrated on I. Applying Measure.map_map and Measure.map_congr to that equality shows that r pushes circle volume to mu. The measurable embedding iota has an injective measure pushforward, so its pushforward identity also shows that e pushes circle volume to nu.")),
                    Paragraph(Text("The quotient respects addition, hence d(pi(x)) = pi(2*x). Combining this with pi(r(y)) = y and the fractional-part representative formula gives the pointwise identity r(d(y)) = F(r(y)). Taking subtype values gives e(d(y)) = U(e(y)), and iota(U(x)) = F(iota(x)) holds by the definition of U. These are pointwise semiconjugacies, without removal of endpoints. Function.Semiconj.iterate_right therefore gives, for every natural n, e(d^n(y)) = U^n(e(y)) and iota(U^n(x)) = F^n(iota(x)); for every real x in I it also gives r(d^n(pi(x))) = F^n(x). The identities include n = 0, the start 0 and the cutpoint 1/2. Equality of measures at endpoints alone would not supply these orbit identities.")),
                    Paragraph(Text("At the pinned Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679, Dynamics/Ergodic/AddCircle.lean supplies AddCircle.ergodic_nsmul with n = 2 and the discharged inequality 1 < 2. The lifted U is measurable because F is the fractional part of the measurable function x ↦ 2*x. Apply MeasurePreserving.ergodic_of_ergodic_semiconj first along e and then along iota. This yields Ergodic U nu and the actual Ergodic F mu on the real restricted measure, including measurable measure preservation of F. Neither ergodicity nor preservation of the interval map is an assumption of this application.")),
                    Paragraph(Text("Take the two fixed real observables g = indicator [0,1/2) and h = indicator [0,1/4), each with value one on its indicated half-open interval and zero elsewhere. Both are integrable under mu by integrability of the constant one and Integrable.indicator for measurable intervals. The integral_indicator_const identity reduces their integrals to the real measures of those intervals. Restricting mu intersects each interval with I, which leaves it unchanged; Real.volume_real_Ico_of_le then gives the actual integrals integral(g,mu) = 1/2 and integral(h,mu) = 1/4.")),
                    Paragraph(Text("Instantiate birkhoff_pointwise_ergodic twice with alpha = Real, this mu, T = F, the established Ergodic F mu, and respectively g and h. Intersect the two conull sets. For mu-almost every x, simultaneously the sum of g(F^j(x)) over 0 ≤ j < n divided by n tends to 1/2 and the corresponding sum for h tends to 1/4 as n tends to infinity through all natural numbers. Unfolding birkhoffAverage and birkhoffSum identifies these literal real-iterate averages; at n = 0 the sum and the canonically defined average are zero.")),
                    Paragraph(Text("This is a checked application of the existing frozen Birkhoff theorem and pinned upstream suppliers. It introduces no separately frozen interval theorem or new mathematical declaration. The common conull set here serves these two fixed indicators only: the result gives no common exceptional set for every integrable observable, no guarantee for any prescribed start, and no convergence rate. Binary expansions and their coding of orbits, rational-orbit examples, floating-point behavior, numerical simulations and SRB or Lorenz claims require their own evidence and are outside this application."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => name switch
    {
        "alpha" => Alpha,
        "mu" => Mu,
        _ => F.Id(name)
    };
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Instance(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Par(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Statement()
    {
        var integral = Call("integral", V("mu"), LambdaOf("y", V("alpha"), App(V("g"), V("y"))));
        var sequence = LambdaOf("n", Nat,
            Call("birkhoffAverage", Real, V("T"), V("g"), V("n"), V("x")));
        var convergence = Call("Tendsto", sequence, Named("atTop"), Call("nhds", integral));
        var ae = Call("Eventually", LambdaOf("x", V("alpha"), convergence), Call("ae", V("mu")));
        return Disp(new Formula.Aligned([
            Seq(All("alpha", Seq(Named("Type"), Sp, V("u"))),
                Instance(Call("MeasurableSpace", V("alpha"))),
                All("mu", Call("Measure", V("alpha"))),
                Instance(Call("IsProbabilityMeasure", V("mu")))),
            Seq(All("T", Fn(V("alpha"), V("alpha"))),
                Call("Ergodic", V("T"), V("mu")), Sp, Rightarrow,
                All("g", Fn(V("alpha"), Real)),
                Call("Integrable", V("g"), V("mu")), Sp, Rightarrow),
            ae
        ]));
    }
}
