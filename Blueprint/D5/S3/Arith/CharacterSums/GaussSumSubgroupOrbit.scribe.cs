using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class GaussSumSubgroupOrbitDocument : IScribeDocumentDefinition
{
    private static Formula Over(string variable, string group, Formula term) =>
        Seq(Sum, Underscore, Grp(F.Id(variable), InMacro, Sp, F.Id(group)), Sp, term);

    private static Formula Tau(Formula shift) =>
        Call("gaussSum", F.Id("chi"), Call("mulShift", F.Id("psi"), shift));

    private static Formula Weighted(Formula point) =>
        Call("weightedOrbitSum", F.Id("H"), F.Id("rho"), F.Id("F"), point);

    private static Formula Orbit => Over("h", "H", Seq(
        Call("rho", F.Id("h")), Cdot, Sp,
        Tau(Seq(F.Id("a"), Cdot, Sp, F.Id("h")))));

    private static Formula RatioTerm(string variable) => Seq(
        Call("rho", F.Id(variable)), Cdot, Sp,
        Call("sigma", F.Id(variable)), Caret, Grp(Minus, D(1)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted orbit sums lie in the inverse-weight eigenspace for subgroup translation. Comparing this eigencharacter with that of a Gauss function gives the weighted Gauss-sum orbit formula.",
        H("Weighted subgroup orbits of Gauss sums"),
        Blocks(
            Paragraph(Text("Let A be a finite commutative ring, K a commutative ring, chi a multiplicative character from A to K, psi an additive character, H a subgroup of the unit group of A, rho a homomorphism from H to the units of K, and a any element of A. In the orbit formulas below h is coerced from H through the units of A into A. Write sigma for chi.toUnitHom.comp H.subtype. Neither a nor the subgroup cardinality needs to be invertible, and psi need not be primitive.")),
            Paragraph(Text("The new group-action ingredient applies to every function F from A to K. The output of the weighted orbit operator belongs to the inverse-rho eigenspace of the right-translation action of H on functions from A to K. The final Gauss formula uses this eigenlaw through the nonzero-weights theorem in its nonmatching branch; it is not an unused companion to the character-sum computation.")),
            Paragraph(Text("Four-slot source-bound audit registrations for the five public theorem targets remain unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/27398. No declared_validated registration status is claimed.")),
            Describe.Lean(
                DescribeId.Create("weighted-orbit-sum"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weightedOrbitSum"),
                H("The weighted orbit operator"),
                StatementSource.FromAuthor(Disp(Seq(Weighted(F.Id("a")), Eq,
                    Over("h", "H", Seq(Call("rho", F.Id("h")), Cdot, Sp,
                        Call("F", Seq(F.Id("a"), Cdot, Sp, F.Id("h")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The operator sums an arbitrary function over the unit-subgroup orbit with the indicated unit-valued weights. It uses no division by the subgroup cardinality and is defined over every commutative coefficient ring."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-orbit-right-eigenlaw"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weightedOrbitSum_mulRight"),
                H("Right translation has inverse-weight eigencharacter"),
                StatementSource.FromAuthor(Disp(Seq(
                    Weighted(Seq(F.Id("a"), Cdot, Sp, F.Id("g"))), Eq,
                    Call("rho", F.Id("g")), Caret, Grp(Minus, D(1)), Cdot, Sp,
                    Weighted(F.Id("a"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every g in H, reindex the finite sum by the subgroup bijection h maps to g*h. The homomorphism law identifies rho(g) inverse times rho(g*h) with rho(h), and associativity identifies the translated arguments. This proves the eigenlaw for arbitrary F without using any Gauss-sum API or a domain hypothesis. The inverse is taken in K units before coercion. In representation terms the operator's image lies in the inverse-weight eigenspace; it is an unnormalized character-selection operator, with no idempotence claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-gauss-subgroup-factor"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weighted_gaussSum_subgroup_factor"),
                H("Factorization over an arbitrary coefficient ring"),
                StatementSource.FromAuthor(Disp(Seq(Orbit, Eq,
                    Open, Over("h", "H", Seq(Call("rho", F.Id("h")), Cdot, Sp,
                        Call("chiInv", F.Id("h")))), Close, Cdot, Sp, Tau(F.Id("a"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here chiInv denotes the inverse multiplicative character, evaluated at h. AddChar.mulShift_mulShift identifies the shift by a*h with the successive shifts by a and h. Mathlib's gaussSum_mulShift_eq extracts chiInv(h) from each summand, and finite-sum distributivity extracts the common Gauss sum. This factorization remains valid when K has zero divisors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-unit-hom-orthogonality"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weighted_unitHom_orthogonality"),
                H("Weighted character orthogonality"),
                StatementSource.FromAuthor(Disp(Seq(Over("g", "G", RatioTerm("g")), Eq,
                    F.Id("if"), Sp, F.Id("rho"), Eq, F.Id("sigma"), Sp,
                    F.Id("then"), Sp, Call("card", F.Id("G")), Sp,
                    F.Id("else"), Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite group G and integral domain K, rho and sigma may be arbitrary homomorphisms from G to K units. Inversion is taken in the unit group and then coerced into K, so field division is unnecessary. Construct the quotient character delta as Units.coeHom composed with rho*sigma inverse. Pointwise injectivity of the unit coercion proves delta=1 if and only if rho=sigma. The genuine Mathlib API sum_hom_units then gives the displayed dichotomy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-gauss-nonzero-weights"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weighted_gaussSum_subgroup_nonzero_weights"),
                H("A nonzero Gauss orbit forces matching weights"),
                StatementSource.FromAuthor(Disp(Seq(Orbit, Neq, D(0), Sp,
                    Implies, Sp, F.Id("rho"), Eq, F.Id("sigma")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume IsDomain K and instantiate the general operator with F(b)=gaussSum chi (psi.mulShift b). Its output has inverse-rho eigencharacter by weightedOrbitSum_mulRight. Independently the Gauss-function shift law, commutativity of A and sum distributivity give the inverse-sigma eigencharacter for the same output. If the orbit value is nonzero, cancellation forces equality of the two eigencharacters at every subgroup element, hence rho=sigma. This proof actually consumes the group-action theorem and does not invoke the weighted orthogonality dichotomy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-gauss-subgroup-orbit"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weighted_gaussSum_subgroup_orbit"),
                H("The weighted orbit selects the restricted character"),
                StatementSource.FromAuthor(Disp(Seq(Orbit, Eq,
                    F.Id("if"), Sp, F.Id("rho"), Eq, F.Id("sigma"), Sp,
                    F.Id("then"), Sp, Call("card", F.Id("H")), Cdot, Sp, Tau(F.Id("a")), Sp,
                    F.Id("else"), Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume IsDomain K. The matching branch uses the general factorization and weighted orthogonality: chiInv(h) is the coercion of sigma(h) inverse, so the coefficient is the subgroup cardinality in K. The nonmatching branch uses weighted_gaussSum_subgroup_nonzero_weights by contradiction, so the live proof path is the subgroup-translation eigenlaw, then nonzero weight matching, then this final orbit formula. In positive characteristic the subgroup cardinality may itself vanish.")),
                    Paragraph(Text("The domain assumption is essential for the orthogonality step. For example the two-element character with value 3 in ZMod 8 is nontrivial but has sum 1+3=4. No orthogonality statement over arbitrary commutative coefficient rings, literature novelty claim, or assertion of a nonzero selected orbit is made."))),
                DescribeRole.Theorem))));
}
