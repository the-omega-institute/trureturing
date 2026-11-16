using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class LcmPowerCollisionCountableDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/fankobayashimolnar2025family");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct prime LCM power thresholds collide at only countably many real parameters kappa>1.",
        H("Countable null sets of collision parameters"),
        Blocks(
            Describe.Remark(
                DescribeId.Create("threshold-definitions"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lcmPowerF"),
                H("The threshold function and its prime value sets"),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Fan, Kobayashi and Molnar, Definition 4.2, define F(kappa,x,a) "
                    + "as log(((x^(a+1)-1)^kappa-(x^a-1)^kappa)/"
                    + "((x^(a+1)-x)^kappa-(x^a-x)^kappa))/(kappa*log(x)). "
                    + "The Lean function used here is the existing lcmPowerF. "
                    + "Their Definition 4.19 associates to a prime p the set "
                    + "E_p={F(kappa,p,j): j is a natural number at least one}.")))),
            Describe.Lean(
                DescribeId.Create("pair-collisions-countable-null"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCountable.collision_parameters_countable_null"),
                H("Two distinct primes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For natural primes p and q with p distinct from q, the set of real "
                        + "kappa>1 for which there are natural i,j at least one satisfying "
                        + "F(kappa,p,i)=F(kappa,q,j) is countable and has Lebesgue measure zero.")),
                    Paragraph(Text(
                        "For fixed positive indices, both functions are real analytic on (1,infinity). "
                        + "A zero power base contributes a locally constant zero function there. "
                        + "All other bases have analytic real powers, and the numerator and "
                        + "denominator differences are strictly positive.")),
                    Paragraph(Text(
                        "Put r=(x^a-1)/(x^(a+1)-1), s=(x^a-x)/(x^(a+1)-x), and "
                        + "L=log((x^(a+1)-1)/(x^(a+1)-x))/log(x). For positive natural m, "
                        + "F(m,x,a)=L+(log(1-r^m)-log(1-s^m))/(m*log(x)), with 0<=s<r<1. "
                        + "The logarithmic correction divided by r^m tends to -1. "
                        + "If p<q, then r(q,j)<1/q<=1/(p+1)<=r(p,i). "
                        + "Identical functions would have equal limits L and equal corrections "
                        + "after division by their base logarithms. Scaling by r(p,i)^m "
                        + "would give both -1/log(p) and zero as the same limit, a contradiction. "
                        + "The analytic identity theorem makes each fixed-index equality set "
                        + "discrete in (1,infinity), hence countable. Take the countable union over indices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-prime-collisions-countable-null"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCountable.all_collision_parameters_countable_null"),
                H("Simultaneous separation for almost every parameter"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The set of real kappa>1 admitting any collision between two distinct "
                    + "natural primes at positive natural indices is countable and has "
                    + "Lebesgue measure zero. Consequently, for Lebesgue almost every real "
                    + "kappa, if kappa>1 then every two distinct primes have disjoint sets E_p "
                    + "and E_q. This follows by a countable union over the prime pairs. "
                    + "Together with the separate density theorem, this shows that the "
                    + "exceptional parameters can be dense while having measure zero."))),
                DescribeRole.Theorem))));
}
