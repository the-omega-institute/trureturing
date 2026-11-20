using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class ZelinskyRadicalComponentConjecture11Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/zelinsky2026smallcomponent");
    private static readonly LibraryNoteRef Compression =
        LibraryNoteRef.Create("D5/L/Scale/lichtman2018primitive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Almost every primitive non-deficient integer satisfies the component condition.",
        H("Zelinsky's Conjecture 11 is false"),
        Blocks(
            Describe.Lean(DescribeId.Create("exceptional-bound"),
                DeclarationHandle.Create(Prefix + "exceptional_bound"),
                H("A uniform exceptional-set estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source, Compression),
                Blocks(
                    Paragraph(Text("There are a positive constant K and a natural threshold X0 such that "
                        + "for every natural X>=X0, the number of positive primitive "
                        + "non-deficient integers n<=X outside radicalComponentSet(2) "
                        + "is at most K*X^(39/40). This estimate concerns the "
                        + "exceptional set for the radical component condition.")),
                    Paragraph(Text("Write h(n)=sigma(n)/n. For a natural parameter "
                        + "M>=100, first count up to "
                        + "M^40. The initial interval n<=M^39 contributes at most "
                        + "M^39. Integers divisible by some b^2 with b>M contribute "
                        + "at most 2*M^40/(M+1). Outside these sets, write n=b^2*a "
                        + "with a squarefree and b<=M. Then n<=M^2*rad(n), and a "
                        + "prime occurring at least twice has its full next prime "
                        + "power at most M^4. Failure of the component condition "
                        + "therefore forces the largest prime factor above M^18.")),
                    Paragraph(Text("Put g=gcd(a,b), r=b^2*g and t=a/g. Then "
                        + "n=r*t, r<=M^3, and t is squarefree and coprime to r. "
                        + "A prime factor of t in [M,M^8] supplies a unitary "
                        + "squarefree divisor d in that interval. If none exists, "
                        + "split t=s*v into primes below M and primes above M^8. "
                        + "The latter part has at most 40 prime factors. If s<M, "
                        + "then u=r*s<=M^4 is a proper divisor, so sigma(u)<=2u-1. "
                        + "Writing z as the sum of 1/p over the primes of v gives "
                        + "z<=40/M^8 and h(v)*(1-z)<=1. Non-deficiency of n then "
                        + "forces 1<=2u*z, contradicting 80u<M^8. Thus s>=M, "
                        + "and a minimal subproduct supplies M<=d<=M^2.")),
                    Paragraph(Text("The compression mapping n to n/d follows the "
                        + "rational-gap method of Lichtman's Lemma 2.2, with d "
                        + "chosen unitary as well as squarefree. Primitivity and "
                        + "the large prime give 2<=h(n)<2+M^(-16). For a fixed "
                        + "cofactor m>1, two admissible d,e<=M^8 must therefore "
                        + "satisfy sigma(d)*e=sigma(e)*d, since distinct rational "
                        + "values have separation at least 1/(d*e). Cancel their "
                        + "common squarefree part. The remaining coprime factors "
                        + "each divide their own divisor sum, so any factor "
                        + "greater than one would be a non-deficient proper "
                        + "divisor of n. Both factors are one, giving d=e. "
                        + "Consequently there are at most M^39 compressed values. "
                        + "The three counts total at most 4*M^39. Finally choose "
                        + "M=ceil(X^(1/40))+100<=102*X^(1/40) for X>=1."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("relative-density-one"),
                DeclarationHandle.Create(Prefix + "relative_density_one"),
                H("Relative density one for sufficiently numerous subfamilies"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let S be any set of primitive non-deficient "
                    + "integers whose positive inclusive count is at least X^(79/80) "
                    + "for every sufficiently large natural X. Then the proportion "
                    + "of its members in B tends to one. Indeed, the missing count "
                    + "is at most K*X^(39/40), so its proportion is at most "
                    + "K*X^(-1/80), which tends to zero. No closure property or "
                    + "independence assumption on S is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 11"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("In section 3, Conjecture 11 asserts "
                    + "lim (B intersect C)(X)/C(X)=0, where C is the set of "
                    + "primitive non-deficient integers and B consists of the "
                    + "positive integers n with p^(v_p(n)+1)<2*rad(n) for every "
                    + "prime divisor p. Counts use inclusive positive bounds."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The limit in Conjecture 11 is one, contradicting zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The odd squarefree lower bound with the "
                    + "empty excluded prime set gives C(X)>=X^(79/80) eventually. "
                    + "The relative density comparison therefore gives "
                    + "(B intersect C)(X)/C(X) tending to one. Uniqueness of limits "
                    + "refutes Conjecture 11. The same comparison applies to the "
                    + "odd family and to each family avoiding finitely many primes, "
                    + "giving the separate refutations of Conjectures 13 and 15."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zelinsky-2026-conjectures-11-13-15"),
                    ResolutionKind.Refuted,
                    additionalMembers: [
                        DeclarationHandle.Create(
                            "D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.result"),
                        DeclarationHandle.Create(
                            "D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture15.result")])))));
}
