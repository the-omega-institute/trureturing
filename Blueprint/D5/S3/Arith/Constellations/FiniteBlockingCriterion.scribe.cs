using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Constellations;

internal sealed class FiniteBlockingCriterionDocument : IScribeDocumentDefinition
{
    private const string TheoremGid =
        "D5/S3/Arith/Constellations/FiniteBlockingCriterion.finite_blocking_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite integer constellation cannot be completely blocked by primes larger "
            + "than the constellation itself.",
        H("Finite Blocking Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-blocking-criterion"),
                DeclarationHandle.Create(TheoremGid),
                H("Finite blocking criterion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite set H of integer offsets and a natural number k equal "
                            + "to its cardinality, let p range over primes larger than k. "
                            + "The forbidden residue set is the image of H under reduction "
                            + "of -h modulo p, and nu_p(H) is its cardinality.")),
                    Paragraph(Text(
                        "The conclusion has exactly three leaves: nu_p(H) is at most k, k is "
                            + "strictly less than p, and admissibility is equivalent to checking "
                            + "nu_q(H) < q only for primes q at most k. The equivalence states in "
                            + "both directions that primes above k cannot give complete residue coverage.")),
                    Paragraph(Text(
                        "ASSUMED-UNVERIFIED: source lines 626-635 use the indexed offset h_1 and "
                            + "normalize h_1 to zero, but neither those lines nor Theorem 10.1 "
                            + "explicitly state k > 0 or that H is nonempty. The Lean statement "
                            + "therefore remains a valid generalized claim whose empty case is trivial."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula constellation = F.Id("H");
        Formula size = F.Id("k");
        Formula prime = F.Id("p");
        Formula smallPrime = F.Id("q");
        Formula finiteIntegers = Seq(
            Operatorname, Grp(F.Id("Finset")), Open, Mathbb, Grp(F.Id("Z")), Close);
        Formula primes = Seq(Mathbb, Grp(F.Id("P")));
        Formula residueCount = Seq(
            new Formula.Subscript(Nu, prime), Open, constellation, Close);
        Formula smallPrimeResidueCount = Seq(
            new Formula.Subscript(Nu, smallPrime), Open, constellation, Close);

        return Disp(Seq(
            Forall, Sp, constellation, Colon, Sp, finiteIntegers, Comma, Sp,
            size, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Call("card", constellation), Sp, Eq, Sp, size, Sp, Rightarrow, Sp,
            Open,
            Open,
            Forall, Sp, prime, Sp, InMacro, Sp, primes, Comma, Esc,
            size, Sp, Lt, Sp, prime, Sp, Rightarrow, Sp,
            Open, residueCount, Sp, Leq, Sp, size, Sp, Land, Sp,
            size, Sp, Lt, Sp, prime, Close, Close, Sp, Land, Sp,
            Open, Call("IsAdmissible", constellation), Sp, Iff, Sp,
            Forall, Sp, smallPrime, Sp, InMacro, Sp, primes, Comma, Esc,
            smallPrime, Sp, Leq, Sp, size, Sp, Rightarrow, Sp,
            smallPrimeResidueCount, Sp, Lt, Sp, smallPrime, Close,
            Close, Dot));
    }
}
