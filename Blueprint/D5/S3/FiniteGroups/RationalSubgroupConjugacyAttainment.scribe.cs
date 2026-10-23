using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class RationalSubgroupConjugacyAttainmentDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef LazorecTarnauceanu =
        LibraryNoteRef.Create("D5/L/FiniteGroups/lazorec2025subgroupconjugacy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every rational strictly between zero and one is the subgroup-conjugacy ratio of an actual finite group.",
        H("Rational Attainment of Subgroup Conjugacy Ratios"),
        Blocks(Describe.Lean(
            DescribeId.Create("rational-subgroup-conjugacy-attainment"),
            DeclarationHandle.Create(
                "D5/S3/FiniteGroups/RationalSubgroupConjugacyAttainment.rational_attainment"),
            H("The universal attainment theorem"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(LazorecTarnauceanu),
            Blocks(
                Paragraph(Text(
                    "The statement answers Problem 4.1 of Lazorec and Tărnăuceanu, "
                    + "https://arxiv.org/html/2508.14267v2#S4, "
                    + "affirmatively. Here latticeCount G is the cardinality of the whole "
                    + "subgroup lattice Subgroup G, and classCount G is the cardinality of "
                    + "its quotient by inner conjugation. FiniteGroup supplies an actual "
                    + "carrier, group structure, and finiteness proof. For every integer pair "
                    + "1 ≤ a < b the witness satisfies b classCount = a latticeCount. "
                    + "Both counts are positive: the lattice contains the trivial subgroup "
                    + "and its conjugacy quotient contains that subgroup's orbit. Thus the "
                    + "equation is equivalent to the exact rational equality in the question. "
                    + "No nilpotence, supersolvability, supplied action, subgroup-count formula, "
                    + "coprime family, or literature theorem is an assumption of the conclusion.")),
                Paragraph(Text(
                    "For a positive natural t and an already constructed finite group W, "
                    + "choose primes q and p with max(4,card W) < q < p and q dividing p−1. "
                    + "The prime supplier uses the infinitude of primes and the pinned theorem "
                    + "Nat.exists_prime_gt_modEq_one. Since p is odd, define "
                    + "n = t((p−1)/2) and s = n−1. The inequalities p > 4 and t > 0 give "
                    + "n ≥ 2 and s > 0. Construct the actual semidirect product "
                    + "V = Cyclic p semidirect Cyclic (q^s), with generator action of exact order q.")),
                Paragraph(Text(
                    "CyclicPrimePowerAction.split_counts gives classCount V = 2s+2 = 2n "
                    + "and latticeCount V = 2s+p+1 = 2n+p−1. The integer identity "
                    + "2n = t(p−1) therefore gives ratio V = t/(t+1). "
                    + "SemidirectProduct.equivProd gives card V = p q^s. Both primes exceed "
                    + "card W, so neither divides that positive cardinality; hence card W "
                    + "and card V are coprime. The coprime-product theorem applies to the "
                    + "actual direct product W × V, including its whole subgroup lattice "
                    + "and its inner-conjugacy quotient.")),
                Paragraph(Text(
                    "Induct on m to construct an actual finite group with positive latticeCount "
                    + "and ratio a/(a+m), for every positive natural a. At m=0 take the "
                    + "trivial group, whose lattice and quotient each have one element. "
                    + "For the step put t=a+m, construct the fresh factor V above, and multiply "
                    + "the ratios: (a/t)(t/(t+1)) = a/(t+1). Choosing each factor above "
                    + "the order of the accumulated product establishes the required "
                    + "coprimality at every step, without a presupposed prime family.")),
                Paragraph(Text(
                    "For the original integers use their nonnegative natural representatives "
                    + "and m=b−a. The induction yields ratio a/b with positive latticeCount. "
                    + "Cross-multiplication in the rationals and exact integer casting give "
                    + "the displayed equation. The full classification and count proofs are "
                    + "kernel dependencies of this construction. Proposition 2.2(ii) already "
                    + "states the factor counts, and Section 1 already states coprime ratio "
                    + "multiplicativity. The additional construction supplies consecutive-ratio "
                    + "factors with orders coprime to any accumulated finite group, completing "
                    + "the sufficient route proposed in Problem 4.1. The conclusion concerns "
                    + "that universal question; it makes no claim about the paper's other "
                    + "open problems or mathematical priority."))),
            DescribeRole.Theorem,
            openProblemResolutionClaim: new OpenProblemResolutionClaim(
                ProblemSlugRef.Create(
                    "lazorec-tarnauceanu-2025-rational-subgroup-conjugacy-attainment"),
                ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(F.Id(name), [.. xs]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Statement()
    {
        var a = F.Id("a"); var b = F.Id("b"); var w = F.Id("W");
        var group = Call("Carrier", w);
        var body = Seq(
            b, Star, Call("integerCast", Call("classCount", group)),
            Eq,
            a, Star, Call("integerCast", Call("latticeCount", group)));
        body = Ex("W", Call("FiniteGroup"), body);
        body = new Formula.TypeArrow(Seq(a, Lt, b), body);
        body = new Formula.TypeArrow(Seq(D(1), Le, Sp, a), body);
        return Disp(All("a", F.Id("Integers"), All("b", F.Id("Integers"), body)));
    }
}
