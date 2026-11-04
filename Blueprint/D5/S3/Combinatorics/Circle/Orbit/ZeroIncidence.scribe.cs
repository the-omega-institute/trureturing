using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit;

internal sealed class ZeroIncidenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orbitwise zero sums are exactly balanced negative incidence, with an exact covering law and a coprime obstruction.",
        H("The labelled circle action and balanced negative incidence"),
        Blocks(
            Describe.Lean(DescribeId.Create("all-equal-of-adjacent"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/ZeroIncidence.all_equal_of_adjacent"),
                H("Adjacent equality makes a cyclic function constant"),
                StatementSource.FromAuthor(Disp(AdjacentEqualityFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A natural-valued function on a nonempty finite cycle is constant when its value agrees with its cyclic successor at every position."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-source-orbit-zero-balanced"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/ZeroIncidence.actualSource_orbit_zero_balanced"),
                H("Orbitwise zero is equivalent to balanced incidence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For k>0, N=2^k-1, a natural seed t, and a physical-label subset S of Fin(k), let f_i=SourceWidth.actualSource(k,t,i), let e_i be 1 exactly when f_i<0, and let n be the number of negative physical labels. For phase h, orbitSum is the integer sum of f_(i+h mod k) over i in S, while orbitNegativeCount is the corresponding number of negative labels. The theorem states that every phase sum is zero if and only if orbitNegativeCount is independent of h. Under that equivalent condition, k times the phase-zero count E equals S.card times n. If Nat.Coprime k n, the subset is empty or all of Fin(k). All Fin(k) labels remain distinct, including repeated source values and shorter numerical periods.")),
                    Paragraph(Text(
                        "Write R_i=f_i+N e_i. The centered source recurrence and SourceWidth.unsigned_step give R_(i+1)=2R_i-N e_i and hence f_(i+1)=2f_i+N(e_i-e_(i+1)). Summing over S after phase h yields C_(h+1)=2 C_h+N(E_h-E_(h+1)). If every C_h is zero, positivity of N forces adjacent E_h to agree, and cyclicity makes E_h constant. Conversely, constant E_h gives C_(h+1)=2C_h; after one finite cycle C_0=2^k C_0, so C_0 and every C_h vanish. This handles k=1, N=1, seed zero, nonunits, and arbitrary repeated source values without an extra zero-source premise.")),
                    Paragraph(Text(
                        "The covering law is a finite group-action count. Sum E_h over all h and reindex each inner sum by the translation finCycle h. Every physical i is carried bijectively through all k labels, so each member of the negative support is counted exactly once for each i in S. Therefore sum_h E_h=S.card*n; when the E_h are constant this is k*E_0=S.card*n. If k and n are coprime, Euclid gives k dividing S.card. Since 0≤S.card≤k, S.card is 0 or k, which is exactly S=∅ or S=Finset.univ.")),
                    Paragraph(Text(
                        "The all-phase hypothesis is essential. In the exact instance k=15, t=329=1+2^3+2^6+2^8, N=32767, gcd(t,N)=7, n=4, gcd(k,n)=1, and S={0,3,6,9,12}, the physical source values are [329,2632,-11711,4613,4137] and sum to zero at phase 0. A shifted list is [658,5264,9345,9226,8274] and has sum N. Across the orbit the phase sums repeat [0,N,-N], while the negative counts repeat [1,0,3]. Thus a one-phase zero subset need not be orbitwise zero; the source has period 15 while S has period 3, and no physical quotient is taken.")),
                    Paragraph(Text(
                        "For any four-bit odd-k corollary, the representative must satisfy 0≤t<N and have four distinct occupied binary positions; this excludes the all-ones and unreduced-weight cases. In the original four-gap setting all gaps are at least two and k≥8, so that qualification is automatic. The generic theorem remains valid for every seed and every negative count. It rules out nontrivial phase-robust zero-return packets when gcd(k,n)=1, but it does not rule out phase-specific packets or fullJ witnesses, and it proves no universal J existence statement."))),
                DescribeRole.Theorem)), []));
    private static Formula AdjacentEqualityFormula()
    {
        Formula k = F.Id("k"), g = F.Id("g"), h = F.Id("h");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula domain = new Formula.Apply(F.Id("Fin"), [k]);
        Formula value = new Formula.Apply(g, [h]);
        Formula successor = new Formula.Apply(new Formula.Apply(F.Id("finRotate"), [k]), [h]);
        Formula adjacent = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("h"),
            domain, new Formula.Relation(value, FormulaRelationOperator.Equal,
                new Formula.Apply(g, [successor])));
        Formula constant = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("h"),
            domain, new Formula.Relation(value, FormulaRelationOperator.Equal,
                new Formula.Apply(g, [new Formula.Number(0)])));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("k"), naturals,
            new Formula.Logic(new Formula.Relation(new Formula.Number(0), FormulaRelationOperator.LessThan, k),
                FormulaLogicOperator.Implies,
                new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("g"),
                    new Formula.TypeArrow(domain, naturals),
                    new Formula.Logic(adjacent, FormulaLogicOperator.Implies, constant))));
    }
}
