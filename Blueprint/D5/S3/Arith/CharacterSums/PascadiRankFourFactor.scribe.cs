using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiRankFourFactorDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common value and derivative congruences determine an integer linear factor in rank four.",
        H("The rank-four root-relevant factor"),
        Blocks(
            Describe.Lean(DescribeId.Create("rank-four-root-relevant-factor"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiRankFourFactor.rank_four_root_relevant_factor"),
                H("A primitive common linear factor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let the integer rows be (q,r,s,l,m) with absolute bounds I^2, 2IJ, J^2, 3I and 3J, where I>=J>=1 and B=IJ. Write Q(T)=q+rT+sT^2 and L(T)=l+mT. The common integer lifts beta, lambda and delta give Q(beta)-lambda L(beta)=0 modulo p^3 and Q'(beta)-lambda L'(beta)-delta L(beta)=0 modulo p for each row.")),
                    Paragraph(Text("Assume p is prime, 2160B^4<p^4, 233280B^6<p^5 and 93312B^6 J<p^5. The rational row rank is at most four, including the empty family. At rank four, choose any actual baseline with L0(beta) a unit modulo p. There exist integers a>0 and n with gcd(a,n)=1, p not dividing a, and p dividing a beta-n. The primitive irreducible polynomial aT-n divides every integer pencil L0 Q-L Q0, including the baseline pencil. The baseline value a l0+n m0 is nonzero.")),
                    Paragraph(Text("A unimodular lower triangular change of columns puts every row in p^3 Z in its first coordinate and p Z in its second. The five-row determinants then lie in p^4 Z and vanish by the first gap. Four independent rows give a nonzero signed cofactor vector U. The transformed vector has divisibilities p, p^3, p^4, p^4 and p^4. The two cofactor minors U0 U2-U1^2 and U0 U4-U1 U3 lie in p^5 Z. Their exact heights force them to vanish, and the p^4 bounds on the individual cofactors force U0 to be nonzero.")),
                    Paragraph(Text("Every row annihilates U. Set theta=U1/U0 and write theta=n/a in lowest terms. The first three cofactors equal d(a^2,an,n^2) for an integer d. The third transformed cofactor equals d(n-a beta)^2. If p did not divide n-a beta, the p^4 divisibility would force all five cofactors to vanish. The row equations give a common rational value relation at theta, so Gauss's lemma gives divisibility of the full integer pencils. Reduction modulo p and the unit L0(beta) give the nonzero baseline value."))),
                DescribeRole.Theorem))));
}
