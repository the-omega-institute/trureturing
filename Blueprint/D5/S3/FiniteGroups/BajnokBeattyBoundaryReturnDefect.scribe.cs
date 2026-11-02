using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattyBoundaryReturnDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first strict reversal of the actual quotient return counts occurs exactly at the excluded short-band boundary.",
        H("Exact first reversal of the return-count comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bajnok-beatty-first-return-reversal"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyBoundaryReturnDefect.first_return_reversal"),
                H("The competing oblique relation outweighs the two horizontal endpoint fibers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let p,t be integers with p>=3 odd and t>=2. Put m=6t-1, n=p(m-3), L=p(m-1), and P=p.toNat. Use the actual integer-plane quotient maps of K19 spanned by (p(m-1)/2,p(m+1)/2), (p(m-9)/2,-p(m+9)/2), and K33 spanned by (p(m-3)/2,p(m+3)/2), (p(m-3)/2,-p(m+3)/2). W counts returns of four signed coordinate-step words. All natural conversions are justified by the proved positivity bounds; composite odd p are included.")),
                    Paragraph(Text("The theorem proves W(F19,l)<=W(F33,l) for every natural l<L, the exact balance W(F33,L)+2 choose(L,4P)=W(F19,L)+2 choose(L,P)^2, and W(F33,L)<W(F19,L). Thus L is the first length where the comparison is strictly reversed; the first unequal return counts still occur earlier at n. It addresses precisely r=p in the length n+2r excluded by the short-band theorem. The earlier positive short-band difference therefore cannot extend through this boundary.")),
                    Paragraph(Text("Since L<pm, the existing rank-one short-lattice relation mechanism still applies. In K19 the only vectors of Lee norm at most L are zero and plus/minus (p(m-5),-4p). In K33 they are zero and plus/minus (n,0): L<2n excludes larger multiples. Positivity of each first coordinate makes the three endpoint fibers disjoint, and the endpoint Lee bound supplies both directions of the actual quotient-return decomposition.")),
                    Paragraph(Text("The two horizontal endpoint fibers each have size choose(L,P)^2. The oblique endpoint has transformed subset sizes 4P and zero; its negative has complementary sizes L-4P and L. The existing word/subset equivalence and binomial symmetry therefore give choose(L,4P) for each oblique fiber. Cancelling the common zero-endpoint fiber gives the exact balance identity.")),
                    Paragraph(Text("For every natural P>=2 and L>=10P, the proof establishes choose(L,P)^2<choose(L,4P). A strict paired-factor product comparison first gives choose(M+5P,P)<choose(M,2P) for M>=5P; a nonnegative Vandermonde summand and the standard choose-product identity yield the stated inequality. Here t>=2 supplies L>=10P, so the exact fiber balance gives the strict return-count reversal. This argument introduces no assumed word count or lattice classification.")),
                    Paragraph(Text("For lengths below n, reuse the already proved first-return defect theorem, which gives equality on the same quotient maps. For every even n<=l<L, n is even and l uniquely has the form n+2r with r<p; reuse the exact short-band formula, whose extra term is nonnegative. For odd l<L<pm, every short lattice relation is a multiple of the generator sum, with even coordinate sum p(m-b). A length-l signed word has endpoint coordinate sum congruent to l modulo two. These parity conditions are incompatible, so both return fibers are empty. The three cases cover every smaller natural length, with no omitted odd lengths.")),
                    Paragraph(Text("This is a return-count result for the displayed quotient maps. It makes no additional assertion about later sign changes, eigenvalue ordering or literature novelty."))),
                DescribeRole.Theorem))));
}
