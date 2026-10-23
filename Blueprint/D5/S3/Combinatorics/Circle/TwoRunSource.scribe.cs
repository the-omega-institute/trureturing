using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class TwoRunSourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual centered doubling source with one cyclic sign run of each kind admits a complete physical-label ordering at its maximum step magnitude.",
        H("Actual two-run sources, genuine periods and physical repetitions"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-two-run-complete-order"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TwoRunSource.exists_order"),
                H("A complete order in the maximum-magnitude strip"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k>0 and let t be any natural number. Set N=2^k-1, c(n)=centered(N,2^n*t), e=minimalPeriod(doubleStep(N),c(0)), s=SourceWidth.actualSource(k,t), and A=max over every physical i:Fin(k) of |s(i)|. The intrinsic selector TwoRun(k,t) means c(0)=0, or c(0) is nonzero and exactly one i:Fin(e) satisfies c(i)<0<c(finRotate(e)(i)). Then there is a word with word.Perm(List.finRange(k)) and SourceWidth.InStrip(s,A,0,word), and 0<=A<=(2^k-2)/2. SourceWidth.inStrip_prefix supplies every natural prefix index, including empty, full and overlength prefixes. Equal source values remain separate physical occurrences.")),
                    Paragraph(Text(
                        "The source is the actual centered dyadic orbit, with no unit, primitive-period, lower bound on k beyond positivity, or size restriction on t. The original centered_full_period gives the k-return. The pinned minimal-period theorems derive 0<e<=k and e dividing k. A nonzero periodic orbit cannot meet zero, since zero is absorbing. On the finite cyclic period, the positive set and its successor preimage have equal cardinality. Consequently the number of negative-to-positive crossings equals the number of positive-to-negative crossings. The selected unique crossing therefore gives one of each. This proves the occurrence count directly, without choosing a sign-run cut.")),
                    Paragraph(Text(
                        "Every same-sign centered-double successor doubles exactly. If A<2c(i), its successor cannot equal 2c(i), because every successor magnitude is bounded by A. The centered bounds and odd modulus force this occurrence to cross from positive to negative. Similarly A<-2c(i) forces a negative-to-positive crossing. Thus each genuine period has at most one doubled-large physical occurrence of either sign. This inference uses the actual source dynamics; it is not an assumed ordering or a free dyadic row.")),
                    Paragraph(Text(
                        "The unsigned potential u(s)=s+N when s<0 and u(s)=s otherwise satisfies u(doubleStep(N,s))-u(s)=s by the original unsigned_step. The original path_range and path_sum telescope this identity around the genuine closed period, giving its exact integer sum zero. This is stronger than a congruence and is what permits complete zero-total words to be concatenated at height zero.")),
                    Paragraph(Text(
                        "Put m=k/e. The physical map Theta(j,i)=j*e+i, for (j,i):Fin(m) x Fin(e), is the canonical finProdFinEquiv followed by finCongr(m*e=k); its inverse is quotient and remainder. This uses the identity period rotation. Its bijectivity certifies disjoint blocks and complete coverage of all Fin(k) labels. Periodicity identifies each block's values with the genuine period. TwoLargeOrdering.exists_order is applied to each physical block with the common capacity A. Perm.flatMap_left preserves every physical occurrence when the resulting words are concatenated, and inStrip_append preserves all their intermediate heights. Applying the two-large premises to the entire repeated row would be invalid: k=6,t=9 already repeats both large signs.")),
                    Paragraph(Text(
                        "The zero branch retains all labels with zero weights. Positive k=1 and k=2, effective modulus one, nonunits, arbitrary repetitions, singleton sign runs, short periods and cyclic seams are included by the statement. The proof gives a sufficient source condition and a complete construction at the maximum step magnitude. Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671, asks for the half-modulus capacity for every original source. That full conjecture remains open here. No optimal-width infrastructure, literature novelty or official uniqueness is asserted."))),
                DescribeRole.Theorem)), []));
}
