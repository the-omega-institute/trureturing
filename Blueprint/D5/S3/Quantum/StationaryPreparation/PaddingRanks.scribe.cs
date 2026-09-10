using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PaddingRanksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula a = Id("a"), h = Id("h"), b = Id("b"), r = Id("r"), chosen = Call("maximalHead",a);
        Formula cap = Call("count",h,a), dimension = Sub(Call("boxCard",a),cap);
        Formula gram = Call("paddingGram",h,a), normalized = Call("normalizedPaddingGram",h,a);
        Formula zeroTail = Call("zeroTail",a,h), concrete = Id("occupation5040");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact individual and aggregate ranks of the actual padding Gram.",
            H("Exact Padding Gram Ranks"),Blocks(
                Paragraph(Text(
                    "A is finite with decidable equality, h is a letter, and a is any occupation multiset. " +
                    "R(a) is the dependent product of Fin(count(i,a)+1); boxCard(a) is the product " +
                    "over all letters i of count(i,a)+1. T(a,h) restricts that product to the tail " +
                    "letters unequal to h, and zeroTail(a,h) is its all-zero element. All ranks " +
                    "below are complex matrix ranks. paddingGram, normalizedPaddingGram, paddingBlock, " +
                    "and the exact occupationSplit are the actual vector matrices defined in PaddingBlocks.")),
                T("padding_block_rank_zero",Setup(Eq(Rank(Call("paddingBlock",h,a,zeroTail)),D(1))),
                    "The prescribed diagonal has one nonzero entry at head index zero. " +
                    "The two lower-ones factors are invertible, so the zero-tail block has rank one."),
                T("padding_block_rank_positive",Setup(All("b",Call("T",a,h),Imp(Ne(b,zeroTail),
                    Eq(Rank(Call("paddingBlock",h,a,b)),Add(cap,D(1)))))),
                    "For a nonzero tail all real difference pivots are strictly positive. " +
                    "The block therefore has full rank count(h,a)+1, also when count(h,a)=0."),
                T("padding_gram_rank",Setup(Eq(Rank(gram),dimension)),
                    "Reindex the actual complete occupation Gram by (head,tail), and combine the " +
                    "prescribed factors with blockDiagonal. Diagonal rank counts its nonzero entries. " +
                    "The zero entries correspond exactly to (j,zeroTail) with j nonzero; this set " +
                    "has count(h,a) elements. Subtracting from the actual occupation carrier gives " +
                    "the displayed aggregate rank. This conclusion is a matrix-rank equality."),
                T("normalized_padding_gram_rank",Setup(Eq(Rank(normalized),dimension)),
                    "The positive normalization diagonal preserves rank on both sides."),
                T("maximal_padding_gram_rank",Setup(Imp(Eq(cap,Call("maximumCapacity",a)),
                    Eq(Rank(normalized),Sub(Call("boxCard",a),Call("maximumCapacity",a))))),
                    "maximumCapacity(a) denotes Finset.univ.sup(a.count). This source specialization " +
                    "has the explicit maximality premise. The general block and aggregate theorems " +
                    "hold for any chosen head."),
                T("zero_padding_gram_rank",Types(All("h",Id("A"),Eq(
                    Rank(Call("normalizedPaddingGram",h,D(0))),D(1)))),
                    "For the all-zero occupation, the actual normalized Gram has rank one."),
                T("occupation_5040_padding_gram_rank",And(
                    Eq(Rank(Call("paddingGram",Id("none"),concrete)),Add(D(1),Mul(D(1,1),D(5)))),
                    Eq(Rank(Call("normalizedPaddingGram",Id("none"),concrete)),D(5,6))),
                    "occupation5040 is the existing CoherentHistorySchmidt.occupation5040, defined as capacityOccupation(4, " +
                    "tailCapacities5040), on Option(Fin(3)); its head is none and its tail capacities " +
                    "are exactly (2,1,1). There are twelve tail occupations, eleven nonzero; the " +
                    "zero-tail rank is one and each positive-tail block has rank five. " +
                    "The actual aggregate ranks are therefore 1+11*5=56."),
                T("physical_source_moments",Chosen(All("r",Call("Multiset",Id("A")),Imp(Le(r,a),Eq(
                    Call("sourceMoment",a,chosen,Call("physicalGate",a),Call("paddingInitial",a),
                        Call("physicalFinal",a),r),
                    Call("if",Eq(Call("tailCount",chosen,r),D(0)),D(1),D(0)))))),
                    "With nonempty A, PaddingBlocks identifies B's actual prefix-derived normalized " +
                    "memories with C's embedded padding vectors for the chosen physicalGate and initial " +
                    "vector. Thus B's source moments are one exactly on the legal head axis and zero elsewhere. " +
                    "The inner product has the normalized residual first and common physicalFinal second."),
                T("physical_source_gram_rank",Chosen(Eq(Rank(Call("normalizedGram",a,chosen,
                    Call("physicalGate",a),Call("paddingInitial",a))),
                    Sub(Call("boxCard",a),Call("maximumCapacity",a)))),
                    "The identified B normalized Gram of the actual C circuit has product-minus-maximum " +
                    "rank. The identification and the rank are proved; neither is an assumption."))));
    }

    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s),[..xs]);
    private static Formula Rank(Formula m) => Call("rank",m);
    private static Formula Types(Formula f) => All("A",Id("Type"),Imp(And(Call("Fintype",Id("A")),Call("DecidableEq",Id("A"))),f));
    private static Formula Setup(Formula f) => Types(All("h",Id("A"),All("a",Call("Multiset",Id("A")),f)));
    private static Formula Chosen(Formula f) => Types(Imp(Call("Nonempty",Id("A")),All("a",Call("Multiset",Id("A")),f)));
    private static Formula All(string n, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,f);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x,FormulaLogicOperator.And,y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x,FormulaLogicOperator.Implies,y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
    private static DocumentBlock T(string name, Formula f, string text) => Describe.Lean(
        DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create("D5/S3/Quantum/StationaryPreparation/PaddingRanks."+name),
        H(name),StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))));
}
