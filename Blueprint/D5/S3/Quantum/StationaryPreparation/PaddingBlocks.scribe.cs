using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PaddingBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula h = Id("h"), a = Id("a"), b = Id("b"), j = Id("j"), k = Id("k"), r = Id("r");
        Formula cap = Count(h,a), headIndex = Call("Fin",Add(cap,D(1)));
        Formula split = Call("occupationSplit",h,a), l = Call("lowerOnes",cap);
        Formula gram = Call("paddingGram",h,a), normalized = Call("normalizedPaddingGram",h,a);
        Formula diagonal = Call("normalizationDiagonal",a);
        Formula weights = Call("diagonal",Lam("j",headIndex,Call("ofReal",Delta(Call("val",j)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual padding occupation blocks and their prescribed difference factorization.",
            H("The Prescribed Padding Gram Factorization"),Blocks(
                Paragraph(Text(
                    "A is a finite type with decidable equality, h is a letter, and a is an arbitrary " +
                    "occupation multiset. Its capacities are count(i,a), hence nonnegative. " +
                    "R(a)=TailBox(a.count) is the dependent product of Fin(count(i,a)+1). " +
                    "T(a,h) is the same dependent product restricted to letters i unequal to h. " +
                    "The selected h need not be maximal for the block identities. All matrix " +
                    "scalars are complex; blockMass and blockDifference are real. Nat subtraction " +
                    "j-1 is truncated at zero. val denotes the natural value of a Fin index.")),
                T("occupationSplit",Setup(Eq(split,Call("piSplitAt",h,
                    Lam("i",Id("A"),Call("Fin",Add(Count(Id("i"),a),D(1))))))),
                    "The existing dependent-function equivalence sends r to (r(h), its tail). " +
                    "Its inverse restores exactly these bounded coordinates."),
                T("blockOccupation",Tail(All("j",N,Eq(Occ(j),Call("headSlice",h,
                    Call("boxOccupation",a,Call("inverseApply",split,Call("pair",D(0),b))),j)))),
                    "The zero-head box representative fixes the actual tail. headSlice replaces " +
                    "only its head count. Scalar masses may use any natural j; actual block " +
                    "vectors use j in Fin(count(h,a)+1). inverseApply(e,x) means e.symm(x)."),
                T("block_occupation_index",Tail(All("j",headIndex,Eq(Occ(Call("val",j)),
                    Call("boxOccupation",a,Call("inverseApply",split,Call("pair",j,b)))))),
                    "The head slice is exactly the occupation of the inverse box index. " +
                    "Thus every matrix vector below is an actual legal paddingResidual."),
                T("block_occupation_tail",Tail(All("j",N,
                    Eq(Call("tailCount",h,Occ(j)),Call("tailSum",b)))),
                    "The tail cardinality is the sum of the actual bounded tail coordinates."),
                T("blockMass",Tail(All("j",N,Eq(Mass(j),
                    Call("NatToReal",Call("multiplicity",Call("card",Occ(j)),Occ(j)))))),
                    "This is m_j=M(j,b), the exact occupation-word multiplicity, included in the reals."),
                T("blockDifference",Tail(All("j",N,Eq(Delta(j),Call("if",Eq(j,D(0)),
                    Mass(D(0)),Sub(Mass(j),Mass(Sub(j,D(1)))))))),
                    "if(P,x,y) is the ternary conditional. The diagonal starts with m_0, " +
                    "then the consecutive differences m_j-m_(j-1)."),
                T("lowerOnes",All("H",N,All("j",Call("Fin",Add(Id("H"),D(1))),
                    All("k",Call("Fin",Add(Id("H"),D(1))),Eq(
                        At(Call("lowerOnes",Id("H")),j,k),Call("if",Le(k,j),D(1),D(0)))))),
                    "The prescribed matrix has literal ones on and below the diagonal and zero above it."),
                T("paddingBlock",Tail(Eq(Block,Call("gram",Id("Complex"),
                    Lam("j",headIndex,Call("paddingResidual",h,a,Occ(Call("val",j))))))),
                    "The block is the complex Gram of actual C padding vectors with this tail."),
                T("paddingGram",Setup(Eq(gram,Call("gram",Id("Complex"),Lam("r",Box,
                    Call("paddingResidual",h,a,Call("boxOccupation",a,r)))))),
                    "The aggregate scaled Gram uses the existing complete occupation index R(a)."),
                T("normalizedPaddingGram",Setup(Eq(normalized,Call("gram",Id("Complex"),Lam("r",Box,
                    Call("normalizedPadding",h,a,Call("boxOccupation",a,r)))))),
                    "The normalized Gram uses the same actual vectors divided by their positive word-count scales."),
                T("padding_gram_eq_diagonal",Setup(Eq(gram,Mul(Mul(diagonal,normalized),diagonal))),
                    "The existing normalizationDiagonal has entries sqrt(M(r)), included in the complex numbers. " +
                    "The inner product conjugates its first operand; these real diagonal entries are unchanged. " +
                    "This is exactly B=DGD on the actual vectors."),
                T("padding_gram_rank_eq",Setup(Eq(Call("rank",gram),Call("rank",normalized))),
                    "The positive diagonal is invertible, so both Gram ranks agree."),
                T("padding_block_entry",Tail(All("j",headIndex,All("k",headIndex,
                    Eq(At(Block,j,k),Call("ofReal",Mass(Call("min",Call("val",j),Call("val",k)))))))),
                    "Entries in a fixed tail block are exactly m_min(j,k)."),
                T("padding_gram_blocks",Setup(Eq(Call("reindex",gram,split,split),
                    Call("blockDiagonal",Lam("b",TailBox,Block)))),
                    "blockDiagonal has index (head,tail). Its entry is this tail's block when the " +
                    "two entire tails are equal, and zero otherwise. This identifies the actual " +
                    "aggregate matrix, including distinct tails of equal cardinality."),
                T("lower_ones_det",All("H",N,Eq(Call("det",Call("lowerOnes",Id("H"))),D(1))),
                    "The lower triangular diagonal consists of ones."),
                T("padding_block_factorization",Tail(Eq(Block,Mul(Mul(l,weights),Call("transpose",l)))),
                    "Expanding the literal matrix product sums consecutive differences up to min(j,k). " +
                    "The finite telescoping identity gives exactly m_min(j,k). The transpose is " +
                    "ordinary transpose, as in the source; the factor's entries are real ones and zeros."),
                T("block_difference_pos",Tail(Imp(Ne(b,Call("zeroTail",a,h)),All("j",N,Lt(D(0),Delta(j))))),
                    "For a positive tail, each difference is the existing strictly positive last-tail " +
                    "mass of the actual head slice. This includes the initial difference at j=0."),
                T("block_mass_strict",Tail(Imp(Ne(b,Call("zeroTail",a,h)),All("j",N,
                    Imp(Lt(D(0),j),Lt(Mass(Sub(j,D(1))),Mass(j)))))),
                    "For j>0 the positive difference proves the strict growth required by the source's " +
                    "ratio argument. No division by a zero head index is used."),
                T("block_difference_zero_tail",Setup(All("j",N,Eq(
                    Call("blockDifference",h,a,Call("zeroTail",a,h),j),
                    Call("if",Eq(j,D(0)),D(1),D(0))))),
                    "For zero tail every head occupation has multiplicity one; exactly the initial pivot survives."),
                Paragraph(Text(
                    "For the following identifications A is also nonempty. The existing maximalHead(a), " +
                    "physicalGate(a), physicalMemoryEquiv(a), physicalResidual(a,r), and physicalFinal(a) " +
                    "are C's actual chosen construction. proposedDimension(a) is the product of capacities " +
                    "plus one, minus the maximum capacity. E(a) is coordinateEmbedding(physicalMemoryEquiv(a).toEmbedding). " +
                    "The B names residualMemory, normalizedResidual, sourceMoment and normalizedGram retain " +
                    "their existing prefix-derived meanings; the following equalities identify the two families.")),
                T("paddingInitial",Chosen(Eq(Call("paddingInitial",a),Call("smulC",
                    Call("inv",Call("ofReal",Call("residualScale",a))),Call("physicalResidual",a,a)))),
                    "This is exactly C's chosen normalized initial vector, in Space(Fin(proposedDimension(a)))."),
                T("padding_residual_identification",Chosen(All("r",Multi,Imp(Le(r,a),Eq(
                    Physical("residualMemory",r),Call("physicalResidual",a,r))))),
                    "C's proved local residual steps give the output of every suffix. B's residual output " +
                    "has the same coefficients and terminal memory. Suffix injectivity identifies the actual " +
                    "vectors, with no identity or rank assumption."),
                T("normalized_padding_identification",Chosen(All("r",Multi,Imp(Le(r,a),Eq(
                    Physical("normalizedResidual",r),At(Call("E",a),
                        Call("normalizedPadding",Call("maximalHead",a),a,r)))))),
                    "The positive normalization scale is the same and the coordinate embedding is complex linear."),
                T("padding_source_moment_identification",Chosen(All("r",Multi,Imp(Le(r,a),Eq(
                    Call("sourceMoment",a,Call("maximalHead",a),Call("physicalGate",a),Call("paddingInitial",a),
                        Call("physicalFinal",a),r),Call("paddingMoment",Call("maximalHead",a),a,r))))),
                    "E(a) sends the padding sink to physicalFinal(a) and preserves the ordered inner product."),
                T("padding_normalized_gram_identification",Chosen(Eq(
                    Call("normalizedGram",a,Call("maximalHead",a),Call("physicalGate",a),Call("paddingInitial",a)),
                    Call("normalizedPaddingGram",Call("maximalHead",a),a))),
                    "The actual prefix-derived B Gram equals the actual normalized padding Gram entry by entry."))));
    }

    private static Formula Multi => Call("Multiset",Id("A"));
    private static Formula Box => Call("R",Id("a"));
    private static Formula TailBox => Call("T",Id("a"),Id("h"));
    private static Formula Block => Call("paddingBlock",Id("h"),Id("a"),Id("b"));
    private static Formula Occ(Formula j) => Call("blockOccupation",Id("h"),Id("a"),Id("b"),j);
    private static Formula Mass(Formula j) => Call("blockMass",Id("h"),Id("a"),Id("b"),j);
    private static Formula Delta(Formula j) => Call("blockDifference",Id("h"),Id("a"),Id("b"),j);
    private static Formula Physical(string name, Formula r) => Call(name,Id("a"),Call("maximalHead",Id("a")),
        Call("physicalGate",Id("a")),Call("paddingInitial",Id("a")),r);
    private static Formula Types(Formula f) => All("A",Id("Type"),Imp(And(Call("Fintype",Id("A")),Call("DecidableEq",Id("A"))),f));
    private static Formula Setup(Formula f) => Types(All("h",Id("A"),All("a",Multi,f)));
    private static Formula Tail(Formula f) => Setup(All("b",TailBox,f));
    private static Formula Chosen(Formula f) => Types(Imp(Call("Nonempty",Id("A")),All("a",Multi,f)));
    private static Formula Id(string s) => F.Id(s);
    private static Formula N => Seq(Mathbb,Grp(Id("N")));
    private static Formula Call(string s, params Formula[] xs) => At(Id(s),xs);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f,[..xs]);
    private static Formula Count(Formula i, Formula a) => Call("count",i,a);
    private static Formula Lam(string n, Formula t, Formula f) => Seq(Id(n),Colon,t,Sp,Mapsto,Sp,f);
    private static Formula All(string n, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,f);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x,FormulaLogicOperator.And,y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x,FormulaLogicOperator.Implies,y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
    private static DocumentBlock T(string name, Formula f, string text) => Describe.Lean(
        DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create("D5/S3/Quantum/StationaryPreparation/PaddingBlocks."+name),
        H(name),StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))));
}
