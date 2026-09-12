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
        Formula emissionStatement = Chosen(All("r", Occupation, Imp(And(Le(r,a),Ne(r,D(0))),
            WithV(Eq(At(Id("V"),PhiAt(r)),PrescribedImage(r))))));
        Formula terminalStatement = Chosen(WithV(Eq(At(Id("V"),PhiAt(D(0))),TerminalImage())));
        Formula j = Id("j"), rj = At(r,j), cj = At(Id("c"),j);
        Formula dependencyStatement = Chosen(All("J",Id("Type"),Imp(Call("Fintype",Id("J")),
            All("r",Arrow(Id("J"),Occupation),All("c",Arrow(Id("J"),Id("Complex")),
                Imp(All("j",Id("J"),Le(rj,a)),Imp(
                    Eq(SumAt("j",Id("J"),Call("smul",cj,PhiAt(rj))),D(0)),
                    Eq(SumAt("j",Id("J"),Call("smul",cj,
                        Call("if",Eq(rj,D(0)),TerminalImage(),PrescribedImage(rj)))),D(0)))))))));
        Formula headPositive = new Formula.Relation(D(0),FormulaRelationOperator.LessThan,
            Call("count",chosen,a));
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
                    "rank. The identification and the rank are proved; neither is an assumption."),
                Paragraph(Text(
                    "For the following statements A is also nonempty. Write h=maximalHead(a) and " +
                    "d=proposedDimension(a). Space(I) is the complex Euclidean space indexed by I. " +
                    "The displayed normalizedResidual is the actual prefix-derived residual for " +
                    "physicalGate(a) and paddingInitial(a), divided by ofReal(residualScale(r)); " +
                    "residualScale(r) is sqrt(NatToReal(multiplicity(card(r),r))). The initial " +
                    "padding vector is scaled once by the inverse of residualScale(a).")),
                Paragraph(Text(
                    "TensorProduct(Complex,E,F) is the tensor product over the complex numbers, " +
                    "and tmul(Complex,x,y) puts the letter vector x first and the memory vector y " +
                    "second. LinearIsometry(Complex,E,F) denotes the complex linear isometries " +
                    "from E to F. For the tensor product of the two displayed orthonormal bases, " +
                    "repr maps a tensor to coordinates indexed by (letter,memory). Its inverse, " +
                    "regarded as a linear isometry, is composed with the existing emission. " +
                    "Thus the local V below is fixed by a and is independent of r and time. " +
                    "NatToReal casts a natural number to the reals; ofReal then embeds the real " +
                    "square root into the complex numbers. smul is complex scalar multiplication.")),
                T("physical_normalized_emission",emissionStatement,
                    "For a legal nonzero remaining occupation, the actual fixed circuit has the " +
                    "prescribed square-root emission amplitudes. Its all-word output gives the " +
                    "normalized letter equations. Applying the tensor basis representation " +
                    "assembles those coordinates into the displayed equality. Absent letters " +
                    "have count zero, so their summands vanish even though erase is defined for them."),
                T("physical_normalized_terminal_emission",terminalStatement,
                    "The normalized zero residual is the embedded padding basis vector at none. " +
                    "The actual gate fixes the joint basis vector (h,none), so this terminal " +
                    "memory emits h and remains unchanged. This equality includes a=0 and " +
                    "requires no positive head count."),
                T("physical_normalized_dependencies",dependencyStatement,
                    "Let J be any finite type, r any family of legal residual occupations, and c " +
                    "any complex coefficients. Repetitions and zero residuals are allowed. Apply " +
                    "the same complex linear isometry V to the assumed zero sum. For each index, " +
                    "the terminal emission equality supplies the zero branch and the nonzero " +
                    "emission equality supplies the other branch of if. Both are required for " +
                    "the resulting prescribed tensor sum to vanish."),
                T("physical_normalized_span",Chosen(Eq(GeneratedSpan(false),MemoryTop)),
                    "The complex span of all actual legal normalized residuals is the whole " +
                    "physical memory space. Restrict the boxOccupation-indexed family to this " +
                    "subspace. Its inner products give exactly the actual normalizedGram. " +
                    "physical_source_gram_rank identifies its rank with d. Factoring that Gram " +
                    "through orthonormal coordinates in the subspace bounds d by its finrank; " +
                    "the ambient space has finrank d, hence the subspace is top."),
                T("physical_normalized_zero_eq_head",Chosen(Imp(headPositive,
                    Eq(PhiAt(D(0)),PhiAt(Call("replicate",D(1),chosen))))),
                    "When the chosen head has positive count, its singleton is legal. Both its " +
                    "normalized padding vector and the zero normalized padding vector are " +
                    "exactly basis(none). Their identical coordinate embeddings give equality " +
                    "of the actual residuals, including their complex phase."),
                T("physical_normalized_nonterminal_span",Chosen(Imp(headPositive,
                    Eq(GeneratedSpan(true),MemoryTop))),
                    "Under the positive head-count condition, remove the zero occupation from " +
                    "the generating family. Every nonzero generator remains, and the zero " +
                    "generator equals the legal nonzero head singleton by the preceding equality. " +
                    "The full span result therefore gives the same whole memory space. For a=0 " +
                    "the memory dimension is one and the nonterminal family is empty; the " +
                    "positive head-count condition excludes that case."))));
    }

    private static Formula Occupation => Call("Multiset",Id("A"));
    private static Formula Memory => Call("Space",Call("Fin",Call("proposedDimension",Id("a"))));
    private static Formula MemoryTop => Call("top",Call("Submodule",Id("Complex"),Memory));
    private static Formula PhiAt(Formula r) => Call("normalizedResidual",Id("a"),
        Call("maximalHead",Id("a")),Call("physicalGate",Id("a")),Call("paddingInitial",Id("a")),r);
    private static Formula Tensor(Formula x, Formula y) => Call("tmul",Id("Complex"),x,y);
    private static Formula TerminalImage() => Tensor(Call("basis",Call("maximalHead",Id("a"))),PhiAt(D(0)));
    private static Formula PrescribedImage(Formula r) => SumAt("i",Id("A"),
        Call("smul",Call("ofReal",Seq(Sqrt,Grp(Seq(Frac,
            Grp(Call("NatToReal",Call("count",Id("i"),r))),
            Grp(Call("NatToReal",Call("card",r))))))),
            Tensor(Call("basis",Id("i")),PhiAt(Call("erase",r,Id("i"))))));
    private static Formula WithV(Formula body)
    {
        Formula a = Id("a"), complex = Id("Complex");
        Formula tensorBasis = Call("tensorProduct",Call("basisFun",Id("A"),complex),
            Call("basisFun",Call("Fin",Call("proposedDimension",a)),complex));
        Formula transport = Call("comp",Call("toLinearIsometry",Call("symm",Call("repr",tensorBasis))),
            Call("emission",Call("maximalHead",a),Call("physicalGate",a)));
        Formula type = Call("LinearIsometry",complex,Memory,
            Call("TensorProduct",complex,Call("Space",Id("A")),Memory));
        return Seq(Id("let"),Sp,Id("V"),Colon,type,Sp,F.Eq,Sp,transport,Sp,Id("in"),Sp,body);
    }
    private static Formula GeneratedSpan(bool nonterminal)
    {
        Formula r = Id("r"), v = Id("v");
        Formula equality = Eq(v,PhiAt(r));
        Formula predicate = And(Le(r,Id("a")),nonterminal ? And(Ne(r,D(0)),equality) : equality);
        Formula witness = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("r"),Occupation,predicate);
        return Call("span",Id("Complex"),Seq(OpenBrace,v,Colon,Memory,Sp,Mid,Sp,witness,CloseBrace));
    }
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f,[..xs]);
    private static Formula Arrow(Formula x, Formula y) => Seq(x,Sp,To,Sp,y);
    private static Formula SumAt(string n, Formula t, Formula f) =>
        Seq(new Formula.Subscript(Sum,Seq(Id(n),Colon,t)),Grp(f));

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
