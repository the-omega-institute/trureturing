using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Hunter;
internal sealed class NCHunterPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Hunter/NCHunterPositivity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Analytic/garciavolcic2025hunter");
    public DocumentDefinition Create()
    {
        Formula n=F.Id("n"), d=F.Id("d"), k=F.Id("k"), b=F.Id("B"), g=F.Id("g");
        Formula a=F.Id("a"), c=F.Id("b"), w=F.Id("w"), u=F.Id("u"), v=F.Id("v");
        Formula i=F.Id("i"), j=F.Id("j"), x=F.Id("X"), h=F.Id("H"), t=F.Id("A");
        Formula op=Operators(h), twoD=Mul(D(2),d), zero=D(0), one=D(1);
        Formula countW=Count(w,i);
        Formula sourceX1=Seq(F.Id("X"),Underscore,Grp(D(1)));
        Formula sourceXn=Seq(F.Id("X"),Underscore,Grp(n));
        Formula sourceH=Seq(F.Id("H"),Underscore,Grp(Seq(D(2),d)));
        Formula sourceMu=Seq(Mu,Underscore,Grp(n,Comma,d));
        Formula nn=Cast(Choose(Add(Sub(n,one),d),d),R());
        Formula tt=Cast(Choose(Add(Sub(n,one),twoD),twoD),R());
        Formula muValue=Call("ite",Eqn(n,one),one,Call("ite",Call("Odd",d),
            new Formula.Fraction(tt,Mul(nn,Add(nn,one))),
            new Formula.Fraction(tt,Mul(nn,Sub(Add(nn,Cast(n,R())),one)))));
        Formula coeff=Nk(All(w,Word(n,k),Eqn(Call("coefficient",w),
            new Formula.Fraction(ProdOver(i,Fin(n),Cast(Factorial(countW),C())),Cast(Factorial(k),C())))));
        Formula wordEval=Nk(Monad(t,All(x,Arrow(Fin(n),t),All(w,Word(n,k),Eqn(Call("wordEval",x,w),
            Call("List.prod",Call("List.ofFn",Lam(j,Fin(k),At(x,At(w,j))))))))));
        Formula nchs=Nk(All(t,TypeOf(),Instance("Ring",[t],Instance("Algebra",[C(),t],
            All(x,Arrow(Fin(n),t),Eqn(Call("nchs",n,k,x),
                SumOver(w,Word(n,k),Smul(Call("coefficient",w),Call("wordEval",x,w)))))))));
        Formula residual=Nd(Hilbert(h,All(x,Arrow(Fin(n),op),Eqn(Call("residual",n,d,x),
            Sub(Call("nchs",n,twoD,x),Smul(Cast(Call("mu",n,d),C()),SumOver(i,Fin(n),Pow(At(x,i),twoD)))))),false));
        Formula gram=Nd(Eqn(Call("gram",n,d),Lam(u,Word(n,d),Lam(v,Word(n,d),
            new Formula.Fraction(ProdOver(i,Fin(n),Cast(Factorial(Add(Count(u,i),Count(v,i))),C())),Cast(Factorial(twoD),C()))))));
        Formula pure=Nd(All(w,Word(n,d),new Formula.Logic(Call("pure",w),FormulaLogicOperator.Iff,
            Seq(Exists,Sp,i,Colon,Fin(n),Comma,Sp,All(j,Fin(d),Eqn(At(w,j),i))))));
        Formula pureProjection=Nd(Eqn(Call("pureProjection",n,d),Call("Matrix.diagonal",Lam(w,Word(n,d),
            Call("ite",Call("pure",w),Cast(one,C()),Cast(zero,C()))))));
        Formula sharp=Nd(Eqn(Call("sharpGram",n,d),Sub(Call("gram",n,d),Smul(Cast(Call("mu",n,d),C()),Call("pureProjection",n,d)))));
        Formula equiv=Nd(Eqn(Call("gramWordEquiv",n,d),Call("Equiv.trans",
            Call("Equiv.prodCongr",Call("Equiv.piCongrLeft'",Call("Function.const",Fin(d),Fin(n)),Call("Fin.revPerm")),Call("Equiv.refl",Word(n,d))),
            Call("Fin.appendEquiv",d,d))));
        Formula countReverse=Nk(All(w,Word(n,k),All(i,Fin(n),Eqn(Count(At(Call("Equiv.piCongrLeft'",Call("Function.const",Fin(k),Fin(n)),Call("Fin.revPerm")),w),i),Count(w,i)))));
        Formula countCons=Nk(All(i,Fin(n),All(j,Fin(n),All(w,Word(n,k),Eqn(Count(Call("Fin.cons",i,w),j),
            Add(Call("ite",Eqn(j,i),one,zero),Count(w,j)))))));
        Formula countConst=All(n,N(),All(F.Id("m"),N(),All(i,Fin(n),Eqn(Count(Call("Function.const",Fin(F.Id("m")),i),i),F.Id("m")))));
        Formula countAppend=All(n,N(),All(a,N(),All(c,N(),All(u,Word(n,a),All(v,Word(n,c),All(i,Fin(n),
            Eqn(Count(Call("Fin.append",u,v),i),Add(Count(u,i),Count(v,i)))))))));
        Formula evalAppend=All(n,N(),All(a,N(),All(c,N(),Monad(t,All(x,Arrow(Fin(n),t),All(u,Word(n,a),All(v,Word(n,c),
            Eqn(Call("wordEval",x,Call("Fin.append",u,v)),Mul(Call("wordEval",x,u),Call("wordEval",x,v))))))))));
        Formula evalReverse=Nk(Monad(t,All(x,Arrow(Fin(n),t),Imp(SelfAdjoints(x,n),All(w,Word(n,k),
            Eqn(Call("wordEval",x,At(Call("Equiv.piCongrLeft'",Call("Function.const",Fin(k),Fin(n)),Call("Fin.revPerm")),w)),Call("star",Call("wordEval",x,w)))))),true));
        Formula wordDegree=All(n,N(),All(F.Id("m"),N(),All(w,Word(n,F.Id("m")),All(i,Fin(n),
            Eqn(Call("val",At(Call("val",Call("wordDegree",w)),i)),Count(w,i))))));
        Formula moment=All(n,N(),All(b,N(),All(g,Arrow(Fin(n),N()),All(a,Box(n,b),All(c,Box(n,b),
            Eqn(Call("factorialMoment",g,a,c),ProdOver(i,Fin(n),Cast(Factorial(Add(Add(Cast(At(a,i),N()),Cast(At(c,i),N())),At(g,i))),R()))))))));
        Formula feature=All(n,N(),All(b,N(),All(g,Arrow(Fin(n),N()),All(a,Box(n,b),All(k,Box(n,b),
            Eqn(Call("factorialFeature",g,a,k),ProdOver(i,Fin(n),Mul(
                Cast(Factorial(Add(Cast(At(a,i),N()),At(g,i))),R()),Cast(Choose(Cast(At(a,i),N()),Cast(At(k,i),N())),R())))))))));
        Formula weight=All(n,N(),All(b,N(),All(g,Arrow(Fin(n),N()),All(k,Box(n,b),
            Eqn(Call("factorialWeight",g,k),ProdOver(i,Fin(n),new Formula.Fraction(Cast(Factorial(Cast(At(k,i),N())),R()),
                Cast(Factorial(Add(At(g,i),Cast(At(k,i),N()))),R()))))))));
        Formula featurePos=All(n,N(),All(b,N(),All(g,Arrow(Fin(n),N()),All(a,Box(n,b),LtTo(zero,Call("factorialFeature",g,a,a))))));
        Formula weightPos=All(n,N(),All(b,N(),All(g,Arrow(Fin(n),N()),All(k,Box(n,b),LtTo(zero,Call("factorialWeight",g,k))))));
        Formula diagonal=All(n,N(),All(b,N(),All(d,N(),All(g,Arrow(Fin(n),N()),All(a,Degree(n,b,d),All(c,Degree(n,b,d),
            Imp(NeTo(a,c),Eqn(Call("factorialFeature",g,Call("val",c),Call("val",a)),zero))))))));
        Formula momentGram=All(n,N(),All(b,N(),All(g,Arrow(Fin(n),N()),All(a,Box(n,b),All(c,Box(n,b),
            Eqn(Call("factorialMoment",g,a,c),SumOver(k,Box(n,b),Mul(Mul(Call("factorialWeight",g,k),Call("factorialFeature",g,a,k)),
                Call("factorialFeature",g,c,k)))))))));
        Formula matrixForm=FiniteHilbertMatrix(Eqn(Call("matrixForm",F.Id("D"),v),
            SumOver(i,F.Id("I"),Inner(At(v,i),At(Parenthesized(Smul(F.Id("D"),v)),i)))));
        Formula zeroRows=FiniteHilbertMatrix(Imp(Call("Matrix.PosSemidef",F.Id("D")),Imp(Eqn(Call("matrixForm",F.Id("D"),v),zero),
            All(i,F.Id("I"),Eqn(At(Parenthesized(Smul(F.Id("D"),v)),i),zero)))));
        Formula zeroVectors=FiniteHilbertMatrix(Imp(Call("Matrix.PosDef",F.Id("D")),Imp(Eqn(Call("matrixForm",F.Id("D"),v),zero),
            All(i,F.Id("I"),Eqn(At(v,i),zero)))));
        Formula sumSucc=Nk(All(t,TypeOf(),Instance("AddCommMonoid",[t],All(F.Id("f"),Arrow(Word(n,Add(k,one)),t),
            Eqn(SumOver(w,Word(n,Add(k,one)),At(F.Id("f"),w)),SumOver(i,Fin(n),SumOver(w,Word(n,k),At(F.Id("f"),Call("Fin.cons",i,w)))))))));
        Formula residualGram=Nd(Imp(LtTo(zero,d),Hilbert(h,All(x,Arrow(Fin(n),op),Imp(SelfAdjoints(x,n),All(F.Id("h"),h,
            Eqn(Inner(F.Id("h"),At(Call("residual",n,d,x),F.Id("h"))),Call("matrixForm",Call("sharpGram",n,d),
                Lam(w,Word(n,d),At(Call("wordEval",x,w),F.Id("h")))))))))));
        Formula sharpPsd=Nd(Imp(LeTo(D(2),n),Imp(LtTo(zero,d),Call("Matrix.PosSemidef",Call("sharpGram",n,d)))));
        Formula positivity=Nd(Imp(LtTo(zero,n),Imp(LtTo(zero,d),Hilbert(h,All(x,Arrow(Fin(n),op),Imp(SelfAdjoints(x,n),
            LeTo(Smul(Cast(Call("mu",n,d),C()),SumOver(i,Fin(n),Pow(At(x,i),twoD))),Call("nchs",n,twoD,x))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The literal symmetrized word polynomial satisfies the sharp Garcia--Volcic operator bound, through a finite factorial Gram matrix and explicit inverse columns.",
            H("The sharp noncommutative Hunter inequality"),Blocks(
            Node("coefficient", "Word coefficients", coeff,
                "The coefficient is the reciprocal abelianization-fibre cardinality: the occupation-count formula gives k! divided by the product of multiplicity factorials. All words in one fibre receive the same coefficient.", true, DescribeRole.Definition),
            Node("wordEval", "Ordered evaluation", wordEval,
                "The word is evaluated in its written order using List.ofFn and List.prod. A monoid suffices; operator multiplication is composition.", true, DescribeRole.Definition),
            Node("nchs", "The NCHS polynomial", nchs,
                "Equation (3), page 2: “The noncommutative complete homogeneous symmetric (NCHS) polynomial of degree d in n (noncommuting) variables is” H_d(x_1,...,x_n) := sigma(h_d(x_1,...,x_n)). The displayed word sum is exactly this symmetrized lift, since each commutative monomial occurs once in h_d.", true, DescribeRole.Definition),
            Node("mu", "The literal sharp constant", Nd(Eqn(Call("mu",n,d),muValue)),
                "Theorem 1.1(ii), pages 2--3. The n = 1 branch is retained. Natural subtraction is truncated; division in this formula is real field division.", true, DescribeRole.Definition),
            Node("residual", "The Hunter residual", residual,
                "The residual is the literal difference of H_{2d} and the sharp multiple of the sum of even powers.", true, DescribeRole.Definition),
            Node("gram", "The word Gram matrix", gram,
                "Equation (5), page 3, uses the reciprocal fibre size of the abelianized concatenation of the reversed first word and the second word.", true, DescribeRole.Definition),
            Node("pure", "Pure words", pure,
                "A pure word consists entirely of one letter; its length can be zero in this definition.", true, DescribeRole.Definition),
            Node("pureProjection", "Projection onto pure words", pureProjection,
                "The diagonal is one exactly on the pure words, and zero on the mixed words.", true, DescribeRole.Definition),
            Node("sharpGram", "The sharp residual matrix", sharp,
                "This is the word-indexed residual matrix G minus mu times the pure-word projection.", true, DescribeRole.Definition),
            Node("gramWordEquiv", "Pairing two half-words", equiv,
                "Equiv.piCongrLeft' transports the first half through Fin.revPerm; Fin.appendEquiv then joins the two halves.", false, DescribeRole.Definition),
            Node("count_reverse", "Reversal preserves occupations", countReverse,
                "Reversal permutes positions without changing any letter multiplicity.", false, DescribeRole.Theorem),
            Node("count_cons", "The head contribution", countCons,
                "Fin.cons adds one occurrence of its head letter.", false, DescribeRole.Theorem),
            Node("count_constant", "A constant word count", countConst,
                "A constant word of length m has m occurrences of its letter.", false, DescribeRole.Theorem),
            Node("count_append", "Concatenation adds counts", countAppend,
                "The occupation_append identity gives addition of letter counts.", false, DescribeRole.Theorem),
            Node("word_eval_append", "Evaluation of concatenation", evalAppend,
                "The ordered product of a concatenation is the product of the two ordered products.", false, DescribeRole.Theorem),
            Node("word_eval_reverse", "Reversal and adjoints", evalReverse,
                "For self-adjoint letters, reversing the word gives the star of its evaluation.", false, DescribeRole.Theorem),
            Node("wordDegree", "The multidegree of a word", wordDegree,
                "The value belongs to the subtype of a : Fin n -> Fin(m+1) with sum_i (a i : Nat) = m. Each displayed val is the actual subtype or Fin projection; these coordinates determine the constructor completely.", false, DescribeRole.Definition),
            Node("factorialMoment", "Shifted factorial moments", moment,
                "This finite kernel is the product of shifted factorials.", false, DescribeRole.Definition),
            Node("factorialFeature", "Binomial factorial features", feature,
                "The feature is the product of factorials and natural binomial coefficients.", false, DescribeRole.Definition),
            Node("factorialWeight", "Positive Gram weights", weight,
                "The weights are products of positive real factorial ratios.", false, DescribeRole.Definition),
            Node("degree_feature_diagonal", "Diagonal degree features", diagonal,
                "Distinct multidegrees of equal total degree have a coordinate exceeding the other; the corresponding binomial coefficient vanishes.", false, DescribeRole.Theorem),
            Node("factorial_feature_self_pos", "Strictly positive diagonal features", featurePos,
                "Every diagonal binomial coefficient is one and every factorial is positive.", false, DescribeRole.Theorem),
            Node("factorial_weight_pos", "Strictly positive weights", weightPos,
                "Every numerator and denominator factorial is positive.", false, DescribeRole.Theorem),
            Node("factorial_moment_gram", "The finite factorial Gram identity", momentGram,
                "Vandermonde convolution gives the one-coordinate identity. Taking products gives this finite Gram factorization. No originality claim is made for the scalar identity.", true, DescribeRole.Theorem),
            Node("matrixForm", "The Hilbert-valued matrix form", matrixForm,
                "The action D dot v is Mathlib Matrix.Module scalar multiplication, not entrywise scalar multiplication. The form uses the complex inner product, conjugate-linear in its first entry.", false, DescribeRole.Definition),
            Node("positive_form_zero_rows", "Zero form implies zero rows", zeroRows,
                "A positive semidefinite matrix factors as B-star times B. The form is a sum of squared Hilbert norms, forcing every row to vanish.", false, DescribeRole.Theorem),
            Node("positive_definite_form_zero_vectors", "Strict positivity gives zero coefficients", zeroVectors,
                "After the rows vanish, invertibility of the positive definite matrix forces every coefficient vector to vanish.", false, DescribeRole.Theorem),
            Node("sum_word_succ", "Splitting the leading letter", sumSucc,
                "Fin.consEquiv partitions all words of positive length by their leading letter.", false, DescribeRole.Theorem),
            Node("residual_inner_gram", "The operator form equals the Gram form", residualGram,
                "The reversed-word pairing converts the operator form into the word Gram form; the pure diagonal extracts the even powers.", false, DescribeRole.Theorem),
            Node("sharp_gram_posSemidef", "Positivity at the sharp constant", sharpPsd,
                "Garcia--Volcic, Proposition 3.3, pages 8--9. Explicit inverse columns satisfy G R = E. The positive decomposition uses P = I - mu R E-transpose and the nonnegative pure block.", true, DescribeRole.Theorem),
            Node("sharp_positivity", "The sharp operator inequality", positivity,
                "The Lean carrier is a complete complex inner-product space and bounded complex-linear operators. The zero-based alphabet Fin n reindexes the source letters. The n = 1 case is equality.", true, DescribeRole.Theorem,
                [Text("Theorem 1.1(ii), pages 2–3: “Let "), Math(Seq(n,Comma,d,InMacro,N())), Text(". For all "),
                 Math(Seq(k,InMacro,N())), Text(" and all hermitian operators "), Math(sourceX1), Text("…, "), Math(sourceXn),
                 Text(" on a Hilbert space, "), Math(sourceH), Text("("), Math(sourceX1), Text(",…, "), Math(sourceXn),
                 Text(") ⪰ "), Math(sourceMu), Text(" ("), Math(Pow(sourceX1,Seq(D(2),d))), Text(" + ⋯ + "),
                 Math(Pow(sourceXn,Seq(D(2),d))), Text("),” in which the source defines the Löwner partial order and the three cases of the constant.")])
        ),[]));
    }
    private static DocumentBlock Node(string name,string title,Formula formula,string prose,bool literature,DescribeRole role,Inline[]? quote = null) =>
        Describe.Lean(DescribeId.Create("nc-hunter-positivity-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name),H(title),StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            quote == null ? Blocks(Paragraph(Text(prose))) : Blocks(Paragraph(quote),Paragraph(Text(prose))),role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var parts = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(part == "piCongrLeft'" ? Seq(F.Id("piCongrLeft"), Apos) : F.Id(part));
        }
        return arguments.Length == 0 ? Seq(Operatorname, Grp([.. parts]))
            : new Formula.Apply(Seq(Operatorname, Grp([.. parts])), [.. arguments]);
    }
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(Formula x, Formula type, Formula body) => Seq(Forall, Sp, x, Colon, type, Comma, Sp, body);
    private static Formula Instance(string name, Formula[] args, Formula body) => Seq(OpenBracket, Call(name, args), CloseBracket, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula LtTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan,b);
    private static Formula NeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a,Colon,type));
    private static Formula Lam(Formula x, Formula type, Formula body) => Seq(Parenthesized(Seq(x,Colon,type)),Sp,Mapsto,Sp,body);
    private static Formula TypeOf() => Call("Type");
    private static Formula N() => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula R() => Seq(Mathbb,Grp(F.Id("R")));
    private static Formula C() => Seq(Mathbb,Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Word(Formula n, Formula k) => Arrow(Fin(k),Fin(n));
    private static Formula Box(Formula n, Formula b) => Arrow(Fin(n),Fin(Add(b,D(1))));
    private static Formula MatrixOf(Formula i, Formula j, Formula type) => Call("Matrix",i,j,type);
    private static Formula Count(Formula w, Formula i) => Call("Multiset.count",i,Call("occupation",w));
    private static Formula SumOver(Formula i, Formula type, Formula body) => Seq(Sum,Underscore,Grp(i,Colon,type),Sp,Parenthesized(body));
    private static Formula ProdOver(Formula i, Formula type, Formula body) => Seq(Prod,Underscore,Grp(i,Colon,type),Sp,Parenthesized(body));
    private static Formula Factorial(Formula a) => Call("Nat.factorial",a);
    private static Formula Choose(Formula a, Formula b) => Call("Nat.choose",a,b);
    private static Formula Hilbert(Formula h, Formula body, bool complete = true) => All(h,TypeOf(),
        Instance("NormedAddCommGroup",[h],Instance("InnerProductSpace",[C(),h],
            complete ? Instance("CompleteSpace",[h],body) : body)));
    private static Formula Operators(Formula h) => Call("ContinuousLinearMap",C(),h,h);
    private static Formula Inner(Formula a, Formula b) => Call("inner",C(),a,b);
    private static Formula Degree(Formula n, Formula b, Formula d)
    {
        Formula a=F.Id("a"),i=F.Id("i");
        return Seq(OpenBrace,a,Colon,Box(n,b),Sp,Mid,Sp,
            Eqn(SumOver(i,Fin(n),Cast(At(a,i),N())),d),CloseBrace);
    }
    private static Formula Monad(Formula a, Formula body, bool star = false) => All(a,TypeOf(),
        Instance("Monoid",[a],star ? Instance("StarMul",[a],body) : body));
    private static Formula SelfAdjoints(Formula x, Formula n) => All(F.Id("i"),Fin(n),Call("IsSelfAdjoint",At(x,F.Id("i"))));
    private static Formula Nd(Formula body) => All(F.Id("n"),N(),All(F.Id("d"),N(),body));
    private static Formula Nk(Formula body) => All(F.Id("n"),N(),All(F.Id("k"),N(),body));
    private static Formula FiniteHilbertMatrix(Formula body)
    {
        Formula h=F.Id("H"),i=F.Id("I");
        return Hilbert(h,All(i,TypeOf(),Instance("Fintype",[i],
            All(F.Id("D"),MatrixOf(i,i,C()),All(F.Id("v"),Arrow(i,h),body)))), false);
    }
}
