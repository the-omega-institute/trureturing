using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class RichWordTypeIIOccurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/RichWordTypeIIOccurrence.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Type-II occurrences and complete return vectors in the seven-letter source word.",
        H("Type-II Factors at Positive Substitution Cuts"),
        Blocks(
            Paragraph(Text("The alphabet is Fin 7 and the substitution is phi(a)=[0,a+1] for a<6, "
                + "with phi(6)=[0,6,6]. All words, occurrences, extensions, boundaries, incidence "
                + "columns and half-open return intervals are those of RichWordTypeIOccurrence. "
                + "Consecutiveness permits overlapping occurrence windows. The auxiliary index "
                + "k always denotes original source index n=k+6; indices below six specify the "
                + "factor-count recurrence and are not asserted to have the Type-II return theorem.")),
            Entry("F", "auxiliary-prefix", "Sentinel prefixes", PrefixFormula(),
                "F(0) is empty and F(k+1)=phi(F(k))[0]. Its occurrences at every natural position "
                + "are exactly the iterated cuts cut(k,i), including the origin. After k "
                + "sentinel steps both contexts are obtained by iterating a map that sends "
                + "a<6 to a+1 and fixes 6. Five iterations send 0 to 5 and every other letter to 6."),
            Entry("cut", "iterated-cut", "Iterated native boundaries", CutFormula(),
                "cut(0,i)=i and cut(k+1,i)=boundary(cut(k,i)). These maps are strictly increasing, "
                + "fix zero, and carry positive indices to positive positions. The interval between "
                + "cut(k,i) and cut(k,i+1) is literally the kth image of the actual letter u(i)."),
            Entry("typeII", "typeii-word", "The literal cyclic factor recurrence", WordFormula(),
                "W(0) is empty. At phases other than 5 modulo 6, append a sentinel zero to phi(W(n)). "
                + "At phase 5 use [6]phi(W(n))[0,6]. Thus W(6)=6 F(6) 6, has length 65 and "
                + "Parikh vector (32,16,8,4,2,1,2). Both extra terminal-coordinate units are present. "
                + "Reversal commutes with the sentinel construction, and the terminal construction "
                + "wraps it in two equal letters, so all W(n) are palindromes."),
            Entry("f", "source-vector", "Exact source count recurrence", VectorFormula(),
                "The initial vector is zero and f(n+1)=M f(n)+increment(n). Here increment(n) is "
                + "e(0)+2e(6) at phase 5 and e(0) otherwise. Letter counting on the literal "
                + "word recurrence proves P(W(n))=f(n) at every auxiliary and actual index."),
            Entry("position", "positive-start", "Positive-cut occurrence enumeration", PositionFormula(),
                "position(0,i)=cut(6,i)-1 and position(k+1,i)=occurrenceMap(k+6,position(k,i)). "
                + "The valid source indices are exactly i>0. The natural subtraction at i=0 "
                + "does not create an occurrence: the initial F(5) occurrence has no preceding "
                + "letter and is discarded by the first terminal wrap."),
            Entry("NativeData", "native-data", "The complete native contract", NativeFormula(),
                "For each offset k, this proposition records a nonempty palindromic actual "
                + "factor, its exact count vector, a strictly increasing positive enumeration "
                + "of all occurrences, both actual context formulas, both exact extension sets, "
                + "and a unique adjacent-index description of all consecutive pairs. It also "
                + "records the literal ordinary or terminal return-word update, all seven "
                + "return counts, attainment by indices 2 and 3, domination of that vector by "
                + "every consecutive return, the complete seven-column set of attained return "
                + "vectors, and the explicit wrapped seed and overlapping return at 128 and 192."),
            Entry("actual_typeII", "actual-typeii", "Every original index at least six", MainFormula(),
                "For every n at least six, NativeData(n-6) holds. The seed recognizer first "
                + "desubstitutes five sentinels. Its two contexts lie in {5,6}; terminal "
                + "recognition therefore retains precisely the positive cuts. At subsequent "
                + "ordinary phases contexts advance by one, and at terminal phases 5 becomes "
                + "0 while 6 remains 6. All occurrences are transported in both directions, "
                + "so adjacent source indices give exactly the consecutive occurrences. "
                + "Ordinary return intervals are substituted literally; terminal intervals "
                + "prepend 6 and delete the final 6 of the substituted interval, whose final letter is explicitly proved to be 6. The complete "
                + "Parikh vector is unchanged by this cancellation. Hence the return at index "
                + "i has vector M^(k+6)e(u(i)). The first sixfold image of 0 is a prefix of "
                + "every sixfold letter image; applying further substitutions preserves this "
                + "prefix and proves all-coordinate domination. The actual letters u(0),u(1),u(2) "
                + "are 0,1,0, so starts 1 and 2 give context pairs (phase,6) and (6,phase), "
                + "and the return at index 2 attains the minimum. Every letter occurs at a "
                + "positive source index, giving every listed return vector. At the seed the "
                + "attaining interval is [128,192), with return word 6F(6); its two length-65 "
                + "occurrences overlap in one letter. This supplies the Type-II source "
                + "factor and return statements. It does not assert an output exponent bound "
                + "or classify other bispecial factors.", DescribeRole.Theorem))));

    private static ScribeNode Entry(string name, string id, string title, Formula formula,
        string prose, DescribeRole role = DescribeRole.Definition) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix+name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula PrefixFormula() => And(Eq(C("F", D(0)),C("nil")),
        All("k",N(),Eq(C("F",Add(Id("k"),D(1))),C("sentinel",C("F",Id("k"))))));
    private static Formula CutFormula() => All("i",N(),And(Eq(C("cut",D(0),Id("i")),Id("i")),
        All("k",N(),Eq(C("cut",Add(Id("k"),D(1)),Id("i")),
            C("boundary",C("cut",Id("k"),Id("i")))))));
    private static Formula WordFormula() => And(Eq(C("typeII",D(0)),C("nil")),All("n",N(),
        Eq(C("typeII",Add(Id("n"),D(1))),C("ite",Eq(C("mod",Id("n"),D(6)),D(5)),
            C("terminal",C("typeII",Id("n"))),C("sentinel",C("typeII",Id("n")))))));
    private static Formula VectorFormula() => And(Eq(C("f",D(0)),D(0)),All("n",N(),
        Eq(C("f",Add(Id("n"),D(1))),Add(C("mulVec",C("M"),C("f",Id("n"))),C("increment",Id("n"))))));
    private static Formula PositionFormula() => All("i",N(),And(
        Eq(C("position",D(0),Id("i")),Sub(C("cut",D(6),Id("i")),D(1))),
        All("k",N(),Eq(C("position",Add(Id("k"),D(1)),Id("i")),
            C("occurrenceMap",Add(Id("k"),D(6)),C("position",Id("k"),Id("i")))))));
    private static Formula NativeFormula()
    {
        Formula k=Id("k"), i=Id("i"), q=Id("q"), a=Id("a"), b=Id("b"), c=Id("c");
        Formula n=Add(k,D(6)), w=C("typeII",n), phase=C("phase",n);
        Formula P(Formula x) => C("position",k,x);
        Formula R(Formula x) => C("returnWord",P(x),P(Add(x,D(1))));
        Formula V(Formula x) => C("mulVec",C("pow",C("M"),n),C("unit",x));
        Formula Ctx(Formula x) => C("ite",Eq(C("word",x),D(0)),phase,D(6));
        Formula Unique(System.Func<Formula,Formula> predicate) => Ex("i",N(),And(predicate(i),
            All("j",N(),Imp(predicate(Id("j")),Eq(Id("j"),i)))));
        Formula[] fields = [
            Lt(D(0),C("length",w)), Eq(C("reverse",w),w), Eq(C("parikh",w),C("f",n)),
            C("StrictMono",C("position",k)), All("i",N(),Imp(Lt(D(0),i),Lt(D(0),P(i)))),
            All("q",N(),Iff(C("Occ",w,q),Unique(x=>And(Lt(D(0),x),Eq(q,P(x)))))),
            All("i",N(),Imp(Lt(D(0),i),And(Eq(C("word",Sub(P(i),D(1))),Ctx(Sub(i,D(1)))),
                Eq(C("word",Add(P(i),C("length",w))),Ctx(i))))),
            And(Eq(C("word",Sub(P(D(1)),D(1))),phase),And(
                Eq(C("word",Add(P(D(1)),C("length",w))),D(6)),And(
                Eq(C("word",Sub(P(D(2)),D(1))),D(6)),
                Eq(C("word",Add(P(D(2)),C("length",w))),phase)))),
            And(Eq(C("Lext",w),C("pair",phase,D(6))),Eq(C("Rext",w),C("pair",phase,D(6)))),
            All("a",N(),All("b",N(),Iff(C("Consecutive",w,a,b),
                Unique(x=>And(Lt(D(0),x),And(Eq(a,P(x)),Eq(b,P(Add(x,D(1)))))))))),
            All("i",N(),Imp(Lt(D(0),i),Eq(C("returnWord",C("position",Add(k,D(1)),i),
                C("position",Add(k,D(1)),Add(i,D(1)))),C("ite",Eq(C("mod",n,D(6)),D(5)),
                    C("cons",D(6),C("dropLast",C("subst",C("phi"),R(i)))),C("subst",C("phi"),R(i)))))),
            All("i",N(),Imp(Lt(D(0),i),Imp(Eq(C("mod",n,D(6)),D(5)),
                Ex("y",C("List",C("Fin",D(7))),Eq(C("subst",C("phi"),R(i)),
                    C("append",Id("y"),C("singleton",D(6)))))))),
            All("i",N(),Imp(Lt(D(0),i),Eq(C("factor",C("word"),P(i),
                Add(Sub(P(Add(i,D(1))),P(i)),C("length",w))),C("append",R(i),w)))),
            All("i",N(),Imp(Lt(D(0),i),Eq(C("parikh",R(i)),V(C("word",i))))),
            All("i",N(),Imp(Lt(D(0),i),Eq(C("returnWord",C("position",D(0),i),
                C("position",D(0),Add(i,D(1)))),C("cons",D(6),
                C("dropLast",C("image",C("phi"),D(6),C("word",i))))))),
            And(C("Consecutive",w,P(D(2)),P(D(3))),And(Eq(C("parikh",R(D(2))),V(D(0))),
                All("a",N(),All("b",N(),Imp(C("Consecutive",w,a,b),C("le",V(D(0)),C("parikh",C("returnWord",a,b)))))))),
            All("v",C("Function",C("Fin",D(7)),N()),Iff(
                Ex("a",N(),Ex("b",N(),And(C("Consecutive",w,a,b),
                    Eq(C("parikh",C("returnWord",a,b)),Id("v"))))),
                Ex("c",C("Fin",D(7)),Eq(V(c),Id("v"))))),
            SeedFormula()
        ];
        Formula body=fields[^1];
        for(int j=fields.Length-2;j>=0;--j) body=And(fields[j],body);
        return All("k",N(),Iff(C("NativeData",k),body));
    }
    private static Formula SeedFormula() => And(Eq(C("typeII",D(6)),C("cons",D(6),C("append",C("F",D(6)),C("singleton",D(6))))),
        And(Eq(C("length",C("typeII",D(6))),D(6,5)),And(
            Eq(C("parikh",C("typeII",D(6))),C("vector",D(3,2),D(1,6),D(8),D(4),D(2),D(1),D(2))),
            And(Eq(C("position",D(0),D(2)),D(1,2,8)),And(Eq(C("position",D(0),D(3)),D(1,9,2)),
                Eq(C("returnWord",C("position",D(0),D(2)),C("position",D(0),D(3))),C("cons",D(6),C("F",D(6)))))))));
    private static Formula MainFormula() => All("n",N(),Imp(C("le",D(6),Id("n")),C("NativeData",Sub(Id("n"),D(6)))));
    private static Formula N()=>Seq(Mathbb,Grp(Id("N")));
    private static Formula C(string name,params Formula[] args)=>args.Length==0?Id(name):new Formula.Apply(Id(name),[..args]);
    private static Formula All(string x,Formula domain,Formula body)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(x),domain,body);
    private static Formula Ex(string x,Formula domain,Formula body)=>new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(x),domain,body);
    private static Formula Eq(Formula x,Formula y)=>new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Lt(Formula x,Formula y)=>new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula Add(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula And(Formula x,Formula y)=>new Formula.Logic(x,FormulaLogicOperator.And,y);
    private static Formula Imp(Formula x,Formula y)=>new Formula.Logic(x,FormulaLogicOperator.Implies,y);
    private static Formula Iff(Formula x,Formula y)=>new Formula.Logic(x,FormulaLogicOperator.Iff,y);
}
