using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class RichWordOutputDecoderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/RichWordOutputDecoder.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact four-letter marker decoding and attained return minima for the actual seven-letter source.",
        H("Literal Marker Decoding and Actual Returns"), Blocks(
            Paragraph(Text("The input is precisely RichWordTypeIOccurrence.word on Fin 7. Output letters 0,1,2,3 denote a,b,c,d. The dictionary is (a,ab,abb,ac,acc,accdcc,accdccddccdcc), with image lengths (1,2,3,2,3,6,13). Every image begins with its only a; its remaining tail q is marker-free, and the seven tails are distinct, including the empty q(0). No recurrence, context or universality hypothesis is imposed on the source. E is the cumulative image length, and x reads each letter from its unique interval E(j) <= p < E(j+1). Thus x is the actual one-sided eta(u).")),
            Entry("marked_core_recovery", "core", "All-length source reconstruction", Core(),
                "An occurrence of eta(w)a at the actual boundary E(j) reconstructs the whole source window w. The induction compares the next target marker with the next actual boundary. Either unequal distance would place a marker inside a marker-free image tail. Equality of the actual intervening words then identifies the source letter by dictionary injectivity; equal lengths alone do not identify letters. The empty core is included."),
            Entry("occurrence_decoder", "decoder", "The exact filtered occurrence decoder", Decoder(),
                "markerFree(z) means 0 is not a member of z. Left(s,j) means s is empty, or j is positive and s is a suffix of q(u(j-1)). Right(t,w,j) means t is a prefix of q(u(j+length(w))). Both decorations are marker-free. The first marker determines a unique source index, the core reconstruction determines w, and the two actual boundary tails determine the filters. Empty s permits the origin. An empty core has coincident first and last highlighted markers. Adjacent markers from eta(0)=a and overlapping windows are retained."),
            Entry("Transport", "transport", "Exact transport and attained minimum", TransportFormula(),
                "The proposition records all output occurrences as the entire source occurrence set, exact consecutive-pair correspondence, the weighted length of every corresponding return interval, and attainment plus universal domination of the minimum output gap. decorated(w,s,t) is s eta(w) a t, of length W(parikh(w))+1+length(s)+length(t). For s=t=r(n), the six boundary contributions are (1,1,1,3,5,11). sourceOcc(w,j) means the actual source window u[j,j+length(w)) equals w. sourceConsecutive is the same source predicate as RichWordTypeIOccurrence.Consecutive. Consecutive means strictly increasing starts with no intervening occurrence, with no nonoverlap condition. W(v) is the sum of image-length(c) times v(c) over all seven letters. Source returnWord(j,k) is the actual interval u[j,k). The return gap has no added decoration length.", DescribeRole.Definition),
            Entry("typeI_transport", "typei", "Every original Type-I index", Family(false),
                "For every n >= 0, use any suffix s of r(n) and prefix t of r(n), where the six phase values are (empty,empty,empty,c,cc,ccdcc). The source theorem typeI_not_at_origin and the exact witnessed extension sets supply both actual neighbor letters in {n mod 6,6}; both admit r(n). Every source occurrence is therefore retained. The attained componentwise minimum M^n e(6) transfers to the least output return length W(M^n e(6))."),
            Entry("typeII_transport", "typeii", "Original Type-II indices at least six", Family(true),
                "For original n >= 6 and any suffix s and prefix t of r(n), actual_typeII(n) supplies NativeData(n-6). Its occurrence enumeration and positivity exclude the origin, and its actual context formulas supply both neighbors. Rewriting (n-6)+6=n preserves the original phase and matrix exponent. The attained vector M^n e(0), at source indices position(n-6,2) and position(n-6,3), transfers to the attained output minimum. No Type-II return assertion is made below six."),
            Paragraph(Text("The interval identity reuses the original morphic_block helper after an injective encoding of the four output letters into integers; this helper has no UniversalInput premise. All source occurrences, consecutive returns and attained vector minima are reused from the source occurrence theorems. The source scalar inequalities (50), the all-factor ordinary critical-exponent criterion and classification, recurrence and aperiodicity hypotheses for that criterion, and the lower bound are separate inputs. This result does not prove the scalar inequalities or a full ordinary critical exponent.")))));

    private static DocumentBlock Entry(string name, string id, string title, Formula body,
        string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("output-"+id), DeclarationHandle.Create(Prefix+name), H(title),
        StatementSource.FromAuthor(F.Disp(body)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);
    private static Formula C(string name, params Formula[] xs) => xs.Length==0
        ? Seq(Operatorname,Grp(F.Id(name)))
        : new Formula.Apply(Seq(Operatorname,Grp(F.Id(name))),[..xs]);
    private static Formula N() => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula I() => C("List",C("Fin",D(7)));
    private static Formula O() => C("List",C("Fin",D(4)));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),type,body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(name),type,body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Cat(Formula a, Formula b) => C("append",a,b);
    private static Formula Len(Formula a) => C("length",a);
    private static Formula Bound(Formula a, Formula j, Formula s) => Eq(Add(a,Len(s)),C("E",j));
    private static Formula Unique(string name, Formula type, System.Func<Formula,Formula> p) =>
        Ex(name,type,And(p(F.Id(name)),All("z",type,Imp(p(F.Id("z")),Eq(F.Id("z"),F.Id(name))))));
    private static Formula Core()
    {
        Formula w=F.Id("w"), j=F.Id("j");
        return All("w",I(),All("j",N(),Imp(C("Occ",Cat(C("subst",C("eta"),w),C("singleton",D(0))),C("E",j)),C("sourceOcc",w,j))));
    }
    private static Formula Decoder()
    {
        Formula w=F.Id("w"),s=F.Id("s"),t=F.Id("t"),a=F.Id("A");
        Formula P(Formula j) => And(Bound(a,j,s),And(C("sourceOcc",w,j),And(C("Left",s,j),C("Right",t,w,j))));
        Formula body=Iff(C("Occ",Cat(Cat(Cat(s,C("subst",C("eta"),w)),C("singleton",D(0))),t),a),Unique("j",N(),P));
        return All("w",I(),All("s",O(),All("t",O(),All("A",N(),Imp(C("markerFree",s),Imp(C("markerFree",t),body))))));
    }
    private static Formula TransportFormula()
    {
        Formula w=F.Id("w"),s=F.Id("s"),t=F.Id("t"),mu=F.Id("m"),a=F.Id("A"),b=F.Id("B"),j=F.Id("j"),k=F.Id("k");
        Formula v=C("decorated",w,s,t);
        Formula pair=Ex("j",N(),Ex("k",N(),And(Bound(a,j,s),And(Bound(b,k,s),C("sourceConsecutive",w,j,k)))));
        Formula occ=All("A",N(),Iff(C("Occ",v,a),Unique("j",N(),z=>And(Bound(a,z,s),C("sourceOcc",w,z)))));
        Formula con=All("A",N(),All("B",N(),Iff(C("Consecutive",v,a,b),pair)));
        Formula gap=All("A",N(),All("B",N(),All("j",N(),All("k",N(),Imp(Bound(a,j,s),Imp(Bound(b,k,s),Imp(Le(j,k),Eq(Sub(b,a),C("W",C("parikh",C("returnWord",j,k)))))))))));
        Formula attainment=Ex("A",N(),Ex("B",N(),Ex("j",N(),Ex("k",N(),And(C("Consecutive",v,a,b),And(Bound(a,j,s),And(Bound(b,k,s),And(C("sourceConsecutive",w,j,k),And(Eq(C("parikh",C("returnWord",j,k)),mu),Eq(Sub(b,a),C("W",mu)))))))))));
        Formula min=And(attainment,All("A",N(),All("B",N(),Imp(C("Consecutive",v,a,b),Le(C("W",mu),Sub(b,a))))));
        return All("w",I(),All("s",O(),All("t",O(),All("m",new Formula.TypeArrow(C("Fin",D(7)),N()),Iff(C("Transport",w,s,t,mu),And(occ,And(con,And(gap,min))))))));
    }
    private static Formula Family(bool second)
    {
        Formula n=F.Id("n"),s=F.Id("s"),t=F.Id("t"), minimum=C("mulVec",C("pow",C("M"),n),C("unit",D((byte)(second?0:6))));
        Formula body=C("Transport",C(second?"typeII":"typeI",n),s,t,minimum);
        body=All("s",O(),All("t",O(),Imp(C("suffix",s,C("r",n)),Imp(C("prefix",t,C("r",n)),body))));
        return All("n",N(),second?Imp(Le(D(6),n),body):body);
    }
}
