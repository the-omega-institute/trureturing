using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class LocalSearchRobustnessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/LocalSearchRobustness";
    private static readonly Formula E = F.Id("E"), M = F.Id("M"), W = F.Id("w");
    private static readonly Formula Real = Seq(Mathbb, Grp(F.Id("R")));
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static Formula SetE => Call("Set", E);
    private static Formula Bases => Seq(OpenBrace, F.Id("D"), Colon, Sp, SetE, Sp, Mid, Sp,
        Basis(F.Id("D")), CloseBrace);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Accumulated errors of arbitrary single-exchange base paths control all nearby comparator bases.",
        H("Local-search robustness for finite native matroids"),
        Blocks(
            Describe.Lean(DescribeId.Create("attained-base-neighborhood-max"),
                DeclarationHandle.Create(Module + ".neighborhoodMax"),
                H("An attained maximum on the actual base neighborhood"),
                StatementSource.FromAuthor(MaximumStatement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGeometry/okischwarcz2025multipleexchange")),
                Blocks(Paragraph(Text(
                    "For every universe u, finite ambient type E, native matroid M and arbitrary real "
                    + "weight w, W(D) is the existing NativeWeightedBaseRankSaturation.baseWeight w D. "
                    + "A base is represented by the subtype {D : Set E // M.IsBase D}; its set is used "
                    + "in all differences and weights. H_t(B) denotes neighborhoodMax M w B t. "
                    + "The neighborhood is exactly {D | M.IsBase D and (D minus B).ncard <= t}. "
                    + "It is finite because its members are subsets of the finite native ground, "
                    + "and nonempty because it contains B. Set.exists_max_image constructs a "
                    + "maximizing set, and H is the weight of that selected set. No extremum is supplied as a hypothesis."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-base-local-error"),
                DeclarationHandle.Create(Module + ".localError"),
                H("The actual local error"), StatementSource.FromAuthor(ErrorStatement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGeometry/okischwarcz2025multipleexchange")),
                Blocks(Paragraph(Text("The error is defined for two bases of the same M. "
                    + "A radius-one step makes the second base feasible for the first base's actual "
                    + "neighborhood maximum, which gives error nonnegativity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-base-neighborhood-comparison"),
                DeclarationHandle.Create(Module + ".neighborhood_comparison"),
                H("Joint-neighborhood comparison"), StatementSource.FromAuthor(ComparisonStatement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGeometry/okischwarcz2025multipleexchange")),
                Blocks(
                    Paragraph(Text("This is Oki–Schwarcz, Lemma 4.1, in the equivalent r+1 to r form "
                        + "for every natural r, including zero. The maximizing base A is chosen in "
                        + "the radius-(r+1) neighborhood of B0. The printed initial B in the source's "
                        + "argmax is interpreted as B0, as required by equation (21).")),
                    Paragraph(Text("A base already within radius r of B1 supplies the comparison "
                        + "directly; A=B0 is handled separately. Coincident consecutive bases use "
                        + "a symmetric singleton exchange. For distinct B0,B1, write B0 minus B1={x} "
                        + "and B1 minus B0={y}. Membership of x,y in A gives the elementary exchange cases. "
                        + "In the remaining case x belongs to A and y does not, the existing "
                        + "PrescribedExchange.exists_prescribed_exchange is applied with X={x},Y={y}. "
                        + "Its rank cap gives a common exchange size of one or two.")),
                    Paragraph(Text("Size two produces simultaneously a radius-r base around B1 "
                        + "and a radius-one base around B0, preserving the sum of weights. In size one, "
                        + "A minus B0 is nonempty because A and B0 are distinct bases. Select a "
                        + "minimum-weight element there, make a second exchange toward B1, and exchange "
                        + "from B0 toward A. The minimum-weight inequality compensates the weight "
                        + "difference, and both required radii hold for this same pair of bases."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-native-local-search-robustness"),
                DeclarationHandle.Create(Module + ".local_search_robustness"),
                H("Every error is nonnegative and every radius-k comparator is controlled"),
                StatementSource.FromAuthor(RobustnessStatement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGeometry/okischwarcz2025multipleexchange")),
                Blocks(
                    Paragraph(Text("The finite path B : Fin(k+1) -> Base(M) consists of bases of one "
                        + "and the same native matroid. For i : Fin k, i.castSucc indexes Bi and "
                        + "i.succ indexes B(i+1). The sum is over every i : Fin k, and Fin.last k "
                        + "indexes Bk. The conclusion includes every base C in the actual radius-k "
                        + "neighborhood of B0; it is not a claim about a selected comparator alone.")),
                    Paragraph(Text("Repeated application of the joint comparison gives "
                        + "H_k(B0) <= H_(k-1)(B1)+err_0 <= ... <= H_0(Bk)+sum_i err_i. "
                        + "The induction implements this telescope on the finite path and proves "
                        + "H_0(Bk)=W(Bk), since a base contained in another base equals it. "
                        + "The actual neighborhood maximum bounds each feasible comparator.")),
                    Paragraph(Text("This is the mathematical assertion of Oki–Schwarcz, "
                        + "Theorem 1.7, Section 4, printed pages 19–20. The scope retains k=0, "
                        + "repeated bases, signed weights, empty carrier or ground, proper grounds, "
                        + "rank zero, loops, coloops and nonrepresentable matroids. There is no "
                        + "strict-improvement, optimal-start, distinct-step or representability premise, "
                        + "and no supplied maximum, error or optimality premise. The theorem makes "
                        + "no claim about algorithms, query counts, complexity or physical models."))),
                DescribeRole.Theorem))));

    private static Formula MaximumStatement()
    {
        Formula b = F.Id("B"), t = F.Id("t"), a = F.Id("A"), d = F.Id("D");
        Formula body = Some("A", SetE, And(Basis(a), And(Leq(Distance(a,b),t),
            And(Equal(Total(a),Max(b,t)), All("D", SetE,
                Imp(Basis(d),Imp(Leq(Distance(d,b),t),Leq(Total(d),Max(b,t)))))))));
        return Telescope(All("B", Bases, All("t", Nat, body)));
    }
    private static Formula ErrorStatement() => Telescope(All("B0", Bases, All("B1", Bases,
        Equal(Error(F.Id("B0"),F.Id("B1")), Sub(Max(F.Id("B0"),F.Id("1")),Total(F.Id("B1")))))));
    private static Formula ComparisonStatement()
    {
        Formula b0 = F.Id("B0"), b1 = F.Id("B1"), r = F.Id("r");
        return Telescope(All("B0", Bases, All("B1", Bases, All("r", Nat,
            Imp(Leq(Distance(b1,b0),F.Id("1")),
                Leq(Add(Max(b0,Add(r,F.Id("1"))),Total(b1)),Add(Max(b1,r),Max(b0,F.Id("1")))))))));
    }
    private static Formula RobustnessStatement()
    {
        Formula k = F.Id("k"), i = F.Id("i"), c = F.Id("C");
        Formula bi = Call("B",Call("Fin.castSucc",i));
        Formula bn = Call("B",Call("Fin.succ",i));
        Formula b0 = Call("B",F.Id("0")), bk = Call("B",Call("Fin.last",k));
        Formula index = Call("Fin",k);
        Formula errors = Seq(new Formula.Subscript(Sum,Grp(Seq(i,Colon,Sp,index))),Sp,Error(bi,bn));
        Formula conclusion = And(All("i",index,Leq(F.Id("0"),Error(bi,bn))),
            All("C",SetE,Imp(Basis(c),Imp(Leq(Distance(c,b0),k),Leq(Total(c),Add(Total(bk),errors))))));
        Formula path = new Formula.TypeArrow(Call("Fin",Add(k,F.Id("1"))),Bases);
        return Telescope(All("k",Nat,All("B",path,
            Imp(All("i",index,Leq(Distance(bn,bi),F.Id("1"))),conclusion))));
    }
    private static Formula Telescope(Formula body) => Disp(All("E",new Formula.Subscript(F.Id("Type"),F.Id("u")),
        Seq(OpenBracket,Call("Finite",E),CloseBracket,Comma,Sp,
            All("M",Call("Matroid",E),All("w",new Formula.TypeArrow(E,Real),body)))));
    private static Formula Basis(Formula b) => Call("Matroid.IsBase",M,b);
    private static Formula Distance(Formula a, Formula b) => Call("Set.ncard",Paren(Seq(a,Sp,Setminus,Sp,b)));
    private static Formula Total(Formula a) => Call("baseWeight",W,a);
    private static Formula Max(Formula b, Formula t) => Call("neighborhoodMax",M,W,b,t);
    private static Formula Error(Formula b0, Formula b1) => Call("localError",M,W,b0,b1);
    private static Formula Add(Formula a, Formula b) => Paren(Seq(a,Sp,F.Id("+"),Sp,b));
    private static Formula Sub(Formula a, Formula b) => Paren(Seq(a,Sp,F.Id("-"),Sp,b));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname,Grp(F.Id(name))),[.. args]);
    private static Formula Paren(Formula x) => Seq(Open,x,Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall,Sp,Paren(Seq(F.Id(name),Colon,Sp,type)),Comma,Sp,Paren(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists,Sp,Paren(Seq(F.Id(name),Colon,Sp,type)),Comma,Sp,Paren(body));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Paren(a),FormulaLogicOperator.And,Paren(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Paren(a),FormulaLogicOperator.Implies,Paren(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
}
