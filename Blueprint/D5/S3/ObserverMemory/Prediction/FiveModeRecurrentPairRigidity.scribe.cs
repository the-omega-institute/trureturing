using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class FiveModeRecurrentPairRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every recurrent class of the actual synchronized source-observer chain has exact emissions and complete generated future laws.",
        H("Five Mode Recurrent Pair Rigidity"),
        Blocks(
            Paragraph(Text("The passive source has modes State=Fin 5, visible alphabet Visible=Fin 4, B=2, and the fixed transition matrix and uniform initialized law of FiniteStartFiveModeSource. Admissibility means p,q,r>0 and p+q+r<1. Both p=q and r=p+q are included. The visible rows in Lean order (0,1,B,3) are (c,p,r,q), (q,a,p,0), (0,q,a,p), (p,0,q,a), (r,0,b,0), with a=1-p-q, b=1-r and c=1-p-q-r.")),
            Paragraph(Text("A GeneratedObserver on the whole finite carrier Z has an initial configuration, arbitrary total update, and a normalized nonnegative emission row at every configuration. Its retained run folds that same update over actual observations; its generatedLaw multiplies the emissions along the same update on every hypothetical word. All generated-only configurations remain in Z. Forecast-zero actual-legal inputs remain defined. A source mode in a pair is a proof coordinate and supplies no observer input.")),
            Paragraph(Text("History means a finite chronological visible list. historyMass is its actual initialized cylinder mass. The empty query starts at Y0. A nonempty history of length n predicts Yn onward by the conditional acquired posterior. Words(H) is the entire function carrier Fin H to Visible, and finite TV is half the sum of absolute differences over that entire carrier. Thus impossible and zero-weight words are included. The theorem assumes the original guarantee only for positive natural H and arbitrary real epsilon<1. It derives epsilon>=0 from the guarantee and extends it to H=0 using normalization; no error-sign premise is added.")),
            Paragraph(Text("Synchronized(p,q,r,O,t) is witnessed by a positive actual history containing a symbol other than B, with sourceRun pure at mode(t) and the retained run equal to configuration(t). The acquired positive-history invariant identifies its actual posterior with the pure source vector. Every singleton-containing actual history has such a pure source tag. The symbol update nextPure is the singleton reset on 0,1,3; at B it maps 0 and 4 to 4 and the other modes to 2.")),
            Paragraph(Text("S=ActualPair(p,q,r,O) is this subtype of State times Z, hence finite. The positive actual history [0] makes it nonempty. For every source-positive symbol the acquired cylinder quotient gives the literal positive extension mass, and the source and observer folds give nextPair. Thus every such successor is again in S. actualStep is this lifted successor on a positive source weight; on a zero source weight it chooses the present pair as an auxiliary endpoint. This choice changes no transition mass and does not change the total observer update.")),
            Paragraph(Text("K=pairMatrix(p,q,r,O) sums v(mode(t),y) over symbols with actualStep(O,t,y)=u. Here v(i,y)=pureRow(p,q,r,i,y). It is the stochastic matrix on the actual subtype S. ClosedClass(K) means an actual terminal communicating class of the positive support, including reachability by the empty path. ClassStates(C) is its finite state set. The theorem quantifies every such class, proves it nonempty and irreducible, and supplies closure under every positive support path.")),
            Paragraph(Text("For a pair t, let aH(t) be the Bhattacharyya affinity of its pure source H-word law and the observer generated H-word law, and d(t,y)=sqrt(v(mode(t),y)*row(O,configuration(t),y)). The independently defined word laws give a(H+1)(t)=sum_y d(t,y)*aH(nextPair(O,t,y)). Nonnegativity and normalized row affinity make aH decrease from one, so its infimum l(t) is a limit and satisfies the same finite-sum equation. The Hellinger-to-TV lower bracket and the actual-history guarantee imply l(t)>=1-epsilon>0 on S. Source-zero symbols have d(t,y)=0, even if the observer gives them positive weight.")),
            Paragraph(Text("Fix any actual terminal class and maximize l there, with maximum M>0. Closure gives l(nextPair)<=M on every source-positive symbol. Therefore M=sum_y d*l(nextPair)<=M*sum_y d<=M. Equality forces sum_y d=1; normalized Hellinger separation then forces the observer row to equal the complete source row, including its zeros. The nonnegative weighted deficits M-l(nextPair) sum to zero. At an exact row every source-positive coefficient is positive, so each such successor also has limiting affinity M. Actual communication propagates this equality to every pair of the class, forcing every row exact.")),
            Paragraph(Text("With exact rows, induction on the complete future word length gives generatedLaw(O,configuration(t))=pureLaw(p,q,r,mode(t)). A source-zero first symbol makes both word weights zero; a positive first symbol stays inside the class, where the induction applies. This proves equality at every finite horizon without conditioning on a forecast-positive event or discarding generated words.")),
            Paragraph(Text("The positive square edges connect 0,1,2,3 and the positive leaf edges connect 0 and 4. More explicitly, any mode reaches 0 using singleton reads, with mode 2 first reading 1; from 0 the words [], [1], [1,B], [3], [B] reach modes 0,1,2,3,4. These paths lift inside every actual closed class. Choosing one pair above each mode gives actually reachable configurations. Existing full-domain pure-profile separation makes these five configurations distinct. The result does not assert a minimum observer cardinality, exactness of transient configurations, or uniqueness of the recurrent presentation.")),
            Entry("Synchronized", DescribeRole.Definition, SourceParameters(All("t", PairType,
                Iff(Call("Synchronized", P, Q, R, O, T), Exists("h", History,
                    And(Pos(Mass(Hist)), Exists("y", Visible,
                        And(Call("Member", Y, Hist), F.NotEqual(Y, Call("B")))),
                        Equal(Call("sourceRun", Hist), Call("pure", Mode(T))),
                        Equal(Run(Hist), Configuration(T)))))))),
            Entry("ActualPair", DescribeRole.Definition, SourceParameters(
                Equal(S, Call("Subtype", PairType, Call("Synchronized", P, Q, R, O))))),
            Entry("nextPair", DescribeRole.Definition, ObserverParameters(All("t", PairType,
                All("y", Visible, Equal(Call("nextPair", O, T, Y),
                    Call("Pair", Call("nextPure", Mode(T), Y),
                        Call("update", O, Configuration(T), Y))))))),
            Entry("actualStep", DescribeRole.Definition, SourceParameters(All("t", S,
                All("y", Visible, Equal(Call("actualStep", O, T, Y),
                    Call("ifThenElse", Pos(Row(T, Y)),
                        Call("lift", Call("nextPair", O, Call("val", T), Y)), T))))),
                "The lift carries the derived actual-history membership proof; its proof argument is suppressed."),
            Entry("pairMatrix", DescribeRole.Definition, FiniteSourceParameters(All("t", S,
                All("u", S, Equal(Call("entry", Matrix, T, U),
                    Seq(new Formula.Subscript(Sum, Seq(Y, InMacro, Sp, Visible)), Sp,
                        Call("ifThenElse", Equal(Call("actualStep", O, T, Y), U),
                            Row(T, Y), Zero))))))),
            Entry("guarantee_accurate", DescribeRole.Lemma, SourceParameters(All("epsilon", Real,
                Implies(And(Call("admissible", P, Q, R), Guarantee),
                    Call("Accurate", Call("toObserver", O), P, Q, R, Epsilon, Call("true"))))),
                "The guarantee at positive future horizons also gives the zero-horizon bound by normalization. This applies to arbitrary real epsilon and includes the positive empty actual history."),
            Entry("recurrent_pair_rigidity", DescribeRole.Theorem, MainStatement,
                "For all admissible sources, all finite unrestricted normalized self-generated observers, and every real epsilon<1 satisfying the complete actual-history guarantee, all displayed conclusions hold simultaneously."))));

    private static DocumentBlock.Describe Entry(string name, DescribeRole role, Formula formula,
        string note = "The definition uses the full fixed source and actual acquired histories.") =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity." + name),
            H(name.Replace('_', ' ')), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(note))), role);

    private static Formula MainStatement => FiniteSourceParameters(All("epsilon", Real,
        Implies(And(Call("admissible", P, Q, R), Lt(Epsilon, One), Guarantee), Conclusion)));

    private static Formula Conclusion => And(Call("Nonempty", S),
        All("h", History, Implies(And(Pos(Mass(Hist)), SingletonHistory),
            Exists("t", S, And(Equal(Configuration(Call("val", T)), Run(Hist)),
                Equal(Call("acquiredPosterior", P, Q, R, Hist),
                    Call("pureVector", Mode(Call("val", T)))))))),
        All("t", S, All("y", Visible, Implies(Pos(Row(T, Y)),
            Equal(Call("val", Call("actualStep", O, T, Y)),
                Call("nextPair", O, Call("val", T), Y))))),
        Call("RowStochastic", Matrix), Call("Nonempty", Classes), ClassConclusion, Selection);

    private static Formula SingletonHistory => Exists("y", Visible,
        And(Call("Member", Y, Hist), F.NotEqual(Y, Call("B"))));

    private static Formula ClassConclusion => All("C", Classes,
        And(Call("Nonempty", ClassStates),
            Call("IsIrreducible", Call("restriction", Matrix, ClassStates)),
            Members(All("u", S, Implies(Call("Reach", Matrix, T, U), Member(U)))),
            Members(Equal(Call("row", O, Configuration(Call("val", T))),
                Call("pureRow", P, Q, R, Mode(Call("val", T))))),
            Members(Equal(Generated(Configuration(Call("val", T))),
                Pure(Mode(Call("val", T))))),
            All("i", State, Exists("t", S,
                And(Member(T), Equal(Mode(Call("val", T)), I))))));

    private static Formula Selection => Exists("f", Call("Function", State, Z),
        And(Call("Injective", Ff), All("i", State,
            And(Call("Member", Call("apply", Ff, I),
                Call("Reached", Call("toObserver", O), P, Q, R)),
                Equal(Generated(Call("apply", Ff, I)), Pure(I))))));

    private static Formula Guarantee => All("h", History, Implies(Pos(Mass(Hist)),
        All("H", Nat, Implies(Pos(Horizon), Le(Call("totalVariation",
            Call("atHorizon", Call("actualFutureWordWeight", P, Q, R, Hist), Horizon),
            Call("atHorizon", Generated(Run(Hist)), Horizon)), Epsilon)))));

    private static Formula Members(Formula body) => All("t", S, Implies(Member(T), body));
    private static Formula Member(Formula t) => Call("Member", t, ClassStates);
    private static Formula ObserverParameters(Formula body) => All("Z", Call("Type"),
        All("O", Call("GeneratedObserver", Z), body));
    private static Formula SourceParameters(Formula body) => All("Z", Call("Type"),
        All("p", Real, All("q", Real, All("r", Real,
            All("O", Call("GeneratedObserver", Z), body)))));
    private static Formula FiniteSourceParameters(Formula body) => All("Z", Call("Type"),
        Seq(OpenBracket, Call("Fintype", Z), CloseBracket, Sp,
            All("p", Real, All("q", Real, All("r", Real,
                All("O", Call("GeneratedObserver", Z), body))))));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) => F.Call(name, args);
    private static Formula Equal(Formula a, Formula b) => F.Equal(a, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Pos(Formula a) => Lt(Zero, a);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(params Formula[] terms) => terms.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Row(Formula t, Formula y) => Call("pureRow", P, Q, R, Mode(Call("val", t)), y);
    private static Formula Mode(Formula t) => Call("mode", t);
    private static Formula Configuration(Formula t) => Call("configuration", t);
    private static Formula Generated(Formula z) => Call("generatedLaw", Call("update", O), Call("row", O), z);
    private static Formula Pure(Formula i) => Call("pureLaw", P, Q, R, i);
    private static Formula Run(Formula h) => Call("run", Call("toObserver", O), h);
    private static Formula Mass(Formula h) => Call("historyMass", P, Q, R, h);
    private static Formula Matrix => Call("pairMatrix", P, Q, R, O);
    private static Formula Classes => Call("ClosedClass", Matrix);
    private static Formula ClassStates => Call("ClassStates", F.Id("C"));
    private static Formula PairType => Call("Prod", State, Z);
    private static Formula S => Call("ActualPair", P, Q, R, O);
    private static Formula State => Call("State");
    private static Formula Visible => Call("Visible");
    private static Formula History => Call("List", Visible);
    private static Formula Real => Call("Real");
    private static Formula Nat => Call("Nat");
    private static Formula P => F.Id("p");
    private static Formula Q => F.Id("q");
    private static Formula R => F.Id("r");
    private static Formula O => F.Id("O");
    private static Formula Z => F.Id("Z");
    private static Formula T => F.Id("t");
    private static Formula U => F.Id("u");
    private static Formula Y => F.Id("y");
    private static Formula I => F.Id("i");
    private static Formula Hist => F.Id("h");
    private static Formula Horizon => F.Id("H");
    private static Formula Epsilon => F.Id("epsilon");
    private static Formula Ff => F.Id("f");
    private static Formula Zero => F.Num(0);
    private static Formula One => F.Num(1);
}
