using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class RawGroupZeroDriftDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/RawGroupZeroDrift.";
    private static Formula I(string s) => F.Id(s);
    private static Formula Real => Seq(Mathbb, Grp(I("R")));
    private static Formula Arr(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula All(string s, Formula t, Formula b) => Seq(Open, Forall, Sp, I(s), Colon, Sp, t, Comma, Sp, b, Close);
    private static Formula Ex(string s, Formula t, Formula b) => Seq(Open, Exists, Sp, I(s), Colon, Sp, t, Comma, Sp, b, Close);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Sp, Rightarrow, Sp, b, Close);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Sp, Land, Sp, b, Close);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Sp, Cdot, Sp, b, Close);
    private static Formula Inv(Formula a) => Call("inv", a);
    private static Formula Cost(string c, Formula a, Formula b) => Call(c, a, b);
    private static Formula Sym(string m, string c) => All("a", I(m), All("b", I(m), Eqn(Cost(c,I("a"),I("b")),Cost(c,I("b"),I("a")))));
    private static Formula Frame(Formula b) => All("G", new Formula.Subscript(I("Type"),I("u")), All("gG", Call("Group",I("G")),
        All("U", Arr(I("G"),I("G")), All("c", Arr(I("G"),Arr(I("G"),Real)), b))));
    private static Formula Raw => Call("RawCost", I("U"), I("c"));
    private static DocumentBlock Entry(string id, string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Gid + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A countable actual group closed under the marker is fixed before one common limit preserves every ordered comparison.",
        H("Countable group zero-drift realization"), Blocks(
            Paragraph(Text("G is any group in Type u. U:G->G and c:G->G->R are total. RawCost means c(a,b)>=0, c(a,a)=0 and c(a*s,b*t)+c(a*U(s),b*U(t))+c(a*U(U(s)),b*U(U(t)))=3c(a,b)+3c(s,t) for every a,b,s,t. The group instances gG and gS displayed below supply the actual units, multiplication and inverses. No commutativity, countability or topology on G, marker homomorphism, U(1)=1, triangle inequality, Hilbert model, quotient or N5 premise is imposed.")),
            Entry("raw-group-right-invariant", "right_invariant", "Raw group costs are right invariant",
                Frame(Imp(Raw,All("a",I("G"),All("b",I("G"),All("z",I("G"),
                    Eqn(Cost("c",Mul(I("a"),I("z")),Mul(I("b"),I("z"))),Cost("c",I("a"),I("b")))))))),
                "Symmetry is absent. Fix a,b, put F(t)=c(a*t,b*t) and m=inf(range F). The range is nonempty and bounded below by zero. The full balance law at (a*t,b*t,w,w) gives F(t*w)<=3F(t)-2m. For each s, substituting w=t inverse times s makes the left side F(s) for every t. Thus (F(s)+2m)/3 is a lower bound for range F, so F(s)<=m; the converse follows from the infimum property. Hence F is constant. This infimum argument uses neither symmetry nor marker anchoring."),
            Entry("raw-group-inverse-budget", "inverse_budget", "Inversion preserves the unit budget",
                Frame(Imp(Raw,Imp(Sym("G","c"),All("x",I("G"),
                    Eqn(Cost("c",Inv(I("x")),D(1)),Cost("c",I("x"),D(1))))))),
                "Apply this module's right_invariant to (x inverse,1,x), then use the given symmetry. The inverse branch of group19_3 uses this equality on the actual coordinate groups."),
            Entry("raw-group-countable-zero-drift", "group19_3", "One actual countable group preserves the complete finite matrix",
                GroupStatement(),
                "The finite indexing type alpha is arbitrary in Type v and f:alpha->G is arbitrary. Empty types, repeated labels, the unit label and zero costs are retained. The existential S lies in Type u, has the displayed genuine Group instance and Countable instance, and supports one total V, one total real-valued d and one source assignment x for all pairs. The equality d(V(1),1)=0 is a cost statement and asserts no object equality V(1)=1. The source assignment is not asserted to preserve multiplication, inverse, unit or marker."),
            new DocumentBlock.Section(H("Actual carrier and one common limit"), Blocks(
                Paragraph(Text("Word alpha has exactly five constructors: unit, source, mul, inv and mark. eval interprets every finite word in an actual group with an arbitrary total marker. wordGroup is the range of eval as a Subgroup: unit, multiplication and inverse closure are object-level facts before any limits. wordMarker stays in this subgroup using the mark constructor, and label uses the source constructor. Product G is the product over natural n of the actual coordinate group (Sigma(n+1)->G). Set W coordinatewise to arrayMarker U and X(a)(n)=gamma U (n+1) (f(a)). The fixed carrier S is wordGroup W X. Countability follows from Countable (Word alpha) and Set.countable_range; no countability of G is used.")),
                Paragraph(Text("raw_replication gives RawCost and the exact source matrix in every coordinate, together with omega_N=omega(U,c)/(n+1). Symmetry is transported by the finite sum. Word induction gives coordinate-independent finite budgets: B(unit)=0, B(source a)=3c(f(a),1)+3omega, B(mul s t)=3(B(s)+B(t)), B(inv s)=B(s), and B(mark s)=18B(s)+24omega. The inverse case uses inverse_budget on each actual coordinate group. The marker case uses the raw_replication estimate at replication size one. unit_compare bounds each ordered pair by 3(B(s)+B(t)).")),
                Paragraph(Text("The countable product of the intervals [0,3(B(s)+B(t))], indexed by all ordered pairs in this same S, is compact and supplies one convergent subsequence. Its limit d(s,t) exists simultaneously for every pair. All five entries of each balance identity use this common subsequence, as do symmetry and the diagonal. Nonnegative summands bound cost(V(1),1) by omega_N, which tends to zero. The exact coordinate source matrix has constant entries, so the same limit preserves every c(f(a),f(b)). The proof never takes independently chosen limits for different pairs and never adds inverse or marker closure after taking the limit.")))),
            new DocumentBlock.Section(H("Source correspondence and boundaries"), Blocks(
                Paragraph(Text("The source is AURIC_C133_UNANCHORED_MARKER_FINITE_POSITIVITY_BRIDGE, Lemma 19.3. Its finite-subset formulation is obtained by taking alpha to be that finite subtype and f its inclusion; this theorem also permits repeated and empty indexing. The word-range subgroup realizes the source's iterative marker-closed generated subgroup. The common compact-product subsequence supplies the source's common diagonal limit.")),
                Paragraph(Text("The implementation reuses RawUnanchoredReplication.gamma and its checked normalization, rather than identifying it with the paper's differently normalized displayed Gamma. It uses the sufficient marker budget 18B+24omega. It does not prove the paper's stronger displayed budget 3B+3omega or its separate displayed Gamma-unit budget. These intermediate differences leave the full existential conclusion and all its hypotheses intact. RawUnanchoredReplication.raw_zero_drift has a MulOneClass term carrier without inverse closure and is not used as a substitute for a genuine group.")),
                Paragraph(Text("RawUnanchoredReplication.raw_replication, single and unit_compare supply the replication and ordered-pair bounds. Mathlib supplies conditional infima, subgroup operations, countable ranges, compact products and IsCompact.tendsto_subseq. This construction claims no literature novelty.")),
                Paragraph(Text("Lemma 19.2's zero-cost quotient, normality and marker descent remain separate obligations. No 19.4 or 19.5 positivity, Hilbert representation, uniqueness or full classification follows here. Physical preparations, measurements, joint operations, reference systems, time operations and empirical realization require their own contracts. A finite comparison realization does not provide those structures.")))))));

    private static Formula GroupStatement()
    {
        var s=I("S"); var a=I("alpha");
        Formula conclusion=And(Call("RawCost",I("V"),I("d")),And(Sym("S","d"),
            And(Eqn(Cost("d",Call("V",D(1)),D(1)),D(0)),
                All("a",a,All("b",a,Eqn(Cost("d",Call("x",I("a")),Call("x",I("b"))),
                    Cost("c",Call("f",I("a")),Call("f",I("b")))))))));
        Formula result=Ex("S",new Formula.Subscript(I("Type"),I("u")),Ex("gS",Call("Group",s),Ex("hS",Call("Countable",s),
            Ex("V",Arr(s,s),Ex("d",Arr(s,Arr(s,Real)),Ex("x",Arr(a,s),conclusion))))));
        return All("G",new Formula.Subscript(I("Type"),I("u")),All("gG",Call("Group",I("G")),
            All("alpha",new Formula.Subscript(I("Type"),I("v")),All("hAlpha",Call("Finite",a),
                All("U",Arr(I("G"),I("G")),All("c",Arr(I("G"),Arr(I("G"),Real)),
                    Imp(Raw,Imp(Sym("G","c"),All("f",Arr(a,I("G")),result)))))))));
    }
}
