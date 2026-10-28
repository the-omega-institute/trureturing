using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeMaterialRootRecognitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original material roots and syntax are rigid under complete linear terminal order; finite labelled presentations admit an effective inverse.",
        H("Original Material Root Recognition"), Blocks(
            Describe.Lean(DescribeId.Create("native-material-original-rigidity"),
                DeclarationHandle.Create(Prefix + "original_rigidity"),
                H("Universal Original Root and Coordinate Rigidity"),
                StatementSource.FromAuthor(RigidityFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Source is the existing FreeMagma Bool, with true denoting alpha and false beta. "
                        + "D(t) says that readout(pL,t) is never alpha, for every logical address p. "
                        + "Both sources range over this original domain and have at least three logical leaves. "
                        + "No global substitution image, positivity restriction, or alternate birth condition is used.")),
                    Paragraph(Text("C(alpha) is one terminal vertex. C(beta) has its logical root and a distinct "
                        + "left terminal marker. C(pair(l,r)) has its root and both ordered child material trees. "
                        + "The material list retains every vertex, including each beta marker; addresses use the "
                        + "existing Boolean lists and readout. The full terminal list recursively concatenates "
                        + "left then right rosters and replaces a beta logical leaf by its marker. "
                        + "Neighbors comprise outward children and the actual parent, with no supplied orientation "
                        + "in the isomorphism: neighborhood images are permutations, while the entire terminal "
                        + "list image is an equality at every position.")),
                    Paragraph(Text("A nonroot vertex of material degree two is a beta root with an adjacent "
                        + "degree-one marker. A branch root with no terminal neighbor is consequently the unique "
                        + "degree-two vertex without one. If the root has a terminal neighbor, original birth "
                        + "typing rules out a left alpha; that neighbor is the last terminal in the complete "
                        + "linear order. In the latter case both compared roots adjoin that same last terminal, "
                        + "whose unique neighbor forces root preservation. This excludes root ambiguity before "
                        + "any ordered navigation is assumed.")),
                    Paragraph(Text("Root preservation gives depth preservation in both directions, so children "
                        + "map outward. Each child has a terminal descendant. The complete linear terminal order "
                        + "rules out reversing two children, and a beta has its sole left marker child. "
                        + "Induction identifies every material coordinate. Support equality then gives literal "
                        + "readout equality; the existing source_foundation leaf-equality theorem identifies "
                        + "the original ordered source and all its logical constructors."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-material-effective-inverse"),
                DeclarationHandle.Create(Prefix + "effective_inverse"),
                H("Uniform Finite Recognition without Concealed Advice"),
                StatementSource.FromAuthor(InverseFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("FiniteInput supplies only its own vertex enumeration Fin(n), an arbitrary "
                        + "neighbor list for each vertex, and the complete linear terminal list. Recovery contains "
                        + "an original source and one material address for every input vertex. Fits checks coordinate "
                        + "length, permutation of the entire material support, every neighborhood permutation, "
                        + "the complete terminal list equality, the executable original birth check, and at least "
                        + "three logical leaves. It contains no assumed uniqueness or termination field.")),
                    Paragraph(Text("recover enumerates sources of exact material size n and all permutations of "
                        + "their material coordinates, then returns the first candidate satisfying Fits. The "
                        + "finite syntax catalog uses n as its recursion fuel and splits each pair size into its "
                        + "two positive child sizes. Its bounds come entirely from the supplied input. "
                        + "There is no runtime root, original term, Tag, old word, external size bound, or image witness.")),
                    Paragraph(Text("Every actual relabelling is a Fits witness only in the correctness proof. "
                        + "Catalog completeness supplies a candidate. Two successes induce a full unrooted "
                        + "terminal-order-preserving material isomorphism; universal rigidity identifies their "
                        + "sources and every vertex coordinate. Thus recovery returns the unique original parse. "
                        + "The input vertex whose recovered coordinate is empty is its original root. The complete "
                        + "degree-one roster is derived from the material representation and neighbor equations.")),
                    Paragraph(Text("The same correctness path checks the existing six-vertex LAB14.2 input "
                        + "for pair(pair(beta,alpha),alpha). Vertex indices are r=0,h=1,b=2,c=3,d=4,e=5; "
                        + "edges are r-h,r-e,h-b,h-d,b-c and the ordered terminals are c,d,e. "
                        + "Its candidate certificate is checked and passed to the uniform inverse theorem. "
                        + "The rival rooting at b lies outside D and is not a counterexample to this result.")),
                    Paragraph(Text("This is effectiveness by finite exhaustive search, with no polynomial runtime "
                        + "claim. Wave acquisition, first arrivals and subdivision reconstruction; weighted field "
                        + "laws, paid trials and the last-trial cut; persistent fields, guards, framing and adaptive growth; source "
                        + "binding, authority, calibration and backing; zero-field four-view common-image recovery; old serialization; "
                        + "and LAB7/15 numerical resource claims are separate obligations. No physical installation "
                        + "or full callable service is constructed here."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula AndOf(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula RigidityFormula()
    {
        Formula t=V("t"), s=V("s"), e=V("e"), p=V("p"), root=Call("nil");
        Formula conclusion=AndOf(EqOf(Call("forward",e,root),root),
            AndOf(All("p",V("Address"),Imp(Call("member",p,Call("material",t)),
                EqOf(Call("forward",e,p),p))),EqOf(t,s)));
        return Disp(All("t",V("Source"),All("s",V("Source"),
            Imp(Call("D",t),Imp(Call("D",s),
            Imp(Call("atLeastThreeLeaves",t),Imp(Call("atLeastThreeLeaves",s),
            All("e",Call("OrderedIso",t,s),conclusion))))))));
    }
    private static Formula InverseFormula()
    {
        Formula i=V("I"), r=V("R"), s=V("S");
        Formula sound=All("I",V("FiniteInput"),All("R",V("Recovery"),
            Imp(EqOf(Call("recover",i),Call("some",r)),
                AndOf(Call("Fits",i,r),Call("completeDegreeOneRoster",i)))));
        Formula inverse=All("I",V("FiniteInput"),All("R",V("Recovery"),
            Imp(Call("Fits",i,r),AndOf(EqOf(Call("recover",i),Call("some",r)),
                All("S",V("Recovery"),Imp(Call("Fits",i,s),EqOf(s,r)))))));
        Formula concrete=AndOf(EqOf(Call("recover",V("sixVertex")),Call("some",V("sixRecovery"))),
            All("S",V("Recovery"),Imp(Call("Fits",V("sixVertex"),s),EqOf(s,V("sixRecovery")))));
        return Disp(AndOf(sound,AndOf(inverse,concrete)));
    }
}
