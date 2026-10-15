using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeRepeatedPartnerControllersDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/Arith/FibonacciAtomic/Observer/NativeRepeatedPartnerControllers.";
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Six fixed common controllers attain the prescribed export, invocation and total-state counts on the entire actual repeated-partner inverse fiber.",
        H("Matching Full-Fiber Controllers"),Blocks(
            Paragraph(Text("The source domain is the entire infinite NativeSixSourceCones.Fiber. The acquired finite class values are recovered using the exact existing NativeClassRootImage chart. Their six root types give the acquired profile; no query obtains this profile after the access cut. NativeFullRootFeasibility.actual_type supplies precisely its admissibility, and native_full_root_feasibility supplies the whole predecessor-row target. NativeFiniteRootMinimax.finite_root_minimax supplies the executable target equality. The existing admissibleCode_spec is used directly to check the finite admissibility predicate.")),
            Paragraph(Text("The six positions are a,b1,b2,c,b3,b4. Their canonical class ordinals are 0,1,3,4,5,7. The acquired label is j exactly when right class bj has alpha root, and zero otherwise. A finite check of all admissible six-root assignments proves that its old occurrence mask and complete target are exactly holeList(j) and predecessor(j). This check includes arbitrary internal branches: the native chart and target bridge prove that root types suffice for this row. It is not a test of six example sources.")),
            Paragraph(Text("Every installed table has fixed literal addresses and fixed transitions for alpha, beta, branch and absent. All five halts output the complete canonical predecessor rows directly. In the ten-state table a partner state queries LLL; beta leads to the b1,b2 chain, branch leads to the b3,b4 chain, and alpha or absent leads to the zero halt. A right test takes alpha to its named positive halt. Its other replies take the prescribed next state or zero halt. The nine-state table checks b1,b2,b3,b4 sequentially. The eight-state table starts at b1 for labels 0,1,2 and at b3 for labels 3,4; it uses only b1,b2,b3. The seven-state table starts at the zero halt, b1 or b3 for blocks {0},{1,2},{3,4}. The six-state table starts at the corresponding halt for labels 0,1,2, and at b3 for {3,4}. The five-state table starts directly at its output halt.")),
            Describe.Lean(DescribeId.Create("nativerepeatedpartnercontrollers-matching-controllers"),
                DeclarationHandle.Create(Prefix+"matching_controllers"),H("Six Exact Attainments"),
                StatementSource.FromAuthor(Disp(And(
                    Call("Attains",V("ten"),V("constantEntry"),D(1),D(3)),
                    Call("Attains",V("nine"),V("constantEntry"),D(1),D(4)),
                    Call("Attains",V("eight"),V("entryEight"),D(2),D(2)),
                    Call("Attains",V("seven"),V("entrySeven"),D(3),D(1)),
                    Call("Attains",V("six"),V("entrySix"),D(4),D(1)),
                    Call("Attains",V("five"),V("inr"),D(5),D(0))))),
                AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("ConstantEntry maps every acquired label to running state zero. Attains asserts exact realized entry range cardinality, correctness and an invocation upper bound on every actual origin, an actual origin attaining that bound, and reachability on actual origins of every running and halting state. The respective finite running types are Fin 5, Fin 4, Fin 3, Fin 2, Fin 1 and Fin 0; every halt type is Fin 5. Hence the exact (capacity,calls,running,halts,total) tuples are (1,3,5,5,10), (1,4,4,5,9), (2,2,3,5,8), (3,1,2,5,7), (4,1,1,5,6), (5,0,0,5,5).")),
                    Paragraph(Text("The exported value is the whole entry state. Its realized range is proved equal to a finite set with the stated exact cardinality, so inclusion gives the recoverable complete-entry normalization. The encoder and controller are chosen together from the acquired data. These statements assume genuine acquisition, same-version authentication, lawful export and the access cut; they provide no fixed-arbitrary-encoder guarantee and no physical storage, time, table or address-production equivalence.")),
                    Paragraph(Text("All target-zero profiles are included: beta may occur at a, at c, at any bj, or nowhere, while branches can have arbitrary finite internal structure. A partner read is used as a group discriminator only where its actual reply and admissibility justify that transition. The all-fiber proof does not assume that partner queries are target-only group tests. Shared finite states and early halting entries are explicit in the exported-block controllers. The six simultaneous actual origins establish exact range, worst-case and reachability claims; universal correctness comes from the separate actual-profile bridge."))),DescribeRole.Theorem))));
    private static Formula V(string s)=>F.Id(s);
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] a)=>new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..a]);
    private static Formula And(params Formula[] fs)=>Seq(fs.Select((f,i)=>i==0?Par(f):Seq(Sp,Land,Sp,Par(f))).ToArray());
}
