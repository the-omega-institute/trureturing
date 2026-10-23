using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu;
internal sealed class NativeInclusiveImagePartitionDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => F.Id(n);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula IffOf(Formula a, Formula b) => Seq(P(a), Sp, Iff, Sp, P(b));
    private static Formula Imp(Formula a, Formula b) => Seq(P(a), Sp, Implies, Sp, P(b));
    private static Formula Arr(Formula a, Formula b) => Seq(P(a), Sp, To, Sp, P(b));
    private static Formula All(string n, Formula t, Formula f) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, P(f));
    private static Formula Some(string n, Formula t, Formula f) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, P(f));
    private static Formula Conj(params Formula[] fs)
    {
        Formula result = P(fs[0]);
        for (int i = 1; i < fs.Length; i++) result = Seq(result, Sp, Land, Sp, P(fs[i]));
        return result;
    }
    private static Formula C => V("currentRow");
    private static Formula B => Call("relativeDepth", V("M"));
    private static Formula Ret => Call("Retained", C, B);
    private static Formula Raw => Call("Profiles", C, B);
    private static Formula Vars => Call("Variables", V("eta"));
    private static Formula Val => Call("Valuations", V("eta"));
    private static Formula Cls => Call("Classes", C);
    private static Formula Values(Formula u) => Call("sourceValues", u);
    private static Formula At(Formula f, Formula a) => Call("apply", f, a);
    private static Formula Profile(Formula u) => Call("profile", B, u);
    private static Formula Part(Formula u) => Call("partitionEquiv", B, u);
    private static Formula Point(Formula eta, Formula v) => Call("point", eta, v);
    private static Formula Filled(Formula values) => Call("evaluateRow", Call("extend", C, values), C);
    private static Formula Sub(Formula u) => Call("substitution", Call("val", u));
    private static Formula NativeTarget(Formula u) => Call("canonicalRow", V("P"), Call("val", u));
    private static Formula PV => Point(V("eta"), V("v"));
    private static Formula Old => Call("oldValues", Call("val", V("eta")), Call("underlyingValues", V("v")));
    private static Formula GoodAt(string e, Formula u) => Call("Good", V("M"), V(e), V("L"), u);
    private static Formula CellGoodAt(string e) => Call("cellGood", V("M"), V(e), V("L"), V("eta"));
    private static Formula ImageLaw() => All("eta", Raw, All("v", Arr(Vars, V("BranchImage")),
        IffOf(Call("Image", Call("evaluate", Call("underlyingValues", V("v")), Call("wholeTerm", V("eta")))),
            Call("J", Call("wholeTerm", V("eta"))))));
    private static Formula ExtractionLaw() => All("u", V("Fiber"), Conj(
        EqOf(Filled(Values(V("u"))), Sub(V("u"))),
        EqOf(Call("val", Profile(V("u"))), Call("exposeValues", B, Values(V("u")))),
        All("d", Cls, EqOf(Call("subtree", Call("representative", C, V("d")), Sub(V("u"))),
            Call("some", At(Values(V("u")), V("d"))))),
        EqOf(Point(Profile(V("u")), Call("snd", Part(V("u")))), V("u"))));
    private static Formula InverseLaw()
    {
        var d = V("d");
        var x = V("x");
        var pattern = At(Call("val", V("eta")), d);
        var reached = Call("subtree", Call("address", pattern, x), At(Values(PV), d));
        var inserted = Call("some", Call("val", At(Call("val", V("v")), Call("sigma", d, x))));
        var extraction = All("d", Cls, All("x", Call("Frontier", pattern), EqOf(reached, inserted)));
        return All("eta", Ret, All("v", Val, Conj(
            EqOf(Part(PV), Call("sigma", V("eta"), V("v"))),
            EqOf(Sub(PV), Filled(Old)), extraction)));
    }
    private static Formula Singleton() => Imp(Call("IsEmpty", Call("Variables", Call("val", V("eta")))),
        Seq(Exists, Bang, Sp, V("u"), Colon, Sp, V("Fiber"), Comma, Sp, P(EqOf(Profile(V("u")), V("eta")))));
    private static Formula LiveFamily() => Imp(Call("Nonempty", Call("Variables", Call("val", V("eta")))),
        Some("f", Arr(V("Nat"), Call("Cell", V("eta"))), Call("Injective", V("f"))));
    private static Formula DataLaw() => All("u", V("Fiber"), Imp(EqOf(Profile(V("u")), V("eta")), Conj(
        All("q", V("Q"), EqOf(Call("readout", Call("addr", V("M"), V("q")), Sub(V("u"))), Call("cellReplies", V("M"), V("eta"), V("q")))),
        EqOf(NativeTarget(V("u")), Call("cellTarget", V("eta"))),
        IffOf(GoodAt("e0", V("u")), CellGoodAt("e0")),
        IffOf(GoodAt("e1", V("u")), CellGoodAt("e1")))));
    private static Formula CellsLaw() => All("eta", Ret, Conj(
        Call("Nonempty", Call("Cell", V("eta"))), Singleton(), LiveFamily(),
        Call("Countable", Call("Cell", V("eta"))), DataLaw()));
    private static Formula Statement()
    {
        var conclusion = Conj(EqOf(C, V("originalRow")), EqOf(Call("card", Cls), D(6)),
            Call("Finite", Ret), ImageLaw(), ExtractionLaw(), InverseLaw(), CellsLaw());
        var capped = All("L", V("Nat"), conclusion);
        var distinct = Imp(Call("Ne", V("e0"), V("e1")), capped);
        var entries = All("e0", Call("Sum", V("Q"), V("H")),
            All("e1", Call("Sum", V("Q"), V("H")), distinct));
        var table = All("M", Call("Controller", V("Q"), V("H")), entries);
        var finite = Seq(Forall, Sp, OpenBracket, Call("Fintype", V("Q")), CloseBracket, Sp,
            OpenBracket, Call("Fintype", V("H")), CloseBracket, Comma, Sp, P(table));
        return All("Q", V("Type"), All("H", V("Type"), finite));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inclusive branch-image profiles of every original native origin, with exact cell multiplicities and complete good-entry behavior.",
        H("Inclusive Image Profiles and Exact Native Cells"), Blocks(
            Paragraph(Text("Sources are all finite nonempty ordered Boolean trees. The leaf true is alpha and false is beta; false and true address letters are left and right. Substitution sends alpha to beta, beta to the pair (beta,alpha), and preserves ordered pairs. Its image consists of beta, the exceptional literal pair (beta,alpha), and pairs of images. The original image inverse is unique. Every branch subtree of an image is an image, although a literal alpha can occur as the right child of the exceptional pair.")),
            Paragraph(Text("The cut P is all eight words of length three. The fixed complete current row has first-member names (0,1,0,3,4,5,4,7). Its six different classes have names 0,1,3,4,5,7. The original order (a,c,b1,b2,b3,b4) corresponds to these names as (0,4,1,3,5,7). The a and c partners each occur twice, using the same entire class value at both occurrences. Different classes assert all fifteen unordered whole-value disequalities. currentRow equals this entire original row, including exterior and partition. The actual domain is exactly NativeSixSourceCones.Fiber: every finite u with canonicalRow(P,substitution(u)) equal to that row. There is no source-size, height, intrinsic-rank, history or chosen-family bound.")),
            Paragraph(Text("For any immutable finite Controller Q H, relativeDepth(M) is the maximum of zero and length(M.addr(q))-3 over all installed running states. Natural subtraction contributes zero for short words. The maximum uses unused states, states reached only from the other entry, and duplicate literals as separate installed coordinates. If Q is empty the maximum is zero. This is a bound on the installed menu and places no bound on sources.")),
            Paragraph(Text("Pattern(b) records nodes through inclusive relative depth b. At b=0 there are exactly two literal leaves and one branch marker. At positive depth there are the two literal leaves or a pair of smaller patterns. An early leaf stops descent and fixes all strict descendant replies as absent. Frontier contains one position only for a branch marker at depth b; it is empty below a recorded literal leaf. A name is a pair of a class coordinate and a frontier position. Distinct names are independent and their values may coincide. Repeated partner occurrences reuse the same class pattern and the same names. BranchImage requires an actual finite image with branch root, so a name cannot turn into a leaf or a nonimage.")),
            Paragraph(Text("oldTerm expands each pattern into original ordered free syntax. wholeTerm substitutes these terms synchronously into the complete current row. Numbering the finite name type changes only variable labels. J applies the original NativeClassRootImage.im grammar with every name assigned branch root type: J(alpha) is false; J(beta) and J(name) are true; J(pair(A,B)) holds exactly when A is literally beta and B literally alpha, or both J(A) and J(B) hold. NativeClassRootImage.filling_image_iff proves that J is exact under every BranchImage filling. No image or realization bridge is supplied as an assumption.")),
            Paragraph(Text("Retained contains exactly the finite profile tuples with J(wholeTerm) and injective whole free class syntax. Valuations contains every BranchImage assignment for which the evaluated whole class terms remain pairwise different. It imposes no injectivity requirement on the name assignment itself. assemble evaluates the complete row. actualProfiles exposes the recovered original class values; actualFilling extracts the actual reached branch subtrees. The fill and extraction identities prove imageProfileEquiv, and composing with the original imageOriginEquiv proves partitionEquiv on the original unbounded fiber. Both inverse identities, complete source reconstruction and extraction at every named position are conclusions.")),
            Paragraph(Text("Joint realization uses two different all-beta branch images of three leaves as Boolean markers. Placing one selected marker in a right comb and adjoining beta gives branchCode(n,i), an injective finite tuple of branch images with common leaf mass 3*n+2. Choose n above the number of live names and the leaf masses of all six whole free terms. NativeGroundSeparation.bounded_eval_injective then reflects equality simultaneously for the entire finite syntax class. Consequently one lawful assignment satisfies every whole-class negative at once, including negatives involving closed pieces. This uses the original bounded separation result inside the branch-image construction.")),
            Paragraph(Text("family replaces n by n+k for every natural k. Every assignment remains lawful and stays in exactly the same inclusive profile. At any fixed live position, its inserted subtree mass is 3*(n+k)+2 and strictly increases. The corresponding valuations, entire current trees and inverse origins are therefore all different. cellEquiv identifies these valuations with precisely the original actual cell. If there are no live names, the empty assignment is unique and the cell has exactly one actual origin. If there is a live name, family yields an injective natural-number family inside that same cell. Existing finite-tree coding makes each actual cell countable, proving exact countable infinity.")),
            Paragraph(Text("Every installed word shorter than three reads a fixed exterior branch. A longer word consists of one original depth-three occurrence and a relative suffix of length at most b. The inclusive pattern fixes that suffix reply, including frontier branches and all absences below early leaves. Both occurrences of each partner and all unused or duplicate reads are retained. Root replies are also fixed at b=0. The original native_full_root_feasibility theorem therefore fixes the entire canonical predecessor row on each cell, including support, exterior, partition, recomputed names and blocking guards. cellReplies and cellTarget are defined from an attained point of that same cell and agree with every actual point in it.")),
            Paragraph(Text("Good(M,e,L,u) means that the original native Run starts at the unchanged entry e on exactly substitution(u), has an actual paid running-state trace of length at most L, and returns the entire stored LiteralRow equal to canonicalRow(P,u). The public native_evaluate_iff preserves that exact trace and cap. Equal installed replies make the bounded evaluators identical, and equal whole targets make Good constant. The theorem states this for both distinct originally labeled entries e0 and e1 on the same cells. Cycles, shared states, early or wrong halts, unused states and duplicate outputs remain allowed. At L=0 only a correct initial Halt succeeds; a Halt immediately after the final allowed call also succeeds, while a running state at cap does not. No correctness condition on the other entry is assumed.")),
            Describe.Lean(DescribeId.Create("inclusive-image-exact-native-partition"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeInclusiveImagePartition.finite_exact_native_partition"),
                H("Finite Exactly Attained Partition of the Original Fiber"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The finite index type is exactly Retained(currentRow,relativeDepth(M)). For every actual origin the conclusion gives its exact inclusive exposure and complete current reconstruction. Conversely every lawful retained valuation has its unique original inverse and recovers its own profile and frontier values. Every index is attained. Closed cells have a unique actual member; live cells have an injective natural family and are countable. Every installed reply, the entire target and both native Good predicates factor through this one index. The original cap is an arbitrary natural value, including zero; positional binary representation does not change this semantic statement. In the formula, P and originalRow are NativeSixSourceCones.P and row. underlyingValues(v) is x mapped to (v(x)).val, exposeValues(b,f) is d mapped to expose(b,f(d)), apply is function application, sigma is the dependent pair, snd is its second component, and val is the corresponding subtype projection. Injective abbreviates Function.Injective. These are notation for the exact Lean operands.")),
                    Paragraph(Text("This result asserts existence and exactness of the full finite partition. It asserts no efficient construction of that partition. Lawful acquired-code synthesis, language complexity, native preparation and unrelated construction-cost claims are separate questions."))), DescribeRole.Theorem)
        )));
}
