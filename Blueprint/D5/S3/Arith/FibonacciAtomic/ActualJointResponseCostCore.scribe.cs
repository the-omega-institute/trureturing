using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualJointResponseCostCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual four-response routing has a finite simultaneous cost core for globally total tree membership strategies.",
        H("Actual Joint Response Cost Core"),
        Blocks(
            Def("addressOrder", "Shortlex address order", "Shorter words precede longer words; at equal length left precedes right."),
            Def("survivors", "Actual response children", "The child keeps exactly those current indices whose full-vector coordinate equals the actual reported reply."),
            Def("representative", "First shortlex representative", "Each realized complete vector uses its first actual address in shortlex order, with left before right. Replacement preserves every coordinate, including coordinates outside the current survivor set."),
            Def("Recipe", "Strict recursive splitting", "A non-singleton survivor set selects a realized vector having at least two replies. Only its nonempty response children recurse. A singleton ends routing and chooses its prototype verifier; it does not certify an unknown input."),
            Def("gain", "Recursive chi gain", "Each strict split adds chi of the retained actual coordinate to its child gain; singleton gain is zero."),
            Def("Gamma", "Recursive excess vectors", "Gamma(S) contains the coordinate restrictions of every finite splitting recipe's recursively accumulated chi gains. A singleton has zero gain. Every nonempty child is strictly smaller."),
            Def("core", "All numerical core vectors", "The core contains every vector n+gain(r) on the full index set, including vectors dominated by other recipes. It is defined by splitting choices independently of attained strategy costs."),
            Def("Controller", "Finite phase controller", "A finite query tree either accepts or enters actual acquisition. Unexpected replies enter fallback."),
            Def("controllerPolicy", "Own-history phase replay", "Routing consumes only its own requested prefix. After entry to a verifier or fallback, only that continuation's independently acquired suffix is presented as its logical history."),
            Def("controllerOutcome", "Actual phase outcome", "Truthful reports follow actual queries. Fallback outcome is exactly its independently initialized acquisition execution."),
            Def("verifyController", "Complete labelled-leaf test", "The verifier requests the complete fixed prototype leaf list. Exact matches continue; any mismatch starts fresh acquisition. Acceptance requires every labelled leaf."),
            Def("recipeController", "Real representative routing", "Each recipe split requests its first actual full-vector representative and follows the actual reply. Singleton routing selects a complete verifier."),
            Def("routeTrace", "Actual prototype route", "This chronological list contains the truthful requested representative reports, with verifier and fallback reports excluded."),
            Def("recipeStrategy", "Actual total realization", "The strategy requests actual representatives, then the selected prototype's complete labelled leaves. Unexpected routing replies and any leaf mismatch begin the all-input fallback. Each verifier and fallback receives its own empty logical history; prior truthful reports only answer addresses it actually requests."),
            Describe.Lean(DescribeId.Create("actual-joint-response-verifier"),
                DeclarationHandle.Create(Prefix + "verifier"), H("Arbitrary prototype query lists"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every prototype, input and finite address list, the verifier accepts exactly when every listed report matches the prototype or the input is a third substitution image."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-joint-response-matched"),
                DeclarationHandle.Create(Prefix + "matched"), H("A prototype reproduces its query list"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every prototype and finite address list, its own verifier returns precisely the truthful reports at those addresses and accepts."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-joint-response-cost-foundation"),
                DeclarationHandle.Create(Prefix + "cost_foundation"), H("Distinct leaves and exact recipe costs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every tree has a duplicate-free leaf list, and chi of a report is zero exactly at a leaf address. Every recipe on a positive family reproduces its controller outcome on retained prototypes. Its route has distinct joint response vectors and distinct addresses, with length at most the survivor cardinality minus one. Its gain is both the sum of report charges and the number of route addresses outside the leaf set, so its cost is the leaf-list length plus that gain. Every full-family core coordinate lies between its leaf baseline and that baseline plus the family cardinality minus one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-joint-response-cost-core-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Simultaneous attainment and coordinatewise domination"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("All index quantifiers range over Fin(m), and P_i=F(i). Let m be positive and F=(P_i) consist of pairwise distinct actual third-substitution images. "
                        + "Write L_i for the complete leaf-address set, n_i for its cardinality, V for the core, "
                        + "T_r(i) for the truthful representative routing trace and B_r(i) for its distinct-address set. "
                        + "J_sigma(P_i) is the paid set of the canonical terminal execution. In the formula, "
                        + "A_r(i) is the routing address list and V_r(i) its list of complete joint response vectors; "
                        + "E_r(i) is the chronological sum of chi over the truthful routing replies; it also equals the Finset sum over the actual routing address set.")),
                    Paragraph(Text("The core is finite and nonempty. Every member is attained simultaneously by one fixed globally correct total strategy. "
                        + "For every original globally correct total strategy, a single core vector is no larger in any prototype coordinate. "
                        + "Each coordinate lies between its complete-leaf baseline and that baseline plus m-1.")),
                    Paragraph(Text("Every positive prototype leaf is compulsory: changing its label gives a negative tree of the same shape and preserves every other address report. "
                        + "Deterministic same-history replay therefore prevents a correct accepting execution from omitting that leaf. "
                        + "Matching all labelled leaves forces literal equality of ordered trees.")),
                    Paragraph(Text("The fallback requests the root, expands only actual branch reports, and reconstructs each finite input. "
                        + "The measured leaf count bounds a finite enumeration of actual preimages because native substitution never decreases that count. "
                        + "Forward comparison decides membership for positive and negative inputs, including both root leaves. "
                        + "Routing and verification add finite phases before this independently initialized fallback.")),
                    Paragraph(Text("On P_i, routing retains i and selects its own complete verifier. The final paid set is exactly B_r(i) union L_i. "
                        + "An earlier full vector is constant on all descendants of its selected response child, so it cannot split there again. "
                        + "Full vectors and their representative addresses are therefore nonrepeating. Strict survivor decrease bounds routing by m-1. "
                        + "A routing leaf address is already in L_i; every other routing address adds exactly one paid address. "
                        + "This gives the exact response-dependent excess and attained cost. The source theorem also carries the literal Finset sum over the actual paid routing set: sum_{u in B_r(i)} chi(readout(u,P_i)) equals the paid routing set outside L_i.")),
                    Paragraph(Text("For domination, restrict an original strategy to the finite union of addresses in its actual prototype terminal traces. "
                        + "The restricted selector has exactly those executions. Public passive-policy normalization supplies one pruned protocol, "
                        + "preserving terminal candidate fibers and retaining sublists of those traces. Compulsory leaves and labelled-leaf rigidity make every terminal fiber a singleton. "
                        + "Converting that protocol to a recipe preserves complete vectors and chi. Its retained original nonleaf addresses are distinct members "
                        + "of the same original prototype's paid set outside L_i. Representative substitution transfers no old-address cache entries. "
                        + "The complete verifier restores the leaf baseline, giving simultaneous coordinatewise domination.")),
                    Paragraph(Text("Applying the construction to the independently total fallback gives nonemptiness. Bounded coordinates give finiteness. "
                        + "When m=1 the route is empty and the complete leaf verifier remains; no unknown-input promise is introduced. "
                        + "The statement concerns deterministic global strategies and prototype evaluation costs. The original per-source random contracts, their measurable null seed exceptions, extended costs, and "
                        + "and their optimization formulas are separate contracts."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-joint-response-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x,i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, RowBreak, Par(x))).ToArray());
    private static Formula Vars(string names) => Seq(names.Split(',').Select((name,i) =>
        i == 0 ? V(name) : Seq(Comma,Sp,V(name))).ToArray());
    private static Formula All(string x, Formula f) => Seq(Forall, Sp, Vars(x), Comma, Sp, Par(f));
    private static Formula Some(string x, Formula f) => Seq(F.Exists, Sp, Vars(x), Comma, Sp, Par(f));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula InOf(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula ResultFormula()
    {
        Formula m=V("m"), f=V("F"), i=V("i"), r=V("r"), sigma=V("sigma"), pi=V("pi"), v=V("v");
        Formula core=Call("core",f), n=Call("n",i), b=Call("B",r,i), l=Call("L",i);
        Formula excess=Call("card",Call("difference",b,l)), cost=Call("C",sigma,Call("P",i));
        Formula attained=All("v",Imp(InOf(v,core),Some("r,sigma",And(
            Call("Recipe",f,r),Call("Strategy",sigma),EqOf(sigma,Call("recipeStrategy",r)),All("i",And(
                EqOf(cost,Call("coordinate",v,i)), EqOf(Call("J",sigma,Call("P",i)),Call("union",b,l)),
                Call("Nodup",Call("V",r,i)), Call("Nodup",Call("A",r,i)),
                LeOf(Call("length",Call("T",r,i)),Sub(m,D(1))),
                EqOf(excess,Call("E",r,i)),
                EqOf(Call("sum",Seq(V("u"),Sp,InMacro,Sp,b),Call("chi",Call("readout",V("u"),Call("P",i)))),excess),
                EqOf(cost,Add(n,excess))))))));
        Formula comparison=All("i",LeOf(Call("coordinate",v,i),Call("C",pi,Call("P",i))));
        Formula dominated=All("pi",Imp(Call("Strategy",pi),Some("v",And(InOf(v,core),comparison))));
        Formula bounds=All("v",Imp(InOf(v,core),All("i",And(LeOf(n,Call("coordinate",v,i)),
            LeOf(Call("coordinate",v,i),Sub(Add(n,m),D(1)))))));
        Formula hypotheses=And(LeOf(D(1),m),Call("Injective",f),All("i",Call("Positive",Call("P",i))));
        return Disp(All("m,F",Imp(hypotheses,And(Call("Finite",core),Call("Nonempty",core),attained,dominated,bounds))));
    }
}
