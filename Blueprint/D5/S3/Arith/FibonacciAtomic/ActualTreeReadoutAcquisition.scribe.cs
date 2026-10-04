using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualTreeReadoutAcquisitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Truthful address reports force complete positive-tree leaf acquisition and allow total membership decisions on every finite tree.",
        H("Actual Tree Readout and Acquisition"),
        Blocks(
            Def("Address", "Actual addresses", "Addresses are finite left/right words, including the empty root. False is left and true is right."),
            Def("Reply", "Four truthful replies", "A report is an alpha leaf, beta leaf, branch, or absence in the same immutable ordered finite tree."),
            Def("readout", "Unrestricted original readout", "Every finite address is legal without querying its prefixes. No composition, size, height, leaf count, positivity, candidate-family membership, or identity is supplied."),
            Def("leaves", "Complete leaf frontier", "The fixed left-to-right list contains all actual leaf addresses. Their labels are supplied by readout."),
            Def("nodes", "Actual nodes", "Preorder node addresses include each branch and leaf, beginning at the root."),
            Def("flip", "One-leaf competitor", "Flipping an actual addressed leaf changes its label and preserves the full ordered shape."),
            Def("Positive", "Third actual substitution image", "Positive(U) means that an actual source T satisfies rho cubed(T)=U, with rho the native Fibonacci substitution."),
            Def("Policy", "History-only selector", "The next query or returned Boolean depends only on the selector's own chronological address-response history. Common initialization is independent of the unknown input."),
            Def("Strategy", "All-input deterministic contract", "The same policy starts at empty history and has a finite correct terminal execution on every finite source. Fuel witnesses pointwise termination and is not information supplied to the policy."),
            Def("paid", "Distinct actual payment", "All requested reports, including repetitions, enter history. Each different actual address is paid once; repetitions use truthful cached reports."),
            Def("terminal", "Unique terminal execution", "Pointwise totality selects a terminal history and output. Determinism makes this pair independent of the chosen successful fuel."),
            Def("cost", "Finite deterministic cost", "Cost is the cardinality of the terminal paid address set. Internal computation, positioning and address length have no price."),
            Def("chi", "Response-dependent excess", "Chi is zero on both labelled leaves and one on branch and absence. It accounts for route addresses outside the complete leaf baseline."),
            Def("extendedCost", "Extended policy cost", "Any finite return pays for its different requested addresses, including wrong returns. Failure to terminate at any finite fuel has cost positive infinity."),
            Def("wrongReturn", "Wrong-return event", "A seed is wrong on a source when a finite execution returns a Boolean different from the actual image-membership bit."),
            Def("diverges", "Nontermination event", "A seed diverges on a source precisely when no finite-fuel execution returns."),
            Def("RandomContract", "Original per-source random contract", "For each fixed source separately, the wrong-return and nontermination seed events are measurable and have measure zero, and the nonnegative extended cost is measurable. Null exceptional seeds are allowed. Neither completeness, measurable transcripts, nor an assumed common good-seed set is required."),
            Def("RandomStrategy", "Arbitrary seed probability space", "A strategy carries its own seed type, sigma algebra, probability law and history-only policies. The seed law is independent of the input; the same seed and same history determine the same query, cache use, stop and output."),
            Def("Seed", "Literal uniform carrier", "Seed is the closed unit interval, including both endpoints, equipped with the completed Lebesgue sigma algebra."),
            Def("unitSeedMeasure", "Uniform seed law", "The law is completed Lebesgue probability measure on the closed unit interval."),
            Def("UniformRandomStrategy", "Uniform random contract", "The same per-source measurable-null-exception contract is used on the fixed uniform probability space."),
            Def("maxOn", "Nonempty family maximum", "MaxOn takes the finite maximum of extended nonnegative costs over Fin(m), with m positive."),
            Def("randomExpected", "Own-law expectation", "The nonnegative integral uses this strategy's own input-independent seed law and allows infinite values."),
            Def("D", "Deterministic objective", "D(F) is the infimum of the maximum prototype cost over all globally correct total deterministic strategies."),
            Def("R", "Worst fixed-source expectation", "R(F) is the infimum over the original arbitrary seed probability spaces of the maximum of the fixed-prototype expected extended costs."),
            Def("Ru", "Uniform fixed-source expectation", "Ru(F) restricts the preceding infimum to the fixed completed Lebesgue unit-interval seed space."),
            Def("W", "Shared-seed objective", "W(F) integrates the maximum prototype cost at one common controller and seed, then takes the infimum over arbitrary original random strategies."),
            Def("Wu", "Uniform shared-seed objective", "Wu(F) uses that same shared-seed maximum and the fixed uniform seed space. None of these objectives assigns a prior to prototypes or unknown sources."),
            Def("vector", "Full joint responses", "Vector(F,u) is the complete m-coordinate tuple of actual reports at u, retaining coordinates outside any current survivor set."),
            Def("actualVectors", "Actual vector range", "Only vectors produced at actual addresses occur. A finite union of prototype nodes realizes all non-absent vectors; addresses outside it yield the common all-absent vector."),
            Def("alphaValid", "One-step alpha-position law", "Every alpha leaf is the right member of a terminal ordered pair (beta,alpha). Root alpha is excluded."),
            Def("cherryValid", "Two-step terminal-cherry law", "Every terminal cherry has the ordered labels (beta,alpha); branch descendants satisfy the same requirement."),
            Def("sourceLaw", "Third-image source obstruction", "SourceLaw combines the one-step alpha-position and two-step terminal-cherry requirements."),
            Describe.Lean(DescribeId.Create("actual-tree-readout-source-foundation"), DeclarationHandle.Create(Prefix + "source_foundation"),
                H("Leaf obstruction, rigidity and compulsory acquisition"), StatementSource.FromAuthor(SourceFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual positive tree and each of its leaves, the same-shape label flip is negative and every other address report is unchanged. Third substitution images satisfy sourceLaw; single substitutions satisfy alphaValid, and double substitutions satisfy cherryValid. Matching all labelled leaves forces literal ordered-tree equality. A deterministic correct accepting run must therefore acquire every positive leaf, by replay against the negative competitor. Two successful runs of the same policy from the same history on the same input have identical terminal histories and outputs."))), DescribeRole.Theorem),
            Def("acquisitionStep", "Actual frontier transition", "The head pending address is removed after its truthful report. A branch inserts its actual left and right children; a leaf inserts nothing."),
            Def("frontier", "Fresh acquisition frontier", "The pending work starts at the root and is computed only from this acquisition phase's own history."),
            Def("acquisitionTrace", "Actual finite traversal", "The finite preorder traversal records root, actual branches and leaves. It describes the execution for proof, and is not supplied to the unknown-input controller."),
            Def("AcquisitionRun", "Literal transition derivation", "The inductive relation follows the acquisition frontier transitions through the chronological acquired reports."),
            Def("restore", "Report-only reconstruction", "Restore reads only actually acquired reports. It reconstructs a branch from both descendants and refuses missing or absent-node descriptions."),
            Def("boundedSources", "Finite actual preimages", "Composition fibers enumerate all actual sources with at most the acquired leaf count; both root leaves remain in the finite enumeration."),
            Def("finiteDecision", "Finite forward comparison", "The acquired description is positive exactly when one of those finitely many actual candidate descriptions has third substitution equal to it."),
            Def("acquisitionPolicy", "Global actual acquisition", "This history-only policy asks for the root and expands only branch reports. Once reconstruction is complete, it decides by finite forward comparison. It has no hidden description, inverse query, or initial size bound."),
            Describe.Lean(DescribeId.Create("actual-tree-readout-acquisition-foundation"), DeclarationHandle.Create(Prefix + "acquisition_foundation"),
                H("All finite inputs terminate with the correct decision"), StatementSource.FromAuthor(AcquisitionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite source U, finiteDecision(U) is true exactly when U is positive, and acquisitionPolicy from empty history executes exactly the actual finite traversal before returning that bit. Native substitution never decreases leaf count, so every actual preimage lies in the finite enumeration. This proves finite rejection as well as finite acceptance, including both negative root leaves. Traversal reconstruction uses only acquired truthful reports."))), DescribeRole.Theorem),
            Def("fallback", "Independent total fallback", "The fallback uses the all-input acquisition policy from its own initial state and empty logical history. It is correct and finitely terminating on every actual finite input; it is independent of a finite prototype promise."))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-tree-readout-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x,i) => i == 0 ? Par(x) : Seq(Sp, Land, Sp, RowBreak, Par(x))).ToArray());
    private static Formula Vars(string names) => Seq(names.Split(',').Select((name,i) =>
        i == 0 ? V(name) : Seq(Comma,Sp,V(name))).ToArray());
    private static Formula All(string x, Formula f) => Seq(Forall, Sp, Vars(x), Comma, Sp, Par(f));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula InOf(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula SourceFormula()
    {
        Formula t=V("t"), u=V("u"), v=V("v"), p=V("p"), w=V("W"), x=V("X"), y=V("Y"), rho=Call("rhoThree",t);
        return Disp(And(
            All("t",EqOf(Call("sourceLaw",rho),V("true"))),
            All("t,u",Imp(InOf(u,Call("leaves",rho)),Seq(Neg,Call("Positive",Call("flip",rho,u))))),
            All("V,U",Imp(All("u",Imp(InOf(u,Call("leaves",V("V"))),EqOf(Call("readout",u,V("U")),Call("readout",u,V("V"))))),EqOf(V("U"),V("V")))),
            All("V,u,v",Imp(And(InOf(u,Call("leaves",V("V"))),Seq(v,Sp,Neq,Sp,u)),EqOf(Call("readout",v,Call("flip",V("V"),u)),Call("readout",v,V("V"))))),
            All("p,U",Imp(And(Call("Strategy",p),Call("Positive",V("U"))),Call("subset",Call("leaves",V("U")),Call("paid",Call("terminalHistory",p,V("U")))))),
            All("t",EqOf(Call("alphaValid",Call("rho",t)),V("true"))),
            All("t",EqOf(Call("cherryValid",Call("rhoTwo",t)),V("true"))),
            All("policy,n,m,h,U,X,Y",Imp(And(EqOf(Call("execute",V("policy"),V("n"),V("h"),V("U")),Call("some",x)),EqOf(Call("execute",V("policy"),V("m"),V("h"),V("U")),Call("some",y))),EqOf(x,y)))));
    }
    private static Formula AcquisitionFormula()
    {
        Formula u=V("U"), tr=Call("acquisitionTrace",V("emptyAddress"),u), decision=Call("finiteDecision",u);
        return Disp(And(All("U",Seq(EqOf(decision,V("true")),Sp,Iff,Sp,Call("Positive",u))),
            All("U",EqOf(Call("execute",V("acquisitionPolicy"),Seq(Call("length",tr),Plus,D(1)),V("emptyHistory"),u),Call("some",Call("pair",tr,decision))))));
    }
}
