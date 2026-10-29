using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeSignedObservationExtractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact signed observation extraction", H("One original source and all its signed observations"), Blocks(
            Paragraph(Text("Sources are arbitrary nonempty finite ordered Boolean trees. The unary operation is the interpreted native substitution: alpha becomes beta, beta becomes the ordered pair of beta and alpha, and substitution preserves pairs. All occurrences of one frontier name use one whole tree. Different names may receive equal trees.")),
            Entry("endpoint", "Mixed-epoch endpoint expressions",
                "Navigation follows the original finite skeleton. At the requested endpoint the entire remaining term is shifted by the actual epoch. An early original ground leaf is evolved explicitly before its descendants are inspected, so descendants born under substitution are included. A proper descent into an unspecified frontier is rejected. If the requested address is shorter than the original skeleton depth, that last case cannot occur. Evaluation of the returned optional mixed expression is exactly the actual optional whole subtree.", DescribeRole.Definition),
            Entry("comparison", "Both guards precede either sign",
                "Both optional endpoints must be present. A reached pair contributes one equality or one disequality of whole mixed native expressions. An absent endpoint rejects a negative comparison too. The sign does not turn absence into evidence of disequality.", DescribeRole.Definition),
            Entry("compileRecord", "Literal and positive records",
                "Literal replies are constant over all fillings of a sufficiently deep original skeleton, at every supplied epoch. They can therefore be tested on one fixed filling. Positive whole-subtree records retain their actual epochs, both addresses and both reached guards.", DescribeRole.Definition),
            Entry("compileList", "Conjunction without dropping occurrences",
                "The finite list compiler preserves order and repetitions. None denotes a rejected branch, while some empty list denotes the empty conjunction. Every negative record uses the same source term and the same variable valuation as every positive record.", DescribeRole.Definition),
            Entry("ExtractedHolds", "Complete rows remain explicit",
                "The extracted predicate keeps the complete symbolic old and target row records, including concrete exteriors, reached holes, all equality pairs and all cross-class disequalities. Uncut frontier variables remain in the symbolic exterior. The two compiled signed programs are imposed on those same variables. This predicate is an exact observation reduction; its row constraints have not yet been eliminated into a positive native image chart.", DescribeRole.Definition),
            Entry("requiredDepth", "An input-computed finite case depth",
                "Take one plus the maximum length of every old and new cut address and every literal, positive and negative endpoint address. The maximum of an empty set is zero. Epoch magnitudes do not enter this bound. Pattern at that depth is a finite type, and each pattern retains every reached frontier position.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("signed-entire-input-extraction"),
                DeclarationHandle.Create(Prefix + "entire_input_extraction"),
                H("Exact same-original finite pattern reduction"),
                StatementSource.FromAuthor(Disp(Extraction())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For arbitrary finite prefix-free cuts P and Q, arbitrary complete row labels old and target, arbitrary lists H of literals and positive records and K of negative records, and every original source u, the entire input holds exactly when one pattern p at requiredDepth P Q H K and one unrestricted frontier valuation v reconstruct u itself and satisfy ExtractedHolds for patternTerm p id. Contradictory inputs have no satisfying valuation. Empty cuts, empty lists, root cuts, partly absent cuts and patterns with no frontier variables remain included.")),
                    Paragraph(Text("The endpoint proof descends through original pair nodes, uses preservation of pairing by every native power, and computes descendants of early evolved leaves literally. It then proves both guarded signs and concatenation of every supplied record. Exact symbolic recutting supplies both complete row records. Finally the existing depth equivalence selects the actual pattern and actual frontier subtrees of u; filling them returns that same original u.")),
                    Paragraph(Text("This result supplies finite signed observation extraction within the complete original-source stratum construction. It does not synthesize positive whole-tuple native image charts, eliminate the symbolic row constraints, recognize the image-saturation class, construct a completed limit, fix cofinal finite parameters or decide the all-depth alternative. Paid acquisition, complete accessible-state factoring and authentic service epochs remain separate operational premises. Symbolic coordinates supply no original-register read, inverse, reset, clone or free equality operation."))), DescribeRole.Theorem)
        )));

    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("signed-extraction-" + n.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Extraction()
    {
        var p = V("p");
        var v = V("v");
        var depth = Call("requiredDepth", V("P"), V("Q"), V("H"), V("K"));
        var rhs = Some("p", Call("Pattern", depth), Some("v", Arr(Call("Frontier", p), V("Source")),
            And(EqOf(Call("fill", p, v), V("u")),
                Call("ExtractedHolds", V("P"), V("Q"), V("old"), V("target"), V("H"), V("K"),
                    Call("patternTerm", p, V("id")), v))));
        return All("P,Q", V("CutSet"), Imp(And(Call("CutPrefixFree", V("P")), Call("CutPrefixFree", V("Q"))),
            All("old,target", V("Row"), All("H", Call("List", V("Record")),
                All("K", Call("List", V("NegativeRecord")), All("u", V("Source"),
                    IffOf(Call("InputHolds", V("P"), V("Q"), V("old"), V("target"), V("H"), V("K"), V("u")), rhs)))))));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Sp, Land, Sp, b, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Sp, Implies, Sp, b, Close);
    private static Formula IffOf(Formula a, Formula b) => Seq(Open, a, Sp, Iff, Sp, b, Close);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Open, b, Close);
    private static Formula Some(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Open, b, Close);
}
