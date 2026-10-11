using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class FirstWindowBoundaryAttainmentDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAttainment.";
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    public DocumentDefinition Create()
    {
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var m = F.Id("m"); var k = Subtract(Multiply(D(2), m), D(2));
        var phase = Call("ZMod", Add(k, D(1))); var scalar = Call("ZMod", D(2));
        var pair = Seq(scalar, Sp, Times, Sp, scalar);
        var y = F.Id("Y"); var table = F.Id("table"); var label = F.Id("label");
        var f = F.Id("f"); var alphabet = F.Id("alphabet");
        var j = F.Id("j"); var v = F.Id("v"); var s = F.Id("s");
        var initial = Call("some", Seq(Langle, Sp, v, Comma, new Formula.Negate(j), Comma, s, Rangle));
        var outside = All("j", phase, Imp(new Formula.Not(And(
            Le(D(1), Call("val", j)), Le(Call("val", j), m))),
            Equal(Apply(table, j), D(0))));
        var target = All("v", scalar, All("j", phase, All("s", nat,
            Imp(Lt(s, k), Equal(Apply(f, initial), Apply(label, v, Apply(table, j)))))));
        var words = Call("words", m, table);
        var archive = Call("scriptArchive", words, initial);
        var details = All("v", scalar, All("j", phase, All("s", nat,
            Imp(Lt(s, k), And(
                Equal(Call("endpointDifferences", Call("some", v), Call("mapReplies", archive)),
                    Call("code", m, table, j)),
                Equal(Call("length", archive), D(3)),
                Equal(Call("length", Call("flattenWords", archive)), Multiply(D(3), m)))))));
        var statement = All("Y", F.Id("Type"), All("m", nat, All("alphabet", F.Id("Bool"),
            All("f", Arrow(Call("Option", Call("LiveRecord", k)), y),
            All("table", Arrow(phase, pair), All("label", Arrow(scalar, Arrow(pair, y)),
                Imp(And(Le(D(5), m), outside, target), And(
                    Call("OriginalPresetFeasible", k, m, alphabet, f, D(3)),
                    Equal(Call("getOption", words, D(1)), Call("some", Call("pulse", m))),
                    details))))))));

        var support = F.Id("support"); var h = F.Id("h");
        var controller = F.Id("controller"); var word = F.Id("word");
        var supportType = Call("Finset", nat);
        var wordType = Arrow(Call("Fin", m), F.Id("Bool"));
        var supportInside = All("h", nat, Imp(Call("Member", h, support),
            And(Le(D(1), h), Le(h, m))));
        var binaryTarget = All("v", scalar, All("j", phase, All("s", nat,
            Imp(Lt(s, k), Equal(Apply(f, initial),
                Apply(label, v, Call("supportRow", support, Call("val", j))))))));
        var binaryWords = Call("binaryWords", m, support);
        var binaryCost = Call("binaryCost", support);
        var binaryArchive = Call("scriptArchive", binaryWords, initial);
        var binaryDetails = All("v", scalar, All("j", phase, All("s", nat,
            Imp(Lt(s, k), And(
                Equal(Call("endpointDifferences", Call("some", v), Call("mapReplies", binaryArchive)),
                    Call("binaryCode", m, support, j)),
                Equal(Call("length", binaryArchive), binaryCost),
                Equal(Call("length", Call("flattenWords", binaryArchive)), Multiply(binaryCost, m)))))));
        var unequal = new Formula.Not(Equal(Apply(label, v, D(0)), Apply(label, v, D(1))));
        var zeroNecessary = All("v", scalar, Imp(unequal,
            All("controller", Call("Selector", m, y),
                Imp(Call("FiberCorrect", m, alphabet, f, v, D(0), controller),
                    Equal(support, Call("empty"))))));
        var oneNecessary = Imp(Call("Nonempty", support), All("v", scalar, Imp(unequal,
            All("controller", Call("Selector", m, y),
                Imp(Call("FiberCorrect", m, alphabet, f, v, D(1), controller),
                    new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("word"), wordType,
                        And(Equal(Apply(controller, Call("some", v), Call("nil")), Call("inr", word)),
                            Equal(Apply(word, D(0)), F.Id("false")),
                            All("j", phase, Equal(Call("wordIncrement", k, new Formula.Negate(j), word),
                                Call("supportRow", support, Call("val", j)))),
                            Call("Even", Call("card", support)))))))));
        var binaryStatement = All("Y", F.Id("Type"), All("m", nat,
            All("alphabet", F.Id("Bool"), All("support", supportType,
                All("f", Arrow(Call("Option", Call("LiveRecord", k)), y),
                    All("label", Arrow(scalar, Arrow(scalar, y)),
                        Imp(And(Le(D(5), m), supportInside, binaryTarget),
                            And(Call("OriginalPresetFeasible", k, m, alphabet, f, binaryCost),
                                Equal(Call("length", binaryWords), binaryCost),
                                binaryDetails, zeroNecessary, oneNecessary))))))));
        var binaryDescribe = Describe.Lean(
            DescribeId.Create("original-first-window-binary-stream"),
            DeclarationHandle.Create(Owner + "original_first_window_binary_stream"),
            H("Binary supports: actual scripts and arbitrary-value obstructions"),
            StatementSource.FromAuthor(Disp(binaryStatement)), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A support is represented by a Finset of integer phase representatives, "
                    + "all in 1,...,m. Each phase of P has one canonical representative, so this "
                    + "includes every subset of B, with no multiplicity from inherited tails "
                    + "or realizing histories. supportRow(support,h) is one for a member and "
                    + "zero otherwise, in ZMod(2). The label map is arbitrary in each saved "
                    + "free-value fibre. It includes A(v) and B(v), separately unequal for "
                    + "the obstructions, with arbitrary coincidences across values. Every "
                    + "universe of Y is retained and no Fintype Y is assumed.")),
                Paragraph(Text(
                    "binaryCost is zero for an empty support, one for a nonempty even "
                    + "support and two for an odd support. The empty script stops freely. "
                    + "For an even support H, binaryWords consists of the actual root "
                    + "prefix-parity inverse of H. Its first charge is zero and its first "
                    + "literal bit is zero, clearing every inherited legal tail. Its only "
                    + "endpoint difference is precisely membership in H.")),
                Paragraph(Text(
                    "For odd H there are three boundary choices. If m is absent, the root "
                    + "row is H union {m}, and the second physical support is {m,m+1}. If "
                    + "m is present and one absent, the root is H union {1}, and the second "
                    + "physical support is {1,m+1}. If both boundaries are present, the "
                    + "root is H without m, and the second support is {1,m}. These are "
                    + "exactly the three rows of (29.16). In the ordered second path starting "
                    + "at m, their offset supports are respectively {0,1}, {1,m} and {0,m}. "
                    + "Every row is even and has the supplied literal prefix-parity inverse.")),
                Paragraph(Text(
                    "The first odd case gives code (1,0) on H, (1,1) at the added boundary "
                    + "m, (0,1) at the exterior donor m+1, and (0,0) elsewhere. The second "
                    + "case has the same pattern with added boundary one. In the third case, "
                    + "the members of H are exactly the phases with a nonzero two-bit code: "
                    + "one has (1,1), m has (0,1), and the remaining members have (1,0). "
                    + "Thus equal binaryCode lists imply equal support membership on every "
                    + "actual phase. The exterior donor is decoded as base in the first two "
                    + "cases. The decoder chooses a phase with its observed endpoint-difference "
                    + "list and returns that phase's membership label in its own saved value fibre.")),
                Paragraph(Text(
                    "Every root begins zero and has terminal tail at most m-1. In the first "
                    + "odd case the second word is 10^(m-1), with its zero at physical index "
                    + "one, so the joined leading run has length at most m<k. In the second "
                    + "case the second word begins zero. In the last case the root ends zero, "
                    + "followed by the actual all-one length-m inverse of {1,m}. Its run "
                    + "also has length m<k. These are complete-prefix safety statements on "
                    + "every legal inherited tail, rather than separate internal-block checks.")),
                Paragraph(Text("The physical inverses use "),
                    Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse"),
                    Text("; the marked zero at second-word index one uses "),
                    Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety"),
                    Text(". The prescribed selector and original history bridge are the same "
                    + "ones used by the three-block construction. One preselected literal "
                    + "stream serves both values and both original alphabets. Initial bottom "
                    + "has its unrestricted independent label and stops for free. The displayed "
                    + "live script archives contain exactly binaryCost(H) issued complete "
                    + "blocks and m times that number of emitted bits.")),
                Paragraph(Text(
                    "FiberCorrect(m,alphabet,f,v,d,controller) means correctness within "
                    + "budget d on every actual complete-block history whose INITIAL scalar "
                    + "output is v. The target is that history's immutable INITIAL record. "
                    + "The history and its length are not revealed; the controller receives "
                    + "only the saved free output and its own acquired archive. Waits, "
                    + "rejected blocks and early stops remain in the execute recursion.")),
                Paragraph(Text(
                    "For arbitrary v with unequal base and member labels, budget zero forces "
                    + "H empty. For nonempty H, every correct one-block controller chooses "
                    + "a word W at its root. The proof uses native_fiber to obtain every phase "
                    + "with actual inherited tail zero. Since m<k, W succeeds from tail zero. "
                    + "The exterior phase m+1 has zero literal charge and the base label. "
                    + "charge_separates then forces each member to have charge one; comparison "
                    + "with one actual member forces every nonmember to have charge zero. "
                    + "Thus W's charge is exactly H, including zero charge at phase zero. "
                    + "The derivative identity forces W to begin zero, and the full-path "
                    + "charge sum forces H to be even. This argument works for every saved "
                    + "value and uses no value-zero-only root lemma.")),
                Paragraph(Text("The necessary conditions reuse "),
                    Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges"),
                    Text(" for actual-history realization and own-charge separation, and "),
                    Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction"),
                    Text(" for even full literal charge. These scripts and obstructions are "
                    + "the individual binary-support components of (29.8), credited there "
                    + "to PREFIX_DEADLINE_AND_WRAP_COST Theorem 6.1. The present statement "
                    + "does not assemble unequal per-value stopping lengths into one adaptive "
                    + "controller or assert the final GlobalPresetPrice, GlobalAdaptivePrice "
                    + "or actual worst-history bit-price equalities. It supplies the actual "
                    + "0/1/2 scripts and arbitrary-value lower bounds needed for that assembly."))),
            DescribeRole.Theorem);

        return DocumentDefinition.Create(ScribeNode.Create(
            "A middle pulse distinguishes the actual parity donor from the first-window labels.",
            H("First-window common three-block attainment"),
            Blocks(Describe.Lean(
                DescribeId.Create("original-first-window-three-block-stream"),
                DeclarationHandle.Create(Owner + "original_first_window_three_block_stream"),
                H("A common stream on the full INITIAL source"),
                StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix m>=5, k=2m-2 and the complete phase group P=ZMod(2m-1). "
                        + "The pair-valued table is zero outside B={1,...,m}. A first-window "
                        + "support pair is represented by table(j)=(1 if j is in Hzero else 0, "
                        + "1 if j is in Hone else 0). Its components belong to ZMod(2). "
                        + "The label map may depend on the saved INITIAL value and sends "
                        + "this membership pair to the desired label. Thus separate unequal "
                        + "label pairs and arbitrary coincidences between free-value fibres "
                        + "are included. No finiteness assumption is made on Y. The displayed "
                        + "Type includes every universe of the Lean statement.")),
                    Paragraph(Text(
                        "Let p be the sum of table(h) for h=0,...,m, counting each phase "
                        + "once. The zero at phase zero makes this the parity on B. The basis "
                        + "map is z when the first component of p is zero, (z.second,z.first) "
                        + "when only the second component is zero, and (z.first+z.second,z.second) "
                        + "otherwise. It is invertible, including when p is zero, and its "
                        + "first coordinate vanishes on p. Call its coordinates alpha and beta.")),
                    Paragraph(Text(
                        "The first row has charge alpha(table(h)) at the ordered offsets "
                        + "h=0,...,m. The last row has beta(table(h+1)) for h<m and beta(p) "
                        + "at h=m. Both rows have zero sum in ZMod(2). The words are their "
                        + "prefix-parity inverses, separated by pulse(m), whose sole one is "
                        + "at physical index one. This middle word is exactly 010^(m-2); "
                        + "it is issued even when no parity compensation is needed.")),
                    Paragraph(Text(
                        "The calendar identity 2m=1 in P places the last path at phase one. "
                        + "The pulse charge is one precisely at phases m+1 and m+2. Hence "
                        + "the actual difference triple on B is (alpha(table(j)),0,beta(table(j))). "
                        + "At m+1 it is (0,1,beta(p)); at m+2 it is (0,1,0); everywhere "
                        + "else outside B it is (0,0,0). These are exactly code(m,table,j). "
                        + "Both exterior phases remain actual sources. A middle difference "
                        + "one returns the base pair, and otherwise the first and last "
                        + "differences determine the table through the invertible basis. "
                        + "The proof implements an archive-only decoder by choosing a phase "
                        + "with the observed code; equality of codes forces equality of tables.")),
                    Paragraph(Text(
                        "The root begins zero and clears every legal inherited tail. All "
                        + "three words have length m<k. The pulse begins and ends zero, "
                        + "breaking both seams and giving actual tail zero before the final "
                        + "word. The complete original run is therefore safe for every "
                        + "value, phase and inherited tail. The same words are available in "
                        + "both original alphabets and do not depend on any acquired reply "
                        + "or on the free value.")),
                    Paragraph(Text("The literal inverses and full-prefix execution use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse"),
                        Text(". The original archive, prescribed paid selector and endpoint differences use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder"),
                        Text(". The common-stream selector is supplied by "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection"),
                        Text(". OriginalPresetFeasible retains every actual complete-block history, "
                        + "including rejection and unknown history length. Initial bottom has "
                        + "its independent f(none) label and stops for free. Every live source "
                        + "uses only its own three consecutive endpoints and remembered free value.")),
                    Paragraph(Text(
                        "The archive in the final conjunct contains exactly three actual "
                        + "issued words and 3m emitted bits; flattenWords there concatenates "
                        + "the archive's word projections and mapReplies selects its endpoint "
                        + "projections. No interior reading is granted. OriginalPresetFeasible "
                        + "is an upper bound of three blocks. This result does not assert that "
                        + "three is minimal, the two-block boundary relations, the 0/1/2 "
                        + "cases, the adaptive minimum, or the worst bit fee of an optimal "
                        + "controller. The remaining clauses require their separate sharp obstructions and "
                        + "attaining streams."))), DescribeRole.Theorem), binaryDescribe)));
    }
}
