using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class FirstWindowBoundaryCompatibilityDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryCompatibility.";
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Or(params Formula[] clauses) =>
        clauses.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.Or, b));
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
        var y = F.Id("Y"); var h = F.Id("h"); var j = F.Id("j");
        var p = F.Id("p"); var q = F.Id("q"); var v = F.Id("v"); var s = F.Id("s");
        var support = F.Id("H"); var labelA = F.Id("A"); var labelB = F.Id("B");
        var f = F.Id("f"); var alphabet = F.Id("alphabet");
        var x = F.Id("X"); var subset = F.Id("S"); var a = F.Id("a");
        Formula MemberPair(Formula z) => Call("membership", m, support, z);
        var initial = Call("some", Seq(Langle, Sp, v, Comma, new Formula.Negate(j), Comma, s, Rangle));
        var inside = All("v", scalar, All("h", nat,
            Imp(Call("Member", h, Apply(support, v)), And(Le(D(1), h), Le(h, m)))));
        var distinct = All("v", scalar, new Formula.Not(Equal(Apply(labelA, v), Apply(labelB, v))));
        var target = All("v", scalar, All("j", phase, All("s", nat,
            Imp(Lt(s, k), Equal(Apply(f, initial),
                Call("ifThenElse", Call("Member", Call("val", j), Apply(support, v)),
                    Apply(labelB, v), Apply(labelA, v)))))));
        var image = Call("internalImage", m, support);
        var left = Call("left", a); var right = Call("right", a);
        var flip = Call("flip", a); var exterior = Call("exterior", a); var donor = Call("donor", a);
        var words = Call("baseWords", m, subset, a);
        Formula Code(Formula z) => Call("baseCode", m, subset, a, z);
        var archive = Call("scriptArchive", words, initial);
        var subsetDefinition = Call("filter", Call("Ico", D(2), m),
            Call("membershipEquals", m, support, x));
        var assignment = Call("baseChoice", Call("natCast", m), Call("natCast", Call("card", subset)),
            Call("classIndex", x, MemberPair(Call("phaseCast", D(1)))),
            Call("classIndex", x, MemberPair(Call("phaseCast", m))));
        var firstParity = Equal(Add(Add(Add(Call("natCast", Call("card", subset)),
            Multiply(flip, Call("natCast", m))), Call("fst", left)), Call("fst", right)), D(0));
        var secondParity = Equal(Add(Add(Add(Multiply(exterior, Add(Call("natCast", m), D(1))),
            donor), Call("snd", left)), Call("snd", right)), D(0));
        var details = All("v", scalar, All("j", phase, All("s", nat,
            Imp(Lt(s, k), And(
                Equal(Call("endpointDifferences", Call("some", v), Call("mapReplies", archive)),
                    Call("list", Call("some", Call("fst", Code(j))), Call("some", Call("snd", Code(j))))),
                Equal(Call("length", archive), D(2)),
                Equal(Call("length", Call("flattenWords", archive)), Multiply(D(2), m)))))));
        var result = Exists("X", pair, Exists("S", Call("Finset", nat),
            Exists("a", F.Id("BaseAssignment"), And(
                new Formula.Not(Equal(x, D(0))), Equal(image, Call("pairSet", D(0), x)),
                Equal(subset, subsetDefinition), Equal(a, assignment),
                All("h", nat, Imp(Call("Member", h, subset), And(Le(D(2), h), Lt(h, m)))),
                firstParity, secondParity, Equal(Call("length", words), D(2)),
                All("p", phase, All("q", phase, Imp(Equal(Code(p), Code(q)),
                    Equal(MemberPair(p), MemberPair(q))))),
                Call("OriginalPresetFeasible", k, m, alphabet, f, D(2)), details))));
        var piThree = And(Le(Call("card", image), D(2)), Or(Call("Odd", m),
            new Formula.Not(Equal(MemberPair(Call("phaseCast", D(1))), D(0))),
            new Formula.Not(Equal(MemberPair(Call("phaseCast", m)), D(0)))));
        var compatible = new Formula.Logic(
            Call("OriginalPresetFeasible", k, m, alphabet, f, D(2)), FormulaLogicOperator.Iff, piThree);
        var completeResult = And(compatible, Imp(And(Equal(Call("card", image), D(2)),
            Call("Member", D(0), image)), result));
        var statement = All("Y", F.Id("Type"), All("m", nat,
            All("alphabet", F.Id("Bool"), All("H", Arrow(scalar, Call("Finset", nat)),
            All("A", Arrow(scalar, y), All("B", Arrow(scalar, y),
            All("f", Arrow(Call("Option", Call("LiveRecord", k)), y),
            Imp(And(Le(D(5), m), inside, distinct, target,
                Equal(Call("card", Call("fullImage", m, support)), D(3))), completeResult))))))));
        var row0 = Equal(Call("nonbaseRoot", m, subset, flip, left, right, h), Add(Add(Add(Call("supportRow", subset, h),
            Multiply(flip, Call("supportRow", Call("Ico", D(2), m), h))),
            Multiply(Call("fst", left), Call("supportRow", Call("singleton", D(1)), h))),
            Multiply(Call("fst", right), Call("supportRow", Call("singleton", m), h))));
        var row1 = Equal(Call("baseSecond", m, a, h), Add(Add(Add(
            Multiply(exterior, Call("supportRow", Call("Ico", D(1), m), h)),
            Multiply(donor, Call("supportRow", Call("singleton", D(1)), h))),
            Multiply(Call("snd", right), Call("supportRow", Call("singleton", D(0)), h))),
            Multiply(Call("snd", left), Call("supportRow", Call("singleton", m), h))));
        var seam = Or(Equal(Call("snd", right), D(0)), Equal(Add(exterior, donor), D(1)),
            Equal(Call("fst", right), D(0)));
        var physicalStatement = All("m", nat, All("S", Call("Finset", nat),
            All("a", F.Id("BaseAssignment"), All("v", scalar, All("j", phase, All("s", nat,
            Imp(And(Le(D(5), m), All("h", nat, Imp(Call("Member", h, subset),
                And(Le(D(2), h), Lt(h, m)))), firstParity, secondParity, seam, Lt(s, k)),
                Equal(Call("endpointDifferences", Call("some", v), Call("mapReplies", archive)),
                    Call("list", Call("some", Call("fst", Code(j))),
                        Call("some", Call("snd", Code(j))))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The closed three-label compatibility relation includes every safe base-internal boundary construction.",
            H("Three-label first-window boundary compatibility"),
            Blocks(Describe.Lean(
                DescribeId.Create("base-script-code"),
                DeclarationHandle.Create(Owner + "base_script_code"),
                H("Normalized inverse codes on every original inherited tail"),
                StatementSource.FromAuthor(Disp(physicalStatement)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any internal set S and BaseAssignment a, the two displayed "
                    + "even-row equations and seam disjunction make the actual common baseWords prefix "
                    + "safe on every original value, phase and inherited tail. Its acquired consecutive "
                    + "endpoint differences are exactly the two coordinates of baseCode. The successor "
                    + "begins zero, is broken by its index-one zero after a leading one, or enters from "
                    + "a zero-ending root. This statement supplies the literal realization used by "
                    + "both three-label and four-label normalized constructions."))), DescribeRole.Theorem),
                Describe.Lean(
                DescribeId.Create("original-first-window-three-label-compatibility"),
                DeclarationHandle.Create(Owner + "original_first_window_three_label_compatibility"),
                H("The complete Pi3 relation and base-internal physical table"),
                StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix m>=5, k=2m-2 and P=ZMod(2m-1). H(0),H(1) lie in "
                        + "B={1,...,m}; their ordered membership pair is ell. Its full "
                        + "image has three labels. Two-block original GLOBAL feasibility "
                        + "is equivalent to Pi3: the internal image on U={2,...,m-1} has "
                        + "at most two labels, and m is odd or one of the two boundaries "
                        + "is nonbase. For the base-internal clause, the internal image "
                        + "is {0,X}, with X nonzero. The third label Z must occur at one "
                        + "or both boundaries. Thus all six rows of table 29.19 apply, "
                        + "without an additional parity or boundary compatibility condition. "
                        + "The target has arbitrary labels A(v)!=B(v) separately, arbitrary "
                        + "cross-value coincidences, arbitrary Type universes and independently "
                        + "observed f(none). Every original value, phase, inherited tail and "
                        + "unknown legal or rejected history is retained.")),
                    Paragraph(Text(
                        "Necessity directly uses the same-stream row theorem: any correct "
                        + "two-block competitor has even rows, its second row is zero on U, "
                        + "and its row pairs refine both original support coordinates. "
                        + "Hence r<=2. If both boundary labels are base, the full image is "
                        + "exactly {0} union the internal image. With n=3 and r<=2 this "
                        + "forces r=2 and excludes base internally. The already established "
                        + "nonbase-internal obstruction then forces odd m. This comparison "
                        + "retains rejection and early stopping; scheduled rows on stopped "
                        + "sources supply no acquired endpoint or fee.")),
                    Paragraph(Text(
                        "For sufficiency, U is nonempty because it contains phase two. "
                        + "The bound r<=2 therefore gives r=1 or r=2. The homogeneous "
                        + "construction handles r=1. If r=2 and base is absent internally, "
                        + "the nonbase-internal theorem gives a safe common stream exactly "
                        + "under the remaining Pi3 clause. If base is present internally, "
                        + "the following complete table supplies the actual stream. "
                        + "Thus all three-label internal and boundary arrangements are "
                        + "included, while the explicit base-internal clause records its "
                        + "own selected rows, code refinement and archive counts.")),
                    Paragraph(Text(
                        "Let S={h in U: ell(h)=X}, q=|S|, t=q modulo two and e=m modulo "
                        + "two. classIndex(X,z) is 0 for base, 1 for X and 2 for the third "
                        + "label Z. In the table below, Z is the label called Y in 29.19. "
                        + "At least one boundary index is 2. BaseAssignment records flip, "
                        + "exterior, donor and the left and right two-bit boundary codes. "
                        + "baseChoice(e,t,x,y) selects the following exact supports; u is "
                        + "the Z boundary when the boundaries differ and h=m+1 is an actual "
                        + "exterior base-labelled phase.")),
                    Paragraph(Text(
                        "For boundaries Z,Z, E0=S union {1} when q is odd and E0=S when "
                        + "q is even; E1={1,m}. For boundaries Z,X in either order with q "
                        + "odd, E0=S union {1} and E1={1,m}. With q even, E0=S union {1,m} "
                        + "and E1={u,h}. For boundaries Z,0 in either order with q odd, "
                        + "E0=S union {u} and E1={u,h}. With q even and m odd, E0=(U without S) "
                        + "union {u} and E1=R union {1,m}. With q even and m even, E0=(U without S) "
                        + "union {1,m} and E1=R union {u}. These are all six rows and both "
                        + "orientations of each mixed-boundary row.")),
                    Paragraph(Text(
                        "The root row reuses nonbaseRoot and the second row uses offsets "
                        + "from m in the ordered path W1. In the following two formulas, "
                        + "left,right,flip,exterior,donor are the fields of a. supportRow(E,h) "
                        + "is one on E and zero off E; all additions are in ZMod(2). "
                        + "Offset one of the second path is physical phase m+1; offset "
                        + "m wraps to phase one, and offset zero is physical phase m.")),
                    Paragraph(Math(row0)), Paragraph(Math(row1)),
                    Paragraph(Text(
                        "baseWords is exactly the prefix-parity inverse of the root row "
                        + "followed by the prefix-parity inverse of baseSecond. The displayed "
                        + "two parity equations make each complete ordered row even. "
                        + "The first equation counts S and U once, while |U|=m-2 has the "
                        + "same parity as m. The second counts all m-1 exterior phases once "
                        + "plus the donor correction and the two boundaries. This is phase "
                        + "multiplicity, with no repetition from tails or history lengths.")),
                    Paragraph(Text(
                        "Internally the codes are (flip,0) for base and (1+flip,0) for X. "
                        + "Exterior phases have (0,exterior), except m+1 which has "
                        + "(0,exterior+donor). At phase one and m the codes are left and right. "
                        + "Equal codes always imply equal membership labels. Repeated labels "
                        + "may occupy distinct codes: in the odd-q Z,X row, when Z is at "
                        + "phase one, its code is 11 and X uses both 10 internally and 01 "
                        + "at phase m. When Z is at phase m, Z has 01 while X uses 10 and "
                        + "11. In both orientations the supports remain S union {1} and "
                        + "{1,m}, and all unequal labels remain separated. Four-label "
                        + "saturation is not imposed on these three-label assignments.")),
                    Paragraph(Text(
                        "Every root begins zero and clears any legal inherited tail. "
                        + "Its terminal tail is at most m-1. The selected boundary codes "
                        + "satisfy one of three physical seam conditions: the second word "
                        + "begins zero; its first bit is one and the actual donor toggles "
                        + "the next bit to zero; or the root ends zero. In the first case "
                        + "the incoming tail clears immediately. In the second, the seam "
                        + "run is at most m<k, and the zero at literal index one prevents "
                        + "extension. In the last case the second word enters from actual "
                        + "tail zero; its length m<k makes even an all-one word safe. "
                        + "Thus the entire prefix succeeds on every original source, "
                        + "including both seams and every inherited tail.")),
                    Paragraph(Text(
                        "The actual chronological endpoint differences are precisely the "
                        + "two coordinates of baseCode. Each source decodes those differences "
                        + "from its own acquired archive and uses its remembered free value "
                        + "to select the required membership component and A(v) or B(v). "
                        + "The same preselected literal stream serves both free values and "
                        + "both original alphabets. Initial bottom stops freely. The live "
                        + "script archive has exactly two issued blocks and 2m bits; this "
                        + "count does not itself assert an optimal PaidTrace price.")),
                    Paragraph(Text("Ordered membership and the first-row definition use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryCodes"),
                        Text(". Phase shifts and support sums use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAttainment"),
                        Text(". The inverse and clear-seam executions use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse"),
                        Text("; the marked-zero inherited-tail execution uses "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety"),
                        Text(". Original history and common-stream feasibility use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection"), Text(".")),
                    Paragraph(Text(
                        "This result gives the complete three-label two-block compatibility "
                        + "equivalence and the base-internal physical table. It does not "
                        + "assert the least price independently of the zero/one-block "
                        + "lower bounds. Four-label phase pivots and their equivalent boundary "
                        + "table, degenerate membership normalization, full sharp preset "
                        + "prices and unequal adaptive PaidTrace prices are separate "
                        + "statements. No claim that every even refining row pair has a "
                        + "safe concatenation follows from this selected construction."))), DescribeRole.Theorem))));
    }
}
