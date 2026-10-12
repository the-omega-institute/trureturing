using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class FirstWindowBoundaryCodesDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryCodes.";
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
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
        var support = F.Id("H"); var a = F.Id("A"); var b = F.Id("B");
        var f = F.Id("f"); var alphabet = F.Id("alphabet");
        var stream = F.Id("stream"); var stop = F.Id("stop");
        var wordType = Arrow(Call("Fin", m), F.Id("Bool"));
        var archiveType = Call("Archive", m);
        var stopType = Arrow(Call("Option", scalar), Arrow(archiveType, Call("Option", y)));
        var initial = Call("some", Seq(Langle, Sp, v, Comma, new Formula.Negate(j), Comma, s, Rangle));
        var inside = All("v", scalar, All("h", nat,
            Imp(Call("Member", h, Apply(support, v)), And(Le(D(1), h), Le(h, m)))));
        var distinct = All("v", scalar, new Formula.Not(Equal(Apply(a, v), Apply(b, v))));
        var target = All("v", scalar, All("j", phase, All("s", nat,
            Imp(Lt(s, k), Equal(Apply(f, initial),
                Call("ifThenElse", Call("Member", Call("val", j), Apply(support, v)),
                    Apply(b, v), Apply(a, v)))))));
        Formula First(Formula z) => Call("firstCharge", m, stream, z);
        Formula Second(Formula z) => Call("secondCharge", m, stream, z);
        Formula MemberPair(Formula z) => Call("membership", m, support, z);
        var imageSize = Call("card", Call("internalImage", m, support));
        var feasible = Call("OriginalPresetFeasible", k, m, alphabet, f, D(2));
        var root = Imp(Call("Nonempty", Apply(support, D(0))), And(
            Equal(Apply(stop, Call("some", D(0)), Call("nil")), F.Id("none")),
            Equal(Apply(stream, D(0), D(0)), F.Id("false")),
            All("j", phase, Imp(new Formula.Not(And(Le(D(1), Call("val", j)),
                Le(Call("val", j), m))), Equal(First(j), D(0))))));
        var blind = All("j", phase, Imp(Le(D(2), Call("val", j)),
            Imp(Lt(Call("val", j), m), Equal(Second(j), D(0)))));
        var refinement = All("p", phase, All("q", phase,
            Imp(Equal(First(p), First(q)), Imp(Equal(Second(p), Second(q)),
                Equal(MemberPair(p), MemberPair(q))))));
        var necessary = Imp(feasible,
            Exists("stream", Arrow(nat, wordType), Exists("stop", stopType, And(
                All("v", scalar, Call("FiberCorrect", m, alphabet, f, v, D(2),
                    Call("presetSelector", stream, stop))),
                root, blind,
                Equal(Call("PhaseSumFirst", m, stream), D(0)),
                Equal(Call("PhaseSumSecond", m, stream), D(0)),
                refinement, Le(imageSize, D(2))))));
        var words = Call("homogeneousWords", m);
        var archive = Call("scriptArchive", words, initial);
        var details = All("v", scalar, All("j", phase, All("s", nat, Imp(Lt(s, k), And(
            Equal(Call("endpointDifferences", Call("some", v), Call("mapReplies", archive)),
                Call("homogeneousCode", m, j)),
            Equal(Call("length", archive), D(2)),
            Equal(Call("length", Call("flattenWords", archive)), Multiply(D(2), m)))))));
        var statement = All("Y", F.Id("Type"), All("m", nat, All("alphabet", F.Id("Bool"),
            All("H", Arrow(scalar, Call("Finset", nat)), All("A", Arrow(scalar, y),
                All("B", Arrow(scalar, y), All("f", Arrow(Call("Option", Call("LiveRecord", k)), y),
                    Imp(And(Le(D(5), m), inside, distinct, target), And(necessary,
                        Equal(Call("length", words), D(2)),
                        Imp(Equal(imageSize, D(1)), And(feasible, details)))))))))));
        var subset = F.Id("S"); var flip = F.Id("flip");
        var left = F.Id("left"); var right = F.Id("right");
        var nonbaseWords = Call("nonbaseWords", m, subset, flip, left, right);
        Formula NonbaseCode(Formula z) => Call("nonbaseCode", m, subset, flip, left, right, z);
        var nonbaseArchive = Call("scriptArchive", nonbaseWords, initial);
        var rootParity = Equal(Add(Add(Add(Call("natCast", Call("card", subset)),
            Multiply(flip, Call("natCast", m))), Call("fst", left)), Call("fst", right)), D(0));
        var secondParity = Equal(Add(Add(Add(Call("natCast", m), D(1)),
            Call("snd", left)), Call("snd", right)), D(0));
        var subsetInside = All("h", nat, Imp(Call("Member", h, subset),
            And(Le(D(2), h), Lt(h, m))));
        var nonbaseDetails = All("v", scalar, All("j", phase, All("s", nat,
            Imp(Lt(s, k), And(
                Equal(Call("endpointDifferences", Call("some", v), Call("mapReplies", nonbaseArchive)),
                    Call("list", Call("some", Call("fst", NonbaseCode(j))),
                        Call("some", Call("snd", NonbaseCode(j))))),
                Equal(Call("length", nonbaseArchive), D(2)),
                Equal(Call("length", Call("flattenWords", nonbaseArchive)), Multiply(D(2), m)))))));
        var admitted = Or(Call("Odd", m), Or(
            new Formula.Not(Equal(MemberPair(D(1)), D(0))),
            new Formula.Not(Equal(MemberPair(Call("phaseCast", m)), D(0)))));
        var nonbaseStatement = All("Y", F.Id("Type"), All("m", nat,
            All("alphabet", F.Id("Bool"), All("H", Arrow(scalar, Call("Finset", nat)),
            All("A", Arrow(scalar, y), All("B", Arrow(scalar, y),
            All("f", Arrow(Call("Option", Call("LiveRecord", k)), y),
            Imp(And(Le(D(5), m), inside, distinct, target,
                Equal(Call("card", Call("fullImage", m, support)), D(3)),
                Equal(imageSize, D(2)),
                new Formula.Not(Call("Member", D(0), Call("internalImage", m, support)))),
            And(Imp(feasible, admitted), Imp(admitted, Exists("S", Call("Finset", nat), Exists("flip", scalar,
            Exists("left", pair, Exists("right", pair,
                And(subsetInside, rootParity, secondParity,
                    Equal(Call("length", nonbaseWords), D(2)),
                    All("p", phase, All("q", phase, Imp(Equal(NonbaseCode(p), NonbaseCode(q)),
                        Equal(MemberPair(p), MemberPair(q))))), feasible, nonbaseDetails)))))))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Two ordered physical rows constrain the joined membership labels and realize a homogeneous internal image.",
            H("First-window two-block boundary rows"),
            Blocks(Describe.Lean(
                DescribeId.Create("original-first-window-boundary-rows"),
                DeclarationHandle.Create(Owner + "original_first_window_boundary_rows"),
                H("Necessary same-stream refinement and safe homogeneous attainments"),
                StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix m>=5 and k=2m-2. Each support H(v) is a Finset of the actual "
                        + "integer phase representatives 1,...,m in P=ZMod(2m-1). The labels "
                        + "A(v),B(v) are unequal separately; their coincidences across values "
                        + "are unrestricted. The INITIAL target depends on the saved value "
                        + "and support membership, with every inherited tail retained. Y "
                        + "may inhabit any universe and need not be finite. Initial bottom "
                        + "keeps its independent f(none) label and stops freely.")),
                    Paragraph(Text(
                        "membership(m,H,j) is the ordered pair (supportRow(H(0),j.val), "
                        + "supportRow(H(1),j.val)). The internal phases are those with "
                        + "2<=j.val<m, and internalImage is their finite actual membership "
                        + "image. Its cardinality is r in Definition 29.1. Each phase is "
                        + "counted once; realizing histories and inherited tails add no "
                        + "multiplicity. firstCharge and secondCharge are the increments "
                        + "of stream(0) at phase -j and stream(1) at phase -j+m. PhaseSumFirst "
                        + "and PhaseSumSecond in the formula sum these respective rows over "
                        + "the entire phase group.")),
                    Paragraph(Text(
                        "For every correct original two-block GLOBAL competitor, the same "
                        + "literal stream and its own-archive stop function supply both rows. "
                        + "The witness retains correctness on every actual history in each "
                        + "free-value fibre. Equal first and second charges force equality "
                        + "of both membership coordinates: native_fiber realizes each phase, "
                        + "and native_two_same identifies its entire two-block execution "
                        + "with that of any phase having the same pair. The proof applies "
                        + "separately to each value using its unequal A,B labels. Cross-value "
                        + "label collisions cannot remove either membership coordinate.")),
                    Paragraph(Text(
                        "The native execution comparison includes stopping before either "
                        + "word and common absorption after a rejected block. A second word "
                        + "scheduled for a source that already stopped is used only to define "
                        + "its algebraic profile: it supplies neither an acquired endpoint "
                        + "nor a paid suffix to that source. Every actually issued complete "
                        + "word, including waits and rejecting attempts, remains charged by "
                        + "OriginalPresetFeasible and FiberCorrect.")),
                    Paragraph(Text(
                        "If H(0) is nonempty, its actual value-zero target is nonconstant, "
                        + "since phase zero is base-labelled. The root therefore cannot stop "
                        + "freely. A leading one rejects every phase with inherited tail "
                        + "k-1 into the same absorbing archive; root_zero consequently forces "
                        + "the actual first bit to be zero. The literal derivative then "
                        + "vanishes on R=P without {1,...,m}, including phase zero. The "
                        + "second moving window has zero charge throughout U={2,...,m-1}. "
                        + "Both full rows have even charge. Since only two first-coordinate "
                        + "values are available on U and the second coordinate is zero, "
                        + "joined refinement forces r<=2. Thus r>=3 excludes every correct "
                        + "two-block competitor.")),
                    Paragraph(Text(
                        "For r=1, the normalized inverse rows are precisely the two "
                        + "homogeneous-internal constructions of (29.17). At odd widths their "
                        + "physical supports are Ico(1,m) and {1,m}; "), Text(
                        "and their region codes on (U,R,{1},{m}) are (10,00,11,01). "
                        + "At even widths their supports are {1,m} and R union {1}; "), Text(
                        "and their region codes are (00,01,11,10). Distinct regions have "
                        + "distinct codes. The internal region has one membership label and "
                        + "the entire exterior is base-labelled, so equal codes always imply "
                        + "equal membership pairs, without any condition on the two boundary labels.")),
                    Paragraph(Text(
                        "homogeneousRoot is Ico(1,m) for odd m and {1,m} for even m. "
                        + "homogeneousSecond records ordered second-path offsets, namely "
                        + "{0,m} for odd m and Icc(1,m) for even m. These offset sets give "
                        + "the physical supports above after translating by m in P. All "
                        + "four sets are even in their applicable branch. homogeneousWords "
                        + "issues exactly their prefix-parity inverses, and homogeneousCode "
                        + "is the corresponding chronological pair of successful differences "
                        + "on every phase, including all exterior sources.")),
                    Paragraph(Text(
                        "Every root begins zero, clearing all legal inherited tails. "
                        + "For odd m its terminal charge at m is zero, so the root ends "
                        + "zero before the all-one second inverse of {0,m}. For even m the "
                        + "second inverse begins zero. Each whole prefix is therefore safe: "
                        + "the second word enters from tail zero or clears the tail immediately, "
                        + "and every word has length m<k. The decoder chooses a phase with "
                        + "its own acquired difference pair and returns that phase's membership "
                        + "component selected by its remembered free value. This uses one "
                        + "preselected literal stream for both values and both original alphabets.")),
                    Paragraph(Text("The native comparison and even-charge identity use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction"),
                        Text("; actual-phase realization and the root-zero result use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges"),
                        Text(". The sum and phase-shift identities use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAttainment"),
                        Text("; the ordered inverse and complete-prefix safety use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse"),
                        Text(". Original history and own-archive feasibility use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection"), Text(".")),
                    Paragraph(Text(
                        "The displayed live script archive contains exactly two issued "
                        + "blocks and 2m bits; mapReplies and flattenWords project those "
                        + "actual archive components. The theorem gives necessary row "
                        + "refinement and the r=1 safe construction. It leaves the complete "
                        + "Pi3/Pi4 conditions, the other r=2 safe assignments, the four-label pivot "
                        + "table, unequal adaptive stopping lengths and exact worst-history "
                        + "prices to their further classification. A script length alone "
                        + "does not assert an optimal actual paid-trace price."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-first-window-nonbase-internal-stream"),
                DeclarationHandle.Create(Owner + "original_first_window_nonbase_internal_stream"),
                H("Two nonbase internal labels: normalized safe literal selection"),
                StatementSource.FromAuthor(Disp(nonbaseStatement)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Retain the full original source, supports, labels and operations above. "
                        + "fullImage is membership[P], of size n. Suppose n=3, the internal "
                        + "image has size two, and it excludes the base pair zero. The admitted "
                        + "condition is odd m or a nonbase membership label at phase one or m, "
                        + "the remaining clause of Pi3 for this branch. The integer one and "
                        + "phaseCast(m) in the formula denote their actual phase-group casts.")),
                    Paragraph(Text(
                        "The internal labels are two distinct nonzero pairs X,Z. Every actual "
                        + "phase has label zero, X or Z: the exterior contributes zero, and "
                        + "the internal two-label image already exhausts the other two labels "
                        + "of fullImage. Put S={h in U: membership(h)=Z}, t=|S| modulo two "
                        + "and e=m modulo two. Choose an orientation flip and boundary code "
                        + "pairs left,right. Internal X and Z have codes (flip,0) and "
                        + "(1+flip,0); every exterior phase has code (0,1). At phases one "
                        + "and m the codes are left and right. Equal codes must represent "
                        + "equal labels, while one label may occupy more than one code.")),
                    Paragraph(Text(
                        "The required parity equations are t+flip*e+left.first+right.first=0 "
                        + "and e+1+left.second+right.second=0 in ZMod(2). At odd widths, "
                        + "changing orientation changes the internal root parity. If both "
                        + "boundary labels are internal, select their canonical codes and "
                        + "orient to make the root even. If exactly one is base, orient the "
                        + "odd internal class to code (1,0), then use (1,1) for the internal "
                        + "boundary and (0,1) for base. If both are base, one may use the "
                        + "spare (1,1) to correct root parity. At even widths, at least one "
                        + "boundary is internal. Give that boundary its canonical code with "
                        + "second bit zero, and give the other second bit one. The orientation "
                        + "and spare code then solve the root equation. The formal selector "
                        + "checks these two equations and separation simultaneously.")),
                    Paragraph(Text(
                        "nonbaseRoot(h) is supportRow(S,h)+flip*supportRow(U,h) plus "
                        + "left.first at h=1 and right.first at h=m. nonbaseSecond uses "
                        + "ordered offsets from m: it is one on Ico(1,m), right.second at "
                        + "offset zero and left.second at offset m. Its interior offsets "
                        + "are exactly the exterior physical phases, including phase zero "
                        + "and the donor m+1. The internal count m-2 has parity e, and "
                        + "the exterior count m-1 has parity e+1; hence both complete "
                        + "ordered rows sum to zero. nonbaseWords is precisely the list "
                        + "of their two prefix-parity inverses. nonbaseCode is their actual "
                        + "chronological difference pair, rather than an unrestricted query.")),
                    Paragraph(Text(
                        "nonbase_even gives both ordered-row sums zero and the root charge "
                        + "at zero under the displayed parity equations. nonbase_charges "
                        + "identifies both windowCharge coordinates with nonbaseCode. "
                        + "Their first-row projections also supply the root calculations "
                        + "for the base-internal donor construction. classIndex sends base, "
                        + "X and Z to 0,1,2; classLabel reverses these three distinct labels, "
                        + "and class_restore gives the exact inverse on their full image.")),
                    Paragraph(Text(
                        "The root charge at zero vanishes, so its first literal bit is "
                        + "zero and it clears every inherited legal tail. Its terminal tail "
                        + "is at most m-1. If right.second is zero, the second word starts "
                        + "zero. If it is one, the exterior charge at offset one toggles "
                        + "the prefix immediately, giving a zero at literal index one. "
                        + "The leading seam run is then at most m<k. The proof applies "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety"),
                        Text(" at that actual zero, and the ordered inverse and clear seam from "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse"),
                        Text(". Thus the complete two-block prefix succeeds for every original "
                        + "value, phase and inherited tail; no arbitrary refining inverse "
                        + "assignment is asserted safe.")),
                    Paragraph(Text(
                        "Conversely, suppose both boundary labels are base and a correct "
                        + "two-block GLOBAL competitor exists. Apply the necessary row "
                        + "theorem above. The two internal nonbase labels have second charge "
                        + "zero and unequal first charges, exhausting both first-coordinate "
                        + "values. If any base-labelled phase also had second charge zero, "
                        + "it would collide with one of those internal labels. Thus the "
                        + "second charge is one at every exterior phase and both boundaries, "
                        + "and zero on U. Its full-phase sum is m+1 modulo two. The required "
                        + "even charge forces m odd. This uses native_two_same through "
                        + "the already established necessary rows, including all stopping "
                        + "and rejection semantics. It introduces no additional "
                        + "mixed-archive transport premise.")),
                    Paragraph(Text(
                        "The common selector issues this same preselected list in both "
                        + "value fibres. Its decoder matches the two differences in its own "
                        + "acquired archive, recovers the membership label, and selects "
                        + "the component belonging to its saved free value. Separately "
                        + "unequal A(v),B(v), arbitrary cross-value coincidences, arbitrary "
                        + "Type universes and arbitrary independently observed bottom are "
                        + "retained. Both original alphabets use these same length-m words. "
                        + "Every live script archive has two issued blocks and 2m bits. "
                        + "This establishes the full physical two-nonbase-internal branch "
                        + "of (29.18). The six base-internal cases, four-label pivot, "
                        + "other sharp obstructions and exact paid-trace prices are "
                        + "separate obligations."))), DescribeRole.Theorem))));
    }
}
