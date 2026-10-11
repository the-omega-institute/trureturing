using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class FirstWindowBoundaryFourLabelsDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryFourLabels.";
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
        var v = F.Id("v"); var s = F.Id("s"); var z = F.Id("z"); var d = F.Id("d");
        var support = F.Id("H"); var labelA = F.Id("A"); var labelB = F.Id("B");
        var f = F.Id("f"); var alphabet = F.Id("alphabet");
        var g = F.Id("g"); var subset = F.Id("S"); var a = F.Id("a");
        Formula MemberPair(Formula q) => Call("membership", m, support, q);
        Formula Code(Formula q) => Apply(g, MemberPair(q));
        Formula NotEqual(Formula q, Formula r) => new Formula.Not(Equal(q, r));
        Formula Iff(Formula q, Formula r) => new Formula.Logic(q, FormulaLogicOperator.Iff, r);
        var initial = Call("some", Seq(Langle, Sp, v, Comma, new Formula.Negate(j), Comma, s, Rangle));
        var inside = All("v", scalar, All("h", nat,
            Imp(Call("Member", h, Apply(support, v)), And(Le(D(1), h), Le(h, m)))));
        var distinct = All("v", scalar, NotEqual(Apply(labelA, v), Apply(labelB, v)));
        var target = All("v", scalar, All("j", phase, All("s", nat,
            Imp(Lt(s, k), Equal(Apply(f, initial),
                Call("ifThenElse", Call("Member", Call("val", j), Apply(support, v)),
                    Apply(labelB, v), Apply(labelA, v)))))));
        var image = Call("internalImage", m, support); var pivot = Call("pivot", m, support);
        var pi = And(Le(Call("card", Call("erase", image, pivot)), D(1)),
            Imp(Call("Member", D(0), image), Equal(pivot, D(0))));
        var outlier = All("d", pair, Iff(All("z", pair, Imp(NotEqual(z, d), NotEqual(
            Call("natCast", Call("multiplicity", m, support, z)),
            Call("natCast", Call("multiplicity", m, support, d))))), Equal(pivot, d)));
        var feasible = Call("OriginalPresetFeasible", k, m, alphabet, f, D(2));
        var left = Call("left", a); var right = Call("right", a);
        var flip = Call("flip", a); var exterior = Call("exterior", a); var donor = Call("donor", a);
        var words = Call("baseWords", m, subset, a); var archive = Call("scriptArchive", words, initial);
        var firstParity = Equal(Add(Add(Add(Call("natCast", Call("card", subset)),
            Multiply(flip, Call("natCast", m))), Call("fst", left)), Call("fst", right)), D(0));
        var secondParity = Equal(Add(Add(Add(Multiply(exterior, Add(Call("natCast", m), D(1))),
            donor), Call("snd", left)), Call("snd", right)), D(0));
        var seam = Or(Equal(Call("snd", right), D(0)), Equal(Add(exterior, donor), D(1)),
            Equal(Call("fst", right), D(0)));
        var details = All("v", scalar, All("j", phase, All("s", nat,
            Imp(Lt(s, k), And(
                Equal(Call("endpointDifferences", Call("some", v), Call("mapReplies", archive)),
                    Call("list", Call("some", Call("fst", Code(j))), Call("some", Call("snd", Code(j))))),
                Equal(Call("length", archive), D(2)),
                Equal(Call("length", Call("flattenWords", archive)), Multiply(D(2), m)))))));
        var assignment = Call("BaseAssignment", D(0), Call("snd", Apply(g, D(0))), D(0),
            Code(Call("phaseCast", D(1))), Code(Call("phaseCast", m)));
        var subsetDefinition = Call("filter", Call("Ico", D(2), m),
            Call("firstCodeEqualsOne", g, m, support));
        var witnesses = Exists("g", Arrow(pair, pair), Exists("S", Call("Finset", nat),
            Exists("a", F.Id("BaseAssignment"), And(Call("Bijective", g),
                Equal(Apply(g, pivot), D(0)), Equal(Call("fst", Apply(g, D(0))), D(0)),
                All("z", pair, Imp(Call("Member", z, image), Equal(Call("snd", Apply(g, z)), D(0)))),
                Equal(subset, subsetDefinition), Equal(a, assignment),
                All("h", nat, Imp(Call("Member", h, subset), And(Le(D(2), h), Lt(h, m)))),
                firstParity, secondParity, seam,
                All("j", phase, Equal(Call("baseCode", m, subset, a, j), Code(j))),
                Equal(Call("length", words), D(2)), feasible, details))));
        var result = And(outlier, Iff(feasible, pi), Imp(pi, witnesses));
        var statement = All("Y", F.Id("Type"), All("m", nat,
            All("alphabet", F.Id("Bool"), All("H", Arrow(scalar, Call("Finset", nat)),
            All("A", Arrow(scalar, y), All("B", Arrow(scalar, y),
            All("f", Arrow(Call("Option", Call("LiveRecord", k)), y),
            Imp(And(Le(D(5), m), inside, distinct, target,
                Equal(Call("card", Call("fullImage", m, support)), D(4))), result))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Four distinct membership labels have exact two-block compatibility on the complete original first-window source.",
            H("Saturated four-label first-window boundaries"),
            Blocks(Describe.Lean(
                DescribeId.Create("original-first-window-four-label-compatibility"),
                DeclarationHandle.Create(Owner + "original_first_window_four_label_compatibility"),
                H("The phase-once pivot and safe Pi4 construction"),
                StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix m>=5, k=2m-2 and P=ZMod(2m-1). The arbitrary supports H(0),H(1) "
                        + "lie in B={1,...,m}; ell is their ordered membership pair. Its full image has four "
                        + "labels. The output labels A(v),B(v) differ separately for each free value, while "
                        + "all cross-value coincidences remain allowed. Y is an arbitrary type, without a "
                        + "finite-type hypothesis, and the separately observed bottom label is arbitrary. "
                        + "The theorem retains both original alphabets, every actual value and phase, all "
                        + "legal inherited tails, and unknown legal or rejected histories.")),
                    Paragraph(Text("multiplicity(m,H,z) is the number of phases with ell(j)=z. Its domain is "
                        + "the phase set itself, so each phase contributes once; histories and tails do not "
                        + "repeat a contribution. pivot is the sum of ell(j) over all phases in the pair "
                        + "vector space. Since 2m-1 is odd, one or three multiplicity parities are odd. The "
                        + "first conclusion identifies pivot as the unique label whose parity differs from "
                        + "the other three. It includes both parity patterns. Pi4 means that erasing this "
                        + "label from the internal image leaves at most one label, and that an internal "
                        + "base occurrence forces the pivot to be base.")),
                    Paragraph(Text("Necessity uses the actual common scheduled rows. Equal row pairs refine "
                        + "both membership coordinates, including sources with different stopping times. "
                        + "Four labels exhaust four binary codes. Choosing one representative per label "
                        + "gives an injective, hence bijective, code map; surjectivity then forces every "
                        + "phase of one label to have that same code. This no-splitting statement uses four "
                        + "labels. It imposes no corresponding restriction on three-label families.")),
                    Paragraph(Text("For a bijection g of the four pair vectors, the sum of g(ell(j)) is "
                        + "g(pivot). This follows by grouping the phases by their four labels and using "
                        + "the odd total multiplicity. Both physical rows are even, so g(pivot)=00. The "
                        + "second row is zero on U={2,...,m-1}, leaving only codes 00 and 10 internally. "
                        + "Thus at most one internal label differs from the pivot. If base occurs internally, "
                        + "its second bit is zero there and its first bit is zero at exterior phase zero; "
                        + "its code is therefore 00 and bijectivity forces pivot=base.")),
                    Paragraph(Text("For sufficiency the internal labels together with base and the two "
                        + "boundary labels fill the four-label set. Select a bijection with pivot code 00, "
                        + "first bit zero on base and second bit zero on the internal image. Its normalized "
                        + "boundary codes additionally satisfy the displayed seam disjunction. When the "
                        + "pivot differs from base, base has code 01, so every exterior phase, including "
                        + "m+1, has second charge one. When the pivot is base, the normalized last "
                        + "boundary has first charge zero, giving a zero-ending root before a possible "
                        + "all-one successor. These are the normalized alternatives of 29.20-29.22.")),
                    Paragraph(Text("S contains exactly those internal phases whose selected first bit is "
                        + "one. BaseAssignment has flip=0, exterior equal to the selected base second bit, "
                        + "donor=0, and the selected codes at phases one and m. The phase sum is zero by "
                        + "g(pivot)=00. Expanding its first coordinate gives the first displayed row-parity "
                        + "equation; expanding the second counts m-1 exterior phases and the two boundaries, "
                        + "giving the second equation. The actual baseCode equals g(ell(j)) at every phase, "
                        + "including both boundaries, phase zero and every exterior donor.")),
                    Paragraph(Text("baseWords is the ordered prefix-parity inverse of these two even physical "
                        + "rows. The root begins zero and clears every inherited tail. The seam disjunction "
                        + "means the successor begins zero, has a zero at literal index one after its "
                        + "leading one, or enters from a zero-ending root. In the middle case the root tail "
                        + "is at most m-1 and the leading run adds at most one, below k=2m-2. In the last "
                        + "case an all-one length-m successor is safe because m<k. Thus the entire "
                        + "two-block prefix succeeds for every original source. The exact base_script_code "
                        + "supplier establishes its own consecutive endpoint differences.")),
                    Paragraph(Text("Each source inverts the bijection from its own acquired differences, "
                        + "then uses its remembered free value to select A(v) or B(v). A single literal "
                        + "stream serves both values; no archive or output is borrowed from another source. "
                        + "Initial bottom stops freely. Every live displayed script has two acquired blocks "
                        + "and 2m emitted bits. These script counts do not themselves establish an exact "
                        + "optimal PaidTrace price, an adaptive branch price, or the equivalent boundary "
                        + "rows of table 29.6.")),
                    Paragraph(Text("The physical inverse, normalized code and inherited-tail seam execution use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryCompatibility"),
                        Text(". Actual common-row necessity uses "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryCodes"),
                        Text(". Phase support sums use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAttainment"),
                        Text(". Actual histories and one common preset stream use "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection"), Text("."))),
                DescribeRole.Theorem))));
    }
}
