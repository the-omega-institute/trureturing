using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class DonorCorrectionDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.";
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Record(Formula v, Formula j, Formula s) =>
        Call("some", Seq(Langle, Sp, v, Comma, new Formula.Negate(j), Comma, s, Rangle));

    public DocumentDefinition Create()
    {
        var nat = Seq(Mathbb, Grp(F.Id("N"))); var bit = F.Id("Bool");
        var m = F.Id("m"); var k = Subtract(Multiply(D(2), m), D(2));
        var group = Call("ZMod", Add(k, D(1))); var scalar = Call("ZMod", D(2));
        var label = F.Id("Y"); var alphabet = F.Id("alphabet");
        var target = F.Id("f"); var table = F.Id("table"); var pi = F.Id("pi");
        var d = F.Id("d"); var t = F.Id("t"); var j = F.Id("j"); var l = F.Id("l");
        var s = F.Id("s"); var v = F.Id("v"); var c = F.Id("c"); var history = F.Id("history");
        var w = Call("flattenWords", history);
        var sameTable = All("v", scalar, All("j", group, All("s", nat,
            Imp(Lt(s, k), Equal(Apply(target, Record(v, j, s)), Apply(table, j))))));
        var correct = All("history", Call("List", Call("AllowedBlock", k, m, alphabet)),
            Imp(Equal(Call("output", k, w), Call("some", D(0))),
                Exists("c", nat, And(Le(c, d),
                    Equal(Call("execute", k, pi, d, w, Call("some", D(0)), F.Id("nil")),
                        Call("some", Seq(Open, Apply(target, Call("OriginalRecord", k, w)),
                            Comma, c, Close)))))));
        var rows = Call("codingRows", table, pi, d);
        var actions = Call("chargeBlocks", k, m, alphabet, rows);
        var current = Record(v, j, s);
        var archive = Call("fixedBlockArchive", actions, current);
        var preserved = All("t", Call("Fin", d), All("j", group,
            Imp(new Formula.Not(Call("Donor", m, j)),
                Equal(Call("windowCharge", k, m, Call("codingRow", table, pi, d, Call("val", t)),
                    Subtract(j, Multiply(Call("val", t), m))),
                    Call("phaseCharges", table, pi, d, Call("val", t), j)))));
        var statement = All("Y", F.Id("Type"), All("m", nat, All("alphabet", bit,
            All("f", Arrow(Call("Option", Call("LiveRecord", k)), label),
            All("table", Arrow(group, label), All("pi", Call("Selector", m, label), All("d", nat,
            All("v", scalar, All("j", group, All("s", nat,
                Imp(And(Le(D(5), m), sameTable, Le(D(1), d),
                    Le(d, Subtract(Multiply(D(2), m), D(1,0))), correct, Lt(s, k)),
                    And(preserved, Equal(Call("length", actions), d),
                        Equal(archive, Call("chargeArchive", k, m, rows, v, j)),
                        Equal(Call("length", archive), d),
                        new Formula.Not(new Formula.Relation(F.Id("none"),
                            FormulaRelationOperator.MemberOf, archive))))))))))))));
        var presetStatement = All("Y", F.Id("Type"), All("m", nat, All("alphabet", bit,
            All("f", Arrow(Call("Option", Call("LiveRecord", k)), label),
            All("table", Arrow(group, label), All("pi", Call("Selector", m, label), All("d", nat,
                Imp(And(Le(D(5), m), sameTable, Le(D(1), d),
                    Le(d, Subtract(Multiply(D(2), m), D(1,0))), correct),
                    Call("OriginalPresetFeasible", k, m, alphabet, target,
                        Add(d, D(4)))))))))));
        var uniformStatement = All("Y", F.Id("Type"), All("m", nat, All("alphabet", bit,
            All("f", Arrow(Call("Option", Call("LiveRecord", k)), label),
            All("table", Arrow(group, label),
                Imp(And(Le(D(5), m), sameTable),
                    Call("OriginalPresetFeasible", k, m, alphabet, target,
                        Call("uniformHorizon", m))))))));
        var adaptivePrice = Call("GlobalAdaptivePrice", k, m, alphabet, target);
        var presetPrice = Call("GlobalPresetPrice", k, m, alphabet, target);
        var priceStatement = All("Y", F.Id("Type"), All("m", nat, All("alphabet", bit,
            All("f", Arrow(Call("Option", Call("LiveRecord", k)), label),
            All("table", Arrow(group, label),
                Imp(And(Le(D(5), m), sameTable), And(Le(adaptivePrice, presetPrice),
                    Le(presetPrice, Add(adaptivePrice, D(4))),
                    Lt(Add(adaptivePrice, D(4)), Infty))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Six actual donors convert an adaptive charge array into one global preset stream.",
            H("Three-donor correction on the actual calendar"), Blocks(
                Describe.Lean(DescribeId.Create("outside"),
                    DeclarationHandle.Create(Owner + "outside"), H("Non-donor entries"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("outside(a,r,i) is zero at r,r+1,r+2 and equals a(i) "
                        + "at every other natural offset."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("corrected-row"),
                    DeclarationHandle.Create(Owner + "correctedRow"), H("The repaired ordered row"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Let u be the sum of a(h) over h<r and z the sum of "
                        + "outside(a,r,h) over h<=m, in ZMod(2). The corrected row equals outside "
                        + "plus u at r and u+z at r+2. It is zero at r+1. The three donors absorb "
                        + "full-window parity and cancel the prefix through r, making the literal "
                        + "inverse zero at that mark. All other entries remain unchanged."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("donor"),
                    DeclarationHandle.Create(Owner + "Donor"), H("Six ordinary INITIAL phases"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Donor(m,j) means j=m-4+e*m+delta in ZMod(2m-1), "
                        + "for natural e<2 and delta<3. The six phases retain their original "
                        + "INITIAL labels; the theorem does not remove these sources."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("coding-row"),
                    DeclarationHandle.Create(Owner + "codingRow"), H("Chronological corrected charges"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("At issued index t, first read the own-path array at "
                        + "INITIAL phase t*m+h in the cyclic phase group, for each local offset h. "
                        + "Then correct that row at local mark m-4-floor(t/2). The physical word is "
                        + "its prefix-parity inverse, with exactly m literal bits."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("original-donor-coding-archive"),
                    DeclarationHandle.Create(Owner + "original_donor_coding_archive"),
                    H("Native shared coding archive and unchanged non-donors"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The display uses k=2m-2. codingRows(table,pi,d) is "
                        + "List.ofFn(t:Fin(d) => codingRow(table,pi,d,val(t))). Proof arguments to "
                        + "chargeBlocks, output, execute and OriginalRecord are omitted; nil is "
                        + "the empty acquired archive. flattenWords is the original history flatMap "
                        + "of complete literal words. Cyclic subtraction includes the cast of the "
                        + "chronological index times m. Y is arbitrary, including higher universes.")),
                        Paragraph(Text("The arbitrary correct controller supplies the root-zero "
                            + "and support facts from "),
                            Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges"),
                            Text(". The root mark is m-4>0, so the correction preserves its zero "
                            + "first entry. This clears every inherited legal tail. The marks are "
                            + "nonincreasing, giving each chronological seam inequality; all three "
                            + "corrected donor positions lie within the ordered window. The parity "
                            + "and prefix-zero identities therefore permit direct use of "),
                            Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety"),
                            Text(" for the full literal archive, under either original alphabet.")),
                        Paragraph(Text("Write t=2h+e. The actual calendar identity 2m=1 in "
                            + "ZMod(2m-1) puts each corrected offset at INITIAL phase m-4+e*m+delta. "
                            + "The horizon bound keeps h<=m-4, so natural subtraction has not "
                            + "truncated this placement. Outside these six phases, the full-window "
                            + "charge remains exactly the original own-path coordinate. Off the "
                            + "physical window both charges are zero. The same words work for both "
                            + "INITIAL scalars; only their own scalar archives are read.")),
                        Paragraph(Text("This is the first d-block coding portion. Donor coordinates "
                            + "have been changed and require the four additional identifying rows. "
                            + "Those rows, their seam safety, label decoding, other adaptive horizons, "
                            + "finite price attainment and the four-block price inequality are "
                            + "outside this coding-prefix theorem."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("pair-row"),
                    DeclarationHandle.Create(Owner + "pairRow"), H("One literal occupied bit"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("pairRow(r,h) is one exactly at h=r or h=r+1, "
                        + "and zero elsewhere. Its prefix-parity inverse is the complete word "
                        + "whose only true bit is at local position r."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("suffix-row"),
                    DeclarationHandle.Create(Owner + "suffixRow"), H("Four actual identifying rows"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("suffixRow(m,d,t) is pairRow at local position "
                        + "m-4-floor((d+t)/2)+floor(t/2). For t=0,1,2,3 its INITIAL "
                        + "support is the consecutive pair beginning at "
                        + "m-4+((d+t) mod 2)*m+floor(t/2). Thus the first and second "
                        + "occurrences of each parity test the first and second edge of "
                        + "its own donor triple on the actual moving calendar."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("conversion-rows"),
                    DeclarationHandle.Create(Owner + "conversionRows"), H("The complete paid prefix"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("conversionRows(table,pi,d) lists d+4 rows: "
                        + "codingRow(table,pi,d,t) when t<d, and suffixRow(m,d,t-d) otherwise. "
                        + "Every row is issued as its m-bit prefix-parity inverse."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("original-donor-preset-feasible"),
                    DeclarationHandle.Create(Owner + "original_donor_preset_feasible"),
                    H("One global stream with four additional paid blocks"),
                    StatementSource.FromAuthor(Disp(presetStatement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The display uses k=2m-2 and the same flattenWords "
                        + "convention as the coding-prefix theorem. Proof arguments are omitted. "
                        + "OriginalPresetFeasible is the original global interface from "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction"),
                        Text(". It quantifies one literal stream shared by both free scalar "
                            + "values and all archives, an own-archive stopping rule, lawful "
                            + "issued words under either original alphabet, free initial bottom, "
                            + "and correct bounded execution on every original complete-word history.")),
                        Paragraph(Text("The coding marks are m-4-floor(t/2). The first literal "
                            + "bit is zero and clears every inherited legal tail. In the four suffix "
                            + "words the occupied position is at most m-3, so their final bit is "
                            + "zero. Use that final bit as the suffix mark. At the transition from "
                            + "coding to suffix, the last coding mark is at least one; this proves "
                            + "the same chronological seam inequality used for the whole coding "
                            + "prefix. All d+4 blocks therefore execute successfully on every live "
                            + "INITIAL record. No interior endpoint or reset is needed.")),
                        Paragraph(Text("In the two even-index suffix coordinates the three lower "
                            + "donors have codes 10,11,01, and in the two odd-index coordinates "
                            + "the upper donors have the same codes. The other two coordinates "
                            + "are zero. These six nonzero suffix columns are distinct, whereas "
                            + "every non-donor has suffix 0000. Equal full columns involving a "
                            + "donor therefore identify its original phase. For two non-donors, "
                            + "the unchanged coding coordinates separate unequal original labels.")),
                        Paragraph(Text("Each live source subtracts successive own scalar endpoints, "
                            + "starting from its own remembered free value. The scalar offset "
                            + "cancels. A classical decoder chooses a phase having that difference "
                            + "column; all such phases have the same table label. The finite words "
                            + "extend by fixed zero words to one infinite literal stream. Live "
                            + "sources stop after the d+4 displayed words and pay exactly d+4 "
                            + "complete-block fees. Initial bottom stops immediately with f(none). "
                            + "The paid trace law also counts a complete issued rejecting word "
                            + "when present, rather than only its accepted part.")),
                        Paragraph(Text("The hypothesis is correctness of the supplied controller "
                            + "on the entire free-zero original-history fibre. It contains no "
                            + "assumed preset construction, suffix separation or safety property. "
                            + "The range 1<=d<=2m-10 is retained; the zero and one depth optimizations, "
                            + "uniform fallback at other horizons, minimum-cost attainment and "
                            + "the unconditional full-family price inequality are separate results."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("uniform-horizon"),
                    DeclarationHandle.Create(Owner + "uniformHorizon"),
                    H("Uniform finite horizon"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "uniformHorizon(m)=2m-4-min(2,m-5)=max(2m-6,m+1), for m>=5. "
                        + "It equals six at width five, seven at width six, and 2m-6 thereafter."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("uniform-occupied"),
                    DeclarationHandle.Create(Owner + "uniformOccupied"),
                    H("Strictly internal actual positions"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "Put q=min(2,m-5). At issued index t the sole occupied bit is at "
                        + "i=m-2-q if 4<=t<4+q, and at i=1 otherwise. Every such bit is "
                        + "strictly internal. Both head and tail bits are zero."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("original-uniform-phase-preset"),
                    DeclarationHandle.Create(Owner + "original_uniform_phase_preset"),
                    H("Full-family native uniform fallback"),
                    StatementSource.FromAuthor(Disp(uniformStatement)),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "The display uses k=2m-2, arbitrary Y, and omits proof arguments. "
                        + "The schedule above is a literal word of length m at every issued index. "
                        + "Its charge tests the actual INITIAL edge {t*m+i,t*m+i+1} modulo 2m-1. "
                        + "At m>=7 the missing edge starts are {0,3,m-1,m,m+3}. Every other start "
                        + "has an explicitly constructed chronological index. The four neighboring "
                        + "edge tests imply that equal incidence columns have equal vertices. "
                        + "The width-five and width-six branches prove injectivity for the exact "
                        + "finite schedule by kernel decision and are consumed by the uniform proof.")),
                        Paragraph(Text("The zero heads clear every legal inherited tail; the "
                            + "zero tails make successive seams safe. Native execution therefore "
                            + "produces the incidence column in each own endpoint-difference archive. "
                            + "A classical inverse identifies the INITIAL phase and returns its "
                            + "unchanged table label. The empty live column is an ordinary successful "
                            + "column, never bottom or rejection. One fixed stream serves both free "
                            + "values and all original histories under either original alphabet. "
                            + "Live executions pay exactly uniformHorizon(m) complete blocks; initial bottom "
                            + "stops freely. No construction or safety premise remains.")),
                        Paragraph(Text("Incidence tests are the mature test-cover interpretation "
                            + "of this separator; see de Bontridder et al., Approximation algorithms "
                            + "for the test cover problem, Mathematical Programming 98, 477-491, "
                            + "Lemma 4.2, DOI 10.1007/s10107-003-0414-6. The Lean proof supplies its "
                            + "own actual calendar, separating columns and native execution bridge. "
                            + "No originality or finite numerical extrapolation is claimed."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("original-adaptive-feasible"),
                    DeclarationHandle.Create(Owner + "OriginalAdaptiveFeasible"),
                    H("One original global adaptive controller"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "OriginalAdaptiveFeasible(k,m,hk,alphabet,f,d) means one legal Selector "
                        + "stops immediately on initial bottom with f(none), and its original "
                        + "execution succeeds within d issued complete words on every original "
                        + "history, using that history's own free endpoint. Both free-value "
                        + "fibres share this same selector. Rejection remains paid and absorbing."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("global-adaptive-price"),
                    DeclarationHandle.Create(Owner + "GlobalAdaptivePrice"),
                    H("Global adaptive minimum"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "GlobalAdaptivePrice is BudgetPrice of OriginalAdaptiveFeasible, the "
                        + "infimum of feasible natural budgets in extended naturals. It is "
                        + "infinity when no natural budget is feasible."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("global-preset-price"),
                    DeclarationHandle.Create(Owner + "GlobalPresetPrice"),
                    H("Global preset minimum"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "GlobalPresetPrice is BudgetPrice of the existing OriginalPresetFeasible "
                        + "interface. The stream is shared across both initial scalars and all "
                        + "running archives; stopping and decoding use each execution's own archive."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("original-uniform-paid-feedback-bound"),
                    DeclarationHandle.Create(Owner + "original_uniform_paid_feedback_bound"),
                    H("Unconditional four-block paid-feedback bound"),
                    StatementSource.FromAuthor(Disp(priceStatement)),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "The display uses k=2m-2 and omits the positive-k proof argument. "
                        + "The arbitrary target has the same phase-label table for both free "
                        + "values and every legal tail; f(none) is arbitrary. The costs are true "
                        + "global original-history costs, not separately optimized fibre prices.")),
                        Paragraph(Text("The uniform fallback supplies a finite preset budget. "
                            + "Preset inclusion supplies an adaptive budget. Well-ordering of the "
                            + "natural budgets attains each minimum, with its original one-selector "
                            + "or one-stream witness. A correct zero-budget controller forces a "
                            + "constant table. At depth one, a stopping root is constant; otherwise "
                            + "the root-zero charge forces a false first bit. This same issued word "
                            + "is safe for every inherited tail, and its own scalar difference "
                            + "decodes the common table for both free values.")),
                        Paragraph(Text("For 1<=d<=2m-10 use the six-donor construction. "
                            + "Outside that range and with d>=2, uniformHorizon(m)<=d+4: width five "
                            + "uses six blocks, width six uses seven once d>=3, and m>=7 uses "
                            + "2m-6 blocks once d>=2m-9. Budget extension preserves the exact "
                            + "returned fee through the native paid-trace equivalence. Applying "
                            + "this conversion to the attained adaptive minimum yields the upper "
                            + "inequality. Preset inclusion yields the lower inequality, and both "
                            + "attained natural minima prove finiteness. No attainment, "
                            + "separation, construction or safety hypothesis is left in the statement.")),
                        Paragraph(Text("This result is the full same-table upper price bound. "
                            + "It does not assert a sharp lower gap, supremum equality, or "
                            + "the separate attainment claim in section 31."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("calendar"),
                DeclarationHandle.Create(Owner + "calendar"), H("The near-critical literal calendar"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every m>=5 and all natural h, eps and i, in ZMod(2m-1) the vertex ((2h+eps)m+i) equals h+eps*m+i. The identity follows from 2m=1 modulo 2m-1. It supplies physical window positions, rather than acquired observations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("script-global-preset"),
                DeclarationHandle.Create(Owner + "script_global_preset"), H("A fixed original script supplies one common preset"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any label universe Y, k>=2, m<k, either original alphabet, immutable target f, fixed finite list words of m-bit literals and decoder decode(saved scalar,own archive), assume the scriptArchive at every scalar, phase and legal inherited tail decodes to f of that INITIAL record. Then OriginalPresetFeasible holds at words.length. Every actual history is included. Initial bottom returns f(bottom) freely; live sources use one literal stream extending words by zero words, stop at the final acquired endpoint and pay the full script length. The actual archive and execution follow the existing original_final_script and native paid-trace equivalence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("row-readings-index"),
                DeclarationHandle.Create(Owner + "row_readings_index"), H("A scheduled row within the own reading sequence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all natural k,m,t, any finite list of charge rows and phase j, entry t of rowReadings(k,m,rows,j) is obtained by mapping rows[t] to the optional scalar windowCharge(k,m,row,j-t*m). The index uses the chronological paid position. The formula describes a fixed physical reading sequence; it grants no endpoint after a source has stopped."))), DescribeRole.Theorem))));
    }
}
