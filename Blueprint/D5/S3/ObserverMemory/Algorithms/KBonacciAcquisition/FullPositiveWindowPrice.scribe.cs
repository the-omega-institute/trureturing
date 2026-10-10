using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class FullPositiveWindowPriceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FullPositiveWindowPrice.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact additional prices on actual full-positive children",
        H("Exact additional prices on actual full-positive children"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fullpositivewindowprice-operationalrequest"),
                DeclarationHandle.Create(Owner + "OperationalRequest"),
                H("One original source at one acquired archive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A request retains the immutable INITIAL record and current record of the same original history, its remembered free output and its whole acquired archive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fullpositivewindowprice-childrequests"),
                DeclarationHandle.Create(Owner + "ChildRequests"),
                H("The whole actual child"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The child contains exactly all original allowed histories matching the free output and the entire chronological archive. Histories at the same phase may have different original tails and lengths. No independently reachable coordinates are substituted for this fiber."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fullpositivewindowprice-selectorlegal"),
                DeclarationHandle.Create(Owner + "SelectorLegal"),
                H("Both original alphabets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every selected complete word respects the selected original alphabet. In the critical width m less than k all m-bit words are internally legal; their seam can still reject."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fullpositivewindowprice-presetpolicy"),
                DeclarationHandle.Create(Owner + "PresetPolicy"),
                H("One child-local literal suffix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected suffix is indexed by additional paid archive length from this actual acquired offset. Stops and decoding depend on the source own complete endpoints. No compatibility with another child or free-value fiber is required."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fullpositivewindowprice-requestfeasible"),
                DeclarationHandle.Create(Owner + "RequestFeasible"),
                H("Correct stopped continuations and paid budgets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One lawful selector returns f of the INITIAL record on every actual request through a stopped paid trace within the additional budget. Remembered INITIAL bottom has its independent free label. Newly reached bottom remains absorbing under the original bit updates. Every complete issued word, including rejection, costs one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fullpositivewindowprice-budgetprice"),
                DeclarationHandle.Create(Owner + "BudgetPrice"),
                H("Attained least finite budgets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The price is the infimum of all feasible natural budgets in the extended naturals. An empty feasible set has infinite price. The exact price theorem exhibits a feasible least natural budget."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fullpositivewindowprice-childadaptiveprice"),
                DeclarationHandle.Create(Owner + "ChildAdaptivePrice"),
                H("Adaptive additional fee"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The adaptive price ranges over every lawful original selector on this whole actual child, with arbitrary own-endpoint stops and literal words."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fullpositivewindowprice-childpresetprice"),
                DeclarationHandle.Create(Owner + "ChildPresetPrice"),
                H("Preset additional fee"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The preset price restricts the same feasible domain to a single literal suffix chosen for this acquired child. The already paid prefix is excluded."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fullpositivewindowprice-full-positive-lower"),
                DeclarationHandle.Create(Owner + "full_positive_lower"),
                H("Every original adaptive competitor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let odd m be at least three and k=m+1. An actual positive child with full support equal to its parent window and one immutable label per surviving phase has at most 2 to the power h distinct labels under any correct original continuation of additional budget h. The actual parent inverse earns common tail one. Actual histories representing labels are selected only for counting; correctness still includes every matched original history. Common-tail compression and the existing exact binary leaf bound supply the inequality for arbitrary actions, waits, repairs, early stops and uniform rejection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fullpositivewindowprice-full-positive-many-attains"),
                DeclarationHandle.Create(Owner + "full_positive_many_attains"),
                H("The actual many-label suffix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For at least three distinct labels, the original physical INITIAL decoder supplies donor-compensated literal words of length d=ceil(log2 n), their exact paid traces and final-endpoint decoding. Its same attained script is made into a preset policy at the acquired archive length. The regular seam and the d=2,n=4 alternative, including m=3, are supplied by the physical decoder. No new question port, clearing block or independently chosen branch stream is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fullpositivewindowprice-binaryexception"),
                DeclarationHandle.Create(Owner + "BinaryException"),
                H("The exact binary obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In coordinates translated by the actual paid index, one label occupies precisely vertices m and m-2 and a different label occupies every other surviving vertex. In absolute coordinates this is H={u+m,u+2m} modulo m+2, where u=am. The translation is a calculation from the known issued count."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fullpositivewindowprice-fullfee"),
                DeclarationHandle.Create(Owner + "fullFee"),
                H("The four exact cases"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fee is zero for one distinct label, two for the exact binary obstruction, one for every other two-label table, and ceil(log2 n) for at least three labels. It counts the distinct label image on actual support rather than phase occurrences."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fullpositivewindowprice-original-full-positive-price"),
                DeclarationHandle.Create(Owner + "original_full_positive_price"),
                H("Original adaptive and child-preset minima"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual acquired archive with the full positive support, both original alphabets and every repeated-label INITIAL table satisfying the per-phase label law, one literal child-preset continuation attains fullFee. Every correct original adaptive competitor pays at least that fee. Consequently the two original additional prices both equal fullFee. The same actual history supplies INITIAL labels, current phase, current scalar and inherited tail."))),
                DescribeRole.Theorem),
            Paragraph(Text("The parent is the actual alternating word beginning and ending in one. Its internal zero earns inherited tail one from every surviving original history. The current phase is INITIAL phase plus (a+1)m. These facts come from full_positive_history_trace; positivity without full support is insufficient.")),
            Paragraph(Text("For a nonconstant binary table the next actual window misses only the vertex m-1 of the child. Its label fixes response zero. The unique non-source donor in that next window compensates parity, and the existing prefix-parity inverse gives a complete literal word. An inverse containing a zero is safe from inherited tail one. The all-one inverse is unsafe exactly for the stated H partition. This is the original shallow classification, with every one-block action tested against the same actual histories.")),
            Paragraph(Text("In the exception the complete zero word is issued and paid at a+1. It clears the inherited tail and gives no label information. The complete word 110 followed by m-3 zeros is then issued at a+2; its charge is exactly H, its leading run two is safe from zero, and the final endpoint returns the INITIAL label. Both words belong to the one actual suffix and cost two.")),
            Paragraph(Text("A constant table stops at the acquired endpoint. The many-label lower bound gives h at least ceil(log2 n), while the physical suffix attains that integer. For binary tables it also rules out zero fee; the separate all-action exception proof supplies the stronger lower bound two. These conclusions concern one actual acquired child and do not give a GLOBAL stream across unrelated siblings or an exact price for every full INITIAL target.")))));
}
