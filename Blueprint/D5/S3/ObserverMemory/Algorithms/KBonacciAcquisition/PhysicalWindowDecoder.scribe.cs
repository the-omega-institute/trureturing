using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class PhysicalWindowDecoderDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One physical suffix and final-only original INITIAL decoder.",
        H("Donor rows, both physical branches and exact final decoding"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("physical-window-vertexbit"),
                DeclarationHandle.Create(Owner + "vertexBit"),
                H("One code coordinate at each ordered vertex"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A selected label code supplies a scalar bit at each ordered child vertex. Repeated occurrences of one label retain their separate vertices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-window-physicalcharge"),
                DeclarationHandle.Create(Owner + "physicalCharge"),
                H("The donor-compensated actual charge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On each of the m+1 child vertices the charge is its selected code coordinate. At the absent donor m+1 it is the sum over all child vertices, counting every repetition. The selected unavailable vertex contributes zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-window-actualrow"),
                DeclarationHandle.Create(Owner + "actualRow"),
                H("Rows at their actual issued indices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coordinate i rotates the physical charge to the complete window beginning at (i+1)m modulo m+2. Offsets zero through m are the full ordered window."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-window-actualrows"),
                DeclarationHandle.Create(Owner + "actualRows"),
                H("All code coordinates in order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There is exactly one ordered charge row for each of the d code coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-window-donor-rows-inverse"),
                DeclarationHandle.Create(Owner + "donor_rows_inverse"),
                H("Parity and the direct literal inverse"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every m at least three, every repeated-label table, fitting coordinate dimension, selected unary zeros and each coordinate, the unavailable offset m+1 is zero and the complete row has even charge. The native short-window inverse directly realizes this row. Its first and last literal bits are zero exactly when the corresponding endpoint charges are zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-window-regular-rows-safe"),
                DeclarationHandle.Create(Owner + "regular_rows_safe"),
                H("The regular Selection supplies every seam zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For m at least three and d at least two, the regular selected code lists force the first row head zero and safeRows for all ordered rows. Each later common boundary has zero in at least one adjacent literal bit. No additional safety hypothesis is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-window-issued-phase-code"),
                DeclarationHandle.Create(Owner + "issued_phase_code"),
                H("The actual issued-phase code"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every prior archive length a, child vertex v and coordinate i, the literal row at actual issued index a+i+1 increments the native scalar by that vertex label code coordinate. The modular phase includes the complete prior archive rotation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-window-exceptional-row-coordinates"),
                DeclarationHandle.Create(Owner + "exceptional_row_coordinates"),
                H("The exact four-label charges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit four-label code assignment at dimension two makes the first head charge zero, its last and preceding charges one, and the second first three charges 1,0,1. This holds for every m at least three, including m=3, with arbitrary repeated occurrences elsewhere in the table."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-window-exceptional-literal-execution"),
                DeclarationHandle.Create(Owner + "exceptional_literal_execution"),
                H("The exceptional two-word seam"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every incoming scalar, phase and valid tail, the exact selected first word starts zero and ends 01, with terminal tail exactly one. The second word begins 110. Its crossing run is three, strictly below k=m+1 including m=3. The first native step succeeds and the second succeeds by first_zero_block_exact, without safeRows or a repair word."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-window-scriptarchive"),
                DeclarationHandle.Create(Owner + "scriptArchive"),
                H("The actual fixed-script archive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Recursively issue every complete word and pair it with that source record's own endpoint. The script does not stop early, including on rejection."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-window-finalselector"),
                DeclarationHandle.Create(Owner + "finalSelector"),
                H("The forced-final archive-only selector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selector indexes the prescribed words by its own archive length after the acquired prefix. It issues every available prescribed word before calling the decoder on its own suffix archive. It reads no source phase, hidden clock or sibling reply."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-window-original-final-script"),
                DeclarationHandle.Create(Owner + "original_final_script"),
                H("The original selector pays the exact script length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary label type, k at least two, block width, fixed complete-word list, decoder, given original history, free reading and acquired prefix, the prescribed selector has a PaidTrace issuing exactly that list. The issued archive length and returned original fee both equal the full script length; the decoder is called only after every word. Rejecting words are still paid. This theorem alone does not assert decoder correctness or successful endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-window-actualwords"),
                DeclarationHandle.Create(Owner + "actualWords"),
                H("The fixed physical suffix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Map every selected ordered donor row through the native prefix-parity inverse, in code coordinate order. Each complete word has width m and is legal in both original alphabets because m is less than k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-window-endpointdifferences"),
                DeclarationHandle.Create(Owner + "endpointDifferences"),
                H("Only own-endpoint differences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subtract the remembered scalar from the next actual endpoint and continue from that endpoint. Rejection is retained as an unavailable difference; no source coordinate is read."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-window-physical-endpoint-codes"),
                DeclarationHandle.Create(Owner + "physical_endpoint_codes"),
                H("Both branches give all code coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary odd m at least three, fitting d at least two, repeated-label table and actual Selection, each child vertex starting at the common value and inherited tail one executes the same d literal words. Every endpoint succeeds, and its own successive differences equal all that vertex label code coordinates. The regular branch uses safeRows implied by Selection; the exceptional branch uses the exact terminal01 and prefix110 proof. Both alphabets remain universal. Each supplied native starting record determines its own actual endpoint sequence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-window-codevector"),
                DeclarationHandle.Create(Owner + "codeVector"),
                H("The full final code vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected binary code is represented as d successful endpoint differences in their original coordinate order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-window-decodearchive"),
                DeclarationHandle.Create(Owner + "decodeArchive"),
                H("Decode only the final own archive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Match the final own-endpoint differences to the fixed selected code table and return the matching label. A fallback exists only for transcripts outside the stated compatible source fiber."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-window-original-physical-initial-decoder"),
                DeclarationHandle.Create(Owner + "original_physical_initial_decoder"),
                H("One complete original-source physical INITIAL decoder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For odd m at least three and k=m+1, fix either original alphabet, an arbitrary acquired archive with remembered free scalar and prior endpoint, a successful positive parent, full surviving phase support equal to its physical window, and the assumed per-phase factorization of immutable INITIAL labels. If the actual rotated table has at least three distinct labels, let d be its binary ceiling logarithm. There exist injective selected codes and one archive-only original selector issuing the same complete donor-compensated suffix on every given original history compatible with that same entire archive. Every issued endpoint succeeds; the actual issued words equal the displayed suffix and their number is exactly d. The final own-endpoint differences equal the entire selected code of a label explicitly equal to f(INITIAL). The prescribed selector has a same-record PaidTrace and returns the immutable f(INITIAL) in the original execute with exact additional fee d. Every emitted word is legal; no early stop, omitted paid word, wait, reset, repair, hidden observation or sibling information is used. The proof derives each history's actual current phase, scalar and tail one from OriginalAcquiredTrace; arbitrary repeated labels remain in scope. This is suffix attainment, not a minimum-price or GLOBAL theorem."))),
                DescribeRole.Theorem)
        )));
}
